import Mathlib.Tactic.FinCases
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_818

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def edgePairs : List (ℕ × ℕ) := [(0, 1), (0, 5), (1, 2), (2, 3), (2, 7), (3, 4), (3, 6), (4, 5)]

def wireIndex (i : ℕ) : Fin 8 := ⟨i % 8, Nat.mod_lt _ (by decide)⟩

theorem index_val (v : Fin 8) : wireIndex v.val = v := by
  apply Fin.ext
  exact Nat.mod_eq_of_lt v.isLt

theorem edge_bounds : ∀ e ∈ edgePairs, e.1 < 8 ∧ e.2 < 8 := by
  decide

def edgeBool (x : Fin 8 → Bool) : Bool :=
  edgePairs.any (fun e => x (wireIndex e.1) && x (wireIndex e.2))

theorem edge_spec (x : Fin 8 → Bool) :
    edgeBool x = true ↔ ∃ u v : Fin 8, (u.val, v.val) ∈ edgePairs ∧ x u = true ∧ x v = true := by
  simp only [edgeBool, List.any_eq_true, Bool.and_eq_true]
  constructor
  · rintro ⟨⟨a,b⟩, he, ha, hb⟩
    obtain ⟨ha',hb'⟩ := edge_bounds (a,b) he
    refine ⟨wireIndex a, wireIndex b, ?_, ha, hb⟩
    change (a % 8, b % 8) ∈ edgePairs
    simpa only [Nat.mod_eq_of_lt ha', Nat.mod_eq_of_lt hb'] using he
  · rintro ⟨u, v, he, hu, hv⟩
    exact ⟨(u.val, v.val), he, by simpa only [index_val] using hu, by simpa only [index_val] using hv⟩

def circuit : Circuit where
  gates := [⟨.or, [1, 5]⟩,
    ⟨.and, [0, 8]⟩,
    ⟨.or, [1, 3]⟩,
    ⟨.or, [10, 7]⟩,
    ⟨.and, [2, 11]⟩,
    ⟨.or, [4, 6]⟩,
    ⟨.and, [3, 13]⟩,
    ⟨.and, [4, 5]⟩,
    ⟨.or, [9, 12]⟩,
    ⟨.or, [16, 14]⟩,
    ⟨.or, [17, 15]⟩]
  output := 18

theorem binary : FanInTwo circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

def Recorded (t : ℕ → Bool) : ℕ → List Gate → Prop
  | _, [] => True
  | k, g :: gs => (∀ i ∈ g.inputs, i < k) ∧ g.op.eval (g.inputs.map t) = t k ∧ Recorded t (k+1) gs

def snapshot (t : ℕ → Bool) (k : ℕ) : List Bool := List.ofFn (fun i : Fin k => t i.val)

theorem read_snapshot (t : ℕ → Bool) (k i : ℕ) (hi : i < k) : (snapshot t k).getD i false = t i := by
  simp [snapshot, List.getD_eq_getElem?_getD, hi]

theorem next_snapshot (t : ℕ → Bool) (k : ℕ) : snapshot t (k+1) = snapshot t k ++ [t k] :=
  List.ofFn_succ_last

theorem gate_and (t : ℕ → Bool) (a b : ℕ) :
    GateOp.and.eval ([a,b].map t) = (t a && t b) := by
  simp [GateOp.eval]

theorem gate_or (t : ℕ → Bool) (a b : ℕ) :
    GateOp.or.eval ([a,b].map t) = (t a || t b) := by
  simp [GateOp.eval]

theorem fold_trace (t : ℕ → Bool) (gs : List Gate) (k : ℕ) (h : Recorded t k gs) :
    gs.foldl (fun s g => s ++ [g.op.eval (g.inputs.map (fun i => s.getD i false))]) (snapshot t k) =
      snapshot t (k+gs.length) := by
  induction gs generalizing k with
  | nil => simp
  | cons g gs ih =>
    obtain ⟨bounds, value, rest⟩ := h
    have same : g.inputs.map (fun i => (snapshot t k).getD i false) = g.inputs.map t :=
      List.map_congr_left (fun i hi => read_snapshot t k i (bounds i hi))
    simp only [List.foldl_cons, same, value, ← next_snapshot, ih _ rest, List.length_cons]
    congr 1
    omega

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
theorem computes (x : Fin 8 → Bool) : circuit.eval (List.ofFn x) = edgeBool x := by
  let wires : List Bool := [x 0,
    x 1,
    x 2,
    x 3,
    x 4,
    x 5,
    x 6,
    x 7,
    (x 1 || x 5),
    (x 0 && (x 1 || x 5)),
    (x 1 || x 3),
    ((x 1 || x 3) || x 7),
    (x 2 && ((x 1 || x 3) || x 7)),
    (x 4 || x 6),
    (x 3 && (x 4 || x 6)),
    (x 4 && x 5),
    ((x 0 && (x 1 || x 5)) || (x 2 && ((x 1 || x 3) || x 7))),
    (((x 0 && (x 1 || x 5)) || (x 2 && ((x 1 || x 3) || x 7))) || (x 3 && (x 4 || x 6))),
    ((((x 0 && (x 1 || x 5)) || (x 2 && ((x 1 || x 3) || x 7))) || (x 3 && (x 4 || x 6))) || (x 4 && x 5))]
  let t := fun i => wires.getD i false
  have valid : Recorded t 8 circuit.gates := by
    refine ⟨by decide, ?_, ?_⟩
    · rw [gate_or]
      rfl
    refine ⟨by decide, ?_, ?_⟩
    · rw [gate_and]
      rfl
    refine ⟨by decide, ?_, ?_⟩
    · rw [gate_or]
      rfl
    refine ⟨by decide, ?_, ?_⟩
    · rw [gate_or]
      rfl
    refine ⟨by decide, ?_, ?_⟩
    · rw [gate_and]
      rfl
    refine ⟨by decide, ?_, ?_⟩
    · rw [gate_or]
      rfl
    refine ⟨by decide, ?_, ?_⟩
    · rw [gate_and]
      rfl
    refine ⟨by decide, ?_, ?_⟩
    · rw [gate_and]
      rfl
    refine ⟨by decide, ?_, ?_⟩
    · rw [gate_or]
      rfl
    refine ⟨by decide, ?_, ?_⟩
    · rw [gate_or]
      rfl
    refine ⟨by decide, ?_, ?_⟩
    · rw [gate_or]
      rfl
    exact True.intro
  have inputs : List.ofFn x = snapshot t 8 := by
    apply List.ext_getElem
    · simp [snapshot]
    · intro i hi hj
      have hv : i < 8 := by simpa using hi
      have small : ∀ j : Fin 8, x j = t j.val := by
        intro j
        fin_cases j <;> rfl
      simpa only [snapshot, List.getElem_ofFn] using small ⟨i,hv⟩
  have evaluated := fold_trace _ _ _ valid
  unfold Circuit.eval Circuit.wires
  rw [inputs, evaluated, read_snapshot t _ _ (by decide)]
  simp only [edgeBool, edgePairs, List.any_cons, List.any_nil]
  change ((((x 0 && (x 1 || x 5)) || (x 2 && ((x 1 || x 3) || x 7))) || (x 3 && (x 4 || x 6))) || (x 4 && x 5)) = ((x 0 && x 1) || ((x 0 && x 5) || ((x 1 && x 2) || ((x 2 && x 3) || ((x 2 && x 7) || ((x 3 && x 4) || ((x 3 && x 6) || ((x 4 && x 5) || false))))))))
  simp only [Bool.and_or_distrib_left, Bool.or_assoc, Bool.or_left_comm, Bool.or_comm, Bool.and_comm]
  simp only [Bool.false_or]

end PEqualNP.Outside.L_meta_818

open PEqualNP.Outside.L_meta_818

theorem PEqualNP.Outside.L_meta_818 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, C = ({ gates := [⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 8]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [10, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [2, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [3, 13]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [4, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [16, 14]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [17, 15]⟩], output := 18 } : PEqualNP.CircuitLowerBounds.Circuit) → PEqualNP.MetaComplexity.FanInTwo C ∧ C.size = 11 ∧ (∀ x : Fin 8 → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 8, (u.val, v.val) ∈ ([(0, 1), (0, 5), (1, 2), (2, 3), (2, 7), (3, 4), (3, 6), (4, 5)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true)) := by
  intro C specified
  subst C
  exact ⟨binary, by decide, fun x => (computes x) ▸ edge_spec x⟩
