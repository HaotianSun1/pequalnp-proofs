import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1197

open PEqualNP.CircuitLowerBounds

def circuit : Circuit :=
  ⟨[⟨.or, [1, 2]⟩, ⟨.or, [8, 3]⟩, ⟨.and, [0, 9]⟩,
    ⟨.and, [1, 4]⟩, ⟨.or, [2, 4]⟩, ⟨.and, [5, 12]⟩,
    ⟨.and, [6, 7]⟩, ⟨.or, [10, 11]⟩, ⟨.or, [15, 13]⟩,
    ⟨.or, [16, 14]⟩], 17⟩

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma computes : ∀ a b c d e f g h : Bool,
    circuit.eval [a, b, c, d, e, f, g, h] =
      ((a && b) || (a && c) || (a && d) || (b && e) ||
        (c && f) || (e && f) || (g && h)) := by
  decide

end PEqualNP.Outside.L_meta_1197

open PEqualNP.Outside.L_meta_1197

theorem PEqualNP.Outside.L_meta_1197 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 10 ∧ ∀ x : Fin 8 → Bool, C.eval (List.ofFn x) = (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 4 && x 5) || (x 6 && x 7)) x := by
  refine ⟨circuit, ?_, by decide, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2, circuit]
  · intro x
    have inputs : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7] := by
      simp [List.ofFn_succ]
    rw [inputs]
    exact computes (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7)
