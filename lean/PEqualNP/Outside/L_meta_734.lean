import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Data.Set.Card
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_734

theorem other_color : ∀ c a b : Fin 2, a ≠ c → b ≠ c → a = b := by decide

theorem small_color {n : ℕ} (col : Fin n → Fin 2) (t : Finset (Fin n)) (ht : t.card ≤ 5) :
    ∃ c : Fin 2, (t.filter (fun v => col v = c)).card ≤ 2 := by
  classical
  by_cases h : (t.filter (fun v => col v = 0)).card ≤ 2
  · exact ⟨0,h⟩
  · refine ⟨1,?_⟩
    have colors : ∀ a : Fin 2, a ≠ 0 ↔ a = 1 := by decide
    have partition := t.card_filter_add_card_filter_not (fun v => col v = 0)
    simp only [colors] at partition
    omega

theorem fresh_neighbor {n : ℕ} (G : SimpleGraph (Fin n))
    (square : ∀ a b c d, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a → a = c ∨ b = d)
    (degree : ∀ v, 3 ≤ {w : Fin n | G.Adj v w}.ncard)
    (B : Finset (Fin n)) (hB : B.card ≤ 2) (y : Fin n) (hy : y ∉ B) :
    ∃ u, G.Adj y u ∧ ∀ b ∈ B, ¬ G.Adj u b := by
  classical
  let N := Finset.univ.filter (fun u => G.Adj y u)
  let together (b : Fin n) := N.filter (fun u => G.Adj u b)
  have hN : 3 ≤ N.card := by
    have eq : {u : Fin n | G.Adj y u}.toFinset = N := by ext u; simp [N]
    simpa only [Set.ncard_eq_toFinset_card', eq] using degree y
  have one (b : Fin n) (hb : b ∈ B) : (together b).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro u hu v hv
    obtain ⟨uy,ub⟩ := Finset.mem_filter.mp hu
    obtain ⟨vy,vb⟩ := Finset.mem_filter.mp hv
    have yu : G.Adj y u := (Finset.mem_filter.mp uy).2
    have yv : G.Adj y v := (Finset.mem_filter.mp vy).2
    exact (square y u b v yu ub vb.symm yv.symm).resolve_left (fun eq => hy (eq ▸ hb))
  by_contra! blocked
  have sub : N ⊆ B.biUnion together := by
    intro u hu
    have edge : G.Adj y u := (Finset.mem_filter.mp hu).2
    obtain ⟨b,hb,ub⟩ := blocked u edge
    exact Finset.mem_biUnion.mpr ⟨b,hb,Finset.mem_filter.mpr ⟨hu,ub⟩⟩
  have bound := (Finset.card_le_card sub).trans (Finset.card_biUnion_le_card_mul B together 1 one)
  omega

end PEqualNP.Outside.L_meta_734

theorem PEqualNP.Outside.L_meta_734 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
  G.Colorable 2 →
  (∀ a b c d, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a → a = c ∨ b = d) →
  (∀ v, 3 ≤ {w : Fin n | G.Adj v w}.ncard) →
  ∀ T : Set (Fin n), T.ncard ≤ 5 →
    (∀ I : Set (Fin n), (∀ u ∈ I, ∀ v ∈ I, ¬ G.Adj u v) → (∀ v, v ∉ I → ∃ u ∈ I, G.Adj v u) →
      ∃ t ∈ T, t ∈ I) →
    ∃ v ∈ T, ∀ w, G.Adj v w → w ∈ T := by
  classical
  intro n G hcol square degree T sizeT transversal
  obtain ⟨col⟩ := hcol
  have sizeT' : T.toFinset.card ≤ 5 := by simpa only [Set.ncard_eq_toFinset_card'] using sizeT
  obtain ⟨s,hs⟩ := PEqualNP.Outside.L_meta_734.small_color col T.toFinset sizeT'
  let A := T.toFinset.filter (fun v => col v = s)
  have a_mem (a : A) : (a : Fin n) ∈ T ∧ col a = s := by
    obtain ⟨inT, color⟩ := Finset.mem_filter.mp a.property
    exact ⟨Set.mem_toFinset.mp inT, color⟩
  by_contra no_star
  have escape (v : Fin n) (hv : v ∈ T) : ∃ b, G.Adj v b ∧ b ∉ T := by
    by_contra! trapped
    exact no_star ⟨v,hv,trapped⟩
  let pick (a : A) := Classical.choose (escape a (a_mem a).1)
  have chosen (a : A) : G.Adj (a : Fin n) (pick a) ∧ pick a ∉ T :=
    Classical.choose_spec (escape a (a_mem a).1)
  let B := A.attach.image pick
  have inB (a : A) : pick a ∈ B := Finset.mem_image.mpr ⟨a,Finset.mem_attach _ _,rfl⟩
  have smallB : B.card ≤ 2 := by
    calc B.card ≤ A.attach.card := Finset.card_image_le
         _ = A.card := Finset.card_attach
         _ ≤ 2 := hs
  have b_mem {b} (hb : b ∈ B) : col b ≠ s ∧ b ∉ T := by
    obtain ⟨a,_,rfl⟩ := Finset.mem_image.mp hb
    exact ⟨fun h => col.valid (chosen a).1 ((a_mem a).2.trans h.symm), (chosen a).2⟩
  let X : Set (Fin n) := {u | col u = s ∧ ∀ b ∈ B, ¬ G.Adj u b}
  let Y : Set (Fin n) := {v | col v ≠ s ∧ ∀ u ∈ X, ¬ G.Adj v u}
  have BY {b} (hb : b ∈ B) : b ∈ Y :=
    ⟨(b_mem hb).1, fun u hu edge => hu.2 b hb edge.symm⟩
  have independent : ∀ u ∈ X ∪ Y, ∀ v ∈ X ∪ Y, ¬ G.Adj u v := by
    rintro u (hu | hu) v (hv | hv) edge
    · exact col.valid edge (hu.1.trans hv.1.symm)
    · exact hv.2 u hu edge.symm
    · exact hu.2 v hv edge
    · exact col.valid edge (PEqualNP.Outside.L_meta_734.other_color s _ _ hu.1 hv.1)
  have dominates : ∀ v, v ∉ X ∪ Y → ∃ u ∈ X ∪ Y, G.Adj v u := by
    intro v outside
    by_contra! alone
    by_cases color : col v = s
    · exact outside (Or.inl ⟨color, fun b hb => alone b (Or.inr (BY hb))⟩)
    · exact outside (Or.inr ⟨color, fun u hu => alone u (Or.inl hu)⟩)
  obtain ⟨v,hT,hI⟩ := transversal (X ∪ Y) independent dominates
  rcases hI with vx | vy
  · have va : v ∈ A := Finset.mem_filter.mpr ⟨Set.mem_toFinset.mpr hT, vx.1⟩
    let a : A := ⟨v,va⟩
    exact vx.2 (pick a) (inB a) (chosen a).1
  · have vn : v ∉ B := fun hb => (b_mem hb).2 hT
    obtain ⟨u,vu,avoid⟩ := PEqualNP.Outside.L_meta_734.fresh_neighbor G square degree B smallB v vn
    have color : col u = s := by
      by_contra other
      exact col.valid vu (PEqualNP.Outside.L_meta_734.other_color s _ _ vy.1 other)
    exact vy.2 u ⟨color,avoid⟩ vu
