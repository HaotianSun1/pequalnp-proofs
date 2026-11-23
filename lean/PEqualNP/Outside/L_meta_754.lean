import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Tauto
import PEqualNP.MetaComplexity.L104
import PEqualNP.MetaComplexity.L105

namespace PEqualNP.Outside.L_meta_754

abbrev fork : SimpleGraph (Fin 5) := SimpleGraph.fromRel (fun i j =>
  (i = 0 ∧ (j = 1 ∨ j = 2 ∨ j = 3)) ∨ (i = 1 ∧ j = 4))

lemma connected : fork.Connected := by
  have reachable : ∀ i : Fin 5, fork.Reachable 0 i := by
    intro i
    fin_cases i
    · exact SimpleGraph.Reachable.refl _
    · exact (show fork.Adj 0 1 by decide).reachable
    · exact (show fork.Adj 0 2 by decide).reachable
    · exact (show fork.Adj 0 3 by decide).reachable
    · exact (show fork.Adj 0 1 by decide).reachable.trans
        (show fork.Adj 1 4 by decide).reachable
  exact ⟨fun i j => (reachable i).symm.trans (reachable j)⟩

lemma edge_count : fork.edgeFinset.card = 4 := by decide

lemma acyclic : fork.IsAcyclic := by
  refine (SimpleGraph.isTree_iff_connected_and_card.mpr ⟨connected, ?_⟩).isAcyclic
  rw [Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card, edge_count, Nat.card_fin]

lemma has_edge : ∃ i j : Fin 5, fork.Adj i j := ⟨0, 1, by decide⟩

def cover : Finset (Fin 5) := {0, 1}

lemma cover_upper : ∀ i j : Fin 5, fork.Adj i j → i ∈ cover ∨ j ∈ cover := by decide

lemma cover_count : cover.card = 2 := by decide

-- A cover supplies distinct vertices from the disjoint edges {0, 2} and {1, 4}.
lemma cover_lower (T : Finset (Fin 5))
    (hT : ∀ i j : Fin 5, fork.Adj i j → i ∈ T ∨ j ∈ T) : 2 ≤ T.card := by
  apply Finset.one_lt_card.mpr
  rcases hT 0 2 (by decide) with h0 | h2 <;> rcases hT 1 4 (by decide) with h1 | h4
  · exact ⟨0, h0, 1, h1, by decide⟩
  · exact ⟨0, h0, 4, h4, by decide⟩
  · exact ⟨2, h2, 1, h1, by decide⟩
  · exact ⟨2, h2, 4, h4, by decide⟩

lemma adjacent_pairs : ∀ i j : Fin 5, fork.Adj i j ↔
    (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) ∨
    (i = 0 ∧ j = 2) ∨ (i = 2 ∧ j = 0) ∨
    (i = 0 ∧ j = 3) ∨ (i = 3 ∧ j = 0) ∨
    (i = 1 ∧ j = 4) ∨ (i = 4 ∧ j = 1) := by decide

lemma fork_eval (x : Fin 5 → Bool) :
    decide (∃ i j : Fin 5, fork.Adj i j ∧ x i = true ∧ x j = true) =
      ((x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4)) := by
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq, Bool.or_eq_true, Bool.and_eq_true]
  constructor
  · rintro ⟨i, j, hij, hi, hj⟩
    rcases (adjacent_pairs i j).mp hij with
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> tauto
  · rintro (((⟨h0, h1⟩ | ⟨h0, h2⟩) | ⟨h0, h3⟩) | ⟨h1, h4⟩)
    · exact ⟨0, 1, by decide, h0, h1⟩
    · exact ⟨0, 2, by decide, h0, h2⟩
    · exact ⟨0, 3, by decide, h0, h3⟩
    · exact ⟨1, 4, by decide, h1, h4⟩

end PEqualNP.Outside.L_meta_754

open PEqualNP.Outside.L_meta_754

theorem PEqualNP.Outside.L_meta_754 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4)) s ↔ 5 ≤ s := by
  intro s
  rw [← funext fork_eval]
  constructor
  · intro h
    have bound := PEqualNP.MetaComplexity.L104 5 2 s fork acyclic has_edge cover_lower h
    rw [edge_count] at bound
    omega
  · intro hs
    have five := PEqualNP.MetaComplexity.L105 5 fork cover has_edge cover_upper
    rw [edge_count, cover_count] at five
    obtain ⟨C, hC, hsize, heval⟩ := five
    exact ⟨C, hC, hsize.trans hs, heval⟩
