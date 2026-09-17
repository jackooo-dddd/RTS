-- Translated from: ../rt-proofs/classic/util/ord_quantifier.v
import Mathlib.Tactic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.Basic
import Prosa.Classic.Util.Tactics

namespace Prosa.Classic.Util.Ord_quantifier

section OrdExists

  lemma exists_ord0 (P : Fin 0 → Bool) :
      ¬ ∃ x : Fin 0, P x = true := by
    intro ⟨x, _⟩
    exact x.elim0

  lemma exists_recr (n : ℕ) (P : Fin (n + 1) → Bool) :
      (∃ x : Fin (n + 1), P x = true) ↔
      (∃ x : Fin n, P (Fin.castSucc x) = true) ∨ P (Fin.last n) = true := by
    constructor
    · rintro ⟨x, hx⟩
      have key : ∀ i : Fin (n + 1), P i = true →
          (∃ x : Fin n, P (Fin.castSucc x) = true) ∨ P (Fin.last n) = true :=
        Fin.lastCases (fun hP => Or.inr hP) (fun i hP => Or.inl ⟨i, hP⟩)
      exact key x hx
    · rintro (⟨x, hx⟩ | hx)
      · exact ⟨Fin.castSucc x, hx⟩
      · exact ⟨Fin.last n, hx⟩

end OrdExists

section OrdForall

  lemma forall_ord0 (P : Fin 0 → Bool) :
      ∀ x : Fin 0, P x = true := by
    intro x
    exact x.elim0

  lemma forall_recr (n : ℕ) (P : Fin (n + 1) → Bool) :
      (∀ x : Fin (n + 1), P x = true) ↔
      (∀ x : Fin n, P (Fin.castSucc x) = true) ∧ P (Fin.last n) = true := by
    constructor
    · intro h
      exact ⟨fun x => h (Fin.castSucc x), h (Fin.last n)⟩
    · rintro ⟨hall, hlast⟩ x
      refine Fin.lastCases ?_ ?_ x
      · exact hlast
      · exact hall

end OrdForall

macro "simpl_exists_ord" : tactic =>
  `(tactic| (simp only [exists_recr, exists_ord0]))

macro "simpl_forall_ord" : tactic =>
  `(tactic| (simp only [forall_recr, forall_ord0]))

end Prosa.Classic.Util.Ord_quantifier
