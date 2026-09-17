-- Translated from: ../rt-proofs/classic/util/counting.v
import Mathlib.Data.List.Count
import Mathlib.Data.List.Nodup
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic
import Prosa.Util.Counting
import Prosa.Classic.Util.Tactics

namespace Prosa.Classic.Util.Counting

section Counting

lemma count_or {T : Type _} [DecidableEq T] (l : List T) (P Q : T → Bool) :
    List.countP (fun x => P x || Q x) l ≤ List.countP P l + List.countP Q l := by
  induction l with
  | nil => simp
  | cons x t ih =>
    simp only [List.countP_cons]
    cases hP : P x <;> cases hQ : Q x <;> simp <;> omega

lemma sub_in_count {T : Type _} [DecidableEq T] (l : List T) (P1 P2 : T → Bool) :
    (∀ x, x ∈ l → P1 x = true → P2 x = true) →
    List.countP (fun x => P1 x) l ≤ List.countP (fun x => P2 x) l := by
  intro h
  induction l with
  | nil => simp
  | cons x t ih =>
    simp only [List.countP_cons]
    have ih' := ih (fun y hy hp => h y (List.mem_cons_of_mem x hy) hp)
    cases h1 : P1 x <;> simp
    · cases h2 : P2 x <;> simp <;> omega
    · have h2 : P2 x = true := h x List.mem_cons_self h1
      simp [h2]; omega

lemma count_sub_uniqr {T : Type _} [DecidableEq T] (l1 l2 : List T) (P : T → Bool) :
    l1.Nodup →
    (∀ x, x ∈ l1 → x ∈ l2) →
    List.countP (fun x => P x) l1 ≤ List.countP (fun x => P x) l2 := by
  intro hnodup hsub
  rw [List.countP_eq_length_filter, List.countP_eq_length_filter]
  have hnd : (l1.filter (fun x => P x)).Nodup := List.Nodup.filter _ hnodup
  have hsub' : ∀ x, x ∈ l1.filter (fun x => P x) → x ∈ l2.filter (fun x => P x) := by
    intro x hx
    simp only [List.mem_filter] at hx ⊢
    exact ⟨hsub x hx.1, hx.2⟩
  exact List.Subperm.length_le (List.Nodup.subperm hnd hsub')

lemma count_pred_inj {T : Type _} [DecidableEq T] (l : List T) (P : T → Bool) :
    l.Nodup →
    (∀ x1 x2, P x1 = true → P x2 = true → x1 = x2) →
    List.countP (fun x => P x) l ≤ 1 := by
  intro hnodup hinj
  induction l with
  | nil => simp
  | cons x t ih =>
    simp only [List.countP_cons]
    rw [List.nodup_cons] at hnodup
    have ih' := ih hnodup.2
    cases hpx : P x
    · simp; exact ih'
    · suffices h0 : List.countP (fun x => P x) t = 0 by
        simp [h0]
      rw [List.countP_eq_zero]
      intro y hy hpy
      have := hinj x y hpx hpy
      subst this
      exact hnodup.1 hy

lemma count_exists {T : Type _} [DecidableEq T] (l : List T) (n : ℕ) (P : T → Fin n → Bool) :
    l.Nodup →
    (∀ (y : Fin n) (x1 x2 : T), P x1 y = true → P x2 y = true → x1 = x2) →
    List.countP (fun (x : T) => decide (∃ i : Fin n, P x i = true)) l ≤ n := by
  induction n with
  | zero =>
    intro _ _
    have hf : ∀ x, (decide (∃ i : Fin 0, P x i = true)) = false := by
      intro x; simp
    have : List.countP (fun (x : T) => decide (∃ i : Fin 0, P x i = true)) l = 0 := by
      rw [show (fun (x : T) => decide (∃ i : Fin 0, P x i = true)) = (fun _ => false) from funext hf]
      simp [List.countP_eq_length_filter, List.filter_false]
    omega
  | succ n ih =>
    intro huniq hinj
    have key : ∀ x, (decide (∃ i : Fin (n + 1), P x i = true)) =
        ((decide (∃ i : Fin n, P x (Fin.castSucc i) = true)) || P x (Fin.last n)) := by
      intro x
      apply Bool.eq_iff_iff.mpr
      simp only [Bool.or_eq_true, decide_eq_true_eq]
      constructor
      · intro ⟨i, hi⟩
        by_cases h : i.val < n
        · left; exact ⟨⟨i.val, h⟩, by
            have : (Fin.castSucc ⟨i.val, h⟩) = i := by ext; simp [Fin.castSucc, Fin.castAdd]
            rw [this]; exact hi⟩
        · right
          have : i = Fin.last n := by
            ext; simp [Fin.last]; omega
          rw [this] at hi; exact hi
      · intro h
        cases h with
        | inl h =>
          obtain ⟨i, hi⟩ := h
          exact ⟨Fin.castSucc i, hi⟩
        | inr h =>
          exact ⟨Fin.last n, h⟩
    calc List.countP (fun x => decide (∃ i : Fin (n + 1), P x i = true)) l
        = List.countP (fun x => (decide (∃ i : Fin n, P x (Fin.castSucc i) = true)) || P x (Fin.last n)) l := by
          congr 1; ext x; exact key x
      _ ≤ List.countP (fun x => decide (∃ i : Fin n, P x (Fin.castSucc i) = true)) l +
          List.countP (fun x => P x (Fin.last n)) l :=
          count_or l _ _
      _ ≤ n + 1 := by
          have h1 : List.countP (fun x => decide (∃ i : Fin n, P x (Fin.castSucc i) = true)) l ≤ n := by
            exact ih (fun x i => P x (Fin.castSucc i)) huniq
              (fun y x1 x2 h1 h2 => hinj (Fin.castSucc y) x1 x2 h1 h2)
          have h2 : List.countP (fun x => P x (Fin.last n)) l ≤ 1 := by
            apply count_pred_inj l _ huniq
            intro x1 x2 hp1 hp2
            exact hinj (Fin.last n) x1 x2 hp1 hp2
          omega

end Counting

end Prosa.Classic.Util.Counting
