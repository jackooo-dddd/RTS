-- Translated from: ../rt-proofs/util/sum.v
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic
import Prosa.Util.Notation
import Prosa.Util.Nat

namespace Prosa.Util.Sum

section ExtraLemmas

theorem list_sum_map_add {β : Type*} (ks : List β) (p q : β → ℕ) :
    (ks.map (fun k => p k + q k)).sum = (ks.map p).sum + (ks.map q).sum := by
  induction ks with
  | nil => simp
  | cons _ _ ih => simp only [List.map_cons, List.sum_cons]; omega

theorem list_mem_le_ite_sum {β : Type*} [DecidableEq β]
    : ∀ (ks : List β) (c : ℕ) (b : β), b ∈ ks →
    c ≤ (ks.map (fun k => if b == k then c else 0)).sum
  | [], _, _, hb => nomatch hb
  | k :: rest, c, b, hb => by
    simp only [List.map_cons, List.sum_cons]
    cases List.mem_cons.mp hb with
    | inl heq => rw [show (b == k) = true from beq_iff_eq.mpr heq]; simp
    | inr hmem => have := list_mem_le_ite_sum rest c b hmem; omega

theorem leq_sum_seq {I : Type _} [DecidableEq I] (r : List I) (P : I → Bool)
    (E1 E2 : I → ℕ)
    (h : ∀ i, i ∈ r → P i = true → E1 i ≤ E2 i) :
    ((r.filter (fun i => P i)).map E1).sum ≤ ((r.filter (fun i => P i)).map E2).sum := by
  induction r with
  | nil => simp
  | cons a t ih =>
    simp only [List.filter_cons]
    split
    · case isTrue hP =>
      simp only [List.map_cons, List.sum_cons]
      apply Nat.add_le_add
      · exact h a List.mem_cons_self hP
      · exact ih (fun i hi hPi => h i (List.mem_cons_of_mem a hi) hPi)
    · case isFalse hP =>
      exact ih (fun i hi hPi => h i (List.mem_cons_of_mem a hi) hPi)

theorem eq_sum_seq {I : Type _} [DecidableEq I] (r : List I) (P : I → Bool)
    (E1 E2 : I → ℕ)
    (h : ∀ i, i ∈ r → P i = true → E1 i = E2 i) :
    ((r.filter (fun i => P i)).map E1).sum = ((r.filter (fun i => P i)).map E2).sum := by
  apply le_antisymm
  · exact leq_sum_seq r P E1 E2 (fun i hi hPi => le_of_eq (h i hi hPi))
  · exact leq_sum_seq r P E2 E1 (fun i hi hPi => le_of_eq (h i hi hPi).symm)

theorem sum_nat_eq0_nat {T : Type _} [DecidableEq T] (F : T → ℕ) (r : List T) :
    (r.all (fun x => F x == 0)) = ((r.map F).sum == 0) := by
  induction r with
  | nil => simp
  | cons a t ih =>
    simp only [List.all_cons, List.map_cons, List.sum_cons]
    rw [ih]
    cases F a <;> cases (List.map F t).sum <;> simp

theorem sum_seq_gt0P {T : Type _} [DecidableEq T] (r : List T) (F : T → ℕ) :
    (∃ i, i ∈ r ∧ 0 < F i) ↔ 0 < (r.map F).sum := by
  constructor
  · rintro ⟨i, hi, hpos⟩
    induction r with
    | nil => simp at hi
    | cons a t ih =>
      simp only [List.map_cons, List.sum_cons]
      rcases List.mem_cons.mp hi with rfl | ht
      · omega
      · have := ih ht
        omega
  · intro hpos
    induction r with
    | nil => simp at hpos
    | cons a t ih =>
      simp only [List.map_cons, List.sum_cons] at hpos
      by_cases ha : 0 < F a
      · exact ⟨a, List.mem_cons_self, ha⟩
      · push_neg at ha
        have : 0 < (t.map F).sum := by omega
        obtain ⟨i, hi, hFi⟩ := ih this
        exact ⟨i, List.mem_cons_of_mem a hi, hFi⟩

theorem sum_notin_rem_eqn {T : Type _} [DecidableEq T] (a : T) (xs : List T) (P : T → Bool)
    (F : T → ℕ) (h : a ∉ xs) :
    ((xs.filter (fun x => P x && (x != a))).map F).sum =
    ((xs.filter (fun x => P x)).map F).sum := by
  congr 1; congr 1
  apply List.filter_congr
  intro x hx
  have hne : x ≠ a := fun heq => h (heq ▸ hx)
  have : (x != a) = true := by
    rw [ne_eq] at hne
    exact bne_iff_ne.mpr hne
  rw [this, Bool.and_true]

theorem sum0 (m n : ℕ) :
    ∑ i ∈ Finset.Ico m n, (0 : ℕ) = 0 := by
  simp

theorem big_nat_eq0 (m n : ℕ) (F : ℕ → ℕ) :
    ∑ i ∈ Finset.Ico m n, F i = 0 ↔ (∀ i, m ≤ i ∧ i < n → F i = 0) := by
  constructor
  · intro hsum i ⟨hle, hlt⟩
    have hmem : i ∈ Finset.Ico m n := Finset.mem_Ico.mpr ⟨hle, hlt⟩
    exact Finset.sum_eq_zero_iff.mp hsum i hmem
  · intro hall
    apply Finset.sum_eq_zero
    intro i hi
    exact hall i ⟨(Finset.mem_Ico.mp hi).1, (Finset.mem_Ico.mp hi).2⟩

theorem sum_majorant_constant {T : Type _} [DecidableEq T] (r : List T) (P : T → Bool)
    (F : T → ℕ) (const : ℕ)
    (h : ∀ a, a ∈ r → P a = true → F a ≤ const) :
    ((r.filter (fun j => P j)).map F).sum ≤ const * (r.filter (fun j => P j)).length := by
  induction r with
  | nil => simp
  | cons a t ih =>
    simp only [List.filter_cons]
    split
    · case isTrue hP =>
      simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.mul_succ, Nat.add_comm]
      apply Nat.add_le_add
      · exact h a List.mem_cons_self hP
      · exact ih (fun x hx hPx => h x (List.mem_cons_of_mem a hx) hPx)
    · case isFalse hP =>
      exact ih (fun x hx hPx => h x (List.mem_cons_of_mem a hx) hPx)

theorem sum_majorant_eqn {T : Type _} [DecidableEq T] (xs : List T) (F1 F2 : T → ℕ)
    (P : T → Bool)
    (h1 : ∀ x, x ∈ xs → P x = true → F1 x ≤ F2 x)
    (h2 : ((xs.filter (fun x => P x)).map F1).sum =
          ((xs.filter (fun x => P x)).map F2).sum)
    (x : T) (hx : x ∈ xs) (hPx : P x = true) :
    F1 x = F2 x := by
  induction xs with
  | nil => simp at hx
  | cons a t ih =>
    simp only [List.filter_cons] at h2
    have h1t : ∀ y, y ∈ t → P y = true → F1 y ≤ F2 y :=
      fun y hy hPy => h1 y (List.mem_cons_of_mem a hy) hPy
    have hle_t : ((t.filter (fun x => P x)).map F1).sum ≤
                 ((t.filter (fun x => P x)).map F2).sum :=
      leq_sum_seq t P F1 F2 h1t
    rcases List.mem_cons.mp hx with rfl | hxt
    · -- x = a
      simp only [hPx, ite_true, List.map_cons, List.sum_cons] at h2
      have hle_a := h1 x List.mem_cons_self hPx
      omega
    · -- x ∈ t
      have h2t : ((t.filter (fun x => P x)).map F1).sum =
                 ((t.filter (fun x => P x)).map F2).sum := by
        split at h2
        · case isTrue hPa =>
          simp only [List.map_cons, List.sum_cons] at h2
          have hle_a := h1 a List.mem_cons_self hPa
          omega
        · case isFalse hPa =>
          exact h2
      exact ih h1t h2t hxt

theorem sum_of_ones (t Δ : ℕ) :
    ∑ _x ∈ Finset.Ico t (t + Δ), (1 : ℕ) = Δ := by
  simp

theorem sum_le_summation_range (f : ℕ → ℕ) (t Δ : ℕ)
    (h : ∑ x ∈ Finset.Ico t (t + Δ), f x < Δ) :
    ∃ x, t ≤ x ∧ x < t + Δ ∧ f x = 0 := by
  by_contra hall
  push_neg at hall
  have : Δ ≤ ∑ x ∈ Finset.Ico t (t + Δ), f x := by
    calc Δ = ∑ _x ∈ Finset.Ico t (t + Δ), (1 : ℕ) := (sum_of_ones t Δ).symm
    _ ≤ ∑ x ∈ Finset.Ico t (t + Δ), f x := by
        apply Finset.sum_le_sum
        intro i hi
        rw [Finset.mem_Ico] at hi
        have := hall i hi.1 hi.2
        omega
  omega

end ExtraLemmas

section SumArithmetic

theorem sum_seq_diff {T : Type _} [DecidableEq T] (rs : List T) (F G : T → ℕ)
    (h : ∀ i, i ∈ rs → G i ≤ F i) :
    (rs.map (fun i => F i - G i)).sum =
    (rs.map F).sum - (rs.map G).sum := by
  induction rs with
  | nil => simp
  | cons a t ih =>
    simp only [List.map_cons, List.sum_cons]
    have ha := h a List.mem_cons_self
    have ht : ∀ i, i ∈ t → G i ≤ F i :=
      fun i hi => h i (List.mem_cons_of_mem a hi)
    rw [ih ht]
    have hle : (t.map G).sum ≤ (t.map F).sum := by
      have : ∀ (l : List T), (∀ i, i ∈ l → G i ≤ F i) →
          (l.map G).sum ≤ (l.map F).sum := by
        intro l hl
        induction l with
        | nil => simp
        | cons b s ihs =>
          simp only [List.map_cons, List.sum_cons]
          apply Nat.add_le_add
          · exact hl b List.mem_cons_self
          · exact ihs (fun i hi => hl i (List.mem_cons_of_mem b hi))
      exact this t ht
    omega

theorem sum_diff (n : ℕ) (F G : ℕ → ℕ)
    (h : ∀ i, i < n → F i ≥ G i) :
    ∑ i ∈ Finset.Ico 0 n, (F i - G i) =
    (∑ i ∈ Finset.Ico 0 n, F i) - (∑ i ∈ Finset.Ico 0 n, G i) := by
  have hle : ∑ i ∈ Finset.Ico 0 n, G i ≤ ∑ i ∈ Finset.Ico 0 n, F i :=
    Finset.sum_le_sum (fun i hi => h i ((Finset.mem_Ico.mp hi).2))
  have key : ∑ i ∈ Finset.Ico 0 n, (F i - G i) + ∑ i ∈ Finset.Ico 0 n, G i =
             ∑ i ∈ Finset.Ico 0 n, F i := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    exact Nat.sub_add_cancel (h i ((Finset.mem_Ico.mp hi).2))
  omega

theorem sum_pred_diff {T : Type _} [DecidableEq T] (rs : List T) (P : T → Bool) (F : T → ℕ) :
    ((rs.filter (fun r => P r)).map F).sum =
    (rs.map F).sum - ((rs.filter (fun r => !P r)).map F).sum := by
  have key : ((rs.filter (fun r => P r)).map F).sum +
             ((rs.filter (fun r => !P r)).map F).sum =
             (rs.map F).sum := by
    induction rs with
    | nil => simp
    | cons a t ih =>
      simp only [List.filter_cons, List.map_cons, List.sum_cons]
      cases hPa : P a <;> simp [hPa] <;> omega
  omega

end SumArithmetic

end Prosa.Util.Sum
