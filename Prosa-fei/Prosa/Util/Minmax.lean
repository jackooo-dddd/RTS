-- Translated from: ../rt-proofs/util/minmax.v
import Mathlib
import Prosa.Util.Notation

namespace Prosa.Util.Minmax

section ExtraLemmas

/-- The big max over a list with a condition, computing max of `F i` for elements
    satisfying `P` in list `r`. Corresponds to MathComp's `\max_(i <- r | P i) F i`. -/
noncomputable def bigMaxListCond {T : Type _} [DecidableEq T] (r : List T)
    (P : T → Prop) [DecidablePred P] (F : T → ℕ) : ℕ :=
  (r.filter P).map F |>.foldl max 0

theorem leq_bigmax_cond_seq {T : Type _} [DecidableEq T]
    (P : T → Prop) [DecidablePred P] (r : List T) (F : T → ℕ) (i0 : T) :
    i0 ∈ r → P i0 → F i0 ≤ bigMaxListCond r P F := by
  intro h_mem h_P
  unfold bigMaxListCond
  have h_mono : ∀ (acc1 acc2 : ℕ) (l : List ℕ), acc1 ≤ acc2 → l.foldl max acc1 ≤ l.foldl max acc2 := by
    intro acc1 acc2 l
    induction l generalizing acc1 acc2 with
    | nil => exact id
    | cons y ys ihy =>
      intro hle; simp only [List.foldl_cons]
      apply ihy; exact max_le_max_right y hle
  have h_le_foldl : ∀ (acc : ℕ) (l : List ℕ), acc ≤ l.foldl max acc := by
    intro acc l
    induction l generalizing acc with
    | nil => exact le_refl acc
    | cons y ys ihy =>
      simp only [List.foldl_cons]
      exact le_trans (le_max_left acc y) (ihy _)
  have h_mem_le : ∀ (l : List ℕ) (a : ℕ), a ∈ l → a ≤ l.foldl max 0 := by
    intro l
    induction l with
    | nil => intro a ha; simp at ha
    | cons x xs ih =>
      intro a ha
      simp only [List.foldl_cons]
      rcases List.mem_cons.mp ha with rfl | h
      · conv_lhs => rw [show a = max 0 a from (Nat.zero_max a ▸ rfl)]
        exact h_le_foldl _ xs
      · exact le_trans (ih a h) (h_mono 0 (max 0 x) xs (Nat.zero_le _))
  apply h_mem_le
  simp only [List.mem_map]
  exact ⟨i0, List.mem_filter_of_mem h_mem (by simp [h_P]), rfl⟩

theorem bigmax_sup_seq {T : Type _} [DecidableEq T]
    (i : T) (r : List T) (P : T → Prop) [DecidablePred P] (m : ℕ) (F : T → ℕ) :
    i ∈ r → P i → m ≤ F i → m ≤ bigMaxListCond r P F := by
  intro h_mem h_P h_le
  exact le_trans h_le (leq_bigmax_cond_seq P r F i h_mem h_P)

theorem bigmax_leq_seqP {T : Type _} [DecidableEq T]
    (P : T → Prop) [DecidablePred P] (r : List T) (F : T → ℕ) (m : ℕ) :
    bigMaxListCond r P F ≤ m ↔ ∀ i, i ∈ r → P i → F i ≤ m := by
  constructor
  · intro h_le i h_mem h_P
    exact le_trans (leq_bigmax_cond_seq P r F i h_mem h_P) h_le
  · intro h_all
    unfold bigMaxListCond
    have h_foldl_le : ∀ (l : List ℕ) (acc : ℕ),
        (∀ x, x ∈ l → x ≤ m) → acc ≤ m → l.foldl max acc ≤ m := by
      intro l
      induction l with
      | nil => intro acc _ h; exact h
      | cons y ys ih =>
        intro acc h_all_l h_acc
        simp only [List.foldl_cons]
        apply ih
        · intro x hx; exact h_all_l x (List.mem_cons_of_mem y hx)
        · exact max_le h_acc (h_all_l y (List.mem_cons.mpr (Or.inl rfl)))
    apply h_foldl_le
    · intro x hx
      simp only [List.mem_map] at hx
      obtain ⟨a, ha_mem, rfl⟩ := hx
      simp only [List.mem_filter] at ha_mem
      exact h_all a ha_mem.1 (by simpa using ha_mem.2)
    · exact Nat.zero_le m

theorem leq_big_max {T : Type _} [DecidableEq T]
    (P : T → Prop) [DecidablePred P] (r : List T) (F1 F2 : T → ℕ) :
    (∀ i, i ∈ r → P i → F1 i ≤ F2 i) →
    bigMaxListCond r P F1 ≤ bigMaxListCond r P F2 := by
  intro h_le
  rw [bigmax_leq_seqP]
  intro i h_mem h_P
  exact le_trans (h_le i h_mem h_P) (leq_bigmax_cond_seq P r F2 i h_mem h_P)

theorem bigmax_ord_ltn_identity (n : ℕ) :
    n > 0 →
    Finset.sup Finset.univ (fun (i : Fin n) => i.val) < n := by
  intro h_pos
  rw [Finset.sup_lt_iff h_pos]
  intro i _
  exact i.isLt

theorem bigmax_ltn_ord (n : ℕ) (P : ℕ → Prop) [DecidablePred P] (i0 : Fin n) :
    P i0.val →
    Finset.sup (Finset.univ.filter (fun (i : Fin n) => P i.val)) (fun (i : Fin n) => i.val) < n := by
  intro hP
  have h_pos : n > 0 := i0.pos
  rw [Finset.sup_lt_iff h_pos]
  intro i hi
  exact i.isLt

theorem bigmax_pred (n : ℕ) (P : ℕ → Prop) [DecidablePred P] (i0 : Fin n) :
    P i0.val →
    P (Finset.sup (Finset.univ.filter (fun (i : Fin n) => P i.val)) (fun (i : Fin n) => i.val)) := by
  intro hP
  set S := Finset.univ.filter (fun (i : Fin n) => P i.val)
  have hne : S.Nonempty := ⟨i0, Finset.mem_filter.mpr ⟨Finset.mem_univ i0, hP⟩⟩
  obtain ⟨j, hj_mem, hj_eq⟩ := Finset.exists_mem_eq_sup S hne (fun (i : Fin n) => i.val)
  simp only [hj_eq]
  exact (Finset.mem_filter.mp hj_mem).2

end ExtraLemmas

end Prosa.Util.Minmax
