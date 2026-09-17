-- Translated from: ../rt-proofs/classic/util/pick.v
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Basic

namespace Prosa.Classic.Util.Pick

section Auxiliary

def default0 {n : ℕ} (x : Option (Fin n)) : ℕ :=
  match x with
  | some y => y.val
  | none => 0

noncomputable def arg_pred_nat {n : ℕ} (P : Fin n → Bool) (ord : Fin n → Fin n → Bool) :
    Fin n → Bool :=
  fun i => P i && decide (∀ j : Fin n, P j → ord i j)

noncomputable def pred_min_nat {n : ℕ} (P : Fin n → Bool) : Fin n → Bool :=
  arg_pred_nat P (fun x y => decide (x.val ≤ y.val))

noncomputable def pred_max_nat {n : ℕ} (P : Fin n → Bool) : Fin n → Bool :=
  arg_pred_nat P (fun x y => decide (y.val ≤ x.val))

def to_pred_ord (n : ℕ) (P : ℕ → Bool) : Fin n → Bool :=
  fun x => P x.val

end Auxiliary

noncomputable def pick_any (n : ℕ) (P : ℕ → Bool) : ℕ :=
  if h : ∃ i : Fin n, P i.val then
    (Classical.choose h).val
  else
    0

noncomputable def pick_min (n : ℕ) (P : ℕ → Bool) : ℕ :=
  let s := (Finset.range n).filter (fun x => P x)
  if h : s.Nonempty then s.min' h else 0

noncomputable def pick_max (n : ℕ) (P : ℕ → Bool) : ℕ :=
  let s := (Finset.range n).filter (fun x => P x)
  if h : s.Nonempty then s.max' h else 0

section PickAny

variable (n : ℕ)
variable (p : ℕ → Bool)
variable (P : ℕ → Prop)

theorem pick_any_holds
    (EX : ∃ x, x < n ∧ p x = true)
    (HOLDS : ∀ x, p x = true → P x) :
    P (pick_any n p) := by
  unfold pick_any
  obtain ⟨x, hlt, hpx⟩ := EX
  have hex : ∃ i : Fin n, p i.val = true := ⟨⟨x, hlt⟩, hpx⟩
  simp [dif_pos hex]
  exact HOLDS _ (Classical.choose_spec hex)

end PickAny

section PickMin

variable (n : ℕ)
variable (p : ℕ → Bool)
variable (P : ℕ → Prop)

variable (EX : ∃ x, x < n ∧ p x = true)
include EX

section Bound

theorem pick_min_ltn :
    pick_min n p < n := by
  unfold pick_min
  obtain ⟨x, hlt, hpx⟩ := EX
  set s := (Finset.range n).filter (fun x => p x)
  have hmem : x ∈ s := by
    simp [s, Finset.mem_filter, Finset.mem_range, hlt, hpx]
  have hne : s.Nonempty := ⟨x, hmem⟩
  rw [dif_pos hne]
  have hmin_mem : s.min' hne ∈ s := Finset.min'_mem s hne
  simp [s, Finset.mem_filter, Finset.mem_range] at hmin_mem
  exact hmin_mem.1

end Bound

section Minimum

theorem pick_min_holds
    (MIN : ∀ x, x < n → p x = true → (∀ y, y < n → p y = true → x ≤ y) → P x) :
    P (pick_min n p) := by
  unfold pick_min
  obtain ⟨x, hlt, hpx⟩ := EX
  set s := (Finset.range n).filter (fun x => p x)
  have hmem : x ∈ s := by
    simp [s, Finset.mem_filter, Finset.mem_range, hlt, hpx]
  have hne : s.Nonempty := ⟨x, hmem⟩
  rw [dif_pos hne]
  set m := s.min' hne
  have hm_mem : m ∈ s := Finset.min'_mem s hne
  have hm_range : m < n := by
    simp [s, Finset.mem_filter, Finset.mem_range] at hm_mem; exact hm_mem.1
  have hm_pred : p m = true := by
    simp [s, Finset.mem_filter, Finset.mem_range] at hm_mem; exact hm_mem.2
  apply MIN m hm_range hm_pred
  intro y hy hpy
  have hy_mem : y ∈ s := by
    simp [s, Finset.mem_filter, Finset.mem_range, hy, hpy]
  exact Finset.min'_le s y hy_mem

end Minimum

end PickMin

section PickMax

variable (n : ℕ)
variable (p : ℕ → Bool)
variable (P : ℕ → Prop)

variable (EX : ∃ x, x < n ∧ p x = true)
include EX

section Bound

theorem pick_max_ltn :
    pick_max n p < n := by
  unfold pick_max
  obtain ⟨x, hlt, hpx⟩ := EX
  set s := (Finset.range n).filter (fun x => p x)
  have hmem : x ∈ s := by
    simp [s, Finset.mem_filter, Finset.mem_range, hlt, hpx]
  have hne : s.Nonempty := ⟨x, hmem⟩
  rw [dif_pos hne]
  have hmax_mem : s.max' hne ∈ s := Finset.max'_mem s hne
  rw [Finset.mem_filter] at hmax_mem
  rw [Finset.mem_range] at hmax_mem
  exact hmax_mem.1

end Bound

section Maximum

theorem pick_max_holds
    (MAX : ∀ x, x < n → p x = true → (∀ y, y < n → p y = true → x ≥ y) → P x) :
    P (pick_max n p) := by
  unfold pick_max
  obtain ⟨x, hlt, hpx⟩ := EX
  set s := (Finset.range n).filter (fun x => p x)
  have hmem : x ∈ s := by
    simp [s, Finset.mem_filter, Finset.mem_range, hlt, hpx]
  have hne : s.Nonempty := ⟨x, hmem⟩
  rw [dif_pos hne]
  set m := s.max' hne
  have hm_mem : m ∈ s := Finset.max'_mem s hne
  have hm_range : m < n := by
    simp [s, Finset.mem_filter, Finset.mem_range] at hm_mem; exact hm_mem.1
  have hm_pred : p m = true := by
    simp [s, Finset.mem_filter, Finset.mem_range] at hm_mem; exact hm_mem.2
  apply MAX m hm_range hm_pred
  intro y hy hpy
  have hy_mem : y ∈ s := by
    simp [s, Finset.mem_filter, Finset.mem_range, hy, hpy]
  exact Finset.le_max' s y hy_mem

end Maximum

end PickMax

section Predicate

variable (n : ℕ)
variable (p : ℕ → Bool)

variable (EX : ∃ x, x < n ∧ p x = true)
include EX

theorem pick_any_pred :
    p (pick_any n p) = true := by
  exact pick_any_holds n p (fun x => p x = true) EX (fun x hx => hx)

theorem pick_min_pred :
    p (pick_min n p) = true := by
  exact pick_min_holds n p (fun x => p x = true) EX (fun x _ hpx _ => hpx)

theorem pick_max_pred :
    p (pick_max n p) = true := by
  exact pick_max_holds n p (fun x => p x = true) EX (fun x _ hpx _ => hpx)

end Predicate

section PickMinCompare

variable (n : ℕ)
variable (p1 p2 : ℕ → Bool)

variable (EX1 : ∃ x, x < n ∧ p1 x = true)
variable (EX2 : ∃ x, x < n ∧ p2 x = true)
include EX1 EX2

theorem pick_min_compare
    (OUT : ∀ x y, x < n → y < n → p1 x = true → p2 y = true → p1 y = false → x ≤ y) :
    pick_min n p1 ≤ pick_min n p2 := by
  set m1 := pick_min n p1
  set m2 := pick_min n p2
  by_cases h : p1 m2 = true
  · -- m2 satisfies p1, so m1 ≤ m2 since m1 is the minimum of p1
    exact pick_min_holds n p1 (fun x => x ≤ m2) EX1
      (fun x _ _ hall => hall m2 (pick_min_ltn n p2 EX2) h)
  · -- m2 doesn't satisfy p1, use OUT
    have h_false : p1 m2 = false := by
      revert h; cases p1 m2 <;> simp
    exact OUT m1 m2
      (pick_min_ltn n p1 EX1)
      (pick_min_ltn n p2 EX2)
      (pick_min_pred n p1 EX1)
      (pick_min_pred n p2 EX2)
      h_false

end PickMinCompare

end Prosa.Classic.Util.Pick
