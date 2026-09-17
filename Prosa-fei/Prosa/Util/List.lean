-- Translated from: ../rt-proofs/util/list.v
import Mathlib.Tactic
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Nodup
import Mathlib.Data.Finset.Basic
import Prosa.Util.Ssromega

namespace Prosa.Util.List

open List

def max0 (xs : List ℕ) : ℕ := xs.foldl Nat.max 0

def first0 (xs : List ℕ) : ℕ := xs.headD 0

def last0 (xs : List ℕ) : ℕ := xs.getLastD 0

def nthD (xs : List ℕ) (n : ℕ) : ℕ := xs.getD n 0

notation:30 xs " [| " n " |] " => nthD xs n

section Last0

  theorem last0_cons (x : ℕ) (xs : List ℕ) (h : xs ≠ []) :
      last0 (x :: xs) = last0 xs := by
    cases xs with
    | nil => contradiction
    | cons y ys =>
      simp only [last0, List.getLastD]
      exact List.getLast_cons (h := List.cons_ne_nil y ys)

  theorem last0_cat (xs_l xs_r : List ℕ) (h : xs_r ≠ []) :
      last0 (xs_l ++ xs_r) = last0 xs_r := by
    induction xs_l with
    | nil => simp
    | cons a tl ih =>
      rw [List.cons_append, last0_cons]
      · exact ih
      · intro hc; simp at hc; exact h hc.2

  theorem last0_nth (xs : List ℕ) :
      last0 xs = nthD xs (xs.length - 1) := by
    unfold last0 nthD
    cases xs with
    | nil => simp [List.getLastD, List.getD]
    | cons a tl =>
      simp only [List.length_cons]
      induction tl generalizing a with
      | nil => simp [List.getLastD, List.getD]
      | cons b tl ih =>
        simp only [List.getLastD, List.getLast_cons]
        simp only [List.length_cons, Nat.add_sub_cancel]
        rw [List.getD_cons_succ]
        exact ih b

  theorem last0_ex_cat (x : ℕ) (xs : List ℕ) (h1 : xs ≠ []) (h2 : last0 xs = x) :
      ∃ xsh, xsh ++ [x] = xs := by
    induction xs with
    | nil => contradiction
    | cons a tl ih =>
      cases tl with
      | nil =>
        simp [last0, List.getLastD] at h2
        subst h2; exact ⟨[], rfl⟩
      | cons b tl =>
        have hne : b :: tl ≠ [] := List.cons_ne_nil b tl
        rw [last0_cons a (b :: tl) hne] at h2
        obtain ⟨xsh, hxsh⟩ := ih hne h2
        exact ⟨a :: xsh, by simp [← hxsh]⟩

  theorem last0_filter (x : ℕ) (xs : List ℕ) (P : ℕ → Bool)
      (h1 : xs ≠ []) (h2 : last0 xs = x) (h3 : P x = true) :
      last0 (xs.filter P) = x := by
    obtain ⟨xsh, hxsh⟩ := last0_ex_cat x xs h1 h2
    rw [← hxsh, List.filter_append, List.filter_cons, h3]
    simp only [ite_true, List.filter_nil]
    rw [last0_cat _ [x] (by simp)]
    simp [last0, List.getLastD]

end Last0

section Max0

  theorem max0_cons (x : ℕ) (xs : List ℕ) :
      max0 (x :: xs) = Nat.max x (max0 xs) := by
    unfold max0; simp only [List.foldl_cons, Nat.zero_max]
    induction xs generalizing x with
    | nil => simp
    | cons a tl ih =>
      simp only [List.foldl_cons, Nat.zero_max]
      rw [ih (Nat.max x a), ih a]
      exact max_assoc x a (tl.foldl Nat.max 0)

  theorem max0_of_uniform_set (k : ℕ) (xs : List ℕ)
      (h1 : xs.length > 0) (h2 : ∀ x, x ∈ xs → x = k) :
      max0 xs = k := by
    induction xs with
    | nil => simp at h1
    | cons a xs ih =>
      have ha : a = k := h2 a (List.mem_cons_self)
      cases xs with
      | nil => simp [max0, List.foldl, ha]
      | cons b xs =>
        rw [max0_cons, ih]
        · subst ha; simp [Nat.max_self]
        · simp
        · intro x hx; exact h2 x (List.mem_cons_of_mem a hx)

  theorem in_max0_le (xs : List ℕ) (x : ℕ) (h : x ∈ xs) :
      x ≤ max0 xs := by
    induction xs with
    | nil => simp at h
    | cons a xs ih =>
      rw [max0_cons]
      rcases List.mem_cons.mp h with rfl | hin
      · exact Nat.le_max_left x (max0 xs)
      · exact Nat.le_trans (ih hin) (Nat.le_max_right a (max0 xs))

  theorem max0_in_seq (xs : List ℕ) (h : xs ≠ []) :
      max0 xs ∈ xs := by
    induction xs with
    | nil => contradiction
    | cons a xs ih =>
      cases xs with
      | nil => simp [max0, List.foldl]
      | cons b xs =>
        rw [max0_cons]
        rcases Nat.le_total a (max0 (b :: xs)) with hle | hle
        · simp only [max_eq_right hle]
          exact List.mem_cons_of_mem a (ih (List.cons_ne_nil b xs))
        · simp only [max_eq_left hle]
          exact List.mem_cons_self ..

  theorem max0_2cons_eq (x : ℕ) (xs : List ℕ) :
      max0 (x :: x :: xs) = max0 (x :: xs) := by
    rw [max0_cons x (x :: xs), max0_cons x xs]
    simp [Nat.max_assoc, Nat.max_self]

  theorem max0_2cons_le (x1 x2 : ℕ) (xs : List ℕ) (h : x1 ≤ x2) :
      max0 (x1 :: x2 :: xs) = max0 (x2 :: xs) := by
    rw [max0_cons]
    exact max_eq_right (Nat.le_trans h (in_max0_le _ x2 (List.mem_cons_self)))

  theorem max0_rem0 (xs : List ℕ) :
      max0 (xs.filter (· > 0)) = max0 xs := by
    induction xs with
    | nil => rfl
    | cons a xs ih =>
      simp only [List.filter_cons]
      cases a with
      | zero =>
        simp only [Nat.zero_lt_succ, decide_false, Nat.not_lt_zero, ite_false]
        rw [max0_cons]
        simp only [Nat.zero_max]
        exact ih
      | succ n =>
        simp only [Nat.succ_pos, decide_true, ite_true]
        rw [max0_cons, max0_cons, ih]

  theorem last_of_seq_le_max_of_seq (xs : List ℕ) :
      last0 xs ≤ max0 xs := by
    cases xs with
    | nil => simp [last0, max0, List.getLastD, List.foldl]
    | cons x xs =>
      induction xs generalizing x with
      | nil => simp [last0, max0, List.getLastD, List.foldl]
      | cons y ys ih =>
        rw [last0_cons x (y :: ys) (List.cons_ne_nil y ys), max0_cons]
        exact Nat.le_trans (ih y) (Nat.le_max_right x (max0 (y :: ys)))

  theorem max_of_dominating_seq (xs ys : List ℕ)
      (h : ∀ n, nthD xs n ≤ nthD ys n) :
      max0 xs ≤ max0 ys := by
    suffices key : ∀ (len : ℕ) (xs ys : List ℕ),
        xs.length ≤ len → ys.length ≤ len →
        (∀ n, nthD xs n ≤ nthD ys n) → max0 xs ≤ max0 ys by
      exact key (max xs.length ys.length) xs ys (Nat.le_max_left ..) (Nat.le_max_right ..) h
    intro len
    induction len with
    | zero =>
      intro xs ys hxs hys hdom
      cases xs with
      | nil => simp [max0, List.foldl]
      | cons _ _ => simp at hxs
    | succ n ihn =>
      intro xs ys hxs hys hdom
      cases xs with
      | nil => simp [max0, List.foldl]
      | cons a xs =>
        cases ys with
        | nil =>
          have ha := hdom 0; simp [nthD, List.getD] at ha
          have htl : ∀ m, nthD xs m ≤ nthD ([] : List ℕ) m := by
            intro m; have := hdom (m + 1)
            unfold nthD at this ⊢; simp at this ⊢; exact this
          have : max0 xs = 0 := by
            apply Nat.le_zero.mp
            apply ihn xs [] (by simp at hxs; omega) (by simp)
            exact htl
          simp [max0_cons, this]; omega
        | cons b ys =>
          rw [max0_cons, max0_cons]
          have ha := hdom 0; simp [nthD, List.getD] at ha
          have htl : ∀ m, nthD xs m ≤ nthD ys m := by
            intro m; have := hdom (m + 1)
            unfold nthD at this ⊢; simp at this ⊢; exact this
          exact sup_le_sup ha (ihn xs ys (by simp at hxs; omega) (by simp at hys; omega) htl)

end Max0

section RemList

  theorem rem_in {T : Type _} [DecidableEq T] (x y : T) (xs : List T)
      (h : x ∈ xs.erase y) : x ∈ xs := by
    exact List.mem_of_mem_erase h

  theorem filter_size_rem {T : Type _} [DecidableEq T] (x : T) (xs : List T) (P : T → Bool)
      (h1 : x ∈ xs) (h2 : P x = true) :
      (xs.filter P).length = ((xs.erase x).filter P).length + 1 := by
    induction xs with
    | nil => simp at h1
    | cons a xs ih =>
      by_cases hax : a = x
      · -- a = x: erase removes head
        subst hax  -- replaces x with a everywhere
        simp only [List.filter_cons, h2, ite_true, List.length_cons]
        simp
      · -- a ≠ x: erase keeps head
        have hin : x ∈ xs := by
          rcases List.mem_cons.mp h1 with heq | hin
          · exact absurd heq.symm hax
          · exact hin
        rw [show (a :: xs).erase x = a :: xs.erase x from by simp [hax]]
        simp only [List.filter_cons]
        cases hP : P a <;> simp [List.filter_cons, hP, ih hin]

end RemList

section AdditionalLemmas

  theorem nth0_cons (x : ℕ) (xs : List ℕ) (n : ℕ) (h : n > 0) :
      nthD (x :: xs) n = nthD xs (n - 1) := by
    unfold nthD
    cases n with
    | zero => omega
    | succ n => simp [List.getD_cons_succ]

  theorem seq_elim_last {X : Type _} (n : ℕ) (xs : List X) (h : xs.length = n + 1) :
      ∃ x xs__c, xs = xs__c ++ [x] ∧ xs__c.length = n := by
    induction n generalizing xs with
    | zero =>
      match xs, h with
      | [a], _ => exact ⟨a, [], rfl, rfl⟩
    | succ n ih =>
      match xs, h with
      | a :: xs', h =>
        have hlen : xs'.length = n + 1 := by simp at h; omega
        obtain ⟨x, xs__c, heq, hlen'⟩ := ih xs' hlen
        exact ⟨x, a :: xs__c, by rw [heq]; simp, by simp [hlen']⟩

  theorem in_cat {X : Type _} [DecidableEq X] (x : X) (xs : List X)
      (h : x ∈ xs) : ∃ xsl xsr, xs = xsl ++ [x] ++ xsr := by
    induction xs with
    | nil => simp at h
    | cons a xs ih =>
      rcases List.mem_cons.mp h with rfl | hin
      · exact ⟨[], xs, by simp⟩
      · obtain ⟨xsl, xsr, heq⟩ := ih hin
        exact ⟨a :: xsl, xsr, by simp [heq]⟩

  theorem subseq_leq_size {X : Type _} [DecidableEq X] (xs ys : List X)
      (h1 : xs.Nodup) (h2 : ∀ x, x ∈ xs → x ∈ ys) :
      xs.length ≤ ys.length := by
    calc xs.length = xs.toFinset.card := (List.toFinset_card_of_nodup h1).symm
    _ ≤ ys.toFinset.card := by
        apply Finset.card_le_card
        intro a ha; rw [List.mem_toFinset] at ha ⊢; exact h2 a ha
    _ ≤ ys.length := List.toFinset_card_le ys

  theorem filter_in_pred0 {X : Type _} [DecidableEq X] (xs : List X) (P : X → Bool)
      (h : ∀ x, x ∈ xs → P x = false) :
      xs.filter P = [] := by
    induction xs with
    | nil => simp
    | cons a xs ih =>
      simp only [List.filter_cons]
      rw [h a (List.mem_cons_self)]
      exact ih (fun x hx => h x (List.mem_cons_of_mem a hx))

end AdditionalLemmas

def rem_all {X : Type _} [DecidableEq X] (x : X) : List X → List X
  | [] => []
  | a :: xs => if a = x then rem_all x xs else a :: rem_all x xs

section RemAllList

  theorem nin_rem_all {X : Type _} [DecidableEq X] (x : X) (xs : List X) :
      x ∉ rem_all x xs := by
    induction xs with
    | nil => simp [rem_all]
    | cons a xs ih =>
      simp only [rem_all]
      split
      · exact ih
      · rename_i hne
        simp only [List.mem_cons, not_or]
        exact ⟨Ne.symm hne, ih⟩

  theorem in_rem_all {X : Type _} [DecidableEq X] (a x : X) (xs : List X)
      (h : a ∈ rem_all x xs) : a ∈ xs := by
    induction xs with
    | nil => simp [rem_all] at h
    | cons b xs ih =>
      simp only [rem_all] at h
      split at h
      · exact List.mem_cons_of_mem b (ih h)
      · rcases List.mem_cons.mp h with rfl | hin
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem b (ih hin)

  theorem rem_lt_id (x : ℕ) (xs : List ℕ)
      (h : ∀ y, y ∈ xs → x < y) :
      rem_all x xs = xs := by
    induction xs with
    | nil => rfl
    | cons a tl ih =>
      have hne : a ≠ x := by have := h a (List.mem_cons_self); omega
      simp only [rem_all, if_neg hne]
      congr 1
      exact ih (fun y hy => h y (List.mem_cons_of_mem a hy))

end RemAllList

def range (a b : ℕ) : List ℕ := List.range' a (b + 1 - a)

section IotaRange

  def index_iota (a b : ℕ) : List ℕ := List.range' a (b - a)

  theorem index_iota_lt_step (a b : ℕ) (h : a < b) :
      index_iota a b = a :: index_iota (a + 1) b := by
    simp only [index_iota]
    have hlen : b - a = (b - (a + 1)) + 1 := by omega
    rw [hlen, List.range'_succ]

  theorem range_filter_2cons (x : ℕ) (xs : List ℕ) (k : ℕ) :
      (range 0 k).filter (· ∈ (x :: x :: xs)) =
      (range 0 k).filter (· ∈ (x :: xs)) := by
    apply List.filter_congr
    intro y _
    simp only [List.mem_cons, decide_eq_decide]
    tauto

  private theorem mem_rem_all_of_ne_of_mem {X : Type _} [DecidableEq X] (y x : X) (xs : List X)
      (hne : y ≠ x) (hmem : y ∈ xs) : y ∈ rem_all x xs := by
    induction xs with
    | nil => exact hmem
    | cons c tl ih =>
      simp only [rem_all]
      split
      · rename_i hcx; subst hcx
        rcases List.mem_cons.mp hmem with rfl | hin
        · exact absurd rfl hne
        · exact ih hin
      · rcases List.mem_cons.mp hmem with rfl | hin
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (ih hin)

  theorem index_iota_filter_eqx (x a b : ℕ) (h : a ≤ x ∧ x < b) :
      (index_iota a b).filter (· == x) = [x] := by
    obtain ⟨hax, hxb⟩ := h
    suffices key : ∀ (len : ℕ) (a b : ℕ), b - a ≤ len → a ≤ x → x < b →
        (index_iota a b).filter (· == x) = [x] from
      key (b - a) a b (le_refl _) hax hxb
    intro len
    induction len with
    | zero =>
      intro a b hba hax hxb; omega
    | succ n ih =>
      intro a b hba hax hxb
      have hab : a < b := by omega
      rw [index_iota_lt_step a b hab]
      simp only [List.filter_cons]
      by_cases heq : a = x
      · subst heq
        simp only [beq_self_eq_true, ite_true]
        congr 1
        apply filter_in_pred0
        intro y hy
        simp only [index_iota] at hy
        rw [List.mem_range'] at hy
        show (y == a) = false
        rw [show (y == a) = decide (y = a) from rfl]
        simp only [decide_eq_false_iff_not]
        omega
      · have hne : (a == x) = false := by
          rw [show (a == x) = decide (a = x) from rfl]
          simp only [decide_eq_false_iff_not]; exact heq
        simp only [hne, ite_false]
        exact ih (a + 1) b (by omega) (by omega) hxb

  theorem index_iota_filter_singl (x a b : ℕ) (h : a ≤ x ∧ x < b) :
      (index_iota a b).filter (· ∈ [x]) = [x] := by
    have := index_iota_filter_eqx x a b h
    convert this using 1
    apply List.filter_congr
    intro y _
    simp [List.mem_cons, List.not_mem_nil]
    rfl

  theorem index_iota_filter_inxs (a b x : ℕ) (xs : List ℕ) (h : x < a) :
      (index_iota a b).filter (· ∈ xs) =
      (index_iota a b).filter (· ∈ rem_all x xs) := by
    apply List.filter_congr
    intro y hy
    simp only [index_iota] at hy; rw [List.mem_range'] at hy
    have hyx : y ≠ x := by omega
    simp only [decide_eq_decide]
    constructor
    · intro hyin
      induction xs with
      | nil => exact hyin
      | cons c xs ihxs =>
        simp only [rem_all]
        split
        · rename_i heq; subst heq
          rcases List.mem_cons.mp hyin with h2 | h2
          · exact absurd h2 hyx
          · exact ihxs h2
        · rcases List.mem_cons.mp hyin with h2 | h2
          · exact List.mem_cons.mpr (Or.inl h2)
          · exact List.mem_cons_of_mem _ (ihxs h2)
    · exact in_rem_all y x xs

  theorem index_iota_filter_step (x : ℕ) (xs : List ℕ) (a b : ℕ)
      (h1 : a ≤ x ∧ x < b) (h2 : ∀ y, y ∈ xs → x ≤ y) :
      (index_iota a b).filter (· ∈ (x :: xs)) =
      x :: (index_iota a b).filter (· ∈ rem_all x xs) := by
    obtain ⟨hax, hxb⟩ := h1
    suffices key : ∀ (len : ℕ) (a b : ℕ), b - a ≤ len → a ≤ x → x < b →
        (index_iota a b).filter (· ∈ (x :: xs)) =
        x :: (index_iota a b).filter (· ∈ rem_all x xs) from
      key (b - a) a b (le_refl _) hax hxb
    intro len
    induction len with
    | zero => intro a b hba hax hxb; omega
    | succ n ih =>
      intro a b hba hax hxb
      have hab : a < b := by omega
      rw [index_iota_lt_step a b hab]
      by_cases heq : a = x
      · subst heq
        show List.filter (· ∈ (a :: xs)) (a :: index_iota (a + 1) b) =
          a :: List.filter (· ∈ rem_all a xs) (a :: index_iota (a + 1) b)
        rw [List.filter_cons, List.filter_cons]
        simp only [List.mem_cons_self, decide_true, ite_true,
                   show decide (a ∈ rem_all a xs) = false from
                     decide_eq_false_iff_not.mpr (nin_rem_all a xs)]
        congr 1
        apply List.filter_congr
        intro y hy
        simp only [index_iota] at hy; rw [List.mem_range'] at hy
        simp only [decide_eq_decide]
        have hya : y ≠ a := by omega
        constructor
        · intro hyin
          rcases List.mem_cons.mp hyin with rfl | hin
          · exact absurd rfl hya
          · exact mem_rem_all_of_ne_of_mem y a xs hya hin
        · intro hyin
          exact List.mem_cons_of_mem a (in_rem_all y a xs hyin)
      · have halt : a < x := by omega
        have hnotmem1 : a ∉ (x :: xs) := by
          simp only [List.mem_cons, not_or]
          exact ⟨by omega, fun hmem => by have := h2 a hmem; omega⟩
        have hnotmem2 : a ∉ rem_all x xs := by
          intro hmem; have := in_rem_all a x xs hmem; have := h2 a this; omega
        show List.filter (· ∈ (x :: xs)) (a :: index_iota (a + 1) b) =
          x :: List.filter (· ∈ rem_all x xs) (a :: index_iota (a + 1) b)
        rw [List.filter_cons, List.filter_cons]
        simp only [show decide (a ∈ x :: xs) = false from decide_eq_false_iff_not.mpr hnotmem1,
                   show decide (a ∈ rem_all x xs) = false from decide_eq_false_iff_not.mpr hnotmem2]
        exact ih (a + 1) b (by omega) (by omega) hxb

  theorem range_iota_filter_step (x : ℕ) (xs : List ℕ) (k : ℕ)
      (h1 : x ≤ k) (h2 : ∀ y, y ∈ xs → x ≤ y) :
      (range 0 k).filter (· ∈ (x :: xs)) =
      x :: (range 0 k).filter (· ∈ rem_all x xs) := by
    unfold range
    apply index_iota_filter_step
    · exact ⟨Nat.zero_le x, by omega⟩
    · exact h2

  theorem iota_filter_gt (x a b idx : ℕ) (P : ℕ → Bool)
      (h1 : x < a) (h2 : idx < ((index_iota a b).filter P).length) :
      x < ((index_iota a b).filter P).getD idx 0 := by
    suffices key : ∀ (len : ℕ) (a b idx : ℕ), b - a ≤ len → x < a →
        idx < ((index_iota a b).filter P).length →
        x < ((index_iota a b).filter P).getD idx 0 from
      key (b - a) a b idx (le_refl _) h1 h2
    intro len
    induction len with
    | zero =>
      intro a b idx hlen hxa hidx
      simp only [index_iota] at hidx
      have hba : b - a = 0 := by omega
      rw [hba] at hidx; simp at hidx
    | succ n ih =>
      intro a b idx hlen hxa hidx
      by_cases hab : b ≤ a
      · simp only [index_iota] at hidx
        have : b - a = 0 := by omega
        rw [this] at hidx; simp at hidx
      · push_neg at hab
        rw [index_iota_lt_step a b hab] at hidx ⊢
        simp only [List.filter_cons] at hidx ⊢
        by_cases hPa : P a = true
        · simp only [hPa, ite_true] at hidx ⊢
          cases idx with
          | zero =>
            simp only [List.getD_cons_zero]
            exact hxa
          | succ idx =>
            simp only [List.length_cons] at hidx
            rw [List.getD_cons_succ]
            exact ih (a + 1) b idx (by omega) (by omega) (by omega)
        · simp only [Bool.not_eq_true] at hPa
          simp only [hPa] at hidx ⊢
          exact ih (a + 1) b idx (by omega) (by omega) hidx

end IotaRange

end Prosa.Util.List
