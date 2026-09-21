-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: util/list.v

import Mathlib.Data.List.Basic
import Mathlib.Data.List.Chain
import Prosa.Util.Supremum

namespace Prosa.Util.List

/-- Maximum of a sequence of natural numbers, with `0` for the empty list. -/
def max0 (xs : List Nat) : Nat := xs.foldl Nat.max 0

/-- First element of a sequence of natural numbers, with `0` for the empty list. -/
def first0 (xs : List Nat) : Nat := xs.headD 0

/-- Last element of a sequence of natural numbers, with `0` for the empty list. -/
def last0 (xs : List Nat) : Nat := xs.getLastD 0

/-- Removing a head does not change the last element of a non-empty tail. -/
theorem last0_cons (x : Nat) (xs : List Nat) (h : xs ≠ []) :
    last0 (x :: xs) = last0 xs := by
  cases xs with
  | nil => contradiction
  | cons y ys =>
    simp only [last0, List.getLastD]
    exact List.getLast_cons (h := List.cons_ne_nil y ys)

/-- Appending a non-empty right list makes its last element observable. -/
theorem last0_cat (xs_l xs_r : List Nat) (h : xs_r ≠ []) :
    last0 (xs_l ++ xs_r) = last0 xs_r := by
  induction xs_l with
  | nil => simp
  | cons a tl ih =>
    rw [List.cons_append, last0_cons]
    · exact ih
    · intro hc
      simp at hc
      exact h hc.2

/-- `last0` agrees with defaulted indexing at `length - 1`. -/
theorem last0_nth (xs : List Nat) :
    last0 xs = xs.getD (xs.length - 1) 0 := by
  unfold last0
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

/-- A non-empty list whose `last0` is `x` splits as a prefix and `[x]`. -/
theorem last0_ex_cat (x : Nat) (xs : List Nat)
    (h1 : xs ≠ []) (h2 : last0 xs = x) :
    ∃ xsh, xsh ++ [x] = xs := by
  induction xs with
  | nil => contradiction
  | cons a tl ih =>
    cases tl with
    | nil =>
      simp [last0, List.getLastD] at h2
      subst x
      exact ⟨[], rfl⟩
    | cons b tl =>
      have hne : b :: tl ≠ [] := List.cons_ne_nil b tl
      rw [last0_cons a (b :: tl) hne] at h2
      obtain ⟨xsh, hxsh⟩ := ih hne h2
      exact ⟨a :: xsh, by simp [← hxsh]⟩

/-- Filtering preserves a retained last element. -/
theorem last0_filter (x : Nat) (xs : List Nat) (P : Nat → Bool)
    (h1 : xs ≠ []) (h2 : last0 xs = x) (h3 : P x = true) :
    last0 (xs.filter P) = x := by
  obtain ⟨xsh, hxsh⟩ := last0_ex_cat x xs h1 h2
  rw [← hxsh, List.filter_append, List.filter_cons, h3]
  simp only [ite_true, List.filter_nil]
  rw [last0_cat _ [x] (by simp)]
  simp [last0, List.getLastD]

/-- `max0` exposes the maximum of the head and the tail maximum. -/
theorem max0_cons (x : Nat) (xs : List Nat) :
    max0 (x :: xs) = Nat.max x (max0 xs) := by
  unfold max0
  simp only [List.foldl_cons, Nat.zero_max]
  induction xs generalizing x with
  | nil => simp
  | cons a tl ih =>
    simp only [List.foldl_cons, Nat.zero_max]
    rw [ih (Nat.max x a), ih a]
    exact Nat.max_assoc x a (tl.foldl Nat.max 0)

/-- A non-empty uniform list has the common value as its `max0`. -/
theorem max0_of_uniform_set (k : Nat) (xs : List Nat)
    (h1 : xs.length > 0) (h2 : ∀ x, x ∈ xs → x = k) :
    max0 xs = k := by
  induction xs with
  | nil => simp at h1
  | cons a xs ih =>
    have ha : a = k := h2 a List.mem_cons_self
    cases xs with
    | nil => simp [max0, List.foldl, ha]
    | cons b xs =>
      rw [max0_cons, ih]
      · subst a
        simp [Nat.max_self]
      · simp
      · intro x hx
        exact h2 x (List.mem_cons_of_mem a hx)

/-- Every member is bounded by `max0`. -/
theorem in_max0_le (xs : List Nat) (x : Nat) (h : x ∈ xs) :
    x ≤ max0 xs := by
  induction xs with
  | nil => simp at h
  | cons a xs ih =>
    rw [max0_cons]
    rcases List.mem_cons.mp h with rfl | hin
    · exact Nat.le_max_left x (max0 xs)
    · exact Nat.le_trans (ih hin) (Nat.le_max_right a (max0 xs))

/-- The maximum of a non-empty list occurs in that list. -/
theorem max0_in_seq (xs : List Nat) (h : xs ≠ []) :
    max0 xs ∈ xs := by
  induction xs with
  | nil => contradiction
  | cons a xs ih =>
    cases xs with
    | nil => simp [max0, List.foldl]
    | cons b xs =>
      rw [max0_cons]
      rcases Nat.le_total a (max0 (b :: xs)) with hle | hle
      · simp only [Nat.max_eq_right hle]
        exact List.mem_cons_of_mem a (ih (List.cons_ne_nil b xs))
      · simp only [Nat.max_eq_left hle]
        exact List.mem_cons_self

/-- Duplicating the head does not change `max0`. -/
theorem max0_2cons_eq (x : Nat) (xs : List Nat) :
    max0 (x :: x :: xs) = max0 (x :: xs) := by
  rw [max0_cons x (x :: xs), max0_cons x xs]
  exact (Nat.max_assoc x x (max0 xs)).symm.trans (by
    rw [Nat.max_self])

/-- A head dominated by the next element can be removed for `max0`. -/
theorem max0_2cons_le (x1 x2 : Nat) (xs : List Nat) (h : x1 ≤ x2) :
    max0 (x1 :: x2 :: xs) = max0 (x2 :: xs) := by
  rw [max0_cons]
  exact Nat.max_eq_right
    (Nat.le_trans h (in_max0_le _ x2 List.mem_cons_self))

/-- Removing zero entries preserves `max0`. -/
theorem max0_rem0 (xs : List Nat) :
    max0 (xs.filter (fun x => decide (0 < x))) = max0 xs := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    simp only [List.filter_cons]
    cases a with
    | zero =>
      simp only [Nat.not_lt_zero, decide_false, Bool.false_eq_true, if_false]
      rw [max0_cons]
      simp only [Nat.zero_max]
      exact ih
    | succ n =>
      simp only [Nat.succ_pos, decide_true, if_true]
      rw [max0_cons, max0_cons, ih]

/-- The last element is bounded by the maximum element. -/
theorem last_of_seq_le_max_of_seq (xs : List Nat) :
    last0 xs ≤ max0 xs := by
  cases xs with
  | nil => simp [last0, max0, List.getLastD, List.foldl]
  | cons x xs =>
    induction xs generalizing x with
    | nil => simp [last0, max0, List.getLastD, List.foldl]
    | cons y ys ih =>
      rw [last0_cons x (y :: ys) (List.cons_ne_nil y ys), max0_cons]
      exact Nat.le_trans (ih y) (Nat.le_max_right x (max0 (y :: ys)))

/-- Pointwise domination under defaulted indexing implies `max0` domination. -/
theorem max_of_dominating_seq (xs ys : List Nat)
    (h : ∀ n, xs.getD n 0 ≤ ys.getD n 0) :
    max0 xs ≤ max0 ys := by
  suffices key : ∀ (len : Nat) (xs ys : List Nat),
      xs.length ≤ len → ys.length ≤ len →
      (∀ n, xs.getD n 0 ≤ ys.getD n 0) → max0 xs ≤ max0 ys by
    exact key (max xs.length ys.length) xs ys
      (Nat.le_max_left ..) (Nat.le_max_right ..) h
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
        have ha := hdom 0
        simp [List.getD] at ha
        have htl : ∀ m, xs.getD m 0 ≤ ([] : List Nat).getD m 0 := by
          intro m
          have hm := hdom (m + 1)
          simp [List.getD] at hm ⊢
          exact hm
        have hxzero : max0 xs = 0 := by
          apply Nat.le_zero.mp
          have hxs' : xs.length ≤ n := by
            simpa only [List.length_cons, Nat.add_one,
              Nat.succ_le_succ_iff] using hxs
          apply ihn xs [] hxs' (by simp)
          exact htl
        rw [max0_cons, hxzero, ha]
        exact Nat.le_refl _
      | cons b ys =>
        rw [max0_cons, max0_cons]
        have ha := hdom 0
        simp [List.getD] at ha
        have htl : ∀ m, xs.getD m 0 ≤ ys.getD m 0 := by
          intro m
          have hm := hdom (m + 1)
          simp [List.getD] at hm ⊢
          exact hm
        have hxs' : xs.length ≤ n := by
          simpa only [List.length_cons, Nat.add_one,
            Nat.succ_le_succ_iff] using hxs
        have hys' : ys.length ≤ n := by
          simpa only [List.length_cons, Nat.add_one,
            Nat.succ_le_succ_iff] using hys
        apply Nat.max_le.mpr
        constructor
        · exact Nat.le_trans ha (Nat.le_max_left b (max0 ys))
        · exact Nat.le_trans (ihn xs ys hxs' hys' htl)
            (Nat.le_max_right b (max0 ys))

/-- Positive-index defaulted lookup on a cons list moves to the predecessor
    index in the tail. -/
theorem nth0_cons (x : Nat) (xs : List Nat) (n : Nat) (h : n > 0) :
    (x :: xs).getD n 0 = xs.getD (n - 1) 0 := by
  cases n with
  | zero => simp at h
  | succ n => simp [List.getD_cons_succ]

/-- Membership after erasing one occurrence implies original membership. -/
theorem rem_in {T : Type _} [DecidableEq T] (x y : T) (xs : List T)
    (h : x ∈ xs.erase y) : x ∈ xs := by
  exact List.mem_of_mem_erase h

/-- An element distinct from the erased value remains present. -/
theorem in_neq_impl_rem_in {T : Type _} [DecidableEq T]
    (x y : T) (xs : List T) (hmem : x ∈ xs) (hne : x ≠ y) :
    x ∈ xs.erase y := by
  induction xs with
  | nil => simp at hmem
  | cons a xs ih =>
    cases hbeq : a == y with
    | true =>
      have hay : a = y := eq_of_beq hbeq
      simp only [List.erase, hbeq]
      rcases List.mem_cons.mp hmem with hxa | hx
      · exact False.elim (hne (hxa.trans hay))
      · exact hx
    | false =>
      simp only [List.erase, hbeq]
      rcases List.mem_cons.mp hmem with hxa | hx
      · subst x
        exact List.mem_cons_self
      · exact List.mem_cons_of_mem a (ih hx)

/-- Removing a retained element decreases the filtered length by one. -/
theorem filter_size_rem {T : Type _} [DecidableEq T]
    (x : T) (xs : List T) (P : T → Bool)
    (h1 : x ∈ xs) (h2 : P x = true) :
    (xs.filter P).length = ((xs.erase x).filter P).length + 1 := by
  induction xs with
  | nil => simp at h1
  | cons a xs ih =>
    by_cases hax : a = x
    · subst a
      simp only [List.filter_cons, h2, ite_true, List.length_cons]
      simp
    · have hin : x ∈ xs := by
        rcases List.mem_cons.mp h1 with heq | hin
        · exact False.elim (hax heq.symm)
        · exact hin
      rw [show (a :: xs).erase x = a :: xs.erase x from by simp [hax]]
      simp only [List.filter_cons]
      cases hP : P a <;> simp [List.filter_cons, hP, ih hin]

/-- Duplicate removal preserves the Boolean membership observation. -/
theorem in_seq_equiv_undup {T : Type _} [DecidableEq T]
    (xs : List T) (x : T) :
    decide (x ∈ xs.eraseDups) = decide (x ∈ xs) := by
  simp

/-- Boolean equality of singleton lists agrees with Boolean equality of the
    corresponding optional values. -/
theorem seq1_some {T : Type _} [DecidableEq T] (x y : T) :
    decide (([x] : List T) = [y]) =
      decide ((some x : Option T) = some y) := by
  by_cases hxy : x = y <;> simp [hxy]

/-- A list of successor length splits into a prefix of the predecessor length
    and its last element. -/
theorem seq_elim_last {T : Type _} (n : Nat) (xs : List T)
    (h : xs.length = n + 1) :
    ∃ x pre, xs = pre ++ [x] ∧ pre.length = n := by
  induction n generalizing xs with
  | zero =>
      match xs, h with
      | [x], _ => exact ⟨x, [], rfl, rfl⟩
  | succ n ih =>
      match xs, h with
      | x :: tail, h =>
        have htail : tail.length = n + 1 := by
          simp at h
          omega
        obtain ⟨last, pre, hsplit, hlength⟩ := ih tail htail
        exact ⟨last, x :: pre, by rw [hsplit]; simp,
          by simp [hlength]⟩

/-- A member splits its list into a prefix, the member, and a suffix. -/
theorem in_cat {T : Type _} [DecidableEq T] (x : T) (xs : List T)
    (h : x ∈ xs) :
    ∃ left right, xs = left ++ [x] ++ right := by
  induction xs with
  | nil => simp at h
  | cons a tail ih =>
      rcases List.mem_cons.mp h with rfl | hin
      · exact ⟨[], tail, by simp⟩
      · obtain ⟨left, right, hsplit⟩ := ih hin
        exact ⟨a :: left, right, by simp [hsplit]⟩

/-- If every member fails a Boolean predicate, filtering by that predicate
    produces the empty list. -/
theorem filter_in_pred0 {T : Type _} [DecidableEq T]
    (xs : List T) (P : T → Bool)
    (h : ∀ x, x ∈ xs → P x = false) :
    xs.filter P = [] := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
      simp only [List.filter_cons, h a List.mem_cons_self, Bool.false_eq_true,
        if_false]
      exact ih (fun x hx => h x (List.mem_cons_of_mem a hx))

/-- Remove every occurrence of a value from a list. -/
def rem_all {T : Type _} [DecidableEq T] (x : T) : List T → List T
  | [] => []
  | a :: xs => if a = x then rem_all x xs else a :: rem_all x xs

/-- The removed value is absent after `rem_all`. -/
theorem nin_rem_all {T : Type _} [DecidableEq T]
    (x : T) (xs : List T) :
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

/-- Every member surviving `rem_all` was a member of the input list. -/
theorem in_rem_all {T : Type _} [DecidableEq T]
    (a x : T) (xs : List T) (h : a ∈ rem_all x xs) :
    a ∈ xs := by
  induction xs with
  | nil => simp [rem_all] at h
  | cons b xs ih =>
      simp only [rem_all] at h
      split at h
      · exact List.mem_cons_of_mem b (ih h)
      · rcases List.mem_cons.mp h with rfl | hin
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem b (ih hin)

/-- Removing a natural number strictly below every list member is the
    identity operation. -/
theorem rem_lt_id (x : Nat) (xs : List Nat)
    (h : ∀ y, y ∈ xs → x < y) :
    rem_all x xs = xs := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
      have hne : a ≠ x := by
        have hlt := h a List.mem_cons_self
        omega
      simp only [rem_all, if_neg hne]
      congr 1
      exact ih (fun y hy => h y (List.mem_cons_of_mem a hy))

/-- A duplicate-free list included in another list cannot be longer. -/
theorem subseq_leq_size {X : Type _} [DecidableEq X]
    (xs ys : List X) (huniq : xs.Nodup)
    (hsub : ∀ x, x ∈ xs → x ∈ ys) :
    xs.length ≤ ys.length := by
  exact huniq.length_le_of_subset hsub

/-- Equal-length defaulted lookups at a valid common index give a member of
    the pointwise zip. -/
theorem in_zip {X Y : Type _} [DecidableEq X] [DecidableEq Y]
    (xs : List X) (ys : List Y) (x xDefault : X) (y yDefault : Y)
    (hlen : xs.length = ys.length)
    (hlookup : ∃ idx, idx < xs.length ∧
      xs.getD idx xDefault = x ∧ ys.getD idx yDefault = y) :
    (x, y) ∈ xs.zip ys := by
  obtain ⟨idx, hidx, hx, hy⟩ := hlookup
  induction xs generalizing ys idx with
  | nil => simp at hidx
  | cons a xs ih =>
      cases ys with
      | nil => simp at hlen
      | cons b ys =>
          cases idx with
          | zero =>
              simp [List.getD] at hx hy
              subst x
              subst y
              simp
          | succ idx =>
              have hlen' : xs.length = ys.length := by
                simpa using Nat.succ.inj hlen
              have hidx' : idx < xs.length := by
                simpa using hidx
              have hx' : xs.getD idx xDefault = x := by
                simpa [List.getD_cons_succ] using hx
              have hy' : ys.getD idx yDefault = y := by
                simpa [List.getD_cons_succ] using hy
              exact List.mem_cons_of_mem (a, b)
                (ih ys hlen' idx hidx' hx' hy')

/-- Two members with the same first index are equal. -/
theorem eq_ind_in_seq {X : Type _} [DecidableEq X]
    (a b : X) (xs : List X)
    (hidx : xs.idxOf a = xs.idxOf b)
    (ha : a ∈ xs) (_hb : b ∈ xs) :
    a = b := by
  exact (List.idxOf_inj ha).mp hidx

/-- A defaulted lookup returns either the default or a list member. -/
theorem default_or_in {X : Type _} [DecidableEq X]
    (n : Nat) (d : X) (xs : List X) :
    xs.getD n d = d ∨ xs.getD n d ∈ xs := by
  induction xs generalizing n with
  | nil => simp [List.getD]
  | cons a xs ih =>
      cases n with
      | zero => simp [List.getD]
      | succ n =>
          rw [List.getD_cons_succ]
          rcases ih n with h | h
          · exact Or.inl h
          · exact Or.inr (List.mem_cons_of_mem a h)

/-- A duplicate-free list of length greater than one has two distinct
    members. -/
theorem exists_two {X : Type _} [DecidableEq X]
    (xs : List X) (hlen : 1 < xs.length) (huniq : xs.Nodup) :
    ∃ a b, a ≠ b ∧ a ∈ xs ∧ b ∈ xs := by
  cases xs with
  | nil => simp at hlen
  | cons a xs =>
      cases xs with
      | nil => simp at hlen
      | cons b xs =>
          have hnot : a ∉ b :: xs := (List.nodup_cons.mp huniq).1
          have hab : a ≠ b := by
            intro hab
            apply hnot
            simp [hab]
          exact ⟨a, b, hab, by simp, by simp⟩

/-- If every member satisfies a Boolean predicate and the list is non-empty,
    then some member satisfies it. -/
theorem has_all_nilp {T : Type _} [DecidableEq T]
    (s : List T) (P : T → Bool)
    (hall : s.all P = true) (hnil : s.isEmpty = false) :
    s.any P = true := by
  cases s with
  | nil => simp at hnil
  | cons a s =>
      simp only [List.all_cons, Bool.and_eq_true] at hall
      simp [List.any_cons, hall.1]

/-- LEAN_HELPER: adjacent Boolean relation observations for the MathComp
    `sorted` representation. -/
def boolSorted {X : Type _} (R : X → X → Bool) (xs : List X) : Prop :=
  xs.IsChain (fun x y => R x y = true)

/-- A list sorted by a natural-valued key splits its filtered members at a
    threshold into the lower and upper contiguous parts. -/
theorem sorted_split {X : Type _} [DecidableEq X]
    (xs : List X) (P : X → Bool) (f : X → Nat) (t : Nat)
    (hsorted : boolSorted (fun x y => decide (f x ≤ f y)) xs) :
    xs.filter P =
      xs.filter (fun x => P x && decide (f x ≤ t)) ++
      xs.filter (fun x => P x && decide (t < f x)) := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
      have htail : boolSorted (fun x y => decide (f x ≤ f y)) xs := by
        exact List.IsChain.of_cons hsorted
      have ihEq := ih htail
      cases hPa : P a with
      | false =>
          simpa [List.filter_cons, hPa] using ihEq
      | true =>
          by_cases hle : f a ≤ t
          · have hnlt : ¬ t < f a := Nat.not_lt_of_ge hle
            simpa [List.filter_cons, hPa, hle, hnlt] using
              congrArg (List.cons a) ihEq
          · have hgt : t < f a := Nat.lt_of_not_ge hle
            have hsortedNat :
                (a :: xs).IsChain (fun x y => f x ≤ f y) := by
              apply hsorted.imp
              intro x y hxy
              exact of_decide_eq_true hxy
            have hpair :
                (a :: xs).Pairwise (fun x y => f x ≤ f y) :=
              hsortedNat.pairwise
            have hhead : ∀ x ∈ xs, f a ≤ f x :=
              (List.pairwise_cons.mp hpair).1
            have hlowFalse : ∀ x, x ∈ xs →
                (P x && decide (f x ≤ t)) = false := by
              intro x hx
              have hax : f a ≤ f x := hhead x hx
              have hnot : ¬ f x ≤ t := by omega
              simp [hnot]
            have hlowNil :
                xs.filter (fun x => P x && decide (f x ≤ t)) = [] :=
              filter_in_pred0 xs _ hlowFalse
            simp [List.filter_cons, hPa, hle, hgt, ihEq, hlowNil]

/-- Sortedness of an append implies sortedness of each component. -/
theorem sorted_cat {X : Type _} [DecidableEq X]
    (R : X → X → Bool) (xs1 xs2 : List X)
    (_htrans : ∀ x y z, R x y = true → R y z = true → R x z = true)
    (hsorted : boolSorted R (xs1 ++ xs2)) :
    boolSorted R xs1 ∧ boolSorted R xs2 := by
  exact ⟨hsorted.left_of_append, hsorted.right_of_append⟩

/-- The default does not affect `getLastD` on a non-empty list. -/
theorem nonnil_last {X : Type _} [DecidableEq X]
    (xs : List X) (d1 d2 : X) (hne : xs ≠ []) :
    xs.getLastD d1 = xs.getLastD d2 := by
  cases xs with
  | nil => contradiction
  | cons a xs => simp [List.getLastD]

end Prosa.Util.List
