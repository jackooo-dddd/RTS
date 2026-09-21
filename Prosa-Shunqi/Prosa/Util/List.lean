-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: util/list.v

import Mathlib.Data.List.Basic
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

end Prosa.Util.List
