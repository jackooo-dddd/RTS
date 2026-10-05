import Prosa.Util.Nondecreasing

namespace Prosa.Validation.NondecreasingInterface

open Prosa.Util.List
open Prosa.Util.Nondecreasing

universe u v

/-- Public validation spelling of the source's zero-defaulted list lookup. -/
def nthD (xs : List Nat) (n : Nat) : Nat := xs.getD n 0

/-- Exact body guards for the three production definitions. -/
theorem production_nondecreasing_sequence_eq (xs : List Nat) :
    nondecreasing_sequence xs ↔
      ∀ n₁ n₂, n₁ ≤ n₂ ∧ n₂ < xs.length → nthD xs n₁ ≤ nthD xs n₂ :=
  Iff.rfl

theorem production_increasing_sequence_eq (xs : List Nat) :
    increasing_sequence xs ↔
      ∀ n₁ n₂, n₁ < n₂ ∧ n₂ < xs.length → nthD xs n₁ < nthD xs n₂ :=
  Iff.rfl

theorem production_distances_eq (xs : List Nat) :
    distances xs = (xs.zip (xs.drop 1)).map (fun p => p.2 - p.1) := rfl

/-- Constructor equations for the artifact-local ordered-list interface. -/
theorem production_nthD_nil (n : Nat) : nthD [] n = 0 := by
  rfl

theorem production_nthD_zero (x : Nat) (xs : List Nat) :
    nthD (x :: xs) 0 = x := by rfl

theorem production_nthD_succ (x : Nat) (xs : List Nat) (n : Nat) :
    nthD (x :: xs) (n + 1) = nthD xs n := by
  rfl

theorem production_length_nil : List.length ([] : List Nat) = 0 := rfl

theorem production_length_cons (x : Nat) (xs : List Nat) :
    List.length (x :: xs) = Nat.succ xs.length := rfl

/-- Direct computation equations for the actual production `distances` body.
    They avoid replaying the implementation proof graph in Rocq. -/
theorem production_distances_nil : distances [] = [] := rfl

theorem production_distances_single (x : Nat) : distances [x] = [] := rfl

theorem production_distances_cons (x y : Nat) (xs : List Nat) :
    distances (x :: y :: xs) = (y - x) :: distances (y :: xs) := rfl

theorem production_append_nil (ys : List Nat) : [] ++ ys = ys := rfl

theorem production_append_cons (x : Nat) (xs ys : List Nat) :
    (x :: xs) ++ ys = x :: (xs ++ ys) := rfl

theorem production_drop_zero (xs : List Nat) : xs.drop 0 = xs := rfl

theorem production_drop_succ_nil (n : Nat) :
    ([] : List Nat).drop (Nat.succ n) = [] := rfl

theorem production_drop_succ_cons (x : Nat) (xs : List Nat) (n : Nat) :
    (x :: xs).drop (Nat.succ n) = xs.drop n := rfl

theorem production_zip_nil_left (ys : List Nat) :
    List.zip ([] : List Nat) ys = [] := rfl

theorem production_zip_nil_right (xs : List Nat) :
    List.zip xs ([] : List Nat) = [] := by cases xs <;> rfl

theorem production_zip_cons (x y : Nat) (xs ys : List Nat) :
    List.zip (x :: xs) (y :: ys) = (x, y) :: List.zip xs ys := rfl

theorem production_map_nil (f : Nat × Nat → Nat) :
    List.map f [] = [] := rfl

theorem production_map_cons (f : Nat × Nat → Nat) (p : Nat × Nat)
    (xs : List (Nat × Nat)) :
    List.map f (p :: xs) = f p :: List.map f xs := rfl

theorem production_filter_nil (p : Nat → Bool) :
    List.filter p [] = [] := rfl

theorem production_filter_cons (p : Nat → Bool) (x : Nat) (xs : List Nat) :
    List.filter p (x :: xs) =
      match p x with
      | true => x :: List.filter p xs
      | false => List.filter p xs := rfl

theorem production_dedup_nil : List.dedup ([] : List Nat) = [] := rfl

theorem production_dedup_cons (x : Nat) (xs : List Nat) :
    List.dedup (x :: xs) =
      if x ∈ xs then List.dedup xs else x :: List.dedup xs := by
  simp [List.dedup_cons]

/-- Exact equations for already accepted utility operations reused here. -/
theorem production_index_iota_eq (a b : Nat) :
    Prosa.Util.List.index_iota a b = List.range' a (b - a) := rfl

theorem production_first0_nil : first0 [] = 0 := rfl

theorem production_first0_cons (x : Nat) (xs : List Nat) :
    first0 (x :: xs) = x := rfl

theorem production_last0_nil : last0 [] = 0 := rfl

theorem production_last0_cons (x : Nat) (xs : List Nat) (h : xs ≠ []) :
    last0 (x :: xs) = last0 xs := Prosa.Util.List.last0_cons x xs h

theorem production_max0_nil : max0 [] = 0 := rfl

theorem production_max0_cons (x : Nat) (xs : List Nat) :
    max0 (x :: xs) = Nat.max x (max0 xs) :=
  Prosa.Util.List.max0_cons x xs

theorem production_range_prime_zero (start : Nat) :
    List.range' start 0 = [] := rfl

theorem production_range_prime_succ (start len : Nat) :
    List.range' start (Nat.succ len) = start :: List.range' (start + 1) len := rfl

end Prosa.Validation.NondecreasingInterface
