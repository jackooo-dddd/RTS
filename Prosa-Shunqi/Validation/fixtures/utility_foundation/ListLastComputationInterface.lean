import Prosa.Util.List

/-!
Validation-only monomorphic computation equations.  Every proof is `rfl`, so
the Lean kernel confirms that these are definitional observations of the exact
operations used by the freshly compiled production module; they do not add a
semantic premise or follow Mathlib theorem proof dependencies.
-/

namespace Prosa.Validation.ListLastInterface

universe u

theorem nat_zero : (0 : Nat) = Nat.zero := by rfl

theorem nat_one : (1 : Nat) = Nat.succ Nat.zero := by rfl

theorem append_nil (ys : List Nat) : ([] ++ ys) = ys := by rfl

theorem append_cons (x : Nat) (xs ys : List Nat) :
    (x :: xs) ++ ys = x :: (xs ++ ys) := by rfl

theorem filter_nil (P : Nat → Bool) : List.filter P [] = [] := by rfl

theorem filter_cons (P : Nat → Bool) (x : Nat) (xs : List Nat) :
    List.filter P (x :: xs) =
      match P x with
      | true => x :: List.filter P xs
      | false => List.filter P xs := by
  rfl

theorem length_nil : List.length ([] : List Nat) = 0 := by rfl

theorem length_cons (x : Nat) (xs : List Nat) :
    List.length (x :: xs) = List.length xs + 1 := by rfl

theorem length_cons_succ (x : Nat) (xs : List Nat) :
    List.length (x :: xs) = Nat.succ (List.length xs) := by rfl

theorem getD_nil (n : Nat) : List.getD ([] : List Nat) n 0 = 0 := by
  rfl

theorem getD_zero (x : Nat) (xs : List Nat) :
    List.getD (x :: xs) 0 0 = x := by rfl

theorem getD_succ (x : Nat) (xs : List Nat) (n : Nat) :
    List.getD (x :: xs) (n + 1) 0 = List.getD xs n 0 := by rfl

theorem getD_succ_direct (x : Nat) (xs : List Nat) (n : Nat) :
    List.getD (x :: xs) (Nat.succ n) 0 = List.getD xs n 0 := by rfl

theorem sub_zero (n : Nat) : n - 0 = n := by rfl

theorem sub_succ (n m : Nat) : n - (m + 1) = Nat.pred (n - m) := by
  rfl

theorem sub_one (n : Nat) : n - 1 = Nat.pred n := by rfl

theorem generic_erase_nil {T : Type u} [DecidableEq T] (y : T) :
    List.erase [] y = [] := by
  rfl

theorem generic_erase_cons {T : Type u} [deq : DecidableEq T]
    (a : T) (xs : List T) (y : T) :
    List.erase (a :: xs) y =
      match @decide (a = y) (deq a y) with
      | true => xs
      | false => a :: List.erase xs y := by
  rfl

theorem generic_filter_nil {T : Type u} (P : T → Bool) :
    List.filter P [] = [] := by rfl

theorem generic_filter_cons {T : Type u} (P : T → Bool)
    (a : T) (xs : List T) :
    List.filter P (a :: xs) =
      match P a with
      | true => a :: List.filter P xs
      | false => List.filter P xs := by
  rfl

theorem generic_length_nil {T : Type u} :
    List.length ([] : List T) = 0 := by rfl

theorem generic_length_cons {T : Type u} (a : T) (xs : List T) :
    List.length (a :: xs) = Nat.succ (List.length xs) := by rfl

/- This is a validation interface for the actual `eraseDups` implementation.
   Unlike the equations above it is not definitional (`eraseDups` uses its
   tail-recursive loop), so its proof body is exported and checked by both
   kernels. It is an operation-level dependency, not the Prosa target theorem
   being validated. -/
theorem generic_mem_eraseDups {T : Type u} [DecidableEq T]
    (x : T) (xs : List T) :
    x ∈ xs.eraseDups ↔ x ∈ xs := by
  exact List.mem_eraseDups

/-- Kernel-checked equations for the actual production `rem_all` body. -/
theorem generic_rem_all_nil {T : Type u} [DecidableEq T] (x : T) :
    Prosa.Util.List.rem_all x [] = [] := by
  rfl

theorem generic_rem_all_cons {T : Type u} [deq : DecidableEq T]
    (x a : T) (xs : List T) :
    Prosa.Util.List.rem_all x (a :: xs) =
      if a = x then Prosa.Util.List.rem_all x xs
      else a :: Prosa.Util.List.rem_all x xs := by
  rfl

end Prosa.Validation.ListLastInterface
