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

theorem generic_getD_nil {T : Type u} (n : Nat) (d : T) :
    List.getD ([] : List T) n d = d := by rfl

theorem generic_getD_zero {T : Type u} (a d : T) (xs : List T) :
    List.getD (a :: xs) 0 d = a := by rfl

theorem generic_getD_succ {T : Type u} (a d : T) (xs : List T) (n : Nat) :
    List.getD (a :: xs) (Nat.succ n) d = List.getD xs n d := by rfl

theorem generic_zip_nil_left {T U : Type u} (ys : List U) :
    List.zip ([] : List T) ys = [] := by rfl

theorem generic_zip_nil_right {T U : Type u} (xs : List T) :
    List.zip xs ([] : List U) = [] := by
  cases xs <;> rfl

theorem generic_zip_cons {T U : Type u} (a : T) (xs : List T)
    (b : U) (ys : List U) :
    List.zip (a :: xs) (b :: ys) = (a, b) :: List.zip xs ys := by rfl

theorem generic_idxOf_nil {T : Type u} [DecidableEq T] (x : T) :
    List.idxOf x ([] : List T) = 0 := by rfl

theorem generic_idxOf_cons {T : Type u} [DecidableEq T]
    (x a : T) (xs : List T) :
    List.idxOf x (a :: xs) =
      bif a == x then 0 else List.idxOf x xs + 1 := by
  exact List.idxOf_cons

theorem generic_all_nil {T : Type u} (P : T → Bool) :
    List.all ([] : List T) P = true := by rfl

theorem generic_all_cons {T : Type u} (P : T → Bool)
    (a : T) (xs : List T) :
    List.all (a :: xs) P = (P a && List.all xs P) := by rfl

theorem generic_any_nil {T : Type u} (P : T → Bool) :
    List.any ([] : List T) P = false := by rfl

theorem generic_any_cons {T : Type u} (P : T → Bool)
    (a : T) (xs : List T) :
    List.any (a :: xs) P = (P a || List.any xs P) := by rfl

theorem generic_isEmpty_nil {T : Type u} :
    List.isEmpty ([] : List T) = true := by rfl

theorem generic_isEmpty_cons {T : Type u} (a : T) (xs : List T) :
    List.isEmpty (a :: xs) = false := by rfl

theorem generic_getLastD_nil {T : Type u} (d : T) :
    List.getLastD ([] : List T) d = d := by rfl

theorem generic_getLastD_singleton {T : Type u} (a d : T) :
    List.getLastD [a] d = a := by rfl

theorem generic_getLastD_cons_cons {T : Type u}
    (a b d : T) (xs : List T) :
    List.getLastD (a :: b :: xs) d = List.getLastD (b :: xs) d := by rfl

theorem generic_boolSorted_nil {T : Type u} (R : T → T → Bool) :
    Prosa.Util.List.boolSorted R [] := by
  exact List.IsChain.nil

theorem generic_boolSorted_singleton {T : Type u} (R : T → T → Bool)
    (a : T) : Prosa.Util.List.boolSorted R [a] := by
  exact List.IsChain.singleton a

theorem generic_boolSorted_cons_cons {T : Type u}
    (R : T → T → Bool) (a b : T) (xs : List T) :
    Prosa.Util.List.boolSorted R (a :: b :: xs) ↔
      R a b = true ∧ Prosa.Util.List.boolSorted R (b :: xs) := by
  exact List.isChain_cons_cons

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

/-- Kernel-checked equations for the actual `List.range'` operation and the
    production interval helpers used by List batch 4. -/
theorem generic_range_prime_zero (start : Nat) :
    List.range' start 0 = [] := by rfl

theorem generic_range_prime_succ (start len : Nat) :
    List.range' start (Nat.succ len) =
      start :: List.range' (start + 1) len := by rfl

theorem production_index_iota_eq (a b : Nat) :
    Prosa.Util.List.index_iota a b = List.range' a (b - a) := by rfl

theorem production_range_eq (a b : Nat) :
    Prosa.Util.List.range a b =
      Prosa.Util.List.index_iota a (b + 1) := by rfl

/- Kernel-checked generic computation equations required by the final List
   cluster. -/
theorem generic_map_nil {T U : Type u} (f : T → U) :
    List.map f [] = [] := by rfl

theorem generic_map_cons {T U : Type u} (f : T → U)
    (a : T) (xs : List T) :
    List.map f (a :: xs) = f a :: List.map f xs := by rfl

/- Monomorphic Nat equations are kept separately because lean4export emits a
   distinct specialized List carrier/operation in the production definitions
   [shift_points_pos] and [shift_points_neg]. -/
theorem nat_map_nil (f : Nat → Nat) :
    List.map f ([] : List Nat) = [] := by rfl

theorem nat_map_cons (f : Nat → Nat) (a : Nat) (xs : List Nat) :
    List.map f (a :: xs) = f a :: List.map f xs := by rfl

theorem generic_countP_nil {T : Type u} (P : T → Bool) :
    List.countP P [] = 0 := by rfl

theorem generic_countP_cons {T : Type u} (P : T → Bool)
    (a : T) (xs : List T) :
    List.countP P (a :: xs) =
      List.countP P xs + if P a = true then 1 else 0 := by
  exact List.countP_cons

theorem nat_countP_nil (P : Nat → Bool) :
    List.countP P ([] : List Nat) = 0 := by rfl

theorem nat_countP_cons (P : Nat → Bool) (a : Nat) (xs : List Nat) :
    List.countP P (a :: xs) =
      List.countP P xs + if P a = true then 1 else 0 := by
  exact List.countP_cons

/- Exact definitional guards for the four production definitions in the
   final List cluster. -/
theorem production_prefix_of_eq {T : Type u} [DecidableEq T]
    (xs ys : List T) :
    Prosa.Util.List.prefix_of xs ys ↔ ∃ tail, xs ++ tail = ys := by rfl

theorem production_strict_prefix_of_eq {T : Type u} [DecidableEq T]
    (xs ys : List T) :
    Prosa.Util.List.strict_prefix_of xs ys ↔
      ∃ tail, tail ≠ [] ∧ xs ++ tail = ys := by rfl

theorem production_shift_points_pos_eq (xs : List Nat) (s : Nat) :
    Prosa.Util.List.shift_points_pos xs s =
      xs.map (fun x => s + x) := by rfl

theorem production_shift_points_neg_eq (xs : List Nat) (s : Nat) :
    Prosa.Util.List.shift_points_neg xs s =
      (xs.filter (fun x => decide (s ≤ x))).map (fun x => x - s) := by rfl

end Prosa.Validation.ListLastInterface
