import Prosa.Util.Sum

/-!
Validation-only computation equations for the exact production operations
used by the sequence/filter cluster of `Prosa.Util.Sum`.

The equations in this file are deliberately small.  They expose the
kernel-checked recursion interface of the freshly compiled definitions while
avoiding expansion of implementation details such as `List.brecOn`.  This is
an operation-level interface; none of the Prosa target theorems is used to
establish its own semantic correspondence.
-/

namespace Prosa.Validation.SumSequenceInterface

universe u

theorem generic_filter_nil {T : Type u} (P : T → Bool) :
    List.filter P [] = [] := by rfl

theorem generic_filter_cons {T : Type u} (P : T → Bool)
    (x : T) (xs : List T) :
    List.filter P (x :: xs) =
      match P x with
      | true => x :: List.filter P xs
      | false => List.filter P xs := by
  rfl

theorem generic_map_nil {T U : Type u} (F : T → U) :
    List.map F [] = [] := by rfl

theorem generic_map_cons {T U : Type u} (F : T → U)
    (x : T) (xs : List T) :
    List.map F (x :: xs) = F x :: List.map F xs := by rfl

theorem generic_length_nil {T : Type u} :
    List.length ([] : List T) = 0 := by rfl

theorem generic_length_cons {T : Type u} (x : T) (xs : List T) :
    List.length (x :: xs) = Nat.succ (List.length xs) := by rfl

theorem generic_all_nil {T : Type u} (P : T → Bool) :
    List.all ([] : List T) P = true := by rfl

theorem generic_all_cons {T : Type u} (P : T → Bool)
    (x : T) (xs : List T) :
    List.all (x :: xs) P = (P x && List.all xs P) := by rfl

theorem generic_any_nil {T : Type u} (P : T → Bool) :
    List.any ([] : List T) P = false := by rfl

theorem generic_any_cons {T : Type u} (P : T → Bool)
    (x : T) (xs : List T) :
    List.any (x :: xs) P = (P x || List.any xs P) := by rfl

theorem generic_isEmpty_nil {T : Type u} :
    List.isEmpty ([] : List T) = true := by rfl

theorem generic_isEmpty_cons {T : Type u} (x : T) (xs : List T) :
    List.isEmpty (x :: xs) = false := by rfl

theorem nat_sum_nil : List.sum ([] : List Nat) = 0 := by rfl

theorem nat_sum_cons (x : Nat) (xs : List Nat) :
    List.sum (x :: xs) = x + List.sum xs := by rfl

theorem nat_foldr_max_nil :
    List.foldr max 0 ([] : List Nat) = 0 := by rfl

theorem nat_foldr_max_cons (x : Nat) (xs : List Nat) :
    List.foldr max 0 (x :: xs) = max x (List.foldr max 0 xs) := by rfl

theorem production_sumSeq_nil {T : Type u} (F : T → Nat) :
    Prosa.Util.Sum.sumSeq ([] : List T) F = 0 := by rfl

theorem production_sumSeq_cons {T : Type u} (x : T) (xs : List T)
    (F : T → Nat) :
    Prosa.Util.Sum.sumSeq (x :: xs) F =
      F x + Prosa.Util.Sum.sumSeq xs F := by rfl

theorem production_sumFiltered_nil {T : Type u}
    (P : T → Bool) (F : T → Nat) :
    Prosa.Util.Sum.sumFiltered ([] : List T) P F = 0 := by rfl

theorem production_sumFiltered_cons {T : Type u}
    (x : T) (xs : List T) (P : T → Bool) (F : T → Nat) :
    Prosa.Util.Sum.sumFiltered (x :: xs) P F =
      match P x with
      | true => F x + Prosa.Util.Sum.sumFiltered xs P F
      | false => Prosa.Util.Sum.sumFiltered xs P F := by
  cases h : P x <;> simp [Prosa.Util.Sum.sumFiltered, h]

theorem production_maxFiltered_nil {T : Type u}
    (P : T → Bool) (F : T → Nat) :
    Prosa.Util.Sum.maxFiltered ([] : List T) P F = 0 := by rfl

theorem production_maxFiltered_cons {T : Type u}
    (x : T) (xs : List T) (P : T → Bool) (F : T → Nat) :
    Prosa.Util.Sum.maxFiltered (x :: xs) P F =
      match P x with
      | true => max (F x) (Prosa.Util.Sum.maxFiltered xs P F)
      | false => Prosa.Util.Sum.maxFiltered xs P F := by
  cases h : P x <;> simp [Prosa.Util.Sum.maxFiltered, h]

theorem production_subseqb_nil_right {T : Type u} [DecidableEq T]
    (xs : List T) :
    Prosa.Util.Sum.subseqb xs [] = xs.isEmpty := by rfl

theorem production_subseqb_nil_left_cons {T : Type u} [DecidableEq T]
    (y : T) (ys : List T) :
    Prosa.Util.Sum.subseqb [] (y :: ys) = true := by rfl

theorem production_subseqb_cons_cons {T : Type u} [DecidableEq T]
    (x : T) (xs : List T) (y : T) (ys : List T) :
    Prosa.Util.Sum.subseqb (x :: xs) (y :: ys) =
      if x = y then Prosa.Util.Sum.subseqb xs ys
      else Prosa.Util.Sum.subseqb (x :: xs) ys := by
  rfl

theorem production_sumOfPartition_eq {X Y : Type u} [DecidableEq Y]
    (xToY : X → Y) (f : X → Nat) (P : X → Bool)
    (xs : List X) (y : Y) :
    Prosa.Util.Sum.sumOfPartition xToY f P xs y =
      Prosa.Util.Sum.sumFiltered xs
        (fun x => P x && decide (xToY x = y)) f := by
  rfl

theorem production_sumOverPartitions_eq {X Y : Type u} [DecidableEq Y]
    (xToY : X → Y) (f : X → Nat) (P : X → Bool)
    (xs : List X) (ys : List Y) :
    Prosa.Util.Sum.sumOverPartitions xToY f P xs ys =
      Prosa.Util.Sum.sumSeq ys
        (Prosa.Util.Sum.sumOfPartition xToY f P xs) := by
  rfl

end Prosa.Validation.SumSequenceInterface
