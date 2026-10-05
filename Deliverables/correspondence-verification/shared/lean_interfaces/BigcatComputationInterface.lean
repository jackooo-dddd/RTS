import Prosa.Util.Bigcat

namespace Prosa.Validation.BigcatInterface

universe u v

open Prosa.Util.Notation
open Prosa.Util.Bigcat

/-- Exact actual-artifact equations for the three Bigcat computational interfaces. -/
theorem production_bigCat_eq {T : Type u} (m n : Nat) (f : Nat → List T) :
    bigCat m n f = ((_root_.List.range (n - m)).map (fun i => f (m + i))).flatten := rfl

theorem production_bigCat_same {T : Type u} (m : Nat) (f : Nat → List T) :
    bigCat m m f = [] := by simp [bigCat]

theorem production_bigCat_of_le {T : Type u} (m n : Nat)
    (f : Nat → List T) (h : n ≤ m) : bigCat m n f = [] := by
  simp [bigCat, Nat.sub_eq_zero_of_le h]

theorem production_bigCat_add_succ {T : Type u} (m d : Nat)
    (f : Nat → List T) :
    bigCat m (m + (d + 1)) f = bigCat m (m + d) f ++ f (m + d) := by
  simp only [bigCat, Nat.add_sub_cancel_left, List.range_succ,
    List.map_append, List.map_singleton, List.flatten_append,
    List.flatten_singleton]

theorem production_bigCatFin_eq {T : Type u} {n : Nat} (f : Fin n → List T) :
    bigCatFin f = (List.ofFn f).flatten := rfl

theorem production_bigCatFin_zero {T : Type u} (f : Fin 0 → List T) :
    bigCatFin f = [] := by simp [bigCatFin]

theorem production_bigCatFin_succ {T : Type u} (n : Nat)
    (f : Fin (n + 1) → List T) :
    bigCatFin f = f 0 ++ bigCatFin (fun i : Fin n => f i.succ) := by
  simp [bigCatFin, List.ofFn_succ]

theorem production_bigCatSeq_eq {X : Type u} {Y : Type v}
    (xs : List X) (p : X → Bool) (f : X → List Y) :
    bigCatSeq xs p f = (xs.filter p).flatMap f := rfl

theorem production_bigCatSeqAll_eq {X : Type u} {Y : Type v}
    (xs : List X) (f : X → List Y) :
    bigCatSeqAll xs f = xs.flatMap f := rfl

/-- Constructor equations used to validate the operations compositionally. -/
theorem production_range_zero : (_root_.List.range 0) = [] := rfl

theorem production_range_succ (n : Nat) :
    _root_.List.range (Nat.succ n) = _root_.List.range n ++ [n] := by
  exact _root_.List.range_succ

theorem production_map_nil {A : Type u} {B : Type v} (f : A → B) :
    List.map f [] = [] := rfl

theorem production_map_cons {A : Type u} {B : Type v} (f : A → B)
    (x : A) (xs : List A) : List.map f (x :: xs) = f x :: List.map f xs := rfl

theorem production_flatten_nil {A : Type u} : List.flatten ([] : List (List A)) = [] := rfl

theorem production_flatten_cons {A : Type u} (xs : List A) (xss : List (List A)) :
    List.flatten (xs :: xss) = xs ++ List.flatten xss := rfl

theorem production_append_nil {A : Type u} (ys : List A) :
    ([] : List A) ++ ys = ys := rfl

theorem production_append_cons {A : Type u} (x : A) (xs ys : List A) :
    (x :: xs) ++ ys = x :: (xs ++ ys) := rfl

theorem production_flatMap_nil {A : Type u} {B : Type v} (f : A → List B) :
    List.flatMap f [] = [] := rfl

theorem production_flatMap_cons {A : Type u} {B : Type v} (f : A → List B)
    (x : A) (xs : List A) : List.flatMap f (x :: xs) = f x ++ List.flatMap f xs := rfl

theorem production_filter_nil {A : Type u} (p : A → Bool) :
    List.filter p [] = [] := rfl

theorem production_filter_cons {A : Type u} (p : A → Bool) (x : A) (xs : List A) :
    List.filter p (x :: xs) =
      match p x with
      | true => x :: List.filter p xs
      | false => List.filter p xs := rfl

theorem production_length_nil {A : Type u} : List.length ([] : List A) = 0 := rfl

theorem production_length_cons {A : Type u} (x : A) (xs : List A) :
    List.length (x :: xs) = Nat.succ (List.length xs) := rfl

end Prosa.Validation.BigcatInterface
