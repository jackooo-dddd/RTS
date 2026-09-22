import Prosa.Util.Poet

namespace Prosa.Validation.PoetInterface

universe u v

theorem production_length_nil {T : Type u} : ([] : List T).length = 0 := rfl

theorem production_length_cons {T : Type u} (x : T) (xs : List T) :
    (x :: xs).length = Nat.succ xs.length := rfl

theorem production_zip_nil_left {T : Type u} {U : Type v} (ys : List U) :
    List.zip ([] : List T) ys = [] := rfl

theorem production_zip_nil_right {T : Type u} {U : Type v} (xs : List T) :
    List.zip xs ([] : List U) = [] := by cases xs <;> rfl

theorem production_zip_cons {T : Type u} {U : Type v} (x : T) (xs : List T)
    (y : U) (ys : List U) :
    List.zip (x :: xs) (y :: ys) = (x, y) :: List.zip xs ys := rfl

theorem production_all_nil {T : Type u} (P : T → Bool) :
    List.all ([] : List T) P = true := rfl

theorem production_all_cons {T : Type u} (P : T → Bool) (x : T)
    (xs : List T) :
    List.all (x :: xs) P = (P x && List.all xs P) := rfl

end Prosa.Validation.PoetInterface
