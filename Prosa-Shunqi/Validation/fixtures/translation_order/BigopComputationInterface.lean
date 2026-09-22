import Prosa.Util.Bigop

namespace Prosa.Validation.BigopInterface

universe u v

theorem production_bigSeq_nil {R : Type u} {X : Type v}
    (idx : R) (op : R → R → R) (P : X → Bool) (F : X → R) :
    Prosa.Util.Bigop.bigSeq idx op P F [] = idx := by
  rfl

theorem production_bigSeq_cons {R : Type u} {X : Type v}
    (idx : R) (op : R → R → R) (P : X → Bool) (F : X → R)
    (x : X) (xs : List X) :
    Prosa.Util.Bigop.bigSeq idx op P F (x :: xs) =
      if P x then op (F x) (Prosa.Util.Bigop.bigSeq idx op P F xs)
      else Prosa.Util.Bigop.bigSeq idx op P F xs := by
  rfl

end Prosa.Validation.BigopInterface
