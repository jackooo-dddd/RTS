import Prosa.Util.Setoid

namespace Prosa.Validation.SetoidInterface

theorem production_leqRW_apply {m n : Nat} (h : m ≤ n) :
    Prosa.Util.Setoid.leqRW h = h := by
  rfl

end Prosa.Validation.SetoidInterface
