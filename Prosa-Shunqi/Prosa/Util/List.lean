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

end Prosa.Util.List
