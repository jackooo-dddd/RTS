-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: util/int.v

import Mathlib.Algebra.Order.Ring.Int

/-!
This module is the Lean re-export boundary corresponding to Prosa's
`util/int.v`.  The source declares no Prosa object; it re-exports MathComp's
integer, ordered-ring, numeric, and order interfaces.  Lean's `Int` linear
ordered commutative ring interface is provided by the import above. In this
non-`module` project style, imported declarations remain available to modules
that import `Prosa.Util.Int`.
-/
