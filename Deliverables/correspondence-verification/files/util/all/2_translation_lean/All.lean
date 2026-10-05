-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: util/all.v

import Prosa.Util.Notation
import Prosa.Util.Bigcat
import Prosa.Util.Bigop
import Prosa.Util.Div_mod
import Prosa.Util.List
import Prosa.Util.Nat
import Prosa.Util.Sum
import Prosa.Util.Seqset
import Prosa.Util.UnitGrowth
import Prosa.Util.Epsilon
import Prosa.Util.SearchArg
import Prosa.Util.Rel
import Prosa.Util.Minmax
import Prosa.Util.Supremum
import Prosa.Util.Nondecreasing
import Prosa.Util.Setoid
import Prosa.Util.Tactics
import Prosa.Util.Poet

/-!
This module is the Lean aggregation counterpart of `prosa.util.all`.  The
authoritative Rocq file contains no named declaration: its observable role is
to re-export the utility modules above together with their external library
interfaces.  Lean imports are transitive, so importing this module exposes the
same translated utility boundary.  The external MathComp boundary is supplied
by the pinned Mathlib dependencies of these translated modules.
-/
