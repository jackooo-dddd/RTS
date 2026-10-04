-- Authoritative source:
-- ProsaBuddy classic Prosa (prosabuddy commit f692cb7479780cf6009493f373a309e13165201c)
-- source: classic/analysis/global/parallel/interference_bound.v
-- sha256: see Prosa-Shunqi/classic-prosa/comprehensive-classic/file_order.csv (rank 111)

import Prosa.Classic.Util.All
import Prosa.Classic.Model.Schedule.Global.Basic.Schedule
import Prosa.Classic.Analysis.Global.Parallel.WorkloadBound

/-!
Generic interference bound for parallel jobs (Rocq module `InterferenceBoundGeneric` of
`classic/analysis/global/parallel/interference_bound.v`).

Representation notes (as in the accepted `classic/analysis/global/basic/interference_bound.v`):
`task_with_response_time := (sporadic_task * time)%type` is `sporadic_task × time`; `fst`/`snd` are `.1`/`.2`; the
section-local `Let`s are unfolded. Binder lists follow the Rocq contract (`tsk`, `task_deadline` and `R_prev` are
not taken).
-/

set_option linter.unusedVariables false

namespace Prosa.Classic.Analysis.Global.Parallel.InterferenceBound.InterferenceBoundGeneric

open Prosa.Classic.Model.Time.Time
open Prosa.Classic.Analysis.Global.Parallel.WorkloadBound.WorkloadBound (W)

universe u

def interference_bound_generic {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost task_period : sporadic_task → time) (delta : time) (tsk_R : sporadic_task × time) : Nat :=
  W task_cost task_period tsk_R.1 tsk_R.2 delta

end Prosa.Classic.Analysis.Global.Parallel.InterferenceBound.InterferenceBoundGeneric
