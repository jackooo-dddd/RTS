-- Authoritative source:
-- ProsaBuddy classic Prosa (prosabuddy commit f692cb7479780cf6009493f373a309e13165201c)
-- source: classic/analysis/global/jitter/interference_bound.v
-- sha256: see Prosa-Shunqi/classic-prosa/comprehensive-classic/file_order.csv (rank 127)

import Prosa.Classic.Util.All
import Prosa.Classic.Model.Arrival.Basic.ArrivalSequence
import Prosa.Classic.Model.Priority
import Prosa.Classic.Model.Schedule.Global.Jitter.Schedule
import Prosa.Classic.Model.Schedule.Global.Jitter.Interference
import Prosa.Classic.Analysis.Global.Jitter.WorkloadBound

/-!
Generic interference bound with release jitter (Rocq module `InterferenceBoundJitter`).

Representation notes (as in the accepted `classic/analysis/global/basic/interference_bound.v`):
`task_with_response_time := (sporadic_task * time)%type` is `sporadic_task × time`; `fst`/`snd` are `.1`/`.2`;
`minn` is `min`; the section-local `Let`s are unfolded. Binder lists follow the Rocq contract (`task_deadline` and
`R_prev` are not taken).
-/

set_option linter.unusedVariables false

namespace Prosa.Classic.Analysis.Global.Jitter.InterferenceBound.InterferenceBoundJitter

open Prosa.Classic.Model.Time.Time
open Prosa.Classic.Analysis.Global.Jitter.WorkloadBound.WorkloadBoundJitter (W_jitter)

universe u

def interference_bound_generic {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost task_period task_jitter : sporadic_task → time) (tsk : sporadic_task) (delta : time)
    (tsk_R : sporadic_task × time) : Nat :=
  min (W_jitter task_cost task_period task_jitter tsk_R.1 tsk_R.2 delta) (delta - task_cost tsk + 1)

end Prosa.Classic.Analysis.Global.Jitter.InterferenceBound.InterferenceBoundJitter
