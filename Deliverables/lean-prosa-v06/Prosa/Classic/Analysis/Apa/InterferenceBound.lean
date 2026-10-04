-- Authoritative source:
-- ProsaBuddy classic Prosa (prosabuddy commit f692cb7479780cf6009493f373a309e13165201c)
-- source: classic/analysis/apa/interference_bound.v
-- sha256: see Prosa-Shunqi/classic-prosa/casestudy-translation/file_order.csv (rank 39)

import Prosa.Classic.Model.Schedule.Global.Basic.Schedule
import Prosa.Classic.Analysis.Apa.WorkloadBound

/-!
Bertogna and Cirinei's generic interference bound (Rocq module
`InterferenceBoundGeneric`).

Representation notes: the section-local `Let task_with_response_time` is
`sporadic_task × time`, and `Let tsk_other := fst tsk_R`, `Let R_other := snd tsk_R`
are unfolded to `tsk_R.1` / `tsk_R.2`; `minn` is `min`.  Binder lists follow the
Rocq contract: the section variables `task_deadline` and `R_prev` (and, in this APA file, `num_cpus`) are not
used by the definition, so it does not take them.
-/

namespace Prosa.Classic.Analysis.Apa.InterferenceBound.InterferenceBoundGeneric

open Prosa.Classic.Model.Time.Time
open Prosa.Classic.Analysis.Apa.WorkloadBound.WorkloadBound (W)

universe u

def interference_bound_generic {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost task_period : sporadic_task → time) (tsk : sporadic_task) (delta : time)
    (tsk_R : sporadic_task × time) : Nat :=
  min (W task_cost task_period tsk_R.1 tsk_R.2 delta) (delta - task_cost tsk + 1)

end Prosa.Classic.Analysis.Apa.InterferenceBound.InterferenceBoundGeneric
