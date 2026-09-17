-- Translated from: ../rt-proofs/classic/analysis/global/basic/interference_bound.v
import Prosa.Classic.Util.All
import Prosa.Classic.Model.Schedule.Global.Basic.Schedule
import Prosa.Classic.Analysis.Global.Basic.Workload_bound

set_option autoImplicit false

namespace Prosa.Classic.Analysis.Global.Basic.Interference_bound

open Prosa.Classic.Model.Time
open Prosa.Classic.Analysis.Global.Basic.Workload_bound.WorkloadBound

namespace InterferenceBoundGeneric

section Definitions

variable {sporadic_task : Type _} [DecidableEq sporadic_task]
variable (task_cost : sporadic_task → Time)
variable (task_period : sporadic_task → Time)
variable (task_deadline : sporadic_task → Time)

variable (tsk : sporadic_task)

abbrev task_with_response_time (sporadic_task : Type _) := sporadic_task × Time

variable (R_prev : List (task_with_response_time sporadic_task))

variable (delta : Time)

section PerTask

variable (tsk_R : task_with_response_time sporadic_task)

def interference_bound_generic : ℕ :=
  let tsk_other := tsk_R.1
  let R_other := tsk_R.2
  min (W task_cost task_period tsk_other R_other delta) (delta - task_cost tsk + 1)

end PerTask

end Definitions

end InterferenceBoundGeneric

end Prosa.Classic.Analysis.Global.Basic.Interference_bound
