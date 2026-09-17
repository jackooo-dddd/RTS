-- Translated from: ../rt-proofs/classic/analysis/global/parallel/interference_bound_fp.v
import Prosa.Classic.Util.All
import Prosa.Classic.Model.Priority
import Prosa.Classic.Model.Schedule.Global.Workload
import Prosa.Classic.Model.Schedule.Global.Basic.Schedule
import Prosa.Classic.Analysis.Global.Parallel.Workload_bound
import Prosa.Classic.Analysis.Global.Parallel.Interference_bound

set_option autoImplicit false

namespace Prosa.Classic.Analysis.Global.Parallel.Interference_bound_fp

open Prosa.Classic.Model.Time
open Prosa.Classic.Model.Priority
open Prosa.Classic.Analysis.Global.Parallel.Workload_bound.WorkloadBound
open Prosa.Classic.Analysis.Global.Parallel.Interference_bound.InterferenceBoundGeneric

namespace InterferenceBoundFP

section Definitions

variable {sporadic_task : Type _} [DecidableEq sporadic_task]
variable (task_cost : sporadic_task → Time)
variable (task_period : sporadic_task → Time)
variable (task_deadline : sporadic_task → Time)

variable (tsk : sporadic_task)

variable (R_prev : List (task_with_response_time sporadic_task))

variable (delta : Time)

variable (higher_eq_priority : FP_policy sporadic_task)

def total_interference_bound_fp : ℕ :=
  (R_prev.map (fun tsk_R => interference_bound_generic task_cost task_period delta tsk_R)).sum

end Definitions

end InterferenceBoundFP

end Prosa.Classic.Analysis.Global.Parallel.Interference_bound_fp
