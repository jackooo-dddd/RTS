-- Translated from: ../rt-proofs/classic/analysis/apa/interference_bound_fp.v
import Prosa.Classic.Util.All
import Prosa.Classic.Model.Priority
import Prosa.Classic.Model.Schedule.Global.Workload
import Prosa.Classic.Model.Schedule.Global.Basic.Schedule
import Prosa.Classic.Model.Schedule.Apa.Interference
import Prosa.Classic.Analysis.Apa.Workload_bound
import Prosa.Classic.Analysis.Apa.Interference_bound
import Prosa.Classic.Model.Schedule.Apa.Affinity
import Mathlib.Tactic

set_option autoImplicit false

namespace Prosa.Classic.Analysis.Apa.Interference_bound_fp

open Prosa.Classic.Model.Time
open Prosa.Classic.Model.Priority
open Prosa.Classic.Model.Schedule.Apa.Interference
open Prosa.Classic.Model.Schedule.Apa.Affinity
open Prosa.Classic.Analysis.Apa.Workload_bound.WorkloadBound
open Prosa.Classic.Analysis.Apa.Interference_bound.InterferenceBoundGeneric

namespace InterferenceBoundFP

section Definitions

variable {sporadic_task : Type _} [DecidableEq sporadic_task]
variable (task_cost : sporadic_task → Time)
variable (task_period : sporadic_task → Time)
variable (task_deadline : sporadic_task → Time)

variable {num_cpus : ℕ}
variable (alpha : task_affinity sporadic_task num_cpus)

variable (tsk : sporadic_task)

variable (alpha' : affinity num_cpus)

variable (R_prev : List (task_with_response_time sporadic_task))

variable (delta : Time)

variable (higher_eq_priority : FP_policy sporadic_task)

instance decHigherPriorityTaskIn (tsk_other : sporadic_task) :
    Decidable (higher_priority_task_in alpha higher_eq_priority tsk alpha' tsk_other) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

def total_interference_bound_fp : ℕ :=
  (R_prev.filter (fun tsk_R =>
    decide (higher_priority_task_in alpha higher_eq_priority tsk alpha' tsk_R.1))).map
    (fun tsk_R => interference_bound_generic task_cost task_period tsk delta tsk_R)
  |>.sum

end Definitions

end InterferenceBoundFP

end Prosa.Classic.Analysis.Apa.Interference_bound_fp
