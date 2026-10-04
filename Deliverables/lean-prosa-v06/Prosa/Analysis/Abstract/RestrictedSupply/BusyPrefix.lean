-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: analysis/abstract/restricted_supply/busy_prefix.v

import Prosa.Model.Priority.Classes
import Prosa.Analysis.Facts.Behavior.Completion
import Prosa.Analysis.Definitions.Service
import Prosa.Analysis.Definitions.ServiceInversion.Pred
import Prosa.Analysis.Abstract.Definitions

namespace Prosa.Analysis.Abstract.RestrictedSupply.BusyPrefix

open Prosa.Behavior.Arrival_sequence
open Prosa.Behavior.Job
open Prosa.Behavior.Schedule
open Prosa.Behavior.Time
open Prosa.Model.Task.Concept
open Prosa.Model.Priority.Definitions
open Prosa.Model.Priority.Coercion
open Prosa.Analysis.Definitions.ServiceInversion.Pred
open Prosa.Analysis.Abstract.Definitions

/-! Service inversion within abstract busy-interval prefixes. Representation
notes: the JLFP policy reaches the JLDP-based predicates through the accepted
low-priority `JLFP_to_JLDP` instance, as the source coercion does; the abstract
busy-interval prefix is the accepted `Analysis.Abstract.Definitions` notion
(over the `Interference`/`InterferingWorkload` instances). Binder orders follow
the elaborated types (the unused `TaskCost` context is absent). -/

section ServiceInversionOfJob

variable {Job : JobType} [DecidableEq Job] [JobArrival Job] [JobCost Job]
variable {PState : ProcessorState Job}
variable (arr_seq : arrival_sequence Job) (sched : schedule PState)
variable [Interference Job] [InterferingWorkload Job] [JLFP_policy Job]

/-- The service inversion of `j` within any abstract busy-interval prefix is
bounded by `B` of its relative arrival. -/
def service_inversion_of_job_is_bounded_by (j : Job) (B : duration → duration) : Prop :=
  pred_service_inversion_of_job_is_bounded_by arr_seq sched (busy_interval_prefix sched) j B

end ServiceInversionOfJob

section ServiceInversionOfTask

variable {Task : TaskType} [DecidableEq Task]
variable {Job : JobType} [DecidableEq Job] [JobTask Job Task] [JobArrival Job] [JobCost Job]
variable {PState : ProcessorState Job}
variable (arr_seq : arrival_sequence Job) (sched : schedule PState)
variable [Interference Job] [InterferingWorkload Job] [JLFP_policy Job]

/-- Every job of `tsk` has service inversion bounded by `B` within its
abstract busy-interval prefixes. -/
def service_inversion_is_bounded_by (tsk : Task) (B : duration → duration) : Prop :=
  pred_service_inversion_is_bounded_by arr_seq sched (busy_interval_prefix sched) tsk B

end ServiceInversionOfTask

end Prosa.Analysis.Abstract.RestrictedSupply.BusyPrefix
