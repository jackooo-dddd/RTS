-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: analysis/definitions/service_inversion/busy_prefix.v

import Prosa.Analysis.Definitions.ServiceInversion.Pred
import Prosa.Analysis.Definitions.BusyInterval.Classical

namespace Prosa.Analysis.Definitions.ServiceInversion.BusyPrefix

open Prosa.Behavior.Arrival_sequence
open Prosa.Behavior.Job
open Prosa.Behavior.Schedule
open Prosa.Behavior.Time
open Prosa.Model.Task.Concept
open Prosa.Model.Priority.Definitions
open Prosa.Model.Priority.Coercion
open Prosa.Analysis.Definitions.ServiceInversion.Pred
open Prosa.Analysis.Definitions.BusyInterval.Classical

/-! Representation notes: the JLFP policy reaches the JLDP-based predicates
through the accepted low-priority `JLFP_to_JLDP` instance, as the source
coercion does. Binder orders follow the elaborated types (unused section
context is absent). -/

section ServiceInversion

variable {Task : TaskType} [DecidableEq Task] [TaskCost Task]
variable {Job : JobType} [DecidableEq Job] [JobTask Job Task] [JobArrival Job] [JobCost Job]
variable {PState : ProcessorState Job}
variable (arr_seq : arrival_sequence Job) (sched : schedule PState)
variable [JLFP_policy Job]

/-- The service inversion of `j` within any busy-interval prefix is bounded
by `B` of its relative arrival. -/
def service_inversion_of_job_is_bounded_by (j : Job) (B : duration → duration) : Prop :=
  pred_service_inversion_of_job_is_bounded_by arr_seq sched (busy_interval_prefix arr_seq sched) j B

/-- Every job of `tsk` has service inversion bounded by `B` within its
busy-interval prefixes. -/
def service_inversion_is_bounded_by (tsk : Task) (B : duration → duration) : Prop :=
  pred_service_inversion_is_bounded_by arr_seq sched (busy_interval_prefix arr_seq sched) tsk B

end ServiceInversion

end Prosa.Analysis.Definitions.ServiceInversion.BusyPrefix
