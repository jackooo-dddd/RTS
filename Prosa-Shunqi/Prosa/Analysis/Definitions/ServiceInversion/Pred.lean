-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: analysis/definitions/service_inversion/pred.v

import Prosa.Model.Priority.Classes
import Prosa.Analysis.Definitions.Service

namespace Prosa.Analysis.Definitions.ServiceInversion.Pred

open Prosa.Behavior.Arrival_sequence
open Prosa.Behavior.Job
open Prosa.Behavior.Schedule
open Prosa.Behavior.Service
open Prosa.Behavior.Time
open Prosa.Model.Task.Concept
open Prosa.Model.Priority.Definitions
open Prosa.Analysis.Definitions.Service

/-! Representation notes: `x \notin s` is `!decide (x ∈ s)`; `has p s` is
`s.any p`; `~~ b` is `!b`; `\sum_(t1 <= t < t2) b t` over Booleans is
`∑ t ∈ Finset.Ico t1 t2, (b t).toNat` (as in the accepted abstract
definitions); a Boolean in `Prop` position is `= true`; `a > b` is `b < a`.
Binder orders follow the elaborated types (unused section context is
absent). -/

section ServiceInversion

variable {Job : JobType} [DecidableEq Job] [JobArrival Job]
variable {PState : ProcessorState Job}
variable (arr_seq : arrival_sequence Job) (sched : schedule PState)
variable [JLDP_policy Job]

/-- At `t`, `j` receives no service while some lower-priority job does. -/
noncomputable def service_inversion (j : Job) (t : instant) : Bool :=
  !decide (j ∈ served_jobs_at arr_seq sched t) &&
    (served_jobs_at arr_seq sched t).any (fun jlp => !hep_job_at t jlp j)

/-- Cumulative service inversion of `j` over `[t1, t2)`. -/
noncomputable def cumulative_service_inversion (j : Job) (t1 t2 : instant) : Nat :=
  ∑ t ∈ Finset.Ico t1 t2, (service_inversion arr_seq sched j t).toNat

/-- The cumulative service inversion of `j` over every interval satisfying
`P j` is bounded by `B` of the distance to `j`'s arrival. -/
def pred_service_inversion_of_job_is_bounded_by
    (P : Job → instant → instant → Prop) (j : Job) (B : duration → duration) : Prop :=
  ∀ t1 t2 : instant, P j t1 t2 →
    cumulative_service_inversion arr_seq sched j t1 t2 ≤ B (job_arrival j - t1)

end ServiceInversion

/-- Every arriving job of `tsk` with positive cost has bounded service inversion. -/
def pred_service_inversion_is_bounded_by {Task : TaskType} [DecidableEq Task]
    {Job : JobType} [DecidableEq Job] [JobTask Job Task] [JobArrival Job] [JobCost Job]
    {PState : ProcessorState Job} (arr_seq : arrival_sequence Job) (sched : schedule PState)
    [JLDP_policy Job] (P : Job → instant → instant → Prop) (tsk : Task)
    (B : duration → duration) : Prop :=
  ∀ j : Job, arrives_in arr_seq j → job_of_task tsk j = true → 0 < job_cost j →
    pred_service_inversion_of_job_is_bounded_by arr_seq sched P j B

end Prosa.Analysis.Definitions.ServiceInversion.Pred
