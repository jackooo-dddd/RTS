-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: analysis/definitions/priority_inversion.v

import Prosa.Analysis.Definitions.BusyInterval.Classical
import Prosa.Model.Schedule.Scheduled
import Prosa.Model.Task.Concept
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace Prosa.Analysis.Definitions.PriorityInversion

open Prosa.Behavior.Arrival_sequence
open Prosa.Behavior.Job
open Prosa.Behavior.Schedule
open Prosa.Behavior.Time
open Prosa.Model.Task.Concept
open Prosa.Model.Priority.Definitions
open Prosa.Model.Schedule.Scheduled
open Prosa.Analysis.Definitions.BusyInterval.Classical

/-! Representation notes: `x \notin s` is `!decide (x ∈ s)`; `has p s` is
`s.any p`; `~~ b` is `!b`; a Boolean in `Prop` position is `= true`; the
half-open Boolean sum `\sum_(t1 <= t < t2) b t` is
`∑ t ∈ Finset.Ico t1 t2, (b t).toNat`; a single comparison in `Prop` position
is the Lean proposition. Binder orders follow the elaborated types (unused
section context is absent). -/

section PriorityInversion

variable {Task : TaskType} [DecidableEq Task]
variable {Job : JobType} [DecidableEq Job] [JobTask Job Task] [JobArrival Job] [JobCost Job]
variable {PState : ProcessorState Job}
variable (arr_seq : arrival_sequence Job) (sched : schedule PState)
variable [JLFP_policy Job]
variable (j : Job)

/-- `j` incurs priority inversion at `t`: it is not scheduled while some
scheduled job has lower priority. -/
def priority_inversion (t : instant) : Bool :=
  (!decide (j ∈ scheduled_jobs_at arr_seq sched t)) &&
    (scheduled_jobs_at arr_seq sched t).any (fun jlp => !hep_job jlp j)

/-- Priority inversion caused only by jobs satisfying `P`. -/
def priority_inversion_cond (P : Job → Bool) (t : instant) : Bool :=
  (!decide (j ∈ scheduled_jobs_at arr_seq sched t)) &&
    (scheduled_jobs_at arr_seq sched t).any (fun jlp => !hep_job jlp j && P jlp)

/-- Cumulative priority inversion of `j` within `[t1, t2)`. -/
noncomputable def cumulative_priority_inversion (t1 t2 : instant) : Nat :=
  ∑ t ∈ Finset.Ico t1 t2, (priority_inversion arr_seq sched j t).toNat

/-- Cumulative priority inversion of `j` due to jobs satisfying `P`. -/
noncomputable def cumulative_priority_inversion_cond (P : Job → Bool) (t1 t2 : instant) : Nat :=
  ∑ t ∈ Finset.Ico t1 t2, (priority_inversion_cond arr_seq sched j P t).toNat

/-- The priority inversion of `j` is bounded by `B` of its relative arrival
within any busy-interval prefix. -/
def priority_inversion_of_job_is_bounded_by (B : duration → duration) : Prop :=
  ∀ t1 t2 : instant,
    busy_interval_prefix arr_seq sched j t1 t2 →
      cumulative_priority_inversion arr_seq sched j t1 t2 ≤ B (job_arrival j - t1)

/-- The `P`-restricted priority inversion of `j` is bounded by `B`. -/
def priority_inversion_of_job_cond_is_bounded_by (P : Job → Bool) (B : duration → duration) : Prop :=
  ∀ t1 t2 : instant,
    busy_interval_prefix arr_seq sched j t1 t2 →
      cumulative_priority_inversion_cond arr_seq sched j P t1 t2 ≤ B (job_arrival j - t1)

end PriorityInversion

section TaskPriorityInversionBound

variable {Task : TaskType} [DecidableEq Task] [TaskCost Task]
variable {Job : JobType} [DecidableEq Job] [JobTask Job Task] [JobArrival Job] [JobCost Job]
variable {PState : ProcessorState Job}
variable (arr_seq : arrival_sequence Job) (sched : schedule PState)
variable [JLFP_policy Job]
variable (tsk : Task)

/-- Every job of `tsk` has priority inversion bounded by `B`. -/
def priority_inversion_is_bounded_by (B : duration → duration) : Prop :=
  ∀ j : Job,
    arrives_in arr_seq j →
    job_of_task tsk j = true →
    0 < job_cost j →
    priority_inversion_of_job_is_bounded_by arr_seq sched j B

/-- Every job of `tsk` has `P`-restricted priority inversion bounded by `B`. -/
def priority_inversion_cond_is_bounded_by (P : Job → Bool) (B : duration → duration) : Prop :=
  ∀ j : Job,
    arrives_in arr_seq j →
    job_of_task tsk j = true →
    0 < job_cost j →
    priority_inversion_of_job_cond_is_bounded_by arr_seq sched j P B

end TaskPriorityInversionBound

end Prosa.Analysis.Definitions.PriorityInversion
