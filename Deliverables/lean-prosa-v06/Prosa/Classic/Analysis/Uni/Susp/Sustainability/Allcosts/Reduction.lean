-- Authoritative source:
-- ProsaBuddy classic Prosa (prosabuddy commit f692cb7479780cf6009493f373a309e13165201c)
-- source: classic/analysis/uni/susp/sustainability/allcosts/reduction.v
-- sha256: see Prosa-Shunqi/classic-prosa/comprehensive-classic/file_order.csv (rank 132)

import Prosa.Classic.Util.All
import Prosa.Classic.Model.Priority
import Prosa.Classic.Model.Suspension
import Prosa.Classic.Model.Schedule.Uni.Susp.Schedule
import Prosa.Classic.Model.Schedule.Uni.Susp.Platform
import Prosa.Classic.Model.Schedule.Uni.Susp.BuildSuspensionTable
import Prosa.Classic.Model.Schedule.Uni.Transformation.Construction

/-!
Reduction inflating all job costs in a suspension-aware schedule: the construction
(Rocq module `SustainabilityAllCosts`).

Representation notes: `[seq x <- s | P x]` is `s.filter P`; `~~ b` is `!b`; boolean `<` is `decide (· < ·)`;
`seq_min` is the classic `Prosa.Classic.Util.Minmax.seq_min`; `pending` is the uniprocessor `pending` (re-exported by
`ScheduleWithSuspensions`) and `suspended_at` the `SuspensionIntervals` one. The section-local `Let`s (`arr_j`,
`arrivals`, `job_is_pending`, `empty_schedule`, `job_is_suspended_in_sched_susp`) are unfolded.
Binder lists follow the Rocq contract.
-/

set_option linter.unusedVariables false

namespace Prosa.Classic.Analysis.Uni.Susp.Sustainability.Allcosts.Reduction.SustainabilityAllCosts

open Prosa.Classic.Model.Time.Time
open Prosa.Classic.Model.Arrival.Basic.ArrivalSequence.ArrivalSequence
open Prosa.Classic.Model.Priority.Priority
open Prosa.Classic.Model.Suspension.Suspension
open Prosa.Classic.Model.Schedule.Uni.Schedule.UniprocessorSchedule (schedule pending service scheduled_at)
open Prosa.Classic.Model.Schedule.Uni.Susp.SuspensionIntervals.SuspensionIntervals (suspended_at)
open Prosa.Classic.Model.Schedule.Uni.Susp.BuildSuspensionTable.SuspensionTableConstruction
  (build_suspension_duration)
open Prosa.Classic.Model.Schedule.Uni.Transformation.Construction.ScheduleConstruction
  (build_schedule_from_prefixes)
open Prosa.Classic.Util.Minmax (seq_min)

universe v

def job_is_late {Job : Type v} [DecidableEq Job] (job_cost : Job → time) (sched_susp : schedule Job)
    (inflated_job_cost : Job → time) (sched_prefix : schedule Job) (any_j : Job) (t : time) : Bool :=
  decide (service sched_prefix any_j t < service sched_susp any_j t + (inflated_job_cost any_j - job_cost any_j))

def jobs_that_are_late_or_scheduled_in_sched_susp {Job : Type v} [DecidableEq Job] (job_arrival job_cost : Job → time)
    (arr_seq : arrival_sequence Job) (sched_susp : schedule Job) (inflated_job_cost : Job → time)
    (sched_prefix : schedule Job) (t : time) : List Job :=
  (jobs_arrived_up_to arr_seq t).filter (fun any_j =>
    pending job_arrival inflated_job_cost sched_prefix any_j t &&
      (job_is_late job_cost sched_susp inflated_job_cost sched_prefix any_j t || scheduled_at sched_susp any_j t))

def highest_priority_late_job {Job : Type v} [DecidableEq Job] (job_arrival job_cost : Job → time)
    (arr_seq : arrival_sequence Job) (higher_eq_priority : JLDP_policy Job) (sched_susp : schedule Job)
    (inflated_job_cost : Job → time) (sched_prefix : schedule Job) (t : time) : Option Job :=
  seq_min (higher_eq_priority t)
    (jobs_that_are_late_or_scheduled_in_sched_susp job_arrival job_cost arr_seq sched_susp inflated_job_cost
      sched_prefix t)

def pending_jobs {Job : Type v} [DecidableEq Job] (job_arrival : Job → time) (arr_seq : arrival_sequence Job)
    (inflated_job_cost : Job → time) (sched_prefix : schedule Job) (t : time) : List Job :=
  (jobs_arrived_up_to arr_seq t).filter (fun any_j => pending job_arrival inflated_job_cost sched_prefix any_j t)

def highest_priority_job {Job : Type v} [DecidableEq Job] (job_arrival : Job → time) (arr_seq : arrival_sequence Job)
    (higher_eq_priority : JLDP_policy Job) (inflated_job_cost : Job → time) (sched_prefix : schedule Job)
    (t : time) : Option Job :=
  seq_min (higher_eq_priority t) (pending_jobs job_arrival arr_seq inflated_job_cost sched_prefix t)

def build_schedule {Job : Type v} [DecidableEq Job] (job_arrival job_cost : Job → time)
    (arr_seq : arrival_sequence Job) (higher_eq_priority : JLDP_policy Job) (sched_susp : schedule Job)
    (inflated_job_cost : Job → time) (j : Job) (R : time) (sched_prefix : schedule Job) (t : time) : Option Job :=
  if t < job_arrival j + R then
    highest_priority_late_job job_arrival job_cost arr_seq higher_eq_priority sched_susp inflated_job_cost
      sched_prefix t
  else
    highest_priority_job job_arrival arr_seq higher_eq_priority inflated_job_cost sched_prefix t

def sched_new {Job : Type v} [DecidableEq Job] (job_arrival job_cost : Job → time)
    (arr_seq : arrival_sequence Job) (higher_eq_priority : JLDP_policy Job) (sched_susp : schedule Job)
    (inflated_job_cost : Job → time) (j : Job) (R : time) : schedule Job :=
  build_schedule_from_prefixes
    (build_schedule job_arrival job_cost arr_seq higher_eq_priority sched_susp inflated_job_cost j R)
    (fun _ => none)

def suspended_in_sched_new {Job : Type v} [DecidableEq Job] (job_arrival job_cost : Job → time)
    (arr_seq : arrival_sequence Job) (higher_eq_priority : JLDP_policy Job) (sched_susp : schedule Job)
    (job_suspension_duration : job_suspension Job) (inflated_job_cost : Job → time) (j : Job) (R : time)
    (any_j : Job) (t : time) : Bool :=
  decide (t < job_arrival j + R) && suspended_at job_arrival job_cost job_suspension_duration sched_susp any_j t &&
    !job_is_late job_cost sched_susp inflated_job_cost
      (sched_new job_arrival job_cost arr_seq higher_eq_priority sched_susp inflated_job_cost j R) any_j t

def reduced_suspension_duration {Job : Type v} [DecidableEq Job] (job_arrival job_cost : Job → time)
    (arr_seq : arrival_sequence Job) (higher_eq_priority : JLDP_policy Job) (sched_susp : schedule Job)
    (job_suspension_duration : job_suspension Job) (inflated_job_cost : Job → time) (j : Job) (R : time) :
    job_suspension Job :=
  build_suspension_duration
    (sched_new job_arrival job_cost arr_seq higher_eq_priority sched_susp inflated_job_cost j R)
    (job_arrival j + R)
    (suspended_in_sched_new job_arrival job_cost arr_seq higher_eq_priority sched_susp job_suspension_duration
      inflated_job_cost j R)

end Prosa.Classic.Analysis.Uni.Susp.Sustainability.Allcosts.Reduction.SustainabilityAllCosts
