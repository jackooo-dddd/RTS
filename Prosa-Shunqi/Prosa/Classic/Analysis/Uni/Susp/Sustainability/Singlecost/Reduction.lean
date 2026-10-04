-- Authoritative source:
-- ProsaBuddy classic Prosa (prosabuddy commit f692cb7479780cf6009493f373a309e13165201c)
-- source: classic/analysis/uni/susp/sustainability/singlecost/reduction.v
-- sha256: see Prosa-Shunqi/classic-prosa/comprehensive-classic/file_order.csv (rank 114)

import Prosa.Classic.Util.All
import Prosa.Classic.Model.Priority
import Prosa.Classic.Model.Suspension
import Prosa.Classic.Model.Schedule.Uni.Susp.Schedule
import Prosa.Classic.Model.Schedule.Uni.Transformation.Construction

/-!
Reduction inflating the cost of a single job in a suspension-aware schedule: the construction
(Rocq module `SustainabilitySingleCost`).

Representation notes: `[seq x <- s | P x]` is `s.filter P`; `~~ b` is `!b`; `if o is Some x then a else b` is a
`match`; `seq_min` is the classic `Prosa.Classic.Util.Minmax.seq_min`; `pending` is the uniprocessor `pending`
(re-exported by `ScheduleWithSuspensions`) and `suspended_at` the `SuspensionIntervals` one. The section-local `Let`s
(`job_is_pending`, `job_is_suspended`, `actual_job_arrivals_up_to`, `job_is_ready`, `empty_schedule`) are unfolded.
Binder lists follow the Rocq contract (`job_cost` and `j` are not taken).
-/

set_option linter.unusedVariables false

namespace Prosa.Classic.Analysis.Uni.Susp.Sustainability.Singlecost.Reduction.SustainabilitySingleCost

open Prosa.Classic.Model.Time.Time
open Prosa.Classic.Model.Arrival.Basic.ArrivalSequence.ArrivalSequence
open Prosa.Classic.Model.Priority.Priority
open Prosa.Classic.Model.Suspension.Suspension
open Prosa.Classic.Model.Schedule.Uni.Schedule.UniprocessorSchedule (schedule pending)
open Prosa.Classic.Model.Schedule.Uni.Susp.SuspensionIntervals.SuspensionIntervals (suspended_at)
open Prosa.Classic.Model.Schedule.Uni.Transformation.Construction.ScheduleConstruction
  (build_schedule_from_prefixes)
open Prosa.Classic.Util.Minmax (seq_min)

universe v

def ready_jobs {Job : Type v} [DecidableEq Job] (job_arrival : Job → time) (arr_seq : arrival_sequence Job)
    (job_suspension_duration : job_suspension Job) (inflated_job_cost : Job → time) (sched_prefix : schedule Job)
    (t : time) : List Job :=
  (jobs_arrived_up_to arr_seq t).filter (fun j_other =>
    pending job_arrival inflated_job_cost sched_prefix j_other t &&
      !suspended_at job_arrival inflated_job_cost job_suspension_duration sched_prefix j_other t)

def highest_priority_job {Job : Type v} [DecidableEq Job] (job_arrival : Job → time)
    (arr_seq : arrival_sequence Job) (higher_eq_priority : JLDP_policy Job)
    (job_suspension_duration : job_suspension Job) (inflated_job_cost : Job → time) (sched_prefix : schedule Job)
    (t : time) : Option Job :=
  seq_min (higher_eq_priority t)
    (ready_jobs job_arrival arr_seq job_suspension_duration inflated_job_cost sched_prefix t)

def build_schedule {Job : Type v} [DecidableEq Job] (job_arrival : Job → time) (arr_seq : arrival_sequence Job)
    (higher_eq_priority : JLDP_policy Job) (sched_susp : schedule Job) (job_suspension_duration : job_suspension Job)
    (inflated_job_cost : Job → time) (sched_prefix : schedule Job) (t : time) : Option Job :=
  match highest_priority_job job_arrival arr_seq higher_eq_priority job_suspension_duration inflated_job_cost
      sched_prefix t with
  | some j_hp =>
    match sched_susp t with
    | some j_in_susp =>
      if (pending job_arrival inflated_job_cost sched_prefix j_in_susp t &&
            !suspended_at job_arrival inflated_job_cost job_suspension_duration sched_prefix j_in_susp t) &&
          higher_eq_priority t j_in_susp j_hp then
        some j_in_susp
      else some j_hp
    | none => some j_hp
  | none => none

def sched_susp_highercost {Job : Type v} [DecidableEq Job] (job_arrival : Job → time)
    (arr_seq : arrival_sequence Job) (higher_eq_priority : JLDP_policy Job) (sched_susp : schedule Job)
    (job_suspension_duration : job_suspension Job) (inflated_job_cost : Job → time) : schedule Job :=
  build_schedule_from_prefixes
    (build_schedule job_arrival arr_seq higher_eq_priority sched_susp job_suspension_duration inflated_job_cost)
    (fun _ => none)

end Prosa.Classic.Analysis.Uni.Susp.Sustainability.Singlecost.Reduction.SustainabilitySingleCost
