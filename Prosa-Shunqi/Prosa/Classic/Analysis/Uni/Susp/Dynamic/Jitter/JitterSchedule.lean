-- Authoritative source:
-- ProsaBuddy classic Prosa (prosabuddy commit f692cb7479780cf6009493f373a309e13165201c)
-- source: classic/analysis/uni/susp/dynamic/jitter/jitter_schedule.v
-- sha256: see Prosa-Shunqi/classic-prosa/comprehensive-classic/file_order.csv (rank 75)

import Prosa.Classic.Util.All
import Prosa.Classic.Model.Priority
import Prosa.Classic.Model.Suspension
import Prosa.Classic.Model.Arrival.Basic.ArrivalSequence
import Prosa.Classic.Model.Schedule.Uni.Jitter.Schedule
import Prosa.Classic.Model.Schedule.Uni.Transformation.Construction

/-!
Reduction from a suspension-aware schedule to a jitter-aware schedule: the construction
(Rocq module `JitterScheduleConstruction`).

Representation notes:
* `any_j == j` is `decide (any_j = j)`; `x != y` is `!decide (x = y)`; `~~ b` is `!b`; `minn` is `min`.
* `[seq x <- s | P x & Q x]` is `s.filter (fun x => P x && Q x)`; `if o is Some x then a else b` is a `match`.
* `pending` is the jitter-aware `UniprocessorScheduleWithJitter.pending`.
* The section-local `Let`s (`job_higher_eq_priority`, `arr_j`, `task_of_j`, `other_hep_task`,
  `job_total_suspension`, `distance_to_j`, `job_is_pending`, `actual_job_arrivals_up_to`, `lower_priority`,
  `empty_schedule`) are unfolded.
* Binder lists follow the Rocq contract (e.g. `job_jitter` does not take `arr_seq`, `task_cost` nor
  `job_suspension_duration`).
-/

set_option linter.unusedVariables false

namespace Prosa.Classic.Analysis.Uni.Susp.Dynamic.Jitter.JitterSchedule.JitterScheduleConstruction

open Prosa.Classic.Model.Time.Time
open Prosa.Classic.Model.Arrival.Basic.ArrivalSequence.ArrivalSequence
open Prosa.Classic.Model.Arrival.Jitter.ArrivalSequence.ArrivalSequenceWithJitter
open Prosa.Classic.Model.Priority.Priority
open Prosa.Classic.Model.Suspension.Suspension
open Prosa.Classic.Model.Schedule.Uni.Schedule.UniprocessorSchedule (schedule)
open Prosa.Classic.Model.Schedule.Uni.Jitter.Schedule.UniprocessorScheduleWithJitter (pending)
open Prosa.Classic.Model.Schedule.Uni.Transformation.Construction.ScheduleConstruction
  (build_schedule_from_prefixes)
open Prosa.Classic.Util.Minmax (seq_min)

universe u v

def inflated_job_cost {Job : Type v} [DecidableEq Job] (job_cost : Job → time)
    (job_suspension_duration : job_suspension Job) (j : Job) (any_j : Job) : Nat :=
  if any_j = j then job_cost any_j + total_suspension job_cost job_suspension_duration any_j
  else job_cost any_j

def job_jitter {Task : Type u} [DecidableEq Task] {Job : Type v} [DecidableEq Job]
    (job_arrival : Job → time) (job_task : Job → Task) (higher_eq_priority : FP_policy Task)
    (job_cost : Job → time) (j : Job) (R : Job → time) (any_j : Job) : Nat :=
  if (higher_eq_priority (job_task any_j) (job_task j) && !decide (job_task any_j = job_task j)) then
    min (job_arrival j - job_arrival any_j) (R any_j - job_cost any_j)
  else 0

def pending_jobs_other_than_j {Task : Type u} [DecidableEq Task] {Job : Type v} [DecidableEq Job]
    (job_arrival : Job → time) (job_task : Job → Task) (arr_seq : arrival_sequence Job)
    (higher_eq_priority : FP_policy Task) (job_cost : Job → time) (job_suspension_duration : job_suspension Job)
    (j : Job) (R : Job → time) (sched_prefix : schedule Job) (t : time) : List Job :=
  (actual_arrivals_up_to job_arrival (job_jitter job_arrival job_task higher_eq_priority job_cost j R) arr_seq t).filter
    (fun j_other =>
      pending job_arrival (inflated_job_cost job_cost job_suspension_duration j)
          (job_jitter job_arrival job_task higher_eq_priority job_cost j R) sched_prefix j_other t &&
        !decide (j_other = j))

def highest_priority_job_other_than_j {Task : Type u} [DecidableEq Task] {Job : Type v} [DecidableEq Job]
    (job_arrival : Job → time) (job_task : Job → Task) (arr_seq : arrival_sequence Job)
    (higher_eq_priority : FP_policy Task) (job_cost : Job → time) (job_suspension_duration : job_suspension Job)
    (j : Job) (R : Job → time) (sched_prefix : schedule Job) (t : time) : Option Job :=
  seq_min (FP_to_JLFP job_task higher_eq_priority)
    (pending_jobs_other_than_j job_arrival job_task arr_seq higher_eq_priority job_cost job_suspension_duration j R
      sched_prefix t)

def build_schedule {Task : Type u} [DecidableEq Task] {Job : Type v} [DecidableEq Job]
    (job_arrival : Job → time) (job_task : Job → Task) (arr_seq : arrival_sequence Job)
    (higher_eq_priority : FP_policy Task) (job_cost : Job → time) (job_suspension_duration : job_suspension Job)
    (j : Job) (R : Job → time) (sched_prefix : schedule Job) (t : time) : Option Job :=
  if pending job_arrival (inflated_job_cost job_cost job_suspension_duration j)
      (job_jitter job_arrival job_task higher_eq_priority job_cost j R) sched_prefix j t then
    match highest_priority_job_other_than_j job_arrival job_task arr_seq higher_eq_priority job_cost
        job_suspension_duration j R sched_prefix t with
    | some j_hp => if !FP_to_JLFP job_task higher_eq_priority j_hp j then some j else some j_hp
    | none => some j
  else
    highest_priority_job_other_than_j job_arrival job_task arr_seq higher_eq_priority job_cost
      job_suspension_duration j R sched_prefix t

def sched_jitter {Task : Type u} [DecidableEq Task] {Job : Type v} [DecidableEq Job]
    (job_arrival : Job → time) (job_task : Job → Task) (arr_seq : arrival_sequence Job)
    (higher_eq_priority : FP_policy Task) (job_cost : Job → time) (job_suspension_duration : job_suspension Job)
    (j : Job) (R : Job → time) : schedule Job :=
  build_schedule_from_prefixes
    (build_schedule job_arrival job_task arr_seq higher_eq_priority job_cost job_suspension_duration j R)
    (fun _ => none)

end Prosa.Classic.Analysis.Uni.Susp.Dynamic.Jitter.JitterSchedule.JitterScheduleConstruction
