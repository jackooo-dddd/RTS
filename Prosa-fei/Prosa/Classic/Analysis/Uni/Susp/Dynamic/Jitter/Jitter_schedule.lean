-- Translated from: ../rt-proofs/classic/analysis/uni/susp/dynamic/jitter/jitter_schedule.v
import Prosa.Classic.Util.Minmax
import Prosa.Classic.Model.Priority
import Prosa.Classic.Model.Arrival.Basic.Arrival_sequence
import Prosa.Classic.Model.Schedule.Uni.Jitter.Schedule
import Prosa.Classic.Model.Schedule.Uni.Transformation.Construction
import Prosa.Classic.Model.Suspension

noncomputable section

namespace Prosa.Classic.Analysis.Uni.Susp.Dynamic.Jitter.Jitter_schedule

open Prosa.Classic.Model.Time
open Prosa.Classic.Model.Schedule.Uni.Jitter.Schedule
open Prosa.Classic.Model.Suspension
open Prosa.Classic.Model.Priority
open Prosa.Classic.Model.Schedule.Uni.Transformation.Construction.ScheduleConstruction
open Prosa.Classic.Model.Arrival.Basic.Arrival_sequence
open Prosa.Classic.Model.Arrival.Jitter.Arrival_sequence
open Prosa.Classic.Model.Schedule.Uni.Schedule
open Prosa.Classic.Util.Minmax

namespace JitterScheduleConstruction

variable {Task : Type _} [DecidableEq Task]
variable {Job : Type _} [DecidableEq Job]

def inflated_job_cost
    (job_cost : Job → Time) (job_suspension_duration : job_suspension Job)
    (j any_j : Job) : Time :=
  if any_j == j then
    job_cost any_j + total_suspension job_cost job_suspension_duration any_j
  else
    job_cost any_j

def job_jitter
    (job_arrival : Job → Time) (job_task : Job → Task)
    (higher_eq_priority : FP_policy Task) (job_cost : Job → Time)
    (j : Job) (R : Job → Time) (any_j : Job) : Time :=
  if higher_eq_priority (job_task any_j) (job_task j) && decide (job_task any_j ≠ job_task j) then
    min (job_arrival j - job_arrival any_j) (R any_j - job_cost any_j)
  else 0

def pending_jobs_other_than_j
    (job_arrival : Job → Time) (job_task : Job → Task)
    (higher_eq_priority : FP_policy Task) (job_cost : Job → Time)
    (job_suspension_duration : job_suspension Job)
    (arr_seq : arrival_sequence Job) (j : Job) (R : Job → Time)
    (sched_prefix : schedule Job) (t : Time) : List Job :=
  let jj := job_jitter job_arrival job_task higher_eq_priority job_cost j R
  (actual_arrivals_up_to job_arrival jj arr_seq t).filter
    (fun j_other =>
      decide (actual_arrival job_arrival jj j_other ≤ t) &&
      !decide (inflated_job_cost job_cost job_suspension_duration j j_other ≤
               service sched_prefix j_other t) &&
      decide (j_other ≠ j))

def highest_priority_job_other_than_j
    (job_arrival : Job → Time) (job_task : Job → Task)
    (higher_eq_priority : FP_policy Task) (job_cost : Job → Time)
    (job_suspension_duration : job_suspension Job)
    (arr_seq : arrival_sequence Job) (j : Job) (R : Job → Time)
    (sched_prefix : schedule Job) (t : Time) : Option Job :=
  seq_min (FP_to_JLFP job_task higher_eq_priority)
    (pending_jobs_other_than_j job_arrival job_task higher_eq_priority job_cost
      job_suspension_duration arr_seq j R sched_prefix t)

def build_schedule
    (job_arrival : Job → Time) (job_task : Job → Task)
    (higher_eq_priority : FP_policy Task) (job_cost : Job → Time)
    (job_suspension_duration : job_suspension Job)
    (arr_seq : arrival_sequence Job) (j : Job) (R : Job → Time)
    (sched_prefix : schedule Job) (t : Time) : Option Job :=
  let jj := job_jitter job_arrival job_task higher_eq_priority job_cost j R
  let is_j_pending :=
    decide (actual_arrival job_arrival jj j ≤ t) &&
    !decide (inflated_job_cost job_cost job_suspension_duration j j ≤
             service sched_prefix j t)
  let hp_other :=
    highest_priority_job_other_than_j job_arrival job_task higher_eq_priority
      job_cost job_suspension_duration arr_seq j R sched_prefix t
  if is_j_pending then
    match hp_other with
    | some j_hp =>
      if !(FP_to_JLFP job_task higher_eq_priority j_hp j) then
        some j
      else some j_hp
    | none => some j
  else hp_other

def sched_jitter
    (job_arrival : Job → Time) (job_task : Job → Task)
    (higher_eq_priority : FP_policy Task) (job_cost : Job → Time)
    (job_suspension_duration : job_suspension Job)
    (arr_seq : arrival_sequence Job) (j : Job) (R : Job → Time) : schedule Job :=
  build_schedule_from_prefixes
    (build_schedule job_arrival job_task higher_eq_priority job_cost
      job_suspension_duration arr_seq j R)
    (fun _ => none)

end JitterScheduleConstruction

end Prosa.Classic.Analysis.Uni.Susp.Dynamic.Jitter.Jitter_schedule

end
