-- Translated from: ../rt-proofs/classic/analysis/uni/susp/sustainability/singlecost/reduction.v
import Prosa.Classic.Util.All
import Prosa.Classic.Model.Priority
import Prosa.Classic.Model.Schedule.Uni.Susp.Schedule
import Prosa.Classic.Model.Schedule.Uni.Transformation.Construction

namespace Prosa.Classic.Analysis.Uni.Susp.Sustainability.Singlecost.Reduction

open Prosa.Classic.Model.Time
open Prosa.Classic.Model.Schedule.Uni.Susp.Schedule
open Prosa.Classic.Model.Suspension
open Prosa.Classic.Model.Priority
open Prosa.Classic.Model.Schedule.Uni.Transformation.Construction.ScheduleConstruction
open Prosa.Classic.Model.Schedule.Uni.Schedule
open Prosa.Classic.Model.Arrival.Basic.Arrival_sequence
open Prosa.Classic.Model.Schedule.Uni.Susp.Suspension_intervals
open Prosa.Classic.Util.Minmax
open Classical

noncomputable section

namespace SustainabilitySingleCost

section Reduction

variable {Job : Type _} [DecidableEq Job]
variable (job_arrival : Job → Time)
variable (job_cost : Job → Time)
variable (arr_seq : arrival_sequence Job)
variable (higher_eq_priority : JLDP_policy Job)
variable (sched_susp : schedule Job)
variable (job_suspension_duration : job_suspension Job)
variable (j : Job)
variable (inflated_job_cost : Job → Time)

section ScheduleConstruction

def ready_jobs (sched_prefix : schedule Job) (t : Time) : List Job :=
  (jobs_arrived_up_to arr_seq t).filter
    (fun j_other =>
      decide (pending job_arrival inflated_job_cost sched_prefix j_other t) &&
      !decide (suspended_at job_arrival inflated_job_cost job_suspension_duration sched_prefix j_other t))

def highest_priority_job (sched_prefix : schedule Job) (t : Time) : Option Job :=
  seq_min (higher_eq_priority t)
    (ready_jobs job_arrival arr_seq job_suspension_duration inflated_job_cost sched_prefix t)

def build_schedule (sched_prefix : schedule Job) (t : Time) : Option Job :=
  match highest_priority_job job_arrival arr_seq higher_eq_priority job_suspension_duration
    inflated_job_cost sched_prefix t with
  | some j_hp =>
    match sched_susp t with
    | some j_in_susp =>
      if (decide (pending job_arrival inflated_job_cost sched_prefix j_in_susp t) &&
          !decide (suspended_at job_arrival inflated_job_cost job_suspension_duration sched_prefix j_in_susp t)) &&
         higher_eq_priority t j_in_susp j_hp then
        some j_in_susp
      else
        some j_hp
    | none => some j_hp
  | none => none

def sched_susp_highercost : schedule Job :=
  build_schedule_from_prefixes
    (build_schedule job_arrival arr_seq higher_eq_priority sched_susp job_suspension_duration
      inflated_job_cost)
    (fun _ => none)

end ScheduleConstruction

end Reduction

end SustainabilitySingleCost

end

end Prosa.Classic.Analysis.Uni.Susp.Sustainability.Singlecost.Reduction
