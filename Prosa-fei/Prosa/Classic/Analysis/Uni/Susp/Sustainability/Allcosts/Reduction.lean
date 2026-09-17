-- Translated from: ../rt-proofs/classic/analysis/uni/susp/sustainability/allcosts/reduction.v
import Prosa.Classic.Util.All
import Prosa.Classic.Model.Priority
import Prosa.Classic.Model.Schedule.Uni.Susp.Schedule
import Prosa.Classic.Model.Schedule.Uni.Transformation.Construction
import Prosa.Classic.Model.Suspension
import Prosa.Classic.Model.Schedule.Uni.Schedule
import Prosa.Classic.Model.Schedule.Uni.Susp.Suspension_intervals
import Prosa.Classic.Model.Arrival.Basic.Arrival_sequence
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic

namespace Prosa.Classic.Analysis.Uni.Susp.Sustainability.Allcosts.Reduction

open Prosa.Classic.Model.Time
open Prosa.Classic.Model.Schedule.Uni.Schedule
open Prosa.Classic.Model.Schedule.Uni.Susp.Suspension_intervals
open Prosa.Classic.Model.Schedule.Uni.Susp.Last_execution
open Prosa.Classic.Model.Schedule.Uni.Transformation.Construction.ScheduleConstruction
open Prosa.Classic.Model.Suspension
open Prosa.Classic.Model.Priority
open Prosa.Classic.Model.Arrival.Basic.Arrival_sequence
open Prosa.Classic.Util.Minmax
open Classical

attribute [local instance] propDecidable

noncomputable section

namespace SustainabilityAllCosts

section Reduction

variable {Job : Type _} [DecidableEq Job]
variable (job_arrival : Job → Time)
variable (job_cost : Job → Time)
variable (arr_seq : arrival_sequence Job)
variable (higher_eq_priority : JLDP_policy Job)
variable (sched_susp : schedule Job)
variable (job_suspension_duration : job_suspension Job)
variable (inflated_job_cost : Job → Time)
variable (j : Job)
variable (R : Time)

section ScheduleConstruction

section ConstructionStep

variable (sched_prefix : schedule Job)
variable (t : Time)

def job_is_late (any_j : Job) (t : Time) : Bool :=
  decide (service sched_prefix any_j t <
    service sched_susp any_j t + (inflated_job_cost any_j - job_cost any_j))

def jobs_that_are_late_or_scheduled_in_sched_susp : List Job :=
  (jobs_arrived_up_to arr_seq t).filter (fun any_j =>
    decide (pending job_arrival inflated_job_cost sched_prefix any_j t) &&
    (job_is_late job_cost sched_susp inflated_job_cost sched_prefix any_j t ||
     scheduled_at sched_susp any_j t))

def highest_priority_late_job : Option Job :=
  seq_min (higher_eq_priority t)
    (jobs_that_are_late_or_scheduled_in_sched_susp job_arrival job_cost arr_seq sched_susp
      inflated_job_cost sched_prefix t)

def pending_jobs : List Job :=
  (jobs_arrived_up_to arr_seq t).filter (fun any_j =>
    decide (pending job_arrival inflated_job_cost sched_prefix any_j t))

def highest_priority_job : Option Job :=
  seq_min (higher_eq_priority t)
    (pending_jobs job_arrival arr_seq inflated_job_cost sched_prefix t)

def build_schedule : Option Job :=
  if t < job_arrival j + R then
    highest_priority_late_job job_arrival job_cost arr_seq higher_eq_priority sched_susp
      inflated_job_cost sched_prefix t
  else
    highest_priority_job job_arrival arr_seq higher_eq_priority inflated_job_cost sched_prefix t

end ConstructionStep

def sched_new : schedule Job :=
  build_schedule_from_prefixes
    (fun sched_prefix t => build_schedule job_arrival job_cost arr_seq higher_eq_priority
      sched_susp inflated_job_cost j R sched_prefix t)
    (fun _ => none)

end ScheduleConstruction

section DefiningSuspension

def suspended_in_sched_new (any_j : Job) (t : Time) : Bool :=
  decide (t < job_arrival j + R) &&
  decide (suspended_at job_arrival job_cost job_suspension_duration sched_susp any_j t) &&
  !job_is_late job_cost sched_susp inflated_job_cost
    (sched_new job_arrival job_cost arr_seq higher_eq_priority sched_susp inflated_job_cost j R)
    any_j t

def build_suspension_duration_local
    (sched : schedule Job) (t_max : Time)
    (job_suspended_at : Job → Time → Bool)
    (any_j : Job) (s : Time) : Duration :=
  ∑ t' ∈ Finset.range t_max,
    if (decide (service sched any_j t' = s) && job_suspended_at any_j t') then 1 else 0

def reduced_suspension_duration : job_suspension Job :=
  build_suspension_duration_local
    (sched_new job_arrival job_cost arr_seq higher_eq_priority sched_susp inflated_job_cost j R)
    (job_arrival j + R)
    (suspended_in_sched_new job_arrival job_cost arr_seq higher_eq_priority sched_susp
      job_suspension_duration inflated_job_cost j R)

end DefiningSuspension

end Reduction

end SustainabilityAllCosts

end

end Prosa.Classic.Analysis.Uni.Susp.Sustainability.Allcosts.Reduction
