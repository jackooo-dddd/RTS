-- Authoritative source:
-- ProsaBuddy classic Prosa (prosabuddy commit f692cb7479780cf6009493f373a309e13165201c)
-- source: classic/analysis/uni/basic/tdma_rta_theory.v
-- sha256: see Prosa-Shunqi/classic-prosa/comprehensive-classic/file_order.csv (rank 112)

import Prosa.Classic.Util.All
import Prosa.Classic.Model.Arrival.Basic.Job
import Prosa.Classic.Model.Arrival.Basic.TaskArrival
import Prosa.Classic.Model.Schedule.Uni.Schedulability
import Prosa.Classic.Model.Schedule.Uni.ScheduleOfTask
import Prosa.Classic.Model.Schedule.Uni.ResponseTime
import Prosa.Classic.Analysis.Uni.Basic.TdmaWcrtAnalysis
import Prosa.Classic.Model.Schedule.Uni.Basic.PlatformTdma
import Prosa.Classic.Model.Schedule.Uni.EndTime

/-!
Response-time analysis for TDMA on a uniprocessor (Rocq module `ResponseTimeAnalysisTDMA`).

Representation notes: `{set sporadic_task}` is the v0.6 sequence-set; `tsk \in ts` is `tsk ∈ ts`; Boolean tests in
proposition position are `= true`; the section-local `Let`s (`is_scheduled_at`, `in_time_slot_at`,
`response_time_bounded_by`, `RT`, `no_deadline_missed_by_task`, `no_deadline_missed_by_job`, `BOUND`) are unfolded.
Binder lists follow the Rocq contract (`H_valid_task_parameters` is not taken).
-/

set_option linter.unusedVariables false

namespace Prosa.Classic.Analysis.Uni.Basic.TdmaRtaTheory.ResponseTimeAnalysisTDMA

open Prosa.Classic.Model.Time.Time
open Prosa.Classic.Model.Arrival.Basic.ArrivalSequence.ArrivalSequence
open Prosa.Classic.Model.Arrival.Basic.Job.Job
open Prosa.Classic.Model.Arrival.Basic.TaskArrival.TaskArrival (sporadic_task_model)
open Prosa.Classic.Model.Schedule.Uni.Schedule.UniprocessorSchedule
open Prosa.Classic.Model.Schedule.Uni.ResponseTime.ResponseTime
open Prosa.Classic.Model.Schedule.Uni.Schedulability.Schedulability
open Prosa.Classic.Model.PolicyTdma.PolicyTDMA
open Prosa.Classic.Model.Schedule.Uni.Basic.PlatformTdma.Platform_TDMA
open Prosa.Classic.Analysis.Uni.Basic.TdmaWcrtAnalysis.WCRT_OneJobTDMA (WCRT)
open Prosa.Util.Seqset

universe u v

local macro "omega'" : tactic =>
  `(tactic| ((try dsimp only [Prosa.Classic.Model.Time.Time.time,
    Prosa.Classic.Model.Time.Time.instant, Prosa.Classic.Model.Time.Time.duration] at *) <;>
    omega))

def is_valid_tdma_bound {sporadic_task : Type u} [DecidableEq sporadic_task] (task_deadline : sporadic_task → time) (tsk : sporadic_task) (bound : Nat) : Prop :=
  bound ≤ task_deadline tsk

theorem any_job_completed_before_period {sporadic_task : Type u} [DecidableEq sporadic_task] (task_cost task_period task_deadline : sporadic_task → time) {Job : Type v} [DecidableEq Job]
    (job_arrival job_cost job_deadline : Job → time) (job_task : Job → sporadic_task) (arr_seq : arrival_sequence Job)
    (H_arrival_times_are_consistent : arrival_times_are_consistent job_arrival arr_seq)
    (H_sporadic_tasks : sporadic_task_model task_period job_arrival job_task arr_seq) (sched : schedule Job)
    (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute job_arrival sched)
    (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched)
    (task_time_slot : TDMA_slot sporadic_task) (slot_order : TDMA_slot_order sporadic_task) (ts : set sporadic_task)
    (tsk : sporadic_task) (H_task_in_task_set : tsk ∈ ts)
    (WCRT_le_period : WCRT task_cost task_time_slot ts tsk ≤ task_period tsk)
    (TDMA_policy : Respects_TDMA_policy job_arrival job_cost job_task arr_seq sched ts task_time_slot slot_order)
    (H_valid_time_slot : is_valid_time_slot tsk task_time_slot = true)
    (H_valid_job_parameters : ∀ j, arrives_in arr_seq j →
      valid_sporadic_job task_cost task_deadline job_cost job_deadline job_task j)
    (H_job_cost_le_task_cost : ∀ j, arrives_in arr_seq j → job_cost_le_task_cost task_cost job_cost job_task j = true) :
    ∀ j, arrives_in arr_seq j → job_task j = tsk →
      completed_by job_cost sched j (job_arrival j + task_period (job_task j)) = true := by
  intro j
  induction h : job_arrival j using Nat.strong_induction_on generalizing j with
  | _ n IH =>
    intro ARRj TSKj
    have C := Prosa.Classic.Analysis.Uni.Basic.TdmaWcrtAnalysis.WCRT_OneJobTDMA.job_completed_by_WCRT task_cost task_deadline job_arrival job_cost job_deadline job_task arr_seq
      sched H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute task_time_slot slot_order ts tsk
      H_task_in_task_set j TSKj ARRj (H_valid_job_parameters j ARRj) H_valid_time_slot TDMA_policy
      (fun j_other ARRo SAME LT => by
        have NE : j_other ≠ j := by intro E; subst E; omega'
        have PER := H_sporadic_tasks j_other j NE ARRo ARRj SAME.symm (by omega')
        have IHo := IH (job_arrival j_other) (by omega') j_other rfl ARRo (SAME.symm.trans TSKj)
        exact completion_monotonic job_cost sched j_other _ _ PER IHo)
      (H_job_cost_le_task_cost j ARRj)
    rw [h] at C
    rw [TSKj]
    exact completion_monotonic job_cost sched j _ _ (Nat.add_le_add_left WCRT_le_period _) C

theorem all_previous_jobs_of_same_task_completed {sporadic_task : Type u} [DecidableEq sporadic_task] (task_cost task_period task_deadline : sporadic_task → time) {Job : Type v} [DecidableEq Job]
    (job_arrival job_cost job_deadline : Job → time) (job_task : Job → sporadic_task) (arr_seq : arrival_sequence Job)
    (H_arrival_times_are_consistent : arrival_times_are_consistent job_arrival arr_seq)
    (H_sporadic_tasks : sporadic_task_model task_period job_arrival job_task arr_seq) (sched : schedule Job)
    (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute job_arrival sched)
    (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched)
    (task_time_slot : TDMA_slot sporadic_task) (slot_order : TDMA_slot_order sporadic_task) (ts : set sporadic_task)
    (tsk : sporadic_task) (H_task_in_task_set : tsk ∈ ts)
    (WCRT_le_period : WCRT task_cost task_time_slot ts tsk ≤ task_period tsk)
    (TDMA_policy : Respects_TDMA_policy job_arrival job_cost job_task arr_seq sched ts task_time_slot slot_order)
    (H_valid_time_slot : is_valid_time_slot tsk task_time_slot = true)
    (H_valid_job_parameters : ∀ j, arrives_in arr_seq j →
      valid_sporadic_job task_cost task_deadline job_cost job_deadline job_task j)
    (H_job_cost_le_task_cost : ∀ j, arrives_in arr_seq j → job_cost_le_task_cost task_cost job_cost job_task j = true) :
    ∀ j j_other, arrives_in arr_seq j → job_task j = tsk → arrives_in arr_seq j_other →
      job_task j = job_task j_other → job_arrival j_other < job_arrival j →
      completed_by job_cost sched j_other (job_arrival j) = true := by
  intro j j_other ARRj TSKj ARRo SAME LT
  have NE : j_other ≠ j := by intro E; subst E; omega'
  have PER := H_sporadic_tasks j_other j NE ARRo ARRj SAME.symm (by omega')
  have C := any_job_completed_before_period task_cost task_period task_deadline job_arrival job_cost job_deadline job_task arr_seq H_arrival_times_are_consistent H_sporadic_tasks sched H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute task_time_slot slot_order ts tsk H_task_in_task_set WCRT_le_period TDMA_policy H_valid_time_slot H_valid_job_parameters H_job_cost_le_task_cost j_other ARRo (SAME.symm.trans TSKj)
  exact completion_monotonic job_cost sched j_other _ _ PER C

theorem uniprocessor_response_time_bound_TDMA {sporadic_task : Type u} [DecidableEq sporadic_task] (task_cost task_period task_deadline : sporadic_task → time) {Job : Type v} [DecidableEq Job]
    (job_arrival job_cost job_deadline : Job → time) (job_task : Job → sporadic_task) (arr_seq : arrival_sequence Job)
    (H_arrival_times_are_consistent : arrival_times_are_consistent job_arrival arr_seq)
    (H_sporadic_tasks : sporadic_task_model task_period job_arrival job_task arr_seq) (sched : schedule Job)
    (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute job_arrival sched)
    (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched)
    (task_time_slot : TDMA_slot sporadic_task) (slot_order : TDMA_slot_order sporadic_task) (ts : set sporadic_task)
    (tsk : sporadic_task) (H_task_in_task_set : tsk ∈ ts)
    (WCRT_le_period : WCRT task_cost task_time_slot ts tsk ≤ task_period tsk)
    (TDMA_policy : Respects_TDMA_policy job_arrival job_cost job_task arr_seq sched ts task_time_slot slot_order)
    (H_valid_time_slot : is_valid_time_slot tsk task_time_slot = true)
    (H_valid_job_parameters : ∀ j, arrives_in arr_seq j →
      valid_sporadic_job task_cost task_deadline job_cost job_deadline job_task j)
    (H_job_cost_le_task_cost : ∀ j, arrives_in arr_seq j → job_cost_le_task_cost task_cost job_cost job_task j = true) :
    is_response_time_bound_of_task job_arrival job_cost job_task arr_seq sched tsk
      (WCRT task_cost task_time_slot ts tsk) := by
  intro j ARRj TSKj
  exact Prosa.Classic.Analysis.Uni.Basic.TdmaWcrtAnalysis.WCRT_OneJobTDMA.job_completed_by_WCRT task_cost task_deadline job_arrival job_cost job_deadline job_task arr_seq sched
    H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute task_time_slot slot_order ts tsk H_task_in_task_set j
    TSKj ARRj (H_valid_job_parameters j ARRj) H_valid_time_slot TDMA_policy
    (fun j_other ARRo SAME LT => all_previous_jobs_of_same_task_completed task_cost task_period task_deadline job_arrival job_cost job_deadline job_task arr_seq H_arrival_times_are_consistent H_sporadic_tasks sched H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute task_time_slot slot_order ts tsk H_task_in_task_set WCRT_le_period TDMA_policy H_valid_time_slot H_valid_job_parameters H_job_cost_le_task_cost j j_other ARRj TSKj ARRo SAME LT)
    (H_job_cost_le_task_cost j ARRj)

theorem taskset_schedulable_by_tdma {sporadic_task : Type u} [DecidableEq sporadic_task] (task_cost task_period task_deadline : sporadic_task → time) {Job : Type v} [DecidableEq Job]
    (job_arrival job_cost job_deadline : Job → time) (job_task : Job → sporadic_task) (arr_seq : arrival_sequence Job)
    (H_arrival_times_are_consistent : arrival_times_are_consistent job_arrival arr_seq)
    (H_sporadic_tasks : sporadic_task_model task_period job_arrival job_task arr_seq) (sched : schedule Job)
    (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute job_arrival sched)
    (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched)
    (task_time_slot : TDMA_slot sporadic_task) (slot_order : TDMA_slot_order sporadic_task) (ts : set sporadic_task)
    (tsk : sporadic_task) (H_task_in_task_set : tsk ∈ ts)
    (WCRT_le_period : WCRT task_cost task_time_slot ts tsk ≤ task_period tsk)
    (TDMA_policy : Respects_TDMA_policy job_arrival job_cost job_task arr_seq sched ts task_time_slot slot_order)
    (H_valid_time_slot : is_valid_time_slot tsk task_time_slot = true)
    (H_valid_job_parameters : ∀ j, arrives_in arr_seq j →
      valid_sporadic_job task_cost task_deadline job_cost job_deadline job_task j)
    (H_job_cost_le_task_cost : ∀ j, arrives_in arr_seq j → job_cost_le_task_cost task_cost job_cost job_task j = true)
    (H_is_valid_bound : is_valid_tdma_bound task_deadline tsk (WCRT task_cost task_time_slot ts tsk)) :
    task_misses_no_deadline job_arrival job_cost job_deadline job_task arr_seq sched tsk :=
  task_completes_before_deadline job_arrival job_cost job_deadline job_task arr_seq sched task_deadline
    (fun j ARR => (H_valid_job_parameters j ARR).2.2) tsk (WCRT task_cost task_time_slot ts tsk) H_is_valid_bound
    (uniprocessor_response_time_bound_TDMA task_cost task_period task_deadline job_arrival job_cost job_deadline job_task arr_seq H_arrival_times_are_consistent H_sporadic_tasks sched H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute task_time_slot slot_order ts tsk H_task_in_task_set WCRT_le_period TDMA_policy H_valid_time_slot H_valid_job_parameters H_job_cost_le_task_cost)

theorem jobs_schedulable_by_tdma_rta {sporadic_task : Type u} [DecidableEq sporadic_task] (task_cost task_period task_deadline : sporadic_task → time) {Job : Type v} [DecidableEq Job]
    (job_arrival job_cost job_deadline : Job → time) (job_task : Job → sporadic_task) (arr_seq : arrival_sequence Job)
    (H_arrival_times_are_consistent : arrival_times_are_consistent job_arrival arr_seq)
    (H_sporadic_tasks : sporadic_task_model task_period job_arrival job_task arr_seq) (sched : schedule Job)
    (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute job_arrival sched)
    (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched)
    (task_time_slot : TDMA_slot sporadic_task) (slot_order : TDMA_slot_order sporadic_task) (ts : set sporadic_task)
    (tsk : sporadic_task) (H_task_in_task_set : tsk ∈ ts)
    (WCRT_le_period : WCRT task_cost task_time_slot ts tsk ≤ task_period tsk)
    (TDMA_policy : Respects_TDMA_policy job_arrival job_cost job_task arr_seq sched ts task_time_slot slot_order)
    (H_valid_time_slot : is_valid_time_slot tsk task_time_slot = true)
    (H_valid_job_parameters : ∀ j, arrives_in arr_seq j →
      valid_sporadic_job task_cost task_deadline job_cost job_deadline job_task j)
    (H_job_cost_le_task_cost : ∀ j, arrives_in arr_seq j → job_cost_le_task_cost task_cost job_cost job_task j = true)
    (H_is_valid_bound : is_valid_tdma_bound task_deadline tsk (WCRT task_cost task_time_slot ts tsk)) :
    ∀ j, arrives_in arr_seq j ∧ job_task j = tsk → job_misses_no_deadline job_arrival job_cost job_deadline sched j := by
  intro j ⟨ARRj, TSKj⟩
  exact taskset_schedulable_by_tdma task_cost task_period task_deadline job_arrival job_cost job_deadline job_task arr_seq H_arrival_times_are_consistent H_sporadic_tasks sched H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute task_time_slot slot_order ts tsk H_task_in_task_set WCRT_le_period TDMA_policy H_valid_time_slot H_valid_job_parameters H_job_cost_le_task_cost H_is_valid_bound j ARRj TSKj

end Prosa.Classic.Analysis.Uni.Basic.TdmaRtaTheory.ResponseTimeAnalysisTDMA
