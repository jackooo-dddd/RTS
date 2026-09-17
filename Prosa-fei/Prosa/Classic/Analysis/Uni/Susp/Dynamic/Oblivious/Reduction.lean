-- Translated from: ../rt-proofs/classic/analysis/uni/susp/dynamic/oblivious/reduction.v
import Prosa.Classic.Util.All
import Prosa.Classic.Model.Arrival.Basic.Job
import Prosa.Classic.Model.Arrival.Basic.Task
import Prosa.Classic.Model.Arrival.Basic.Arrival_sequence
import Prosa.Classic.Model.Priority
import Prosa.Classic.Model.Suspension
import Prosa.Classic.Model.Schedule.Uni.Schedule
import Prosa.Classic.Model.Schedule.Uni.Schedulability
import Prosa.Classic.Model.Schedule.Uni.Basic.Platform
import Prosa.Classic.Model.Schedule.Uni.Susp.Suspension_intervals
import Prosa.Classic.Model.Schedule.Uni.Transformation.Construction
import Prosa.Classic.Implementation.Uni.Basic.Schedule
import Mathlib.Tactic

namespace Prosa.Classic.Analysis.Uni.Susp.Dynamic.Oblivious.Reduction

open Prosa.Classic.Model.Time
open Prosa.Classic.Model.Arrival.Basic.Arrival_sequence
open Prosa.Classic.Model.Arrival.Basic.Task.SporadicTaskset
open Prosa.Classic.Model.Priority
open Prosa.Classic.Model.Suspension
open Prosa.Classic.Model.Schedule.Uni.Susp.Suspension_intervals
open Prosa.Classic.Model.Schedule.Uni.Transformation.Construction.ScheduleConstruction
open Prosa.Classic.Util.Minmax

open Prosa.Classic.Model.Schedule.Uni.Schedule

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Classical in
attribute [local instance] propDecidable

noncomputable section

namespace ReductionToBasicSchedule

namespace susp

def backlogged {Job : Type _} [DecidableEq Job]
    (job_arrival : Job → Time) (job_cost : Job → Time)
    (next_suspension : job_suspension Job)
    (sched : schedule Job)
    (j : Job) (t : Time) : Prop :=
  pending job_arrival job_cost sched j t ∧
  ¬ (scheduled_at sched j t = true) ∧
  ¬ suspended_at job_arrival job_cost next_suspension sched j t

end susp

namespace susp_aware

def work_conserving {Job : Type _} [DecidableEq Job]
    (job_arrival : Job → Time) (job_cost : Job → Time)
    (next_suspension : job_suspension Job)
    (arr_seq : arrival_sequence Job)
    (sched : schedule Job) : Prop :=
  ∀ j t,
    arrives_in arr_seq j →
    susp.backlogged job_arrival job_cost next_suspension sched j t →
    ∃ j_other, scheduled_at sched j_other t = true

def respects_JLDP_policy {Job : Type _} [DecidableEq Job]
    (job_arrival : Job → Time) (job_cost : Job → Time)
    (next_suspension : job_suspension Job)
    (arr_seq : arrival_sequence Job)
    (sched : schedule Job)
    (higher_eq_priority : JLDP_policy Job) : Prop :=
  ∀ j j_hp t,
    arrives_in arr_seq j →
    susp.backlogged job_arrival job_cost next_suspension sched j t →
    scheduled_at sched j_hp t = true →
    higher_eq_priority t j_hp j = true

end susp_aware

def inflated_job_cost {Job : Type _} [DecidableEq Job]
    (original_job_cost : Job → Time) (next_suspension : job_suspension Job) (j : Job) : Time :=
  original_job_cost j + total_suspension original_job_cost next_suspension j

def inflated_task_cost {Task : Type _}
    (original_task_cost : Task → Time) (task_suspension_bound : Task → Time) (tsk : Task) : Time :=
  original_task_cost tsk + task_suspension_bound tsk

def reduction_pending_jobs {Job : Type _} [DecidableEq Job]
    (job_arrival : Job → Time) (original_job_cost : Job → Time)
    (next_suspension : job_suspension Job)
    (arr_seq : arrival_sequence Job)
    (sched_prefix : schedule Job)
    (t : Time) : List Job :=
  (jobs_arrived_up_to arr_seq t).filter
    (fun j => decide (has_arrived job_arrival j t) &&
              !decide (inflated_job_cost original_job_cost next_suspension j ≤
                       service sched_prefix j t))

def reduction_highest_priority_job {Job : Type _} [DecidableEq Job]
    (job_arrival : Job → Time) (original_job_cost : Job → Time)
    (next_suspension : job_suspension Job)
    (arr_seq : arrival_sequence Job)
    (higher_eq_priority : JLDP_policy Job)
    (sched_prefix : schedule Job)
    (t : Time) : Option Job :=
  seq_min (higher_eq_priority t) (reduction_pending_jobs job_arrival original_job_cost
    next_suspension arr_seq sched_prefix t)

def reduction_build_schedule {Job : Type _} [DecidableEq Job]
    (job_arrival : Job → Time) (original_job_cost : Job → Time)
    (next_suspension : job_suspension Job)
    (arr_seq : arrival_sequence Job)
    (higher_eq_priority : JLDP_policy Job)
    (sched_susp : schedule Job)
    (sched_prefix : schedule Job)
    (t : Time) : Option Job :=
  let hp := reduction_highest_priority_job job_arrival original_job_cost next_suspension arr_seq
              higher_eq_priority sched_prefix t
  match hp with
  | some j_hp =>
    match sched_susp t with
    | some j_sched =>
      if (decide (has_arrived job_arrival j_sched t) &&
          !decide (inflated_job_cost original_job_cost next_suspension j_sched ≤
                   service sched_prefix j_sched t))
         && higher_eq_priority t j_sched j_hp then
        some j_sched
      else hp
    | none => hp
  | none => hp

def sched_new {Job : Type _} [DecidableEq Job]
    (job_arrival : Job → Time) (original_job_cost : Job → Time)
    (next_suspension : job_suspension Job)
    (arr_seq : arrival_sequence Job)
    (higher_eq_priority : JLDP_policy Job)
    (sched_susp : schedule Job) :
    schedule Job :=
  build_schedule_from_prefixes
    (reduction_build_schedule job_arrival original_job_cost next_suspension arr_seq
      higher_eq_priority sched_susp)
    (fun _ => none)

section Reduction

variable {Task : Type _} [DecidableEq Task]
variable (task_period : Task → Time)
variable (task_deadline : Task → Time)

variable {Job : Type _} [DecidableEq Job]
variable (job_arrival : Job → Time)
variable (job_deadline : Job → Time)
variable (job_task : Job → Task)

variable (ts : List Task)

variable (arr_seq : arrival_sequence Job)
variable (H_arrival_times_are_consistent :
  arrival_times_are_consistent job_arrival arr_seq)

variable (H_jobs_from_taskset :
  ∀ j, arrives_in arr_seq j → job_task j ∈ ts)

variable (higher_eq_priority : JLDP_policy Job)
variable (H_priority_is_reflexive : JLDP_is_reflexive higher_eq_priority)
variable (H_priority_is_transitive : JLDP_is_transitive higher_eq_priority)
variable (H_priority_is_total : JLDP_is_total arr_seq higher_eq_priority)

variable (original_job_cost : Job → Time)
variable (original_task_cost : Task → Time)

variable (next_suspension : job_suspension Job)
variable (task_suspension_bound : Task → Time)
variable (H_dynamic_suspensions :
  dynamic_suspension_model original_job_cost job_task next_suspension task_suspension_bound)

variable (sched_susp : schedule Job)
variable (H_jobs_come_from_arrival_sequence :
  jobs_come_from_arrival_sequence sched_susp arr_seq)

variable (H_jobs_must_arrive_to_execute :
  jobs_must_arrive_to_execute job_arrival sched_susp)

variable (H_completed_jobs_dont_execute :
  completed_jobs_dont_execute original_job_cost sched_susp)

variable (H_work_conserving :
  susp_aware.work_conserving job_arrival original_job_cost next_suspension arr_seq sched_susp)

variable (H_respects_priority :
  susp_aware.respects_JLDP_policy job_arrival original_job_cost next_suspension
    arr_seq sched_susp higher_eq_priority)

variable (H_respects_self_suspensions :
  respects_self_suspensions job_arrival original_job_cost next_suspension sched_susp)

section CostInflation

section NewParametersAreValid

variable (H_inflated_cost_le_deadline_and_period :
  ∀ tsk,
    tsk ∈ ts →
    inflated_task_cost original_task_cost task_suspension_bound tsk ≤ task_deadline tsk ∧
    inflated_task_cost original_task_cost task_suspension_bound tsk ≤ task_period tsk)

include H_arrival_times_are_consistent H_jobs_from_taskset H_priority_is_reflexive H_priority_is_transitive H_priority_is_total H_dynamic_suspensions H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_work_conserving H_respects_priority H_respects_self_suspensions H_inflated_cost_le_deadline_and_period in
theorem suspension_oblivious_job_parameters_remain_valid :
    (∀ j, arrives_in arr_seq j →
      (original_job_cost j > 0 ∧ original_job_cost j ≤ job_deadline j ∧ job_deadline j > 0) ∧
      original_job_cost j ≤ original_task_cost (job_task j) ∧
      job_deadline j = task_deadline (job_task j)) →
    (∀ j, arrives_in arr_seq j →
      (inflated_job_cost original_job_cost next_suspension j > 0 ∧
       inflated_job_cost original_job_cost next_suspension j ≤ job_deadline j ∧
       job_deadline j > 0) ∧
      inflated_job_cost original_job_cost next_suspension j ≤
        inflated_task_cost original_task_cost task_suspension_bound (job_task j) ∧
      job_deadline j = task_deadline (job_task j)) := by
  intro VALID j ARRj
  obtain ⟨⟨h_pos, h_le_dl, h_dl_pos⟩, h_le_tc, h_dl_eq⟩ := VALID j ARRj
  have h_dyn := H_dynamic_suspensions j
  have h_mem := H_jobs_from_taskset j ARRj
  have ⟨h_inf_le_dl, _⟩ := H_inflated_cost_le_deadline_and_period (job_task j) h_mem
  refine ⟨⟨?_, ?_, h_dl_pos⟩, ?_, h_dl_eq⟩
  · exact Nat.lt_of_lt_of_le h_pos
      (Nat.le_add_right (original_job_cost j) (total_suspension original_job_cost next_suspension j))
  · rw [h_dl_eq]
    exact le_trans (show inflated_job_cost original_job_cost next_suspension j ≤
      inflated_task_cost original_task_cost task_suspension_bound (job_task j) from by
        simp only [inflated_job_cost, inflated_task_cost]; exact Nat.add_le_add h_le_tc h_dyn)
      h_inf_le_dl
  · show inflated_job_cost original_job_cost next_suspension j ≤
      inflated_task_cost original_task_cost task_suspension_bound (job_task j)
    simp only [inflated_job_cost, inflated_task_cost]; exact Nat.add_le_add h_le_tc h_dyn

include H_arrival_times_are_consistent H_jobs_from_taskset H_priority_is_reflexive H_priority_is_transitive H_priority_is_total H_dynamic_suspensions H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_work_conserving H_respects_priority H_respects_self_suspensions H_inflated_cost_le_deadline_and_period in
theorem suspension_oblivious_task_parameters_remain_valid :
    valid_sporadic_taskset original_task_cost task_period task_deadline ts →
    valid_sporadic_taskset (inflated_task_cost original_task_cost task_suspension_bound)
        task_period task_deadline ts := by
  intro VALID tsk h_mem
  have h := VALID tsk h_mem
  have ⟨h_inf_le_dl, h_inf_le_period⟩ := H_inflated_cost_le_deadline_and_period tsk h_mem
  open Prosa.Classic.Model.Arrival.Basic.Task.SporadicTask in
  unfold is_valid_sporadic_task at h ⊢
  unfold task_cost_positive task_period_positive task_deadline_positive
    task_cost_le_deadline task_cost_le_period at h ⊢
  obtain ⟨h_pos, h_period_pos, h_dl_pos, _, _⟩ := h
  exact ⟨Nat.lt_of_lt_of_le h_pos
    (Nat.le_add_right (original_task_cost tsk) (task_suspension_bound tsk)),
    h_period_pos, h_dl_pos, h_inf_le_dl, h_inf_le_period⟩

end NewParametersAreValid

end CostInflation

section ScheduleConstruction

theorem sched_new_depends_only_on_service :
    ∀ sched1 sched2 t,
      (∀ j, service sched1 j t = service sched2 j t) →
      reduction_build_schedule job_arrival original_job_cost next_suspension arr_seq
        higher_eq_priority sched_susp sched1 t =
      reduction_build_schedule job_arrival original_job_cost next_suspension arr_seq
        higher_eq_priority sched_susp sched2 t := by
  intro sched1 sched2 t0 ALL
  -- Show the two pending job lists are equal
  have SAME_PEND : reduction_pending_jobs job_arrival original_job_cost next_suspension arr_seq sched1 t0 =
    reduction_pending_jobs job_arrival original_job_cost next_suspension arr_seq sched2 t0 := by
    simp only [reduction_pending_jobs]
    apply List.filter_congr; intro j0 _; rw [ALL j0]
  -- Show the two highest priority jobs are equal
  have SAME_HP : reduction_highest_priority_job job_arrival original_job_cost next_suspension arr_seq higher_eq_priority sched1 t0 =
    reduction_highest_priority_job job_arrival original_job_cost next_suspension arr_seq higher_eq_priority sched2 t0 := by
    simp only [reduction_highest_priority_job]; rw [SAME_PEND]
  -- Now show the whole build_schedule is equal
  simp only [reduction_build_schedule]
  rw [SAME_HP]
  -- Now we only differ in the if-condition service part
  match reduction_highest_priority_job job_arrival original_job_cost next_suspension arr_seq higher_eq_priority sched2 t0 with
  | none => rfl
  | some j_hp =>
    match sched_susp t0 with
    | none => rfl
    | some j_sched => simp [ALL j_sched]

theorem sched_new_uses_construction_function :
    ∀ t,
      sched_new job_arrival original_job_cost next_suspension arr_seq higher_eq_priority sched_susp t =
      reduction_build_schedule job_arrival original_job_cost next_suspension arr_seq
        higher_eq_priority sched_susp
        (sched_new job_arrival original_job_cost next_suspension arr_seq higher_eq_priority sched_susp) t := by
  intro t0
  exact service_dependent_schedule_construction
    (reduction_build_schedule job_arrival original_job_cost next_suspension arr_seq higher_eq_priority sched_susp)
    (fun _ => none)
    (sched_new_depends_only_on_service job_arrival arr_seq higher_eq_priority original_job_cost next_suspension sched_susp)
    t0

end ScheduleConstruction

section GeneratedScheduleIsValid

include H_arrival_times_are_consistent H_jobs_from_taskset H_priority_is_reflexive H_priority_is_transitive H_priority_is_total H_dynamic_suspensions H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_work_conserving H_respects_priority H_respects_self_suspensions in
theorem sched_new_jobs_come_from_arrival_sequence :
    jobs_come_from_arrival_sequence
      (sched_new job_arrival original_job_cost next_suspension arr_seq higher_eq_priority sched_susp)
      arr_seq := by
  simp only [jobs_come_from_arrival_sequence]
  intro j t hSCHED
  simp only [scheduled_at] at hSCHED
  have hEQ := eq_of_beq hSCHED
  rw [sched_new_uses_construction_function] at hEQ
  unfold reduction_build_schedule at hEQ; dsimp only [] at hEQ
  -- Helper: any job from reduction_highest_priority_job arrives in arr_seq
  have get_arr_hp : ∀ x,
      reduction_highest_priority_job job_arrival original_job_cost next_suspension arr_seq
        higher_eq_priority
        (sched_new job_arrival original_job_cost next_suspension arr_seq higher_eq_priority sched_susp)
        t = some x → arrives_in arr_seq x := by
    intro x hx
    simp only [reduction_highest_priority_job] at hx
    have h_mem := seq_min_in_seq _ _ _ hx
    simp only [reduction_pending_jobs, List.mem_filter] at h_mem
    simp only [jobs_arrived_up_to] at h_mem
    exact in_arrivals_implies_arrived job_arrival arr_seq H_arrival_times_are_consistent
      x 0 (t + 1) h_mem.1
  -- Case analysis on reduction_highest_priority_job result
  revert hEQ
  generalize h_hp_def :
    reduction_highest_priority_job job_arrival original_job_cost next_suspension arr_seq
      higher_eq_priority
      (sched_new job_arrival original_job_cost next_suspension arr_seq higher_eq_priority sched_susp)
      t = hp_opt
  cases hp_opt with
  | none => simp
  | some j_hp =>
    dsimp only []
    intro hEQ
    -- Case analysis on sched_susp t
    rcases h_susp : sched_susp t with _ | ⟨j_sched⟩
    · -- sched_susp t = none, so result is some j_hp
      simp [h_susp] at hEQ
      subst hEQ; exact get_arr_hp j_hp h_hp_def
    · -- sched_susp t = some j_sched
      simp only [h_susp] at hEQ
      split at hEQ
      · -- if-condition is true: result is some j_sched
        have hj := Option.some.inj hEQ
        rw [← hj]
        exact H_jobs_come_from_arrival_sequence j_sched t (by simp [scheduled_at, h_susp])
      · -- if-condition is false: result is some j_hp
        have := Option.some.inj hEQ; subst this
        exact get_arr_hp j_hp h_hp_def

include H_arrival_times_are_consistent H_jobs_from_taskset H_priority_is_reflexive H_priority_is_transitive H_priority_is_total H_dynamic_suspensions H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_work_conserving H_respects_priority H_respects_self_suspensions in
theorem sched_new_jobs_must_arrive_to_execute :
    jobs_must_arrive_to_execute job_arrival
      (sched_new job_arrival original_job_cost next_suspension arr_seq higher_eq_priority sched_susp) := by
  simp only [jobs_must_arrive_to_execute]
  intro j t hSCHED
  simp only [scheduled_at] at hSCHED
  have hEQ := eq_of_beq hSCHED
  rw [sched_new_uses_construction_function] at hEQ
  unfold reduction_build_schedule at hEQ; dsimp only [] at hEQ
  -- Helper: hp job has_arrived
  have get_arr_hp : ∀ x,
      reduction_highest_priority_job job_arrival original_job_cost next_suspension arr_seq
        higher_eq_priority
        (sched_new job_arrival original_job_cost next_suspension arr_seq higher_eq_priority sched_susp)
        t = some x → has_arrived job_arrival x t := by
    intro x hx
    simp only [reduction_highest_priority_job] at hx
    have h_mem := seq_min_in_seq _ _ _ hx
    simp only [reduction_pending_jobs, List.mem_filter] at h_mem
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h_mem
    exact h_mem.2.1
  revert hEQ
  generalize h_hp_def :
    reduction_highest_priority_job job_arrival original_job_cost next_suspension arr_seq
      higher_eq_priority
      (sched_new job_arrival original_job_cost next_suspension arr_seq higher_eq_priority sched_susp)
      t = hp_opt
  cases hp_opt with
  | none => simp
  | some j_hp =>
    dsimp only []
    intro hEQ
    rcases h_susp : sched_susp t with _ | ⟨j_sched⟩
    · simp [h_susp] at hEQ; subst hEQ; exact get_arr_hp j_hp h_hp_def
    · simp only [h_susp] at hEQ
      split at hEQ
      · have hj := Option.some.inj hEQ; rw [← hj]
        exact H_jobs_must_arrive_to_execute j_sched t (by simp [scheduled_at, h_susp])
      · have := Option.some.inj hEQ; subst this
        exact get_arr_hp j_hp h_hp_def

include H_arrival_times_are_consistent H_jobs_from_taskset H_priority_is_reflexive H_priority_is_transitive H_priority_is_total H_dynamic_suspensions H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_work_conserving H_respects_priority H_respects_self_suspensions in
theorem sched_new_completed_jobs_dont_execute :
    completed_jobs_dont_execute (inflated_job_cost original_job_cost next_suspension)
      (sched_new job_arrival original_job_cost next_suspension arr_seq higher_eq_priority sched_susp) := by
  simp only [completed_jobs_dont_execute]
  intro j t
  induction t with
  | zero => simp [service, service_during]
  | succ t ih =>
    simp only [service, service_during] at ih ⊢
    rw [Finset.sum_Ico_succ_top (Nat.zero_le t)]
    by_cases h_eq : inflated_job_cost original_job_cost next_suspension j ≤
        ∑ i ∈ Finset.Ico 0 t,
          service_at (sched_new job_arrival original_job_cost next_suspension
            arr_seq higher_eq_priority sched_susp) j i
    · -- j is completed: show service_at = 0 (j not scheduled at t)
      have h_eq' := le_antisymm ih h_eq
      suffices h_not_sched : ¬ (scheduled_at
          (sched_new job_arrival original_job_cost next_suspension arr_seq higher_eq_priority sched_susp) j t
          = true) by
        cases h_b : scheduled_at (sched_new job_arrival original_job_cost next_suspension
            arr_seq higher_eq_priority sched_susp) j t
        · have h0 : service_at (sched_new job_arrival original_job_cost next_suspension
              arr_seq higher_eq_priority sched_susp) j t = 0 := by simp [service_at, h_b]
          rw [h0, Nat.add_zero]; exact ih
        · exact absurd h_b h_not_sched
      -- Prove j not scheduled from construction
      intro h_sched
      simp only [scheduled_at] at h_sched
      have h_some := eq_of_beq h_sched
      rw [sched_new_uses_construction_function] at h_some
      unfold reduction_build_schedule at h_some; dsimp only [] at h_some
      -- Helper: any result from reduction_highest_priority_job is not completed
      have not_completed_hp : ∀ x,
          reduction_highest_priority_job job_arrival original_job_cost next_suspension arr_seq
            higher_eq_priority
            (sched_new job_arrival original_job_cost next_suspension arr_seq higher_eq_priority sched_susp)
            t = some x →
          ¬ (inflated_job_cost original_job_cost next_suspension x ≤
            service (sched_new job_arrival original_job_cost next_suspension arr_seq
              higher_eq_priority sched_susp) x t) := by
        intro x hx
        simp only [reduction_highest_priority_job] at hx
        have h_mem := seq_min_in_seq _ _ _ hx
        simp only [reduction_pending_jobs, List.mem_filter] at h_mem
        simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true',
          decide_eq_false_iff_not] at h_mem
        exact h_mem.2.2
      -- Case analysis on construction
      revert h_some
      generalize h_hp_def :
        reduction_highest_priority_job job_arrival original_job_cost next_suspension arr_seq
          higher_eq_priority
          (sched_new job_arrival original_job_cost next_suspension arr_seq higher_eq_priority sched_susp)
          t = hp_opt
      cases hp_opt with
      | none => simp
      | some j_hp =>
        dsimp only []
        rcases h_susp : sched_susp t with _ | ⟨j_sched⟩
        · -- sched_susp t = none: result is some j_hp
          simp [h_susp]
          intro heq; subst heq
          exact absurd h_eq (not_completed_hp j_hp h_hp_def)
        · -- sched_susp t = some j_sched
          dsimp only []
          split
          · -- if-true: result is some j_sched
            rename_i h_cond
            intro heq; simp only [Option.some.injEq] at heq; subst heq
            simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true',
              decide_eq_false_iff_not] at h_cond
            exact absurd h_eq h_cond.1.2
          · -- if-false: result is some j_hp
            intro heq; simp only [Option.some.injEq] at heq; subst heq
            exact absurd h_eq (not_completed_hp j_hp h_hp_def)
    · -- j not completed: use IH + service_at ≤ 1
      have h_lt : ∑ i ∈ Finset.Ico 0 t,
          service_at (sched_new job_arrival original_job_cost next_suspension
            arr_seq higher_eq_priority sched_susp) j i <
          inflated_job_cost original_job_cost next_suspension j := Nat.lt_of_not_le h_eq
      have h_at := service_at_most_one
        (sched_new job_arrival original_job_cost next_suspension arr_seq higher_eq_priority sched_susp) j t
      omega

include H_arrival_times_are_consistent H_jobs_from_taskset H_priority_is_reflexive H_priority_is_transitive H_priority_is_total H_dynamic_suspensions H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_work_conserving H_respects_priority H_respects_self_suspensions in
theorem sched_new_work_conserving :
    Prosa.Classic.Model.Schedule.Uni.Basic.Platform.Platform.work_conserving
      job_arrival (inflated_job_cost original_job_cost next_suspension) arr_seq
      (sched_new job_arrival original_job_cost next_suspension arr_seq higher_eq_priority sched_susp) := by
  simp only [Prosa.Classic.Model.Schedule.Uni.Basic.Platform.Platform.work_conserving]
  intro j t ARRj BACK
  simp only [backlogged] at BACK
  obtain ⟨⟨hARR, hNOTCOMP⟩, hNOTSCHED⟩ := BACK
  -- j is pending in the new schedule, so j ∈ reduction_pending_jobs
  have h_j_in_pending : j ∈ reduction_pending_jobs job_arrival original_job_cost next_suspension
      arr_seq
      (sched_new job_arrival original_job_cost next_suspension arr_seq higher_eq_priority sched_susp)
      t := by
    simp only [reduction_pending_jobs, List.mem_filter, Bool.and_eq_true, decide_eq_true_eq,
      Bool.not_eq_true', decide_eq_false_iff_not]
    refine ⟨?_, hARR, hNOTCOMP⟩
    simp only [jobs_arrived_up_to]
    exact arrived_between_implies_in_arrivals job_arrival arr_seq H_arrival_times_are_consistent
      j 0 (t + 1) ARRj ⟨Nat.zero_le _, Nat.lt_succ_of_le hARR⟩
  -- Therefore reduction_highest_priority_job is some
  have h_hp_ne_none := seq_min_exists (higher_eq_priority t) _ _ h_j_in_pending
  -- Get construction result
  have h_use := sched_new_uses_construction_function job_arrival arr_seq higher_eq_priority
    original_job_cost next_suspension sched_susp t
  -- Result is not none (someone is scheduled)
  suffices h : sched_new job_arrival original_job_cost next_suspension arr_seq higher_eq_priority
      sched_susp t ≠ none by
    rcases h_val : sched_new job_arrival original_job_cost next_suspension arr_seq
        higher_eq_priority sched_susp t with _ | ⟨j_other⟩
    · exact absurd h_val h
    · exact ⟨j_other, by simp [scheduled_at, h_val]⟩
  -- Show sched_new t ≠ none by unfolding construction
  rw [h_use]
  unfold reduction_build_schedule; dsimp only []
  rcases h_hp_some : seq_min (higher_eq_priority t) (reduction_pending_jobs job_arrival
      original_job_cost next_suspension arr_seq
      (sched_new job_arrival original_job_cost next_suspension arr_seq higher_eq_priority sched_susp)
      t) with _ | ⟨j_hp⟩
  · exact absurd h_hp_some h_hp_ne_none
  · dsimp only [reduction_highest_priority_job]
    rw [h_hp_some]; dsimp only []
    cases sched_susp t <;> simp <;> split <;> simp

include H_arrival_times_are_consistent H_jobs_from_taskset H_priority_is_reflexive H_priority_is_transitive H_priority_is_total H_dynamic_suspensions H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_work_conserving H_respects_priority H_respects_self_suspensions in
theorem sched_new_respects_policy :
    Prosa.Classic.Model.Schedule.Uni.Basic.Platform.Platform.respects_JLDP_policy
      job_arrival (inflated_job_cost original_job_cost next_suspension) arr_seq
      (sched_new job_arrival original_job_cost next_suspension arr_seq higher_eq_priority sched_susp)
      higher_eq_priority := by
  simp only [Prosa.Classic.Model.Schedule.Uni.Basic.Platform.Platform.respects_JLDP_policy]
  intro j1 j2 t ARRj1 BACK hSCHED2
  simp only [backlogged] at BACK
  obtain ⟨⟨hARR1, hNOTCOMP1⟩, hNOTSCHED1⟩ := BACK
  -- j1 is pending but not scheduled; j2 is scheduled
  simp only [scheduled_at] at hSCHED2 hNOTSCHED1
  have hEQ2 := eq_of_beq hSCHED2
  rw [sched_new_uses_construction_function] at hEQ2
  unfold reduction_build_schedule at hEQ2; dsimp only [] at hEQ2
  -- j1 is in pending_jobs
  have h_j1_in_pending : j1 ∈ reduction_pending_jobs job_arrival original_job_cost next_suspension
      arr_seq
      (sched_new job_arrival original_job_cost next_suspension arr_seq higher_eq_priority sched_susp)
      t := by
    simp only [reduction_pending_jobs, List.mem_filter, Bool.and_eq_true, decide_eq_true_eq,
      Bool.not_eq_true', decide_eq_false_iff_not]
    refine ⟨?_, hARR1, hNOTCOMP1⟩
    simp only [jobs_arrived_up_to]
    exact arrived_between_implies_in_arrivals job_arrival arr_seq H_arrival_times_are_consistent
      j1 0 (t + 1) ARRj1 ⟨Nat.zero_le _, Nat.lt_succ_of_le hARR1⟩
  -- Case analysis on construction
  revert hEQ2
  generalize h_hp_def :
    reduction_highest_priority_job job_arrival original_job_cost next_suspension arr_seq
      higher_eq_priority
      (sched_new job_arrival original_job_cost next_suspension arr_seq higher_eq_priority sched_susp)
      t = hp_opt
  cases hp_opt with
  | none =>
    -- No pending jobs, but j1 is pending → contradiction
    simp only [reduction_highest_priority_job] at h_hp_def
    intro habs
    exact absurd h_hp_def (seq_min_exists (higher_eq_priority t) _ _ h_j1_in_pending)
  | some j_hp =>
    dsimp only []
    -- j_hp is min: higher_eq_priority t j_hp j1
    have h_hp_min : higher_eq_priority t j_hp j1 = true := by
      simp only [reduction_highest_priority_job] at h_hp_def
      exact seq_min_computes_min _
        (fun x y z => H_priority_is_transitive t y x z) _
        (fun x y hx hy => by
          simp only [reduction_pending_jobs, List.mem_filter] at hx hy
          simp only [jobs_arrived_up_to] at hx hy
          exact H_priority_is_total x y t
            (in_arrivals_implies_arrived job_arrival arr_seq H_arrival_times_are_consistent
              x 0 (t + 1) hx.1)
            (in_arrivals_implies_arrived job_arrival arr_seq H_arrival_times_are_consistent
              y 0 (t + 1) hy.1))
        j_hp j1 h_hp_def h_j1_in_pending
    -- Case on sched_susp t
    rcases h_susp : sched_susp t with _ | ⟨j_sched⟩
    · -- sched_susp t = none: j2 = j_hp
      dsimp only []
      intro heq; rw [← Option.some.inj heq]; exact h_hp_min
    · -- sched_susp t = some j_sched
      dsimp only []
      split
      · -- if-true: j2 = j_sched, which has higher priority than j_hp
        rename_i h_cond
        intro heq
        simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true',
          decide_eq_false_iff_not] at h_cond
        rw [← Option.some.inj heq]
        exact H_priority_is_transitive t j_hp j_sched j1 h_cond.2 h_hp_min
      · -- if-false: j2 = j_hp
        intro heq; rw [← Option.some.inj heq]; exact h_hp_min

include H_arrival_times_are_consistent H_jobs_from_taskset H_priority_is_reflexive H_priority_is_transitive H_priority_is_total H_dynamic_suspensions H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_work_conserving H_respects_priority H_respects_self_suspensions in
theorem sched_new_breaks_ties :
    ∀ j1 j2 t,
      higher_eq_priority t j1 j2 = true →
      higher_eq_priority t j2 j1 = true →
      scheduled_at sched_susp j1 t = true →
      pending job_arrival (inflated_job_cost original_job_cost next_suspension)
        (sched_new job_arrival original_job_cost next_suspension arr_seq higher_eq_priority sched_susp) j1 t →
      scheduled_at
        (sched_new job_arrival original_job_cost next_suspension arr_seq higher_eq_priority sched_susp) j2 t = true →
      j1 = j2 := by
  intro j1 j2 t HP1 HP2 SCHEDs PEND SCHEDn
  simp only [scheduled_at] at SCHEDs SCHEDn
  have hEQ_s := eq_of_beq SCHEDs
  have hEQ_n := eq_of_beq SCHEDn
  rw [sched_new_uses_construction_function] at hEQ_n
  unfold reduction_build_schedule at hEQ_n; dsimp only [] at hEQ_n
  -- Case on hp
  revert hEQ_n
  generalize h_hp_def :
    reduction_highest_priority_job job_arrival original_job_cost next_suspension arr_seq
      higher_eq_priority
      (sched_new job_arrival original_job_cost next_suspension arr_seq higher_eq_priority sched_susp)
      t = hp_opt
  cases hp_opt with
  | none => simp
  | some j_hp =>
    dsimp only []
    rw [hEQ_s]; dsimp only []
    simp only [pending, completed_by] at PEND
    intro hEQ_n
    split at hEQ_n
    · -- if-true: result is some j1 = some j2
      exact Option.some.inj hEQ_n
    · -- if-false: result is some j_hp = some j2, contradiction
      rename_i h_neg
      rw [← (Option.some.inj hEQ_n)] at HP1
      exfalso; apply h_neg
      simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true',
        decide_eq_false_iff_not]
      exact ⟨PEND, HP1⟩

section Service

section InductiveStep

variable (t : Time)
variable (H_induction_hypothesis :
  ∀ j,
    arrives_in arr_seq j →
    service (sched_new job_arrival original_job_cost next_suspension arr_seq higher_eq_priority sched_susp) j t ≤
    service sched_susp j t +
    cumulative_suspension job_arrival original_job_cost next_suspension sched_susp j t)

variable (j : Job)
variable (H_comes_from_arrival_sequence : arrives_in arr_seq j)

include H_arrival_times_are_consistent H_jobs_from_taskset H_priority_is_reflexive H_priority_is_transitive H_priority_is_total H_dynamic_suspensions H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_work_conserving H_respects_priority H_respects_self_suspensions H_induction_hypothesis H_comes_from_arrival_sequence in
theorem reduction_inductive_step_not_arrived
    (H_not_arrived : ¬ has_arrived job_arrival j t) :
    service (sched_new job_arrival original_job_cost next_suspension arr_seq higher_eq_priority sched_susp) j (t + 1) ≤
    service sched_susp j (t + 1) +
    cumulative_suspension job_arrival original_job_cost next_suspension sched_susp j (t + 1) := by
  simp only [service, service_during]
  have h_le : t + 1 ≤ job_arrival j := by
    simp only [has_arrived] at H_not_arrived; exact Nat.not_le.mp H_not_arrived
  rw [cumulative_service_before_job_arrival_zero job_arrival
    (sched_new job_arrival original_job_cost next_suspension arr_seq higher_eq_priority sched_susp)
    (sched_new_jobs_must_arrive_to_execute job_arrival job_task ts arr_seq
      H_arrival_times_are_consistent H_jobs_from_taskset higher_eq_priority
      H_priority_is_reflexive H_priority_is_transitive H_priority_is_total
      original_job_cost next_suspension task_suspension_bound H_dynamic_suspensions
      sched_susp H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute
      H_completed_jobs_dont_execute H_work_conserving H_respects_priority
      H_respects_self_suspensions) j 0 (t + 1) h_le]
  exact Nat.zero_le _

variable (H_j_has_arrived : has_arrived job_arrival j t)

section CompletedInSuspensionAwareSchedule

variable (H_j_has_completed : completed_by original_job_cost sched_susp j t)

include H_arrival_times_are_consistent H_jobs_from_taskset H_priority_is_reflexive H_priority_is_transitive H_priority_is_total H_dynamic_suspensions H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_work_conserving H_respects_priority H_respects_self_suspensions H_induction_hypothesis H_comes_from_arrival_sequence H_j_has_arrived H_j_has_completed in
theorem reduction_inductive_step_case1_completed :
    service (sched_new job_arrival original_job_cost next_suspension arr_seq higher_eq_priority sched_susp) j (t + 1) ≤
    service sched_susp j (t + 1) +
    cumulative_suspension job_arrival original_job_cost next_suspension sched_susp j (t + 1) := by
  have h_sn_comp := sched_new_completed_jobs_dont_execute job_arrival job_task ts arr_seq
    H_arrival_times_are_consistent H_jobs_from_taskset higher_eq_priority
    H_priority_is_reflexive H_priority_is_transitive H_priority_is_total
    original_job_cost next_suspension task_suspension_bound H_dynamic_suspensions
    sched_susp H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute
    H_completed_jobs_dont_execute H_work_conserving H_respects_priority H_respects_self_suspensions
  have h_comp_t1 := completion_monotonic original_job_cost sched_susp j t (t + 1)
    (Nat.le_succ _) H_j_has_completed
  have h_cum_eq := cumulative_suspension_eq_total_suspension
    job_arrival original_job_cost next_suspension sched_susp j (t + 1)
    H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_respects_self_suspensions
    h_comp_t1
  apply le_trans (cumulative_service_le_job_cost
    (inflated_job_cost original_job_cost next_suspension)
    (sched_new job_arrival original_job_cost next_suspension arr_seq higher_eq_priority sched_susp)
    j h_sn_comp 0 (t + 1))
  simp only [inflated_job_cost]
  rw [← h_cum_eq]
  exact Nat.add_le_add_right h_comp_t1 _

end CompletedInSuspensionAwareSchedule

section PendingInSuspensionAwareSchedule

variable (H_j_is_pending : ¬ completed_by original_job_cost sched_susp j t)

theorem reduction_inductive_step_not_scheduled_in_new
    (H_not_sched : ¬ (scheduled_at
      (sched_new job_arrival original_job_cost next_suspension arr_seq higher_eq_priority sched_susp) j t = true)) :
    (scheduled_at
      (sched_new job_arrival original_job_cost next_suspension arr_seq higher_eq_priority sched_susp) j t).toNat ≤
    (if suspended_at job_arrival original_job_cost next_suspension sched_susp j t then 1 else 0) +
    (scheduled_at sched_susp j t).toNat := by
  have hf := Bool.eq_false_of_not_eq_true H_not_sched
  simp [hf]

theorem reduction_inductive_step_scheduled_in_susp
    (H_sched_susp : scheduled_at sched_susp j t = true) :
    (scheduled_at
      (sched_new job_arrival original_job_cost next_suspension arr_seq higher_eq_priority sched_susp) j t).toNat ≤
    (if suspended_at job_arrival original_job_cost next_suspension sched_susp j t then 1 else 0) +
    (scheduled_at sched_susp j t).toNat := by
  simp [H_sched_susp]
  cases scheduled_at (sched_new job_arrival original_job_cost next_suspension arr_seq higher_eq_priority sched_susp) j t <;> simp [Bool.toNat]

section NotScheduledInSuspensionAware

variable (H_j_scheduled_in_new :
  scheduled_at (sched_new job_arrival original_job_cost next_suspension arr_seq higher_eq_priority sched_susp) j t = true)
variable (H_j_not_scheduled_in_susp : ¬ (scheduled_at sched_susp j t = true))

section ProofByContradiction

variable (H_j_is_not_suspended :
  ¬ suspended_at job_arrival original_job_cost next_suspension sched_susp j t)

include H_arrival_times_are_consistent H_jobs_from_taskset H_priority_is_reflexive H_priority_is_transitive H_priority_is_total H_dynamic_suspensions H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_work_conserving H_respects_priority H_respects_self_suspensions H_induction_hypothesis H_comes_from_arrival_sequence H_j_has_arrived H_j_is_pending H_j_scheduled_in_new H_j_not_scheduled_in_susp H_j_is_not_suspended in
theorem reduction_inductive_step_j_is_backlogged :
    susp.backlogged job_arrival original_job_cost next_suspension sched_susp j t := by
  exact ⟨⟨H_j_has_arrived, H_j_is_pending⟩, H_j_not_scheduled_in_susp, H_j_is_not_suspended⟩

include H_arrival_times_are_consistent H_jobs_from_taskset H_priority_is_reflexive H_priority_is_transitive H_priority_is_total H_dynamic_suspensions H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_work_conserving H_respects_priority H_respects_self_suspensions H_induction_hypothesis H_comes_from_arrival_sequence H_j_has_arrived H_j_is_pending H_j_scheduled_in_new H_j_not_scheduled_in_susp H_j_is_not_suspended in
theorem reduction_inductive_step_exists_hep_job :
    ∃ j_hp,
      arrives_in arr_seq j_hp ∧
      scheduled_at sched_susp j_hp t = true ∧
      higher_eq_priority t j_hp j = true := by
  have h_back := reduction_inductive_step_j_is_backlogged
    job_arrival job_task ts arr_seq
    H_arrival_times_are_consistent H_jobs_from_taskset higher_eq_priority
    H_priority_is_reflexive H_priority_is_transitive H_priority_is_total
    original_job_cost next_suspension task_suspension_bound H_dynamic_suspensions
    sched_susp H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute
    H_completed_jobs_dont_execute H_work_conserving H_respects_priority
    H_respects_self_suspensions
    t H_induction_hypothesis j H_comes_from_arrival_sequence
    H_j_has_arrived H_j_is_pending H_j_scheduled_in_new H_j_not_scheduled_in_susp
    H_j_is_not_suspended
  obtain ⟨j_hp, h_sched_hp⟩ := H_work_conserving j t H_comes_from_arrival_sequence h_back
  exact ⟨j_hp, H_jobs_come_from_arrival_sequence j_hp t h_sched_hp,
    h_sched_hp, H_respects_priority j j_hp t H_comes_from_arrival_sequence h_back h_sched_hp⟩

variable (j_hp : Job)
variable (H_j_hp_comes_from_sequence : arrives_in arr_seq j_hp)
variable (H_j_hp_is_scheduled : scheduled_at sched_susp j_hp t = true)
variable (H_higher_or_equal_priority : higher_eq_priority t j_hp j = true)

include H_arrival_times_are_consistent H_jobs_from_taskset H_priority_is_reflexive H_priority_is_transitive H_priority_is_total H_dynamic_suspensions H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_work_conserving H_respects_priority H_respects_self_suspensions H_induction_hypothesis H_comes_from_arrival_sequence H_j_has_arrived H_j_is_pending H_j_scheduled_in_new H_j_not_scheduled_in_susp H_j_is_not_suspended H_j_hp_comes_from_sequence H_j_hp_is_scheduled H_higher_or_equal_priority in
theorem reduction_inductive_step_j_hp_completed_in_new :
    completed_by (inflated_job_cost original_job_cost next_suspension)
      (sched_new job_arrival original_job_cost next_suspension arr_seq higher_eq_priority sched_susp) j_hp t := by
  -- j_hp is scheduled in sched_susp → pending in sched_susp
  have h_pend_susp := scheduled_implies_pending job_arrival original_job_cost sched_susp
    H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute j_hp t H_j_hp_is_scheduled
  -- Proof by contradiction: assume j_hp not completed in sched_new
  by_contra h_not_comp_new
  -- j_hp arrived (from pending in susp) and not completed in new → pending in new
  have h_arr_hp : has_arrived job_arrival j_hp t := h_pend_susp.1
  have h_pend_new : pending job_arrival (inflated_job_cost original_job_cost next_suspension)
      (sched_new job_arrival original_job_cost next_suspension arr_seq higher_eq_priority sched_susp)
      j_hp t := ⟨h_arr_hp, h_not_comp_new⟩
  -- Case: is j_hp scheduled in sched_new at t?
  by_cases h_sched_hp_new :
      scheduled_at (sched_new job_arrival original_job_cost next_suspension arr_seq
        higher_eq_priority sched_susp) j_hp t = true
  · -- j_hp scheduled in sched_new → j = j_hp (uniprocessor)
    have h_eq := only_one_job_scheduled
      (sched_new job_arrival original_job_cost next_suspension arr_seq higher_eq_priority sched_susp)
      j j_hp t H_j_scheduled_in_new h_sched_hp_new
    -- j = j_hp but j not scheduled in susp while j_hp is
    exact absurd (h_eq ▸ H_j_hp_is_scheduled) H_j_not_scheduled_in_susp
  · -- j_hp not scheduled in sched_new → j_hp backlogged in sched_new
    have h_back_new : backlogged job_arrival (inflated_job_cost original_job_cost next_suspension)
        (sched_new job_arrival original_job_cost next_suspension arr_seq higher_eq_priority sched_susp)
        j_hp t := ⟨h_pend_new, h_sched_hp_new⟩
    -- sched_new respects JLDP → j has priority over j_hp
    have h_sn_resp := sched_new_respects_policy job_arrival job_task ts arr_seq
      H_arrival_times_are_consistent H_jobs_from_taskset higher_eq_priority
      H_priority_is_reflexive H_priority_is_transitive H_priority_is_total
      original_job_cost next_suspension task_suspension_bound H_dynamic_suspensions
      sched_susp H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute
      H_completed_jobs_dont_execute H_work_conserving H_respects_priority H_respects_self_suspensions
    have h_j_over_hp : higher_eq_priority t j j_hp = true :=
      h_sn_resp j_hp j t H_j_hp_comes_from_sequence h_back_new H_j_scheduled_in_new
    -- breaks_ties: j_hp has priority over j AND j has priority over j_hp
    -- → j = j_hp (since j_hp is scheduled in susp and pending in new)
    have h_sn_breaks := sched_new_breaks_ties job_arrival job_task ts arr_seq
      H_arrival_times_are_consistent H_jobs_from_taskset higher_eq_priority
      H_priority_is_reflexive H_priority_is_transitive H_priority_is_total
      original_job_cost next_suspension task_suspension_bound H_dynamic_suspensions
      sched_susp H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute
      H_completed_jobs_dont_execute H_work_conserving H_respects_priority H_respects_self_suspensions
    have h_eq := h_sn_breaks j_hp j t H_higher_or_equal_priority h_j_over_hp
      H_j_hp_is_scheduled h_pend_new H_j_scheduled_in_new
    exact absurd (h_eq ▸ H_j_hp_is_scheduled) H_j_not_scheduled_in_susp

include H_arrival_times_are_consistent H_jobs_from_taskset H_priority_is_reflexive H_priority_is_transitive H_priority_is_total H_dynamic_suspensions H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_work_conserving H_respects_priority H_respects_self_suspensions H_induction_hypothesis H_comes_from_arrival_sequence H_j_has_arrived H_j_is_pending H_j_scheduled_in_new H_j_not_scheduled_in_susp H_j_is_not_suspended H_j_hp_comes_from_sequence H_j_hp_is_scheduled H_higher_or_equal_priority in
theorem reduction_inductive_step_j_hp_completed_in_susp :
    completed_by original_job_cost sched_susp j_hp t := by
  have h_comp_new := reduction_inductive_step_j_hp_completed_in_new
    job_arrival job_task ts arr_seq
    H_arrival_times_are_consistent H_jobs_from_taskset higher_eq_priority
    H_priority_is_reflexive H_priority_is_transitive H_priority_is_total
    original_job_cost next_suspension task_suspension_bound H_dynamic_suspensions
    sched_susp H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute
    H_completed_jobs_dont_execute H_work_conserving H_respects_priority
    H_respects_self_suspensions
    t H_induction_hypothesis j H_comes_from_arrival_sequence
    H_j_has_arrived H_j_is_pending H_j_scheduled_in_new H_j_not_scheduled_in_susp
    H_j_is_not_suspended j_hp H_j_hp_comes_from_sequence H_j_hp_is_scheduled
    H_higher_or_equal_priority
  -- h_comp_new : inflated_cost j_hp ≤ service_new j_hp t
  -- IH: service_new j_hp t ≤ service_susp j_hp t + cumul_susp j_hp t
  have h_ih := H_induction_hypothesis j_hp H_j_hp_comes_from_sequence
  -- cumul_susp ≤ total_susp
  have h_cum_le := cumulative_suspension_le_total_suspension
    job_arrival original_job_cost next_suspension sched_susp j_hp
    H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_respects_self_suspensions 0 t
  -- Chain: inflated_cost ≤ service_susp + total_susp
  -- inflated_cost = original_cost + total_susp
  -- So: original_cost ≤ service_susp
  simp only [completed_by]
  have h_chain : inflated_job_cost original_job_cost next_suspension j_hp ≤
      service sched_susp j_hp t + total_suspension original_job_cost next_suspension j_hp :=
    le_trans h_comp_new (le_trans h_ih (Nat.add_le_add_left h_cum_le _))
  simp only [inflated_job_cost] at h_chain
  exact Nat.le_of_add_le_add_right h_chain

include H_arrival_times_are_consistent H_jobs_from_taskset H_priority_is_reflexive H_priority_is_transitive H_priority_is_total H_dynamic_suspensions H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_work_conserving H_respects_priority H_respects_self_suspensions H_induction_hypothesis H_comes_from_arrival_sequence H_j_has_arrived H_j_is_pending H_j_scheduled_in_new H_j_not_scheduled_in_susp H_j_is_not_suspended H_j_hp_comes_from_sequence H_j_hp_is_scheduled H_higher_or_equal_priority in
theorem reduction_inductive_step_contradiction : False := by
  have h_comp_susp := reduction_inductive_step_j_hp_completed_in_susp
    job_arrival job_task ts arr_seq
    H_arrival_times_are_consistent H_jobs_from_taskset higher_eq_priority
    H_priority_is_reflexive H_priority_is_transitive H_priority_is_total
    original_job_cost next_suspension task_suspension_bound H_dynamic_suspensions
    sched_susp H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute
    H_completed_jobs_dont_execute H_work_conserving H_respects_priority
    H_respects_self_suspensions
    t H_induction_hypothesis j H_comes_from_arrival_sequence
    H_j_has_arrived H_j_is_pending H_j_scheduled_in_new H_j_not_scheduled_in_susp
    H_j_is_not_suspended j_hp H_j_hp_comes_from_sequence H_j_hp_is_scheduled
    H_higher_or_equal_priority
  exact absurd H_j_hp_is_scheduled
    (completed_implies_not_scheduled original_job_cost sched_susp j_hp
      H_completed_jobs_dont_execute t h_comp_susp)

end ProofByContradiction

end NotScheduledInSuspensionAware

include H_arrival_times_are_consistent H_jobs_from_taskset H_priority_is_reflexive H_priority_is_transitive H_priority_is_total H_dynamic_suspensions H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_work_conserving H_respects_priority H_respects_self_suspensions H_induction_hypothesis H_comes_from_arrival_sequence H_j_has_arrived H_j_is_pending in
theorem reduction_inductive_step_case2_pending :
    service (sched_new job_arrival original_job_cost next_suspension arr_seq higher_eq_priority sched_susp) j (t + 1) ≤
    service sched_susp j (t + 1) +
    cumulative_suspension job_arrival original_job_cost next_suspension sched_susp j (t + 1) := by
  have ih := H_induction_hypothesis j H_comes_from_arrival_sequence
  have h1 : service (sched_new job_arrival original_job_cost next_suspension arr_seq
      higher_eq_priority sched_susp) j (t + 1) =
      service (sched_new job_arrival original_job_cost next_suspension arr_seq
        higher_eq_priority sched_susp) j t +
      service_at (sched_new job_arrival original_job_cost next_suspension arr_seq
        higher_eq_priority sched_susp) j t := by
    simp only [service, service_during]
    exact Finset.sum_Ico_succ_top (Nat.zero_le t)
      (fun k => service_at (sched_new job_arrival original_job_cost next_suspension arr_seq
        higher_eq_priority sched_susp) j k)
  have h2 : service sched_susp j (t + 1) =
      service sched_susp j t + service_at sched_susp j t := by
    simp only [service, service_during]
    exact Finset.sum_Ico_succ_top (Nat.zero_le t) (fun k => service_at sched_susp j k)
  have h3 : cumulative_suspension job_arrival original_job_cost next_suspension
      sched_susp j (t + 1) =
      cumulative_suspension job_arrival original_job_cost next_suspension sched_susp j t +
      (if suspended_at job_arrival original_job_cost next_suspension sched_susp j t
        then 1 else 0) := by
    simp only [cumulative_suspension, cumulative_suspension_during]
    exact Finset.sum_Ico_succ_top (Nat.zero_le t)
      (fun k => if suspended_at job_arrival original_job_cost next_suspension sched_susp j k
        then 1 else 0)
  rw [h1, h2, h3]
  suffices h_step :
      service_at (sched_new job_arrival original_job_cost next_suspension arr_seq
        higher_eq_priority sched_susp) j t ≤
      service_at sched_susp j t +
      (if suspended_at job_arrival original_job_cost next_suspension sched_susp j t
        then 1 else 0) by omega
  simp only [service_at]
  by_cases h_sn : scheduled_at (sched_new job_arrival original_job_cost next_suspension
      arr_seq higher_eq_priority sched_susp) j t = true
  · by_cases h_ss : scheduled_at sched_susp j t = true
    · simp [h_ss]; cases scheduled_at (sched_new job_arrival original_job_cost next_suspension
          arr_seq higher_eq_priority sched_susp) j t <;> simp [Bool.toNat]
    · suffices h_susp : suspended_at job_arrival original_job_cost next_suspension
          sched_susp j t by
        simp [h_susp]; cases scheduled_at (sched_new job_arrival original_job_cost next_suspension
            arr_seq higher_eq_priority sched_susp) j t <;> simp [Bool.toNat]
      by_contra h_not_susp
      have h_back : susp.backlogged job_arrival original_job_cost next_suspension
          sched_susp j t := ⟨⟨H_j_has_arrived, H_j_is_pending⟩, h_ss, h_not_susp⟩
      obtain ⟨j_hp, h_sched_hp⟩ := H_work_conserving j t H_comes_from_arrival_sequence h_back
      have h_arr_hp := H_jobs_come_from_arrival_sequence j_hp t h_sched_hp
      have h_prio_hp := H_respects_priority j j_hp t H_comes_from_arrival_sequence
        h_back h_sched_hp
      exact absurd h_sched_hp (completed_implies_not_scheduled original_job_cost sched_susp j_hp
        H_completed_jobs_dont_execute t
        (reduction_inductive_step_j_hp_completed_in_susp
          job_arrival job_task ts arr_seq
          H_arrival_times_are_consistent H_jobs_from_taskset higher_eq_priority
          H_priority_is_reflexive H_priority_is_transitive H_priority_is_total
          original_job_cost next_suspension task_suspension_bound H_dynamic_suspensions
          sched_susp H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute
          H_completed_jobs_dont_execute H_work_conserving H_respects_priority
          H_respects_self_suspensions
          t H_induction_hypothesis j H_comes_from_arrival_sequence
          H_j_has_arrived H_j_is_pending
          h_sn h_ss h_not_susp j_hp h_arr_hp h_sched_hp h_prio_hp))
  · have hf := Bool.eq_false_of_not_eq_true h_sn; simp [hf]

end PendingInSuspensionAwareSchedule

end InductiveStep

include H_arrival_times_are_consistent H_jobs_from_taskset H_priority_is_reflexive H_priority_is_transitive H_priority_is_total H_dynamic_suspensions H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_work_conserving H_respects_priority H_respects_self_suspensions in
theorem suspension_oblivious_preserves_service :
    ∀ j t,
      arrives_in arr_seq j →
      service (sched_new job_arrival original_job_cost next_suspension arr_seq higher_eq_priority sched_susp) j t ≤
      service sched_susp j t +
      cumulative_suspension job_arrival original_job_cost next_suspension sched_susp j t := by
  intro j t; revert j; induction t with
  | zero =>
    intro j _; simp [service, service_during, cumulative_suspension, cumulative_suspension_during]
  | succ t ih =>
    intro j ARRj
    by_cases h_arr : has_arrived job_arrival j t
    · by_cases h_comp : completed_by original_job_cost sched_susp j t
      · exact reduction_inductive_step_case1_completed
          job_arrival job_task ts arr_seq
          H_arrival_times_are_consistent H_jobs_from_taskset higher_eq_priority
          H_priority_is_reflexive H_priority_is_transitive H_priority_is_total
          original_job_cost next_suspension task_suspension_bound H_dynamic_suspensions
          sched_susp H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute
          H_completed_jobs_dont_execute H_work_conserving H_respects_priority
          H_respects_self_suspensions
          t ih j ARRj h_arr h_comp
      · exact reduction_inductive_step_case2_pending
          job_arrival job_task ts arr_seq
          H_arrival_times_are_consistent H_jobs_from_taskset higher_eq_priority
          H_priority_is_reflexive H_priority_is_transitive H_priority_is_total
          original_job_cost next_suspension task_suspension_bound H_dynamic_suspensions
          sched_susp H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute
          H_completed_jobs_dont_execute H_work_conserving H_respects_priority
          H_respects_self_suspensions
          t ih j ARRj h_arr h_comp
    · exact reduction_inductive_step_not_arrived
        job_arrival job_task ts arr_seq
        H_arrival_times_are_consistent H_jobs_from_taskset higher_eq_priority
        H_priority_is_reflexive H_priority_is_transitive H_priority_is_total
        original_job_cost next_suspension task_suspension_bound H_dynamic_suspensions
        sched_susp H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute
        H_completed_jobs_dont_execute H_work_conserving H_respects_priority
        H_respects_self_suspensions
        t ih j ARRj h_arr

include H_arrival_times_are_consistent H_jobs_from_taskset H_priority_is_reflexive H_priority_is_transitive H_priority_is_total H_dynamic_suspensions H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_work_conserving H_respects_priority H_respects_self_suspensions in
theorem suspension_oblivious_preserves_completion :
    ∀ j t,
      arrives_in arr_seq j →
      completed_by (inflated_job_cost original_job_cost next_suspension)
        (sched_new job_arrival original_job_cost next_suspension arr_seq higher_eq_priority sched_susp) j t →
      completed_by original_job_cost sched_susp j t := by
  intro j t ARRj h_comp_new
  simp only [completed_by] at h_comp_new ⊢
  have h_serv := suspension_oblivious_preserves_service
    job_arrival job_task ts arr_seq
    H_arrival_times_are_consistent H_jobs_from_taskset higher_eq_priority
    H_priority_is_reflexive H_priority_is_transitive H_priority_is_total
    original_job_cost next_suspension task_suspension_bound H_dynamic_suspensions
    sched_susp H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute
    H_completed_jobs_dont_execute H_work_conserving H_respects_priority
    H_respects_self_suspensions j t ARRj
  have h_cum_le := cumulative_suspension_le_total_suspension
    job_arrival original_job_cost next_suspension sched_susp j
    H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_respects_self_suspensions 0 t
  -- inflated_cost = original_cost + total_susp ≤ service_new ≤ service_susp + cumul_susp ≤ service_susp + total_susp
  -- So original_cost ≤ service_susp
  have h_chain : inflated_job_cost original_job_cost next_suspension j ≤
      service sched_susp j t + total_suspension original_job_cost next_suspension j :=
    le_trans h_comp_new (le_trans h_serv (Nat.add_le_add_left h_cum_le _))
  simp only [inflated_job_cost] at h_chain
  exact Nat.le_of_add_le_add_right h_chain

end Service

end GeneratedScheduleIsValid

section Schedulability

variable (H_schedulable_without_suspensions :
  ∀ j,
    arrives_in arr_seq j →
    Prosa.Classic.Model.Schedule.Uni.Schedulability.job_misses_no_deadline
      job_arrival (inflated_job_cost original_job_cost next_suspension) job_deadline
      (sched_new job_arrival original_job_cost next_suspension arr_seq higher_eq_priority sched_susp) j)

include H_arrival_times_are_consistent H_jobs_from_taskset H_priority_is_reflexive H_priority_is_transitive H_priority_is_total H_dynamic_suspensions H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_work_conserving H_respects_priority H_respects_self_suspensions H_schedulable_without_suspensions in
theorem suspension_oblivious_preserves_schedulability :
    ∀ j,
      arrives_in arr_seq j →
      Prosa.Classic.Model.Schedule.Uni.Schedulability.job_misses_no_deadline
        job_arrival original_job_cost job_deadline sched_susp j := by
  intro j ARRj
  -- Bridge: Schedulability.service and Schedule.service are propositionally equal
  -- (they differ only in Bool.toNat vs if-then-else)
  have h_bool_bridge : ∀ (b : Bool), (if b = true then (1 : Nat) else 0) = b.toNat := by
    intro b; cases b <;> rfl
  have h_service_eq : ∀ (s : schedule Job) (j' : Job) (t' : Time),
      Prosa.Classic.Model.Schedule.Uni.Schedulability.service s j' t' = service s j' t' := by
    intro s j' t'
    simp only [Prosa.Classic.Model.Schedule.Uni.Schedulability.service,
      Prosa.Classic.Model.Schedule.Uni.Schedulability.service_during, service, service_during]
    apply Finset.sum_congr rfl
    intro k _
    simp only [Prosa.Classic.Model.Schedule.Uni.Schedulability.service_at,
      Prosa.Classic.Model.Schedule.Uni.Schedulability.scheduled_at, service_at, scheduled_at]
    exact h_bool_bridge _
  have h := H_schedulable_without_suspensions j ARRj
  simp only [Prosa.Classic.Model.Schedule.Uni.Schedulability.job_misses_no_deadline,
    Prosa.Classic.Model.Schedule.Uni.Schedulability.completed_by, h_service_eq] at h ⊢
  exact suspension_oblivious_preserves_completion
    job_arrival job_task ts arr_seq
    H_arrival_times_are_consistent H_jobs_from_taskset higher_eq_priority
    H_priority_is_reflexive H_priority_is_transitive H_priority_is_total
    original_job_cost next_suspension task_suspension_bound H_dynamic_suspensions
    sched_susp H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute
    H_completed_jobs_dont_execute H_work_conserving H_respects_priority
    H_respects_self_suspensions
    j (job_arrival j + job_deadline j) ARRj h

end Schedulability

end Reduction

end ReductionToBasicSchedule

end

end Prosa.Classic.Analysis.Uni.Susp.Dynamic.Oblivious.Reduction
