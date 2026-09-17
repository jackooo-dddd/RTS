-- Translated from: ../rt-proofs/classic/analysis/global/jitter/bertogna_fp_comp.v
import Prosa.Classic.Util.All
import Prosa.Classic.Analysis.Global.Jitter.Bertogna_fp_theory
import Mathlib.Tactic

set_option autoImplicit false

namespace Prosa.Classic.Analysis.Global.Jitter.Bertogna_fp_comp

open Prosa.Classic.Model.Time
open Prosa.Classic.Model.Arrival.Basic.Arrival_sequence
open Prosa.Classic.Model.Arrival.Basic.Job
open Prosa.Classic.Model.Arrival.Basic.Task
open Prosa.Classic.Model.Arrival.Basic.Task.SporadicTask
open Prosa.Classic.Model.Arrival.Basic.Task.SporadicTaskset
open Prosa.Classic.Model.Arrival.Basic.Task_arrival
open Prosa.Classic.Model.Schedule.Global.Basic.Schedule
open Prosa.Classic.Model.Schedule.Global.Basic.Schedule.Schedule
open Prosa.Classic.Model.Schedule.Global.Basic.Schedule.ScheduleOfSporadicTask
open Prosa.Classic.Model.Schedule.Global.Response_time.ResponseTime
open Prosa.Classic.Model.Schedule.Global.Schedulability.Schedulability
open Prosa.Classic.Model.Schedule.Global.Jitter.Job
open Prosa.Classic.Model.Schedule.Global.Jitter.Schedule
open Prosa.Classic.Model.Schedule.Global.Jitter.Schedule.ScheduleWithJitter
open Prosa.Classic.Model.Schedule.Global.Jitter.Schedule.ScheduleOfSporadicTaskWithJitter
open Prosa.Classic.Model.Schedule.Global.Jitter.Constrained_deadlines
open Prosa.Classic.Model.Priority
open Prosa.Classic.Analysis.Global.Jitter.Bertogna_fp_theory.ResponseTimeAnalysisFP
open Prosa.Classic.Analysis.Global.Jitter.Workload_bound.WorkloadBoundJitter
open Prosa.Util.Div_mod
open Prosa.Classic.Util.Fixedpoint
open Prosa.Classic.Util.Sorting

attribute [local instance] Classical.propDecidable

namespace ResponseTimeIterationFP

section Analysis

variable {sporadic_task : Type _} [DecidableEq sporadic_task]
variable (task_cost : sporadic_task → Time)
variable (task_period : sporadic_task → Time)
variable (task_deadline : sporadic_task → Time)
variable (task_jitter : sporadic_task → Time)

abbrev task_with_response_time (sporadic_task : Type _) := (sporadic_task × Time)

variable {Job : Type _} [DecidableEq Job]
variable (job_arrival : Job → Time)
variable (job_cost : Job → Time)
variable (job_deadline : Job → Time)
variable (job_task : Job → sporadic_task)
variable (job_jitter : Job → Time)

variable (num_cpus : ℕ)

variable (higher_priority : FP_policy sporadic_task)

noncomputable def per_task_rta (tsk : sporadic_task)
    (R_prev : List (sporadic_task × Time)) (step : ℕ) : Time :=
  (fun t => task_cost tsk +
    div_floor
      (total_interference_bound_fp task_cost task_period task_jitter tsk R_prev t)
      num_cpus)^[step] (task_cost tsk)

def max_steps (tsk : sporadic_task) : ℕ :=
  task_deadline tsk - task_cost tsk + 1

noncomputable def fp_bound_of_task
    (hp_pairs : Option (List (sporadic_task × Time)))
    (tsk : sporadic_task) : Option (List (sporadic_task × Time)) :=
  match hp_pairs with
  | some rt_bounds =>
    let R := per_task_rta task_cost task_period task_jitter num_cpus tsk rt_bounds
                (max_steps task_cost task_deadline tsk)
    if task_jitter tsk + R ≤ task_deadline tsk then
      some (rt_bounds ++ [(tsk, R)])
    else none
  | none => none

noncomputable def fp_claimed_bounds (ts : List sporadic_task) :
    Option (List (sporadic_task × Time)) :=
  ts.foldl (fp_bound_of_task task_cost task_period task_deadline task_jitter num_cpus) (some [])

def fp_schedulable (ts : List sporadic_task) : Prop :=
  fp_claimed_bounds task_cost task_period task_deadline task_jitter num_cpus ts ≠ none

section SimpleLemmas

theorem fp_claimed_bounds_unzip :
    ∀ (ts : List sporadic_task) (hp_bounds : List (sporadic_task × Time)),
      fp_claimed_bounds task_cost task_period task_deadline task_jitter num_cpus ts = some hp_bounds →
      hp_bounds.map Prod.fst = ts := by sorry

theorem fp_claimed_bounds_rcons :
    ∀ (ts' : List sporadic_task) (hp_bounds : List (sporadic_task × Time))
      (tsk1 tsk2 : sporadic_task) (R : Time),
      fp_claimed_bounds task_cost task_period task_deadline task_jitter num_cpus (ts' ++ [tsk1]) =
        some (hp_bounds ++ [(tsk2, R)]) →
      fp_claimed_bounds task_cost task_period task_deadline task_jitter num_cpus ts' = some hp_bounds ∧
      tsk1 = tsk2 ∧
      R = per_task_rta task_cost task_period task_jitter num_cpus tsk1 hp_bounds
            (max_steps task_cost task_deadline tsk1) ∧
      task_jitter tsk1 + R ≤ task_deadline tsk1 := by sorry

theorem fp_claimed_bounds_take :
    ∀ (ts : List sporadic_task) (hp_bounds : List (sporadic_task × Time)) (i : ℕ),
      fp_claimed_bounds task_cost task_period task_deadline task_jitter num_cpus ts = some hp_bounds →
      i ≤ hp_bounds.length →
      fp_claimed_bounds task_cost task_period task_deadline task_jitter num_cpus (ts.take i) =
        some (hp_bounds.take i) := by sorry

theorem fp_claimed_bounds_le_deadline :
    ∀ (ts' : List sporadic_task) (rt_bounds : List (sporadic_task × Time))
      (tsk : sporadic_task) (R : Time),
      fp_claimed_bounds task_cost task_period task_deadline task_jitter num_cpus ts' = some rt_bounds →
      (tsk, R) ∈ rt_bounds →
      task_jitter tsk + R ≤ task_deadline tsk := by sorry

theorem fp_claimed_bounds_ge_cost :
    ∀ (ts' : List sporadic_task) (rt_bounds : List (sporadic_task × Time))
      (tsk : sporadic_task) (R : Time),
      fp_claimed_bounds task_cost task_period task_deadline task_jitter num_cpus ts' = some rt_bounds →
      (tsk, R) ∈ rt_bounds →
      R ≥ task_cost tsk := by
    intro ts'
    induction ts' using List.reverseRecOn with
    | nil =>
      intro rt_bounds tsk R SOME IN
      simp [fp_claimed_bounds, List.foldl] at SOME
      subst SOME
      simp at IN
    | append_singleton ts_init tsk_lst ih =>
      intro rt_bounds tsk_i R SOME IN
      -- rt_bounds must also end with an element
      rcases List.eq_nil_or_concat rt_bounds with rfl | ⟨rt_init, last_pair, rfl⟩
      · -- rt_bounds = []
        have UNZIP := fp_claimed_bounds_unzip task_cost task_period task_deadline task_jitter num_cpus (ts_init ++ [tsk_lst]) [] SOME
        simp at UNZIP
      · -- rt_bounds = rt_init ++ [last_pair]
        obtain ⟨tsk_last, R_last⟩ := last_pair
        rw [List.concat_eq_append] at SOME IN
        rw [List.mem_append, List.mem_singleton] at IN
        rcases IN with IN_front | IN_last
        · -- (tsk_i, R) is in rt_init, use IH
          have RCONS := fp_claimed_bounds_rcons task_cost task_period task_deadline task_jitter num_cpus ts_init rt_init tsk_lst tsk_last R_last SOME
          exact ih rt_init tsk_i R RCONS.1 IN_front
        · -- (tsk_i, R) is the last element
          have RCONS := fp_claimed_bounds_rcons task_cost task_period task_deadline task_jitter num_cpus ts_init rt_init tsk_lst tsk_last R_last SOME
          obtain ⟨_, h_tsk_eq, h_R_eq, _⟩ := RCONS
          rw [Prod.mk.injEq] at IN_last
          obtain ⟨rfl, rfl⟩ := IN_last
          rw [h_R_eq, h_tsk_eq]
          -- R = per_task_rta ... (max_steps ...)
          -- per_task_rta is iter (max_steps) f (task_cost tsk_lst)
          -- so R ≥ task_cost tsk_lst
          unfold per_task_rta
          -- f^[max_steps] (task_cost tsk_lst) ≥ task_cost tsk_lst
          -- Since f x = task_cost + ... ≥ task_cost (because div_floor adds a non-negative number)
          -- and f^[0] x = task_cost, f^[n+1] = f (f^[n] x) ≥ task_cost
          generalize max_steps task_cost task_deadline tsk_i = n
          induction n with
          | zero => simp [Function.iterate_zero]
          | succ n ih_n =>
            rw [Function.iterate_succ', Function.comp]
            exact Nat.le_add_right _ _

theorem per_task_rta_fold :
    ∀ (tsk : sporadic_task) (rt_bounds : List (sporadic_task × Time)),
      task_cost tsk +
        div_floor
          (total_interference_bound_fp task_cost task_period task_jitter tsk rt_bounds
            (per_task_rta task_cost task_period task_jitter num_cpus tsk rt_bounds
              (max_steps task_cost task_deadline tsk)))
          num_cpus =
      per_task_rta task_cost task_period task_jitter num_cpus tsk rt_bounds
        (max_steps task_cost task_deadline tsk + 1) := by
    intro tsk rt_bounds
    simp only [per_task_rta, Nat.add_eq, Nat.add_zero]
    rw [Function.iterate_succ', Function.comp]

end SimpleLemmas

section HighPriorityTasks

variable (ts : List sporadic_task)

variable (H_task_set_is_sorted : List.IsChain (fun a b => higher_priority a b = true) ts)
variable (H_task_set_has_unique_priorities :
  FP_is_antisymmetric_over_task_set higher_priority ts)

variable (H_priority_transitive : FP_is_transitive higher_priority)

variable (hp_bounds : List (sporadic_task × Time))
variable (R : Time)
variable (H_analysis_succeeds :
  fp_claimed_bounds task_cost task_period task_deadline task_jitter num_cpus ts = some hp_bounds)

variable (elem : sporadic_task)

include H_task_set_is_sorted H_task_set_has_unique_priorities
  H_priority_transitive H_analysis_succeeds in
theorem fp_claimed_bounds_hp_tasks_have_smaller_index :
    ∀ (hp_idx idx : ℕ),
      hp_idx < ts.length →
      idx < ts.length →
      hp_idx ≠ idx →
      higher_priority (ts.getD hp_idx elem) (ts.getD idx elem) = true →
      hp_idx < idx := by sorry

end HighPriorityTasks

section Convergence

variable (ts_hp : List sporadic_task)

variable (rt_bounds : List (sporadic_task × Time))
variable (H_test_succeeds :
  fp_claimed_bounds task_cost task_period task_deadline task_jitter num_cpus ts_hp = some rt_bounds)

variable (tsk : sporadic_task)

variable (H_valid_task_parameters :
  valid_sporadic_taskset task_cost task_period task_deadline (ts_hp ++ [tsk]))

variable (H_no_larger_than_deadline :
  per_task_rta task_cost task_period task_jitter num_cpus tsk rt_bounds
    (max_steps task_cost task_deadline tsk) ≤ task_deadline tsk)

include H_test_succeeds H_valid_task_parameters H_no_larger_than_deadline in
theorem bertogna_fp_comp_f_monotonic :
    ∀ (x1 x2 : ℕ), x1 ≤ x2 →
      per_task_rta task_cost task_period task_jitter num_cpus tsk rt_bounds x1 ≤
        per_task_rta task_cost task_period task_jitter num_cpus tsk rt_bounds x2 := by
    intro x1 x2 LEx
    unfold per_task_rta
    apply fun_mon_iter_mon
    · exact LEx
    · -- f x0 ≥ x0: task_cost tsk ≤ task_cost tsk + div_floor ...
      exact Nat.le_add_right _ _
    · -- f is monotonic
      intro a b hab
      show task_cost tsk + div_floor (total_interference_bound_fp task_cost task_period task_jitter tsk rt_bounds a) num_cpus ≤
           task_cost tsk + div_floor (total_interference_bound_fp task_cost task_period task_jitter tsk rt_bounds b) num_cpus
      apply Nat.add_le_add_left
      unfold div_floor
      apply Nat.div_le_div_right
      -- Need to show total_interference_bound_fp ... a ≤ total_interference_bound_fp ... b
      unfold total_interference_bound_fp
      apply List.sum_le_sum
      intro tsk_R h_mem
      -- For each (i, R) in rt_bounds, interference_bound_generic ... a tsk_R ≤ ... b tsk_R
      unfold interference_bound_generic
      apply min_le_min
      · -- W_jitter ... a ≤ W_jitter ... b
        have h_in_rt : (tsk_R.1, tsk_R.2) ∈ rt_bounds := by rwa [Prod.mk.eta]
        have GE_COST := fp_claimed_bounds_ge_cost task_cost task_period task_deadline task_jitter num_cpus ts_hp rt_bounds tsk_R.1 tsk_R.2 H_test_succeeds h_in_rt
        have UNZIP := fp_claimed_bounds_unzip task_cost task_period task_deadline task_jitter num_cpus ts_hp rt_bounds H_test_succeeds
        have INts : tsk_R.1 ∈ ts_hp := by
          rw [← UNZIP]; exact List.mem_map_of_mem (f := Prod.fst) h_in_rt
        have PARAMS := H_valid_task_parameters tsk_R.1 (List.mem_append_left _ INts)
        unfold is_valid_sporadic_task at PARAMS
        exact W_monotonic task_cost task_period task_jitter tsk_R.1 PARAMS.2.1 tsk_R.2 tsk_R.2 GE_COST (Nat.le_refl _) a b hab
      · -- a - task_cost tsk + 1 ≤ b - task_cost tsk + 1
        omega

include H_test_succeeds in
theorem bertogna_fp_comp_f_converges_early :
    (∃ k, k ≤ max_steps task_cost task_deadline tsk ∧
      per_task_rta task_cost task_period task_jitter num_cpus tsk rt_bounds k =
        per_task_rta task_cost task_period task_jitter num_cpus tsk rt_bounds (k + 1)) →
    per_task_rta task_cost task_period task_jitter num_cpus tsk rt_bounds
      (max_steps task_cost task_deadline tsk) =
      per_task_rta task_cost task_period task_jitter num_cpus tsk rt_bounds
        (max_steps task_cost task_deadline tsk + 1) := by
    intro ⟨k, hk_le, hk_eq⟩
    unfold per_task_rta at *
    exact iter_fix ℕ _ (task_cost tsk) k (max_steps task_cost task_deadline tsk) hk_eq hk_le

section DerivingContradiction

variable (H_keeps_diverging :
  ∀ k, k ≤ max_steps task_cost task_deadline tsk →
    per_task_rta task_cost task_period task_jitter num_cpus tsk rt_bounds k ≠
      per_task_rta task_cost task_period task_jitter num_cpus tsk rt_bounds (k + 1))

include H_test_succeeds H_valid_task_parameters H_no_larger_than_deadline
  H_keeps_diverging in
theorem bertogna_fp_comp_f_increases :
    ∀ k, k ≤ max_steps task_cost task_deadline tsk →
      per_task_rta task_cost task_period task_jitter num_cpus tsk rt_bounds k <
        per_task_rta task_cost task_period task_jitter num_cpus tsk rt_bounds (k + 1) := by
    intro k hk
    exact Nat.lt_of_le_of_ne
      (bertogna_fp_comp_f_monotonic task_cost task_period task_deadline task_jitter num_cpus ts_hp rt_bounds H_test_succeeds tsk H_valid_task_parameters H_no_larger_than_deadline k (k + 1) (Nat.le_succ k))
      (H_keeps_diverging k hk)

include H_valid_task_parameters H_keeps_diverging in
theorem bertogna_fp_comp_rt_grows_too_much :
    ∀ k, k ≤ max_steps task_cost task_deadline tsk →
      per_task_rta task_cost task_period task_jitter num_cpus tsk rt_bounds k >
        k + task_cost tsk - 1 := by sorry

end DerivingContradiction

include H_test_succeeds H_valid_task_parameters H_no_larger_than_deadline in
theorem per_task_rta_converges :
    per_task_rta task_cost task_period task_jitter num_cpus tsk rt_bounds
      (max_steps task_cost task_deadline tsk) =
      per_task_rta task_cost task_period task_jitter num_cpus tsk rt_bounds
        (max_steps task_cost task_deadline tsk + 1) := by sorry

end Convergence

section MainProof

variable (ts : List sporadic_task)

variable (H_valid_task_parameters :
  valid_sporadic_taskset task_cost task_period task_deadline ts)

variable (H_constrained_deadlines :
  ∀ tsk, tsk ∈ ts → task_deadline tsk ≤ task_period tsk)

variable (H_task_set_is_sorted :
  List.IsChain (fun a b => higher_priority a b = true) ts)
variable (H_task_set_has_unique_priorities :
  FP_is_antisymmetric_over_task_set higher_priority ts)
variable (H_priority_is_total :
  FP_is_total_over_task_set higher_priority ts)
variable (H_priority_transitive : FP_is_transitive higher_priority)

variable (arr_seq : arrival_sequence Job)

variable (H_all_jobs_from_taskset :
  ∀ j, arrives_in arr_seq j → job_task j ∈ ts)

variable (H_valid_job_parameters :
  ∀ j,
    arrives_in arr_seq j →
    valid_sporadic_job_with_jitter task_cost task_deadline task_jitter job_cost
                                   job_deadline job_task job_jitter j)

variable (H_sporadic_tasks :
  Prosa.Classic.Model.Arrival.Basic.Task_arrival.sporadic_task_model task_period job_arrival job_task arr_seq)

variable {num_cpus : ℕ}
variable (sched : schedule Job num_cpus)
variable (H_at_least_one_cpu : num_cpus > 0)
variable (H_jobs_come_from_arrival_sequence :
  jobs_come_from_arrival_sequence sched arr_seq)

variable (H_jobs_must_arrive_to_execute :
  Prosa.Classic.Model.Schedule.Global.Jitter.Schedule.ScheduleWithJitter.jobs_execute_after_jitter
    job_arrival job_jitter sched)
variable (H_completed_jobs_dont_execute :
  completed_jobs_dont_execute job_cost sched)

variable (H_sequential_jobs : sequential_jobs sched)

variable (H_work_conserving :
  Prosa.Classic.Model.Schedule.Global.Jitter.Constrained_deadlines.work_conserving
    job_arrival job_cost job_jitter arr_seq sched)
variable (H_respects_FP_policy :
  respects_FP_policy_jitter job_arrival job_cost job_task job_jitter arr_seq sched higher_priority)

private abbrev no_deadline_missed_by_task (tsk : sporadic_task) :=
  task_misses_no_deadline job_arrival job_cost job_deadline job_task arr_seq sched tsk

private abbrev no_deadline_missed_by_job (j : Job) :=
  job_misses_no_deadline job_arrival job_cost job_deadline sched j

private abbrev response_time_bounded_by' (tsk : sporadic_task) (R : Time) :=
  is_response_time_bound_of_task job_arrival job_cost job_task arr_seq sched tsk R

include H_valid_task_parameters H_constrained_deadlines
  H_task_set_is_sorted H_task_set_has_unique_priorities
  H_priority_is_total H_priority_transitive
  H_all_jobs_from_taskset H_valid_job_parameters
  H_sporadic_tasks H_at_least_one_cpu
  H_jobs_come_from_arrival_sequence
  H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute
  H_sequential_jobs
  H_work_conserving H_respects_FP_policy in
theorem fp_analysis_yields_response_time_bounds :
    ∀ (tsk : sporadic_task) (R : Time),
      (match fp_claimed_bounds task_cost task_period task_deadline task_jitter num_cpus ts with
       | some rt_bounds => (tsk, R) ∈ rt_bounds
       | none => False) →
      response_time_bounded_by' job_arrival job_cost job_task arr_seq sched tsk
        (task_jitter tsk + R) := by sorry

variable (H_test_succeeds :
  fp_schedulable task_cost task_period task_deadline task_jitter num_cpus ts)

include H_valid_task_parameters H_constrained_deadlines
  H_task_set_is_sorted H_task_set_has_unique_priorities
  H_priority_is_total H_priority_transitive
  H_all_jobs_from_taskset H_valid_job_parameters
  H_sporadic_tasks H_at_least_one_cpu
  H_jobs_come_from_arrival_sequence
  H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute
  H_sequential_jobs
  H_work_conserving H_respects_FP_policy H_test_succeeds in
include H_valid_task_parameters H_constrained_deadlines H_task_set_is_sorted H_task_set_has_unique_priorities H_priority_is_total H_priority_transitive H_all_jobs_from_taskset H_valid_job_parameters H_sporadic_tasks H_at_least_one_cpu H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_sequential_jobs H_work_conserving H_respects_FP_policy H_test_succeeds in
theorem taskset_schedulable_by_fp_rta :
    ∀ tsk, tsk ∈ ts →
      no_deadline_missed_by_task job_arrival job_cost job_deadline job_task arr_seq sched tsk := by
  intro tsk INtsk j ARRj JOBtsk
  -- Get rt_bounds from fp_schedulable
  unfold fp_schedulable at H_test_succeeds
  -- fp_claimed_bounds ts ≠ none
  obtain ⟨rt_bounds, h_eq⟩ : ∃ rt_bounds, fp_claimed_bounds task_cost task_period task_deadline task_jitter num_cpus ts = some rt_bounds := by
    cases h : fp_claimed_bounds task_cost task_period task_deadline task_jitter num_cpus ts with
    | none => exfalso; exact H_test_succeeds h
    | some val => exact ⟨val, rfl⟩
  -- Find R such that (tsk, R) ∈ rt_bounds
  have UNZIP := fp_claimed_bounds_unzip task_cost task_period task_deadline task_jitter num_cpus ts rt_bounds h_eq
  have INmap : tsk ∈ rt_bounds.map Prod.fst := by rw [UNZIP]; exact INtsk
  obtain ⟨⟨tsk', R⟩, h_mem, h_fst⟩ := List.mem_map.mp INmap
  simp at h_fst; subst h_fst
  -- Get the response time bound
  have RLIST := fp_analysis_yields_response_time_bounds task_cost task_period task_deadline task_jitter
    job_arrival job_cost job_deadline job_task job_jitter higher_priority ts
    H_valid_task_parameters H_constrained_deadlines H_task_set_is_sorted
    H_task_set_has_unique_priorities H_priority_is_total H_priority_transitive
    arr_seq H_all_jobs_from_taskset H_valid_job_parameters H_sporadic_tasks sched
    H_at_least_one_cpu H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute
    H_completed_jobs_dont_execute H_sequential_jobs H_work_conserving H_respects_FP_policy
    tsk' R
  -- Apply RLIST with the match
  have h_match : (match fp_claimed_bounds task_cost task_period task_deadline task_jitter num_cpus ts with
     | some rt_bounds => (tsk', R) ∈ rt_bounds
     | none => False) := by rw [h_eq]; exact h_mem
  have COMPLETED := RLIST h_match j ARRj JOBtsk
  -- Get deadline bound
  have DL := fp_claimed_bounds_le_deadline task_cost task_period task_deadline task_jitter num_cpus ts rt_bounds tsk' R h_eq h_mem
  -- job_deadline j = task_deadline tsk'
  have JOBPARAMS := H_valid_job_parameters j ARRj
  unfold valid_sporadic_job_with_jitter at JOBPARAMS
  have h_dl_eq : job_deadline j = task_deadline (job_task j) := JOBPARAMS.1.2.2
  rw [JOBtsk] at h_dl_eq
  -- completed at job_arrival j + (task_jitter tsk' + R)
  -- Need: completed at job_arrival j + job_deadline j
  -- i.e., service sched j (job_arrival j + job_deadline j) ≥ job_cost j
  -- We have: service sched j (job_arrival j + (task_jitter tsk' + R)) ≥ job_cost j
  -- and: task_jitter tsk' + R ≤ task_deadline tsk' = job_deadline j
  -- so: job_arrival j + (task_jitter tsk' + R) ≤ job_arrival j + job_deadline j
  have h_le : job_arrival j + (task_jitter tsk' + R) ≤ job_arrival j + job_deadline j := by
    apply Nat.add_le_add_left
    rw [h_dl_eq]; exact DL
  exact completion_monotonic job_cost sched j H_completed_jobs_dont_execute
    (job_arrival j + (task_jitter tsk' + R)) (job_arrival j + job_deadline j)
    h_le COMPLETED

include H_valid_task_parameters H_constrained_deadlines
  H_task_set_is_sorted H_task_set_has_unique_priorities
  H_priority_is_total H_priority_transitive
  H_all_jobs_from_taskset H_valid_job_parameters
  H_sporadic_tasks H_at_least_one_cpu
  H_jobs_come_from_arrival_sequence
  H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute
  H_sequential_jobs
  H_work_conserving H_respects_FP_policy H_test_succeeds in
theorem jobs_schedulable_by_fp_rta :
    ∀ j, arrives_in arr_seq j →
      no_deadline_missed_by_job job_arrival job_cost job_deadline sched j := by
  intro j ARRj
  have SCHED := taskset_schedulable_by_fp_rta task_cost task_period task_deadline task_jitter
    job_arrival job_cost job_deadline job_task job_jitter higher_priority ts
    H_valid_task_parameters H_constrained_deadlines H_task_set_is_sorted
    H_task_set_has_unique_priorities H_priority_is_total H_priority_transitive
    arr_seq H_all_jobs_from_taskset H_valid_job_parameters H_sporadic_tasks sched
    H_at_least_one_cpu H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute
    H_completed_jobs_dont_execute H_sequential_jobs H_work_conserving H_respects_FP_policy
    H_test_succeeds
  exact SCHED (job_task j) (H_all_jobs_from_taskset j ARRj) j ARRj rfl

end MainProof

end Analysis

end ResponseTimeIterationFP

end Prosa.Classic.Analysis.Global.Jitter.Bertogna_fp_comp
