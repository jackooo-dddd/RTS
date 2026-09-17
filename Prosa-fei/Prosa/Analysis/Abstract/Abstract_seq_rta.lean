-- Translated from: ../rt-proofs/analysis/abstract/abstract_seq_rta.v
import Prosa.Analysis.Definitions.Task_schedule
import Prosa.Analysis.Facts.Model.Rbf
import Prosa.Analysis.Facts.Model.Task_arrivals
import Prosa.Analysis.Facts.Model.Sequential
import Prosa.Analysis.Abstract.Abstract_rta

namespace Prosa.Analysis.Abstract.Abstract_seq_rta

open Prosa.Behavior.Job
open Prosa.Behavior.Time
open Prosa.Behavior.Schedule
open Prosa.Behavior.Service
open Prosa.Behavior.Arrival_sequence
open Prosa.Behavior.Ready
open Prosa.Model.Task.Concept
open Prosa.Model.Processor.Ideal
open Prosa.Model.Task.Arrival.Curves
open Prosa.Model.Processor.Platform_properties
open Prosa.Model.Preemption.Parameter
open Prosa.Model.Task.Preemption.Parameters
open Prosa.Model.Task.Arrivals
open Prosa.Model.Task.Sequentiality
open Prosa.Model.Aggregate.Workload
open Prosa.Model.Aggregate.Service_of_jobs
open Prosa.Analysis.Abstract.Definitions
open Prosa.Analysis.Abstract.Search_space
open Prosa.Analysis.Abstract.Run_to_completion
open Prosa.Analysis.Definitions.Schedulability
open Prosa.Analysis.Definitions.Task_schedule
open Prosa.Analysis.Definitions.Job_properties
open Prosa.Analysis.Definitions.Request_bound_function
open Prosa.Analysis.Facts.Behavior.Completion
open Prosa.Analysis.Facts.Behavior.Service
open Prosa.Analysis.Facts.Model.Rbf
open Prosa.Analysis.Facts.Model.Task_arrivals
open Prosa.Analysis.Facts.Model.Sequential
open Prosa.Util.Epsilon
open Prosa.Analysis.Facts.Model.Ideal_schedule

section Sequential_Abstract_RTA

variable {Task : TaskType}
variable [TaskCost Task]
variable [TaskRunToCompletionThreshold Task]
variable [DecidableEq Task]

variable {Job : JobType}
variable [DecidableEq Job]
variable [JobTask Job Task]
variable [JobArrival Job]
variable [JobCost Job]
variable [JobPreemptable Job]

variable (arr_seq : arrival_sequence Job)
variable (H_arrival_times_are_consistent : consistent_arrival_times arr_seq)
variable (H_arr_seq_is_a_set : arrival_sequence_uniq arr_seq)

attribute [local instance] pstate_instance

variable (sched : schedule (processor_state Job))
variable (H_jobs_come_from_arrival_sequence :
  jobs_come_from_arrival_sequence (Job := Job) sched arr_seq)

variable (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute (Job := Job) sched)
variable (H_completed_jobs_dont_execute : completed_jobs_dont_execute (Job := Job) sched)

variable (H_valid_job_cost : arrivals_have_valid_job_costs (Task := Task) arr_seq)

variable (ts : List Task)

variable (tsk : Task)
variable (H_tsk_in_ts : tsk ∈ ts)

variable (H_valid_preemption_model : valid_preemption_model arr_seq sched)

variable (H_valid_run_to_completion_threshold :
  valid_task_run_to_completion_threshold arr_seq tsk)

variable [MaxArrivals Task]
variable (H_valid_arrival_curve : valid_taskset_arrival_curve ts max_arrivals)
variable (H_is_arrival_curve : taskset_respects_max_arrivals arr_seq ts)

variable (interference : Job → instant → Bool)
variable (interfering_workload : Job → instant → duration)

section Definitions

def interference_and_workload_consistent_with_sequential_tasks
    {Task : TaskType} [TaskCost Task] [DecidableEq Task] {Job : JobType} [DecidableEq Job]
    [JobTask Job Task] [JobArrival Job] [JobCost Job] [JobPreemptable Job]
    (arr_seq : arrival_sequence Job) (sched : schedule (processor_state Job))
    (tsk : Task) (interference : Job → instant → Bool)
    (interfering_workload : Job → instant → duration) : Prop :=
  ∀ (j : Job) (t1 t2 : instant),
    arrives_in arr_seq j →
    job_task j = tsk →
    job_cost j > 0 →
    busy_interval sched interference interfering_workload j t1 t2 →
    task_workload_between arr_seq tsk 0 t1 =
      task_service_of_jobs_in sched tsk (arrivals_between arr_seq 0 t1) 0 t1

def task_interference_received_before
    {Task : TaskType} [TaskCost Task] [DecidableEq Task]
    {Job : JobType} [DecidableEq Job]
    [JobTask Job Task] [JobArrival Job] [JobCost Job]
    (arr_seq : arrival_sequence Job) (sched : schedule (processor_state Job))
    (tsk : Task) (interference : Job → instant → Bool)
    (upper_bound : instant) (t : instant) : Nat :=
  ((!task_scheduled_at sched tsk t) &&
    (task_arrivals_before arr_seq tsk upper_bound).any (fun j => interference j t)).toNat

noncomputable def cumul_task_interference
    {Task : TaskType} [TaskCost Task] [DecidableEq Task]
    {Job : JobType} [DecidableEq Job]
    [JobTask Job Task] [JobArrival Job] [JobCost Job]
    (arr_seq : arrival_sequence Job) (sched : schedule (processor_state Job))
    (tsk : Task) (interference : Job → instant → Bool)
    (upper_bound : instant) (t1 t2 : instant) : Nat :=
  Finset.sum (Finset.Ico t1 t2) fun t =>
    task_interference_received_before arr_seq sched tsk interference upper_bound t

def task_interference_is_bounded_by
    {Task : TaskType} [TaskCost Task] [DecidableEq Task]
    {Job : JobType} [DecidableEq Job]
    [JobTask Job Task] [JobArrival Job] [JobCost Job] [JobPreemptable Job]
    (arr_seq : arrival_sequence Job) (sched : schedule (processor_state Job))
    (tsk : Task) (interference : Job → instant → Bool)
    (interfering_workload : Job → instant → duration)
    (task_interference_bound_function : Task → duration → duration → duration) : Prop :=
  ∀ j R t1 t2,
    arrives_in arr_seq j →
    job_task j = tsk →
    t1 + R < t2 →
    ¬ completed_by sched j (t1 + R) →
    busy_interval sched interference interfering_workload j t1 t2 →
    let offset := job_arrival j - t1
    cumul_task_interference arr_seq sched tsk interference t2 t1 (t1 + R) ≤
      task_interference_bound_function tsk offset R

end Definitions

section ResponseTimeBound

variable (H_work_conserving :
  work_conserving arr_seq sched tsk interference interfering_workload)

variable (H_sequential_tasks : sequential_tasks (Job := Job) (Task := Task) sched)
variable (H_interference_and_workload_consistent_with_sequential_tasks_ :
  interference_and_workload_consistent_with_sequential_tasks
    arr_seq sched tsk interference interfering_workload)

variable (L : duration)
variable (H_busy_interval_exists :
  busy_intervals_are_bounded_by arr_seq sched tsk interference interfering_workload L)

variable (task_interference_bound_function : Task → duration → duration → duration)
variable (H_task_interference_is_bounded :
  task_interference_is_bounded_by arr_seq sched tsk interference interfering_workload
    task_interference_bound_function)

private noncomputable def total_interference_bound_val
    (tsk : Task) [TaskCost Task] [MaxArrivals Task] (A D : duration)
    (task_interference_bound_function : Task → duration → duration → duration) : duration :=
  task_request_bound_function tsk (A + ε) - task_cost tsk +
    task_interference_bound_function tsk A D

variable (R : Nat)
variable (H_R_is_maximum_seq :
  ∀ (A : duration),
    is_in_search_space tsk L
      (fun tsk' A' R' => total_interference_bound_val tsk' A' R' task_interference_bound_function) A →
    ∃ (F : duration),
      A + F = (task_request_bound_function tsk (A + ε) -
                (task_cost tsk - task_run_to_completion_threshold tsk))
              + task_interference_bound_function tsk A (A + F) ∧
      F + (task_cost tsk - task_run_to_completion_threshold tsk) ≤ R)

section CompletionOfJobsFromSameTask

variable (j1 j2 : Job)
variable (H_j1_arrives : arrives_in arr_seq j1)
variable (H_j2_arrives : arrives_in arr_seq j2)
variable (H_j1_from_tsk : job_task j1 = tsk)
variable (H_j2_from_tsk : job_task j2 = tsk)
variable (H_j1_cost_positive : job_cost_positive j1)

variable (t1 t2 : instant)
variable (H_busy_interval :
  busy_interval sched interference interfering_workload j1 t1 t2)

include H_j2_arrives H_j2_from_tsk H_j1_arrives H_j1_from_tsk H_j1_cost_positive
  H_busy_interval H_interference_and_workload_consistent_with_sequential_tasks_
  H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute
  H_completed_jobs_dont_execute H_arrival_times_are_consistent in
theorem completed_before_beginning_of_busy_interval :
    job_arrival j2 < t1 →
    completed_by sched j2 t1 := by
  intro JA
  -- If job_cost j2 = 0 then trivially completed
  by_cases h_zero : job_cost j2 = 0
  · unfold completed_by; rw [h_zero]; exact Nat.zero_le _
  -- Otherwise: use sequential consistency to get workload = service
  have POS : job_cost j2 > 0 := Nat.pos_of_ne_zero h_zero
  have SWEQ := H_interference_and_workload_consistent_with_sequential_tasks_
    j1 t1 t2 H_j1_arrives H_j1_from_tsk (H_j1_cost_positive) H_busy_interval
  -- SWEQ : task_workload_between arr_seq tsk 0 t1 = task_service_of_jobs_in sched tsk (arrivals_between arr_seq 0 t1) 0 t1
  -- This unfolds to: workload_of_jobs (job_of_task tsk) (arrivals_between arr_seq 0 t1)
  --                 = service_of_jobs sched (job_of_task tsk) (arrivals_between arr_seq 0 t1) 0 t1
  -- Use the backward direction of all_jobs_have_completed
  have h_all_compl := (Prosa.Analysis.Facts.Model.Service_of_jobs.workload_eq_service_impl_all_jobs_have_completed
    arr_seq H_arrival_times_are_consistent sched H_jobs_come_from_arrival_sequence
    H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute
    (job_of_task tsk) 0 t1 t1)
  -- Need to apply h_all_compl to SWEQ and then specialize to j2
  -- First, unfold the definitions to match
  unfold task_workload_between task_workload task_service_of_jobs_in at SWEQ
  have h_j2_compl := h_all_compl SWEQ j2
  -- j2 is in arrivals_between 0 t1
  have h_j2_in : j2 ∈ arrivals_between arr_seq 0 t1 := by
    apply Prosa.Analysis.Facts.Behavior.Arrivals.arrived_between_implies_in_arrivals
      arr_seq H_arrival_times_are_consistent j2 0 t1 H_j2_arrives
    unfold arrived_between; constructor <;> [exact Nat.zero_le _; exact JA]
  -- job_of_task tsk j2 = true
  have h_j2_tsk : job_of_task tsk j2 = true := by
    unfold job_of_task; simp [H_j2_from_tsk]
  exact h_j2_compl h_j2_in h_j2_tsk

include H_j2_arrives H_j2_from_tsk H_j1_arrives H_j1_from_tsk H_j1_cost_positive
  H_busy_interval H_interference_and_workload_consistent_with_sequential_tasks_
  H_completed_jobs_dont_execute
  H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute
  H_arrival_times_are_consistent in
theorem arrives_after_beginning_of_busy_interval :
    ∀ t,
      t1 ≤ t →
      pending sched j2 t →
      arrived_between j2 t1 (t + 1) := by
  intro t GE PEND
  unfold arrived_between
  constructor
  · -- t1 ≤ job_arrival j2 by contradiction
    by_contra h; push_neg at h
    have L12 := completed_before_beginning_of_busy_interval
      arr_seq H_arrival_times_are_consistent sched
      H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute
      H_completed_jobs_dont_execute
      tsk interference interfering_workload
      H_interference_and_workload_consistent_with_sequential_tasks_
      j1 j2 H_j1_arrives H_j2_arrives H_j1_from_tsk H_j2_from_tsk
      H_j1_cost_positive t1 t2 H_busy_interval h
    have L12t := completion_monotonic sched j2 t1 t GE L12
    exact PEND.2 L12t
  · -- job_arrival j2 < t + 1
    unfold pending at PEND
    have := PEND.1
    unfold Prosa.Behavior.Arrival_sequence.has_arrived at this
    unfold instant duration at *
    omega

end CompletionOfJobsFromSameTask

section BoundOfCumulativeJobInterference

variable (j : Job)
variable (H_j_arrives : arrives_in arr_seq j)
variable (H_job_of_tsk : job_task j = tsk)
variable (H_job_cost_positive : job_cost_positive j)

variable (t1 t2 : instant)
variable (H_busy_interval :
  busy_interval sched interference interfering_workload j t1 t2)

private noncomputable def A_seq (j : Job) (t1 : instant) : duration := job_arrival j - t1

variable (x : duration)
variable (H_inside_busy_interval : t1 + x < t2)
variable (H_job_j_is_not_completed : ¬ completed_by sched j (t1 + x))

section TaskInterferenceBoundsInterference

section CaseAnalysis

variable (t : instant)
variable (H_t_in_interval : t1 ≤ t ∧ t < t1 + x)

include H_busy_interval H_j_arrives H_job_of_tsk H_job_cost_positive
  H_t_in_interval H_inside_busy_interval H_arrival_times_are_consistent in
theorem interference_plus_sched_le_serv_of_task_plus_task_interference_idle
    (H_idle : sched t = none) :
    (interference j t).toNat + (scheduled_at sched j t).toNat ≤
    service_of_jobs_at sched (job_of_task tsk)
      (arrivals_between arr_seq t1 (t1 + A_seq j t1 + ε)) t +
    task_interference_received_before arr_seq sched tsk interference t2 t := by
  -- scheduled_at j t = false when sched t = none
  have h_not_sched : scheduled_at sched j t = false := by
    rw [scheduled_at_def]; simp [H_idle]
  rw [h_not_sched]; simp only [Bool.toNat_false, Nat.add_zero]
  by_cases h_int : interference j t = true
  · -- interference = true ⟹ toNat = 1
    simp only [h_int, Bool.toNat_true]
    -- suffices: task_interference_received_before ≥ 1
    suffices h : task_interference_received_before arr_seq sched tsk interference t2 t ≥ 1 by omega
    unfold task_interference_received_before
    have h_not_task_sched : task_scheduled_at sched tsk t = false := by
      unfold task_scheduled_at; rw [H_idle]
    have h_any : (task_arrivals_before arr_seq tsk t2).any (fun j' => interference j' t) = true := by
      apply List.any_of_mem (a := j)
      · unfold task_arrivals_before task_arrivals_between
        rw [List.mem_filter]
        constructor
        · apply Prosa.Analysis.Facts.Behavior.Arrivals.arrived_between_implies_in_arrivals
            arr_seq H_arrival_times_are_consistent j 0 t2 H_j_arrives
          unfold arrived_between; constructor
          · exact Nat.zero_le _
          · exact H_busy_interval.1.1.2
        · simp [job_of_task, H_job_of_tsk]
      · exact h_int
    simp [h_not_task_sched, h_any]
  · have h_false : interference j t = false := by
      match h : interference j t with
      | true => exact absurd h h_int
      | false => rfl
    simp [h_false]

include H_busy_interval H_j_arrives H_job_of_tsk H_job_cost_positive
  H_t_in_interval H_jobs_come_from_arrival_sequence H_arrival_times_are_consistent in
theorem interference_plus_sched_le_serv_of_task_plus_task_interference_task
    (j' : Job) (H_sched : sched t = some j') (H_not_job_of_tsk : ¬ (job_task j' = tsk)) :
    (interference j t).toNat + (scheduled_at sched j t).toNat ≤
    service_of_jobs_at sched (job_of_task tsk)
      (arrivals_between arr_seq t1 (t1 + A_seq j t1 + ε)) t +
    task_interference_received_before arr_seq sched tsk interference t2 t := by
  -- j ≠ j' since job_task j = tsk but job_task j' ≠ tsk
  have h_j_neq_j' : j ≠ j' := fun h => by subst h; exact H_not_job_of_tsk H_job_of_tsk
  -- scheduled_at j t = false since sched t = some j' and j ≠ j'
  have h_not_sched : scheduled_at sched j t = false := by
    rw [scheduled_at_def]; simp [H_sched, Ne.symm h_j_neq_j']
  rw [h_not_sched]; simp only [Bool.toNat_false, Nat.add_zero]
  by_cases h_int : interference j t = true
  · simp only [h_int, Bool.toNat_true]
    suffices h : task_interference_received_before arr_seq sched tsk interference t2 t ≥ 1 by omega
    unfold task_interference_received_before
    have h_not_task_sched : task_scheduled_at sched tsk t = false := by
      unfold task_scheduled_at; rw [H_sched]; simp [H_not_job_of_tsk]
    have h_any : (task_arrivals_before arr_seq tsk t2).any (fun j' => interference j' t) = true := by
      apply List.any_of_mem (a := j)
      · unfold task_arrivals_before task_arrivals_between
        rw [List.mem_filter]
        constructor
        · apply Prosa.Analysis.Facts.Behavior.Arrivals.arrived_between_implies_in_arrivals
            arr_seq H_arrival_times_are_consistent j 0 t2 H_j_arrives
          unfold arrived_between; constructor
          · exact Nat.zero_le _
          · exact H_busy_interval.1.1.2
        · simp [job_of_task, H_job_of_tsk]
      · exact h_int
    simp [h_not_task_sched, h_any]
  · have h_false : interference j t = false := by
      match h : interference j t with
      | true => exact absurd h h_int
      | false => rfl
    simp [h_false]

include H_busy_interval H_j_arrives H_job_of_tsk H_job_cost_positive
  H_t_in_interval H_jobs_come_from_arrival_sequence H_work_conserving
  H_inside_busy_interval H_job_j_is_not_completed H_sequential_tasks
  H_completed_jobs_dont_execute H_interference_and_workload_consistent_with_sequential_tasks_
  H_arrival_times_are_consistent H_jobs_must_arrive_to_execute in
theorem interference_plus_sched_le_serv_of_task_plus_task_interference_job
    (j' : Job) (H_sched : sched t = some j')
    (H_is_job_of_tsk : job_task j' = tsk) (H_j_neq_j' : j ≠ j') :
    (interference j t).toNat + (scheduled_at sched j t).toNat ≤
    service_of_jobs_at sched (job_of_task tsk)
      (arrivals_between arr_seq t1 (t1 + A_seq j t1 + ε)) t +
    task_interference_received_before arr_seq sched tsk interference t2 t := by
  -- scheduled_at j t = false since sched t = some j' and j ≠ j'
  have h_not_sched : scheduled_at sched j t = false := by
    rw [scheduled_at_def]; simp [H_sched, Ne.symm H_j_neq_j']
  -- interference j t = true via work_conserving
  have h_t_in : t1 ≤ t ∧ t < t2 := ⟨H_t_in_interval.1, lt_trans H_t_in_interval.2 H_inside_busy_interval⟩
  have h_wc := (H_work_conserving j t1 t2 t H_j_arrives H_job_of_tsk (H_job_cost_positive) H_busy_interval h_t_in).mp
  -- ¬interference = true → scheduled = true, contrapositive: ¬scheduled → interference = true
  have h_int : interference j t = true := by
    by_contra h_neg
    have h_not_int : ¬(interference j t = true) := h_neg
    exact absurd (h_wc h_not_int) (by rw [h_not_sched]; exact Bool.noConfusion)
  rw [h_int, h_not_sched]; simp only [Bool.toNat_true, Bool.toNat_false, Nat.add_zero]
  -- Goal: 1 ≤ service_of_jobs_at + task_interference_received_before
  suffices hsvc : service_of_jobs_at sched (job_of_task tsk)
      (arrivals_between arr_seq t1 (t1 + A_seq j t1 + ε)) t ≥ 1 by
    exact le_trans hsvc (Nat.le_add_right _ _)
  -- j' contributes to the sum
  -- j' is scheduled
  have h_sched_j' : scheduled_at sched j' t = true := by
    rw [scheduled_at_def]; simp [H_sched]
  -- j' arrives_in arr_seq
  have h_j'_arrives : arrives_in arr_seq j' :=
    H_jobs_come_from_arrival_sequence j' t h_sched_j'
  -- j' is pending
  have h_pending : pending sched j' t :=
    scheduled_implies_pending sched H_completed_jobs_dont_execute j'
      ideal_proc_model_ensures_ideal_progress H_jobs_must_arrive_to_execute t h_sched_j'
  -- j' arrives in [t1, t+1) via arrives_after_beginning_of_busy_interval
  have h_arr_between : arrived_between j' t1 (t + 1) :=
    arrives_after_beginning_of_busy_interval
      arr_seq H_arrival_times_are_consistent sched
      H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute
      H_completed_jobs_dont_execute tsk interference interfering_workload
      H_interference_and_workload_consistent_with_sequential_tasks_
      j j' H_j_arrives h_j'_arrives H_job_of_tsk H_is_job_of_tsk
      H_job_cost_positive t1 t2 H_busy_interval t H_t_in_interval.1 h_pending
  -- Now need: job_arrival j' ≤ job_arrival j (for j' ∈ arrivals_between t1 (t1 + A + ε))
  have h_arr_le : job_arrival j' ≤ job_arrival j := by
    by_contra h_gt; push_neg at h_gt
    -- j arrives before j', sequential_tasks gives j completed by t
    have h_compl := H_sequential_tasks j j' t
      (by unfold same_task; simp [H_job_of_tsk, H_is_job_of_tsk]) h_gt h_sched_j'
    -- j completed by t, so completed by t1 + x
    have h_compl_tx := completion_monotonic sched j t (t1 + x) (Nat.le_of_lt H_t_in_interval.2) h_compl
    exact H_job_j_is_not_completed h_compl_tx
  -- j' ∈ arrivals_between t1 (t1 + A_seq j t1 + ε)
  have h_j'_in : j' ∈ arrivals_between arr_seq t1 (t1 + A_seq j t1 + ε) := by
    apply Prosa.Analysis.Facts.Behavior.Arrivals.arrived_between_implies_in_arrivals
      arr_seq H_arrival_times_are_consistent j' t1 (t1 + A_seq j t1 + ε) h_j'_arrives
    unfold arrived_between; constructor
    · exact h_arr_between.1
    · have := H_busy_interval.1.1.1; unfold A_seq ε instant duration at *; omega
  -- service_of_jobs_at ≥ 1 via j'
  unfold service_of_jobs_at
  rw [ge_iff_le, ← Nat.lt_iff_add_one_le, ← Prosa.Util.Sum.sum_seq_gt0P]
  exact ⟨j', List.mem_filter.mpr ⟨h_j'_in, by simp [job_of_task, H_is_job_of_tsk]⟩,
    by rw [service_at_is_scheduled_at, h_sched_j']; simp⟩

include H_busy_interval H_j_arrives H_job_of_tsk H_job_cost_positive
  H_t_in_interval H_work_conserving H_inside_busy_interval
  H_arrival_times_are_consistent in
theorem interference_plus_sched_le_serv_of_task_plus_task_interference_j
    (H_sched : sched t = some j) :
    (interference j t).toNat + (scheduled_at sched j t).toNat ≤
    service_of_jobs_at sched (job_of_task tsk)
      (arrivals_between arr_seq t1 (t1 + A_seq j t1 + ε)) t +
    task_interference_received_before arr_seq sched tsk interference t2 t := by
  -- scheduled_at j t = true since sched t = some j
  have h_sched_j : scheduled_at sched j t = true := by
    rw [scheduled_at_def]; simp [H_sched]
  -- interference j t = false via work_conserving backward
  have h_t_in : t1 ≤ t ∧ t < t2 := ⟨H_t_in_interval.1, lt_trans H_t_in_interval.2 H_inside_busy_interval⟩
  have h_wc := (H_work_conserving j t1 t2 t H_j_arrives H_job_of_tsk (H_job_cost_positive) H_busy_interval h_t_in).mpr h_sched_j
  have h_int_false : interference j t = false := by
    match h : interference j t with
    | true => exact absurd h h_wc
    | false => rfl
  rw [h_int_false, h_sched_j]; simp only [Bool.toNat_false, Bool.toNat_true, Nat.zero_add]
  -- Goal: 1 ≤ service_of_jobs_at + task_interference_received_before
  suffices h : service_of_jobs_at sched (job_of_task tsk) (arrivals_between arr_seq t1 (t1 + A_seq j t1 + ε)) t ≥ 1 by exact le_trans h (Nat.le_add_right _ _)
  -- j contributes 1 to the sum
  have h_j_in : j ∈ arrivals_between arr_seq t1 (t1 + A_seq j t1 + ε) := by
    apply Prosa.Analysis.Facts.Behavior.Arrivals.arrived_between_implies_in_arrivals
      arr_seq H_arrival_times_are_consistent j t1 (t1 + A_seq j t1 + ε) H_j_arrives
    unfold arrived_between; constructor
    · exact H_busy_interval.1.1.1
    · have := H_busy_interval.1.1.1; unfold A_seq ε instant duration at *; omega
  unfold service_of_jobs_at
  rw [ge_iff_le, ← Nat.lt_iff_add_one_le, ← Prosa.Util.Sum.sum_seq_gt0P]
  exact ⟨j, List.mem_filter.mpr ⟨h_j_in, by simp [job_of_task, H_job_of_tsk]⟩,
    by rw [service_at_is_scheduled_at, h_sched_j]; simp⟩

include H_busy_interval H_j_arrives H_job_of_tsk H_job_cost_positive
  H_t_in_interval H_work_conserving H_inside_busy_interval
  H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_job_j_is_not_completed
  H_sequential_tasks H_completed_jobs_dont_execute
  H_interference_and_workload_consistent_with_sequential_tasks_
  H_arrival_times_are_consistent in
theorem interference_plus_sched_le_serv_of_task_plus_task_interference :
    (interference j t).toNat + (scheduled_at sched j t).toNat ≤
    service_of_jobs_at sched (job_of_task tsk)
      (arrivals_between arr_seq t1 (t1 + A_seq j t1 + ε)) t +
    task_interference_received_before arr_seq sched tsk interference t2 t := by
  match h : sched t with
  | none =>
    exact interference_plus_sched_le_serv_of_task_plus_task_interference_idle
      arr_seq H_arrival_times_are_consistent sched tsk interference interfering_workload
      j H_j_arrives H_job_of_tsk H_job_cost_positive
      t1 t2 H_busy_interval x H_inside_busy_interval t H_t_in_interval h
  | some j1 =>
    by_cases h_tsk : job_task j1 = tsk
    · by_cases h_eq : j = j1
      · subst h_eq
        exact interference_plus_sched_le_serv_of_task_plus_task_interference_j
          arr_seq H_arrival_times_are_consistent sched tsk interference interfering_workload
          H_work_conserving j H_j_arrives H_job_of_tsk H_job_cost_positive
          t1 t2 H_busy_interval x H_inside_busy_interval t H_t_in_interval h
      · exact interference_plus_sched_le_serv_of_task_plus_task_interference_job
          arr_seq H_arrival_times_are_consistent sched H_jobs_come_from_arrival_sequence
          H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute tsk interference interfering_workload
          H_work_conserving H_sequential_tasks
          H_interference_and_workload_consistent_with_sequential_tasks_
          j H_j_arrives H_job_of_tsk H_job_cost_positive
          t1 t2 H_busy_interval x H_inside_busy_interval H_job_j_is_not_completed
          t H_t_in_interval j1 h h_tsk h_eq
    · exact interference_plus_sched_le_serv_of_task_plus_task_interference_task
        arr_seq H_arrival_times_are_consistent sched H_jobs_come_from_arrival_sequence tsk interference interfering_workload
        j H_j_arrives H_job_of_tsk H_job_cost_positive
        t1 t2 H_busy_interval x t H_t_in_interval j1 h h_tsk

end CaseAnalysis

-- Helper: exchange summation order (List.sum of Finset.sum → Finset.sum of List.sum)
private theorem list_finset_sum_exchange {T : Type _} (l : List T) (s : Finset ℕ) (f : T → ℕ → ℕ) :
    (l.map (fun j => ∑ t ∈ s, f j t)).sum = ∑ t ∈ s, (l.map (fun j => f j t)).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [ih, ← Finset.sum_add_distrib]

include H_busy_interval H_j_arrives H_job_of_tsk H_job_cost_positive
  H_inside_busy_interval H_job_j_is_not_completed
  H_work_conserving H_jobs_come_from_arrival_sequence
  H_jobs_must_arrive_to_execute
  H_sequential_tasks H_completed_jobs_dont_execute
  H_interference_and_workload_consistent_with_sequential_tasks_
  H_arrival_times_are_consistent in
theorem cumul_interference_plus_sched_le_serv_of_task_plus_cumul_task_interference :
    cumul_interference interference j t1 (t1 + x) ≤
    (task_service_of_jobs_in sched tsk
      (arrivals_between arr_seq t1 (t1 + A_seq j t1 + ε)) t1 (t1 + x) -
      service_during sched j t1 (t1 + x)) +
    cumul_task_interference arr_seq sched tsk interference t2 t1 (t1 + x) := by
  -- j is in arrivals_between
  have j_in : j ∈ arrivals_between arr_seq t1 (t1 + A_seq j t1 + ε) := by
    apply Prosa.Analysis.Facts.Behavior.Arrivals.arrived_between_implies_in_arrivals
      arr_seq H_arrival_times_are_consistent j t1 (t1 + A_seq j t1 + ε) H_j_arrives
    unfold arrived_between; constructor
    · exact H_busy_interval.1.1.1
    · have := H_busy_interval.1.1.1; unfold A_seq ε instant duration at *; omega
  set jobs_filt := (arrivals_between arr_seq t1 (t1 + A_seq j t1 + ε)).filter (fun j' => job_of_task tsk j')
  -- Exchange: TSJ = ∑_t service_of_jobs_at_t
  have h_tsj_eq : task_service_of_jobs_in sched tsk
      (arrivals_between arr_seq t1 (t1 + A_seq j t1 + ε)) t1 (t1 + x) =
      ∑ t ∈ Finset.Ico t1 (t1 + x), service_of_jobs_at sched (job_of_task tsk)
        (arrivals_between arr_seq t1 (t1 + A_seq j t1 + ε)) t := by
    unfold task_service_of_jobs_in service_of_jobs service_of_jobs_at service_during
    exact list_finset_sum_exchange jobs_filt (Finset.Ico t1 (t1 + x)) (fun j t => service_at sched j t)
  -- Step 1: CI + SD ≤ TSJ + CTI (summing pointwise inequality)
  have h_sum : cumul_interference interference j t1 (t1 + x) + service_during sched j t1 (t1 + x) ≤
      task_service_of_jobs_in sched tsk (arrivals_between arr_seq t1 (t1 + A_seq j t1 + ε)) t1 (t1 + x) +
      cumul_task_interference arr_seq sched tsk interference t2 t1 (t1 + x) := by
    rw [h_tsj_eq]
    unfold cumul_interference service_during cumul_task_interference
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro t ht
    have ht_in : t1 ≤ t ∧ t < t1 + x := Finset.mem_Ico.mp ht
    have h_eq : service_at sched j t = (scheduled_at sched j t).toNat := by
      rw [service_at_is_scheduled_at]; cases scheduled_at sched j t <;> simp
    rw [h_eq]
    exact interference_plus_sched_le_serv_of_task_plus_task_interference
      arr_seq H_arrival_times_are_consistent sched H_jobs_come_from_arrival_sequence
      H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute tsk interference interfering_workload
      H_work_conserving H_sequential_tasks
      H_interference_and_workload_consistent_with_sequential_tasks_
      j H_j_arrives H_job_of_tsk H_job_cost_positive
      t1 t2 H_busy_interval x H_inside_busy_interval H_job_j_is_not_completed
      t ht_in
  -- Step 2: SD ≤ TSJ (j is one of the task's jobs)
  have h_sd_le : service_during sched j t1 (t1 + x) ≤
      task_service_of_jobs_in sched tsk (arrivals_between arr_seq t1 (t1 + A_seq j t1 + ε)) t1 (t1 + x) := by
    rw [h_tsj_eq]
    unfold service_during
    apply Finset.sum_le_sum
    intro t _
    unfold service_of_jobs_at
    have h_j_in_f : j ∈ jobs_filt :=
      List.mem_filter.mpr ⟨j_in, by simp [job_of_task, H_job_of_tsk]⟩
    exact List.le_sum_of_mem (List.mem_map.mpr ⟨j, h_j_in_f, rfl⟩)
  -- Conclude: CI ≤ (TSJ - SD) + CTI
  omega

include H_busy_interval H_j_arrives H_job_of_tsk H_job_cost_positive
  H_completed_jobs_dont_execute H_arrival_times_are_consistent
  H_jobs_must_arrive_to_execute in
theorem serv_of_task_le_workload_of_task_plus :
    task_service_of_jobs_in sched tsk
      (arrivals_between arr_seq t1 (t1 + A_seq j t1 + ε)) t1 (t1 + x) -
      service_during sched j t1 (t1 + x) +
    cumul_task_interference arr_seq sched tsk interference t2 t1 (t1 + x) ≤
    (task_workload_between arr_seq tsk t1 (t1 + A_seq j t1 + ε) - job_cost j) +
    cumul_task_interference arr_seq sched tsk interference t2 t1 (t1 + x) := by
  apply Nat.add_le_add_right
  -- Goal: TSJ - SD ≤ TWB - jc
  set jobs_arr := arrivals_between arr_seq t1 (t1 + A_seq j t1 + ε)
  set filt := jobs_arr.filter (fun j' => job_of_task tsk j')
  -- j is in the filtered list
  have j_in : j ∈ arrivals_between arr_seq t1 (t1 + A_seq j t1 + ε) := by
    apply Prosa.Analysis.Facts.Behavior.Arrivals.arrived_between_implies_in_arrivals
      arr_seq H_arrival_times_are_consistent j t1 (t1 + A_seq j t1 + ε) H_j_arrives
    unfold arrived_between; constructor
    · exact H_busy_interval.1.1.1
    · have := H_busy_interval.1.1.1; unfold A_seq ε instant duration at *; omega
  have j_in_filt : j ∈ filt :=
    List.mem_filter.mpr ⟨j_in, by simp [job_of_task, H_job_of_tsk]⟩
  -- Decompose: TSJ = SD + service_others, TWB = jc + workload_others
  have h_perm := List.perm_cons_erase j_in_filt
  -- h_perm : List.Perm filt (j :: filt.erase j)
  have h_tsj_decomp : task_service_of_jobs_in sched tsk jobs_arr t1 (t1 + x) =
      service_during sched j t1 (t1 + x) + ((filt.erase j).map (fun j' => service_during sched j' t1 (t1 + x))).sum := by
    unfold task_service_of_jobs_in service_of_jobs
    show (filt.map (fun j' => service_during sched j' t1 (t1 + x))).sum = _
    rw [(h_perm.map _).sum_eq]; simp [List.map_cons, List.sum_cons]
  have h_twb_decomp : task_workload_between arr_seq tsk t1 (t1 + A_seq j t1 + ε) =
      job_cost j + ((filt.erase j).map (fun j' => job_cost j')).sum := by
    unfold task_workload_between task_workload workload_of_jobs
    show (filt.map (fun j' => job_cost j')).sum = _
    rw [(h_perm.map _).sum_eq]; simp [List.map_cons, List.sum_cons]
  -- Service of others ≤ Workload of others (pointwise: service ≤ cost for any job)
  have h_others : ∀ (l : List Job),
      (l.map (fun j' => service_during sched j' t1 (t1 + x))).sum ≤
      (l.map (fun j' => job_cost j')).sum := by
    intro l; induction l with
    | nil => simp
    | cons a t ih =>
      simp only [List.map_cons, List.sum_cons]
      exact Nat.add_le_add
        (cumulative_service_le_job_cost sched H_completed_jobs_dont_execute a
          ideal_proc_model_provides_unit_service t1 (t1 + x)) ih
  have h_oth := h_others (filt.erase j)
  have h1 : task_service_of_jobs_in sched tsk jobs_arr t1 (t1 + x) -
      service_during sched j t1 (t1 + x) =
      ((filt.erase j).map (fun j' => service_during sched j' t1 (t1 + x))).sum := by
    rw [h_tsj_decomp, Nat.add_sub_cancel_left]
  have h2 : task_workload_between arr_seq tsk t1 (t1 + A_seq j t1 + ε) - job_cost j =
      ((filt.erase j).map (fun j' => job_cost j')).sum := by
    rw [h_twb_decomp, Nat.add_sub_cancel_left]
  rw [h1, h2]
  exact h_oth

include H_busy_interval H_j_arrives H_job_of_tsk H_job_cost_positive
  H_inside_busy_interval H_job_j_is_not_completed
  H_work_conserving H_jobs_come_from_arrival_sequence
  H_jobs_must_arrive_to_execute
  H_sequential_tasks H_completed_jobs_dont_execute
  H_interference_and_workload_consistent_with_sequential_tasks_
  H_arrival_times_are_consistent in
theorem cumulative_job_interference_le_task_interference_bound :
    cumul_interference interference j t1 (t1 + x) ≤
    (task_workload_between arr_seq tsk t1 (t1 + A_seq j t1 + ε) - job_cost j) +
    cumul_task_interference arr_seq sched tsk interference t2 t1 (t1 + x) := by
  apply le_trans
  · exact cumul_interference_plus_sched_le_serv_of_task_plus_cumul_task_interference
      arr_seq H_arrival_times_are_consistent sched H_jobs_come_from_arrival_sequence
      H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute tsk interference interfering_workload
      H_work_conserving H_sequential_tasks
      H_interference_and_workload_consistent_with_sequential_tasks_
      j H_j_arrives H_job_of_tsk H_job_cost_positive
      t1 t2 H_busy_interval x H_inside_busy_interval H_job_j_is_not_completed
  · exact serv_of_task_le_workload_of_task_plus
      arr_seq H_arrival_times_are_consistent sched
      H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute
      tsk interference interfering_workload
      j H_j_arrives H_job_of_tsk H_job_cost_positive
      t1 t2 H_busy_interval x

end TaskInterferenceBoundsInterference

include H_busy_interval H_j_arrives H_job_of_tsk
  H_valid_job_cost H_is_arrival_curve H_arrival_times_are_consistent
  H_arr_seq_is_a_set H_tsk_in_ts in
theorem task_rbf_excl_tsk_bounds_task_workload_excl_j :
    task_workload_between arr_seq tsk t1 (t1 + A_seq j t1 + ε) - job_cost j ≤
    task_request_bound_function tsk (A_seq j t1 + ε) - task_cost tsk := by
  -- Normalize association so set Aε captures all occurrences
  show task_workload_between arr_seq tsk t1 (t1 + (A_seq j t1 + ε)) - job_cost j ≤
    task_request_bound_function tsk (A_seq j t1 + ε) - task_cost tsk
  set Aε := A_seq j t1 + ε
  set jobs_arr := arrivals_between arr_seq t1 (t1 + Aε)
  set filt := jobs_arr.filter (fun j' => job_of_task tsk j')
  -- j is in the filtered list
  have j_in : j ∈ jobs_arr := by
    apply Prosa.Analysis.Facts.Behavior.Arrivals.arrived_between_implies_in_arrivals
      arr_seq H_arrival_times_are_consistent j t1 (t1 + Aε) H_j_arrives
    unfold arrived_between; constructor
    · exact H_busy_interval.1.1.1
    · have := H_busy_interval.1.1.1
      simp only [show Aε = A_seq j t1 + ε from rfl]
      unfold A_seq ε instant duration at *; omega
  have j_in_filt : j ∈ filt :=
    List.mem_filter.mpr ⟨j_in, by simp [job_of_task, H_job_of_tsk]⟩
  -- Decompose TWB = jc + remaining
  have h_perm := List.perm_cons_erase j_in_filt
  have h_twb_decomp : task_workload_between arr_seq tsk t1 (t1 + Aε) =
      job_cost j + ((filt.erase j).map (fun j' => job_cost j')).sum := by
    unfold task_workload_between task_workload workload_of_jobs
    show (filt.map (fun j' => job_cost j')).sum = _
    rw [(h_perm.map _).sum_eq]
    simp [List.map_cons, List.sum_cons]
  -- TWB - jc = remaining
  rw [show task_workload_between arr_seq tsk t1 (t1 + Aε) - job_cost j =
      ((filt.erase j).map (fun j' => job_cost j')).sum from by
    rw [h_twb_decomp, Nat.add_sub_cancel_left]]
  -- Each job in filt.erase j has cost ≤ tc
  have h_each_le : ∀ j' ∈ filt.erase j, job_cost j' ≤ task_cost tsk := by
    intro j' hj'
    have hj'_filt : j' ∈ filt := List.mem_of_mem_erase hj'
    have hj'_arr : j' ∈ jobs_arr := (List.mem_filter.mp hj'_filt).1
    have hj'_task : job_task j' = tsk := by
      have := (List.mem_filter.mp hj'_filt).2
      simp [job_of_task] at this; exact this
    have hj'_arrives : arrives_in arr_seq j' :=
      Prosa.Analysis.Facts.Behavior.Arrivals.in_arrivals_implies_arrived arr_seq H_arrival_times_are_consistent j' t1 (t1 + Aε) hj'_arr
    have hvc := H_valid_job_cost j' hj'_arrives
    simp only [valid_job_cost, hj'_task] at hvc; exact hvc
  -- Sum bound: ∀ l, (∀ j' ∈ l, cost j' ≤ tc) → sum ≤ tc * length
  have h_sum_bound : ∀ (l : List Job),
      (∀ j' ∈ l, job_cost j' ≤ task_cost tsk) →
      (l.map job_cost).sum ≤ task_cost tsk * l.length := by
    intro l hl; induction l with
    | nil => simp
    | cons a t ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.mul_succ]
      have h1 := hl a (by simp)
      have h2 := ih (fun j' hj' => hl j' (List.mem_cons_of_mem a hj'))
      rw [Nat.add_comm (task_cost tsk * t.length)]
      exact Nat.add_le_add h1 h2
  -- remaining ≤ tc * (filt.erase j).length
  have h_rem := h_sum_bound (filt.erase j) h_each_le
  -- (filt.erase j).length = filt.length - 1
  have h_len : (filt.erase j).length = filt.length - 1 :=
    List.length_erase_of_mem j_in_filt
  -- filt.length ≤ max_arrivals tsk Aε
  have h_N_le : filt.length ≤ max_arrivals tsk Aε := by
    have h_ac := H_is_arrival_curve tsk H_tsk_in_ts t1 (t1 + Aε) (Nat.le_add_right t1 Aε)
    simp only [Nat.add_sub_cancel_left] at h_ac
    -- h_ac : number_of_task_arrivals arr_seq tsk t1 (t1+Aε) ≤ max_arrivals tsk Aε
    -- filt.length = number_of_task_arrivals
    convert h_ac using 1
  -- filt.length ≥ 1 (since j ∈ filt)
  have h_ge1 : 0 < filt.length := by
    exact List.length_pos_of_mem j_in_filt
  -- max_arrivals ≥ 1
  have h_max_ge1 : 1 ≤ max_arrivals tsk Aε := le_trans h_ge1 h_N_le
  -- Chain the inequalities
  calc ((filt.erase j).map (fun j' => job_cost j')).sum
      ≤ task_cost tsk * (filt.erase j).length := h_rem
    _ = task_cost tsk * (filt.length - 1) := by rw [h_len]
    _ ≤ task_cost tsk * (max_arrivals tsk Aε - 1) := by
        apply Nat.mul_le_mul_left; omega
    _ = task_cost tsk * max_arrivals tsk Aε - task_cost tsk := by
        cases hm : max_arrivals tsk Aε with
        | zero => omega
        | succ n => simp [Nat.mul_succ, Nat.add_sub_cancel]
    _ = task_request_bound_function tsk Aε - task_cost tsk := by
        simp [task_request_bound_function]

include H_busy_interval H_j_arrives H_job_of_tsk H_job_cost_positive
  H_inside_busy_interval H_job_j_is_not_completed
  H_work_conserving H_jobs_come_from_arrival_sequence
  H_jobs_must_arrive_to_execute
  H_sequential_tasks H_completed_jobs_dont_execute
  H_interference_and_workload_consistent_with_sequential_tasks_
  H_arrival_times_are_consistent H_valid_job_cost H_is_arrival_curve
  H_task_interference_is_bounded
  H_arr_seq_is_a_set H_tsk_in_ts in
theorem cumulative_job_interference_bound :
    cumul_interference interference j t1 (t1 + x) ≤
    (task_request_bound_function tsk (A_seq j t1 + ε) - task_cost tsk) +
    cumul_task_interference arr_seq sched tsk interference t2 t1 (t1 + x) := by
  apply le_trans
  · exact cumulative_job_interference_le_task_interference_bound
      arr_seq H_arrival_times_are_consistent sched H_jobs_come_from_arrival_sequence
      H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute tsk interference interfering_workload
      H_work_conserving H_sequential_tasks
      H_interference_and_workload_consistent_with_sequential_tasks_
      j H_j_arrives H_job_of_tsk H_job_cost_positive
      t1 t2 H_busy_interval x H_inside_busy_interval H_job_j_is_not_completed
  · exact Nat.add_le_add_right
      (task_rbf_excl_tsk_bounds_task_workload_excl_j
        arr_seq H_arrival_times_are_consistent H_arr_seq_is_a_set sched H_valid_job_cost
        ts tsk H_tsk_in_ts H_is_arrival_curve interference interfering_workload
        j H_j_arrives H_job_of_tsk
        t1 t2 H_busy_interval) _

end BoundOfCumulativeJobInterference

section MaxInSeqHypothesisImpMaxInNonseqHypothesis

variable (j : Job)
variable (H_j_arrives : arrives_in arr_seq j)
variable (H_job_of_tsk : job_task j = tsk)

include H_valid_run_to_completion_threshold H_R_is_maximum_seq
  H_valid_arrival_curve H_is_arrival_curve H_tsk_in_ts
  H_arrival_times_are_consistent H_j_arrives H_job_of_tsk in
theorem max_in_seq_hypothesis_implies_max_in_nonseq_hypothesis :
    ∀ (A : duration),
      is_in_search_space tsk L
        (fun tsk' A' R' => total_interference_bound_val tsk' A' R' task_interference_bound_function) A →
      ∃ (F : duration),
        A + F = task_run_to_completion_threshold tsk +
                (task_request_bound_function tsk (A + ε) - task_cost tsk +
                  task_interference_bound_function tsk A (A + F)) ∧
        F + (task_cost tsk - task_run_to_completion_threshold tsk) ≤ R := by
  intro A INSP
  obtain ⟨F, FIX, LE⟩ := H_R_is_maximum_seq A INSP
  refine ⟨F, ?_, LE⟩
  have h_rtct_le_cost : task_run_to_completion_threshold tsk ≤ task_cost tsk :=
    H_valid_run_to_completion_threshold.1
  have hvc := H_valid_arrival_curve tsk H_tsk_in_ts
  have hic := H_is_arrival_curve tsk H_tsk_in_ts
  have h_ge_1 : task_cost tsk ≤ task_request_bound_function tsk 1 :=
    task_rbf_1_ge_task_cost arr_seq H_arrival_times_are_consistent tsk hvc hic j H_j_arrives H_job_of_tsk
  have hm := task_rbf_monotone arr_seq H_arrival_times_are_consistent tsk hvc hic
  have h_mono_applied := hm 1 (A + ε)
  simp only [Nat.ble_eq, decide_eq_true_eq] at h_mono_applied
  have h_rbf_le : task_request_bound_function tsk 1 ≤ task_request_bound_function tsk (A + ε) :=
    h_mono_applied (by unfold ε; omega)
  have h_cost_le_rbf := Nat.le_trans h_ge_1 h_rbf_le
  have h_sub_le : task_cost tsk - task_run_to_completion_threshold tsk ≤
      task_request_bound_function tsk (A + ε) :=
    Nat.le_trans (Nat.sub_le _ _) h_cost_le_rbf
  zify [h_rtct_le_cost, h_cost_le_rbf, h_sub_le] at *
  omega

end MaxInSeqHypothesisImpMaxInNonseqHypothesis

include H_arrival_times_are_consistent H_arr_seq_is_a_set
  H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute
  H_completed_jobs_dont_execute H_valid_job_cost H_tsk_in_ts
  H_valid_preemption_model H_valid_run_to_completion_threshold
  H_valid_arrival_curve H_is_arrival_curve
  H_work_conserving H_sequential_tasks
  H_interference_and_workload_consistent_with_sequential_tasks_
  H_busy_interval_exists H_task_interference_is_bounded
  H_R_is_maximum_seq in
theorem uniprocessor_response_time_bound_seq :
    task_response_time_bound arr_seq sched tsk R := by
  intro j h_j_arr h_j_tsk
  -- Construct H_job_interference_is_bounded for the total_interference_bound_val
  have h_job_bounded : job_interference_is_bounded_by arr_seq sched tsk
      interference interfering_workload
      (fun tsk' A' R' => total_interference_bound_val tsk' A' R'
          task_interference_bound_function) := by
    intro t1' t2' delta j' h_arrives h_tsk h_bi h_lt h_not_compl
    have h_pos : job_cost_positive j' := by
      by_contra h; simp only [job_cost_positive, not_lt, Nat.le_zero] at h
      exact h_not_compl (by unfold completed_by; rw [h]; exact Nat.zero_le _)
    apply le_trans
    · exact cumulative_job_interference_bound
        arr_seq H_arrival_times_are_consistent H_arr_seq_is_a_set sched
        H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute
        H_valid_job_cost ts tsk H_tsk_in_ts H_is_arrival_curve
        interference interfering_workload H_work_conserving
        H_sequential_tasks
        H_interference_and_workload_consistent_with_sequential_tasks_
        task_interference_bound_function H_task_interference_is_bounded
        j' h_arrives h_tsk h_pos t1' t2' h_bi delta h_lt h_not_compl
    · exact Nat.add_le_add_left
        (H_task_interference_is_bounded j' delta t1' t2'
          h_arrives h_tsk h_lt h_not_compl h_bi) _
  -- Construct H_R_is_maximum using job j
  have h_R_max : ∀ A, is_in_search_space tsk L
      (fun tsk' A' R' => total_interference_bound_val tsk' A' R'
          task_interference_bound_function) A →
      ∃ F, A + F = task_run_to_completion_threshold tsk +
          ((fun tsk' A' R' => total_interference_bound_val tsk' A' R'
              task_interference_bound_function) tsk A (A + F)) ∧
          F + (task_cost tsk - task_run_to_completion_threshold tsk) ≤ R :=
    max_in_seq_hypothesis_implies_max_in_nonseq_hypothesis
      arr_seq H_arrival_times_are_consistent
      ts tsk H_tsk_in_ts H_valid_run_to_completion_threshold
      H_valid_arrival_curve H_is_arrival_curve
      L task_interference_bound_function R H_R_is_maximum_seq
      j h_j_arr h_j_tsk
  -- Apply the main abstract RTA theorem
  exact Prosa.Analysis.Abstract.Abstract_rta.uniprocessor_response_time_bound
    arr_seq H_arrival_times_are_consistent sched
    H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute
    H_valid_job_cost tsk H_valid_preemption_model
    H_valid_run_to_completion_threshold interference interfering_workload
    H_work_conserving L H_busy_interval_exists
    (fun tsk' A' R' => total_interference_bound_val tsk' A' R'
        task_interference_bound_function)
    h_job_bounded R h_R_max j h_j_arr h_j_tsk

end ResponseTimeBound

end Sequential_Abstract_RTA

end Prosa.Analysis.Abstract.Abstract_seq_rta
