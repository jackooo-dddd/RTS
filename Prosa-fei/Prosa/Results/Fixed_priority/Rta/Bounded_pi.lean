-- Translated from: ../rt-proofs/results/fixed_priority/rta/bounded_pi.v
import Prosa.Model.Schedule.Priority_driven
import Prosa.Analysis.Facts.Busy_interval.Busy_interval
import Prosa.Analysis.Abstract.Ideal_jlfp_rta
import Prosa.Model.Processor.Ideal
import Prosa.Model.Readiness.Basic
import Prosa.Model.Task.Arrival.Curves

namespace Prosa.Results.Fixed_priority.Rta.Bounded_pi

open Prosa.Behavior.Job
open Prosa.Behavior.Time
open Prosa.Behavior.Schedule
open Prosa.Behavior.Service
open Prosa.Behavior.Arrival_sequence
open Prosa.Behavior.Ready
open Prosa.Model.Task.Concept
open Prosa.Model.Task.Sequentiality
open Prosa.Model.Processor.Ideal
open Prosa.Model.Priority.Classes
open Prosa.Model.Preemption.Parameter
open Prosa.Model.Task.Preemption.Parameters
open Prosa.Model.Task.Arrivals
open Prosa.Model.Task.Arrival.Curves
open Prosa.Model.Aggregate.Workload
open Prosa.Model.Aggregate.Service_of_jobs
open Prosa.Analysis.Definitions.Priority_inversion
open Prosa.Analysis.Definitions.Job_properties
open Prosa.Analysis.Definitions.Task_schedule
open Prosa.Analysis.Definitions.Schedulability
open Prosa.Analysis.Definitions.Request_bound_function
open Prosa.Analysis.Definitions.Busy_interval
open Prosa.Analysis.Abstract.Search_space
open Prosa.Analysis.Facts.Behavior.Completion
open Prosa.Analysis.Facts.Busy_interval.Busy_interval
open Prosa.Model.Schedule.Work_conserving
open Prosa.Util.Epsilon

section AbstractRTAforFPwithArrivalCurves

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

variable [FP_policy Task]

set_option synthInstance.checkSynthOrder false in
noncomputable local instance : JLFP_policy Job := FP_to_JLFP Job Task
set_option synthInstance.checkSynthOrder false in
noncomputable local instance : JLDP_policy Job := JLFP_to_JLDP Job

noncomputable def work_conserving_ab (tsk : Task) :=
  Prosa.Analysis.Abstract.Definitions.work_conserving arr_seq sched tsk
    (Prosa.Analysis.Abstract.Ideal_jlfp_rta.interference sched)
    (Prosa.Analysis.Abstract.Ideal_jlfp_rta.interfering_workload arr_seq sched)

noncomputable def work_conserving_cl :=
  work_conserving arr_seq sched

variable (H_work_conserving : work_conserving arr_seq sched)

variable (H_sequential_tasks : sequential_tasks (Job := Job) (Task := Task) sched)

variable (H_valid_job_cost : arrivals_have_valid_job_costs (Task := Task) arr_seq)

variable (ts : List Task)

variable (H_all_jobs_from_taskset : all_jobs_from_taskset arr_seq ts)

variable [MaxArrivals Task]
variable (H_valid_arrival_curve : valid_taskset_arrival_curve ts max_arrivals)
variable (H_is_arrival_curve : taskset_respects_max_arrivals arr_seq ts)

variable (tsk : Task)
variable (H_tsk_in_ts : tsk ∈ ts)

variable (H_valid_preemption_model : valid_preemption_model arr_seq sched)

variable (H_valid_run_to_completion_threshold :
  valid_task_run_to_completion_threshold arr_seq tsk)

variable (H_priority_is_reflexive : reflexive_priorities (Job := Job))
variable (H_priority_is_transitive : transitive_priorities (Job := Job))

variable (priority_inversion_bound : duration)
variable (H_priority_inversion_is_bounded :
  priority_inversion_is_bounded_by arr_seq sched tsk priority_inversion_bound)

variable (L : duration)
variable (H_L_positive : L > 0)
variable (H_fixed_point : L = priority_inversion_bound + total_hep_request_bound_function_FP ts tsk L)

variable (R : duration)
variable (H_R_is_maximum :
  ∀ (A : duration),
    (A < L) && (task_request_bound_function tsk A != task_request_bound_function tsk (A + ε)) = true →
    ∃ (F : duration),
      A + F = priority_inversion_bound
              + (task_request_bound_function tsk (A + ε) - (task_cost tsk - task_run_to_completion_threshold tsk))
              + total_ohep_request_bound_function_FP ts tsk (A + F) ∧
      F + (task_cost tsk - task_run_to_completion_threshold tsk) ≤ R)

section FillingOutHypothesesOfAbstractRTATheorem

include H_arrival_times_are_consistent H_arr_seq_is_a_set
  H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute
  H_completed_jobs_dont_execute H_work_conserving H_sequential_tasks
  H_priority_is_reflexive H_priority_is_transitive in
theorem instantiated_i_and_w_are_consistent_with_schedule :
    Prosa.Analysis.Abstract.Definitions.work_conserving arr_seq sched tsk
      (Prosa.Analysis.Abstract.Ideal_jlfp_rta.interference sched)
      (Prosa.Analysis.Abstract.Ideal_jlfp_rta.interfering_workload arr_seq sched) := by
  intro j t1 t2 t ARRj TSKj POSj ABI ⟨HLE, HLT⟩
  have h_fp_seq : Prosa.Model.Priority.Classes.policy_respects_sequential_tasks (Task := Task) (Job := Job) := by
    intro j1 j2 hSame _
    show hep_task (job_task (Task := Task) j1) (job_task j2) = true
    rw [hSame]; exact H_priority_is_reflexive 0 j2
  -- Convert abstract BI to concrete BI for not_quiet_implies_not_idle
  have h_cbi := (Prosa.Analysis.Abstract.Ideal_jlfp_rta.instantiated_busy_interval_equivalent_edf_busy_interval
    arr_seq H_arrival_times_are_consistent H_arr_seq_is_a_set sched
    H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute
    H_completed_jobs_dont_execute H_sequential_tasks
    H_priority_is_reflexive H_priority_is_transitive h_fp_seq
    j ARRj t1 t2).mpr ABI
  have h_job_task : Prosa.Model.Task.Concept.job_of_task tsk j = true := by
    simp [Prosa.Model.Task.Concept.job_of_task, TSKj]
  -- Processor not idle within concrete busy interval
  have h_not_idle : ¬ Prosa.Model.Processor.Ideal.is_idle sched t :=
    Prosa.Analysis.Facts.Busy_interval.Busy_interval.not_quiet_implies_not_idle
      arr_seq H_arrival_times_are_consistent sched
      H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute
      H_completed_jobs_dont_execute tsk j ARRj h_job_task POSj
      H_work_conserving H_priority_is_reflexive H_priority_is_transitive
      t1 t2 h_cbi.1 t ⟨HLE, HLT⟩
  -- Derive sched t = some jhp
  have h_not_none : sched t ≠ none := by
    intro h_eq; exact h_not_idle h_eq
  obtain ⟨jhp, h_sched_eq⟩ := Option.ne_none_iff_exists'.mp h_not_none
  -- Helper: interference unfolds to is_PI || is_another_hep
  -- With sched t = some jhp, these depend on hep_job jhp j
  have h_interf_eq : Prosa.Analysis.Abstract.Ideal_jlfp_rta.interference sched j t =
      (!hep_job jhp j || (hep_job jhp j && (jhp != j))) := by
    unfold Prosa.Analysis.Abstract.Ideal_jlfp_rta.interference
      Prosa.Analysis.Definitions.Priority_inversion.is_priority_inversion
      Prosa.Analysis.Abstract.Ideal_jlfp_rta.is_interference_from_another_hep_job
    rw [h_sched_eq]; rfl
  constructor
  · -- Forward: ¬ interference → scheduled
    intro NINT
    by_cases hjhp : jhp = j
    · -- jhp = j → scheduled
      subst hjhp
      rw [Prosa.Analysis.Facts.Model.Ideal_schedule.scheduled_at_def]
      simp [h_sched_eq]
    · -- jhp ≠ j → interference, contradicting NINT
      exfalso; apply NINT
      rw [h_interf_eq]
      have h_bne : (jhp != j) = true := by simp [bne_iff_ne, hjhp]
      cases h_hep : hep_job jhp j <;> simp [h_bne]
  · -- Backward: scheduled → ¬ interference
    intro SCHED
    have hjhp_eq : jhp = j := by
      rw [Prosa.Analysis.Facts.Model.Ideal_schedule.scheduled_at_def] at SCHED
      have h := of_decide_eq_true SCHED
      exact Option.some.inj (h_sched_eq.symm.trans h)
    rw [h_interf_eq, hjhp_eq]
    have h1 : hep_job j j = true := by
      show hep_job_at 0 j j = true
      exact H_priority_is_reflexive 0 j
    have h2 : (j != j) = false := bne_self_eq_false j
    rw [h1, h2, Bool.and_false, Bool.not_true, Bool.false_or]
    exact Bool.false_ne_true

include H_arrival_times_are_consistent H_arr_seq_is_a_set
  H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute
  H_completed_jobs_dont_execute H_sequential_tasks
  H_priority_is_reflexive H_priority_is_transitive in
theorem instantiated_interference_and_workload_consistent_with_sequential_tasks :
    Prosa.Analysis.Abstract.Abstract_seq_rta.interference_and_workload_consistent_with_sequential_tasks
      arr_seq sched tsk
      (Prosa.Analysis.Abstract.Ideal_jlfp_rta.interference sched)
      (Prosa.Analysis.Abstract.Ideal_jlfp_rta.interfering_workload arr_seq sched) := by
  intro j t1 t2 ARR TSK POS BUSY
  simp only [task_workload_between, task_workload, task_service_of_jobs_in]
  apply (Prosa.Analysis.Facts.Model.Service_of_jobs.all_jobs_have_completed_equiv_workload_eq_service
    arr_seq H_arrival_times_are_consistent sched H_jobs_come_from_arrival_sequence
    H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute
    (job_of_task tsk) 0 t1 t1).mp
  intro s ARRs TSKs
  -- s is a job of task tsk that arrived in [0, t1)
  -- Need: completed_by sched s t1
  -- Strategy: abstract quiet_time at t1 → concrete quiet_time → s completed
  have h_s_arrives : arrives_in arr_seq s :=
    Prosa.Analysis.Facts.Behavior.Arrivals.in_arrivals_implies_arrived
      arr_seq H_arrival_times_are_consistent s 0 t1 ARRs
  have h_s_before : arrived_before s t1 :=
    (Prosa.Analysis.Facts.Behavior.Arrivals.in_arrivals_implies_arrived_between
      arr_seq H_arrival_times_are_consistent s 0 t1 ARRs).2
  -- s is hep to j (same task, reflexive priority)
  have h_job_task_s : job_task (Task := Task) s = tsk := by
    simp [Prosa.Model.Task.Concept.job_of_task] at TSKs; exact TSKs
  have h_hep : hep_job s j = true := by
    change hep_task (job_task (Task := Task) s) (job_task j) = true
    rw [h_job_task_s, TSK]
    -- goal: hep_task tsk tsk = true
    have h := H_priority_is_reflexive 0 j
    change hep_task (job_task (Task := Task) j) (job_task j) = true at h
    rw [TSK] at h
    exact h
  -- Get abstract quiet time at t1 from abstract busy interval
  have h_aqt := BUSY.1.2.1
  -- Convert to concrete quiet time using bridge
  have h_fp_seq : Prosa.Model.Priority.Classes.policy_respects_sequential_tasks (Task := Task) (Job := Job) := by
    intro j1 j2 hSame _
    show hep_task (job_task (Task := Task) j1) (job_task j2) = true
    rw [hSame]; exact H_priority_is_reflexive 0 j2
  have h_cqt := Prosa.Analysis.Abstract.Ideal_jlfp_rta.quiet_time_ab_implies_quiet_time_cl
    arr_seq H_arrival_times_are_consistent H_arr_seq_is_a_set sched
    H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute
    H_completed_jobs_dont_execute H_sequential_tasks
    H_priority_is_reflexive H_priority_is_transitive h_fp_seq
    j t1 h_aqt
  -- Apply concrete quiet time: all hep jobs arrived before t1 are completed
  exact h_cqt s h_s_arrives h_hep h_s_before

include H_arrival_times_are_consistent H_arr_seq_is_a_set
  H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute
  H_completed_jobs_dont_execute H_work_conserving H_sequential_tasks
  H_valid_job_cost H_all_jobs_from_taskset
  H_valid_arrival_curve H_is_arrival_curve
  H_tsk_in_ts
  H_priority_is_reflexive H_priority_is_transitive
  H_priority_inversion_is_bounded
  H_L_positive H_fixed_point in
theorem instantiated_busy_intervals_are_bounded :
    Prosa.Analysis.Abstract.Definitions.busy_intervals_are_bounded_by arr_seq sched tsk
      (Prosa.Analysis.Abstract.Ideal_jlfp_rta.interference sched)
      (Prosa.Analysis.Abstract.Ideal_jlfp_rta.interfering_workload arr_seq sched) L := by
  intro j ARR TSK POS
  -- Get per-job PI bound from task-level bound
  have h_pi_job : Prosa.Analysis.Definitions.Priority_inversion.priority_inversion_of_job_is_bounded_by
      arr_seq sched j priority_inversion_bound :=
    H_priority_inversion_is_bounded j ARR TSK POS
  -- Build workload bound: ∀ t, pi_bound + workload_of_hep_jobs(arrivals in [t, t+L)) ≤ L
  have h_wl_bound : ∀ t,
      priority_inversion_bound +
        workload_of_higher_or_equal_priority_jobs j (arrivals_between arr_seq t (t + L)) ≤ L := by
    intro t
    have h_wl_le_rbf := Prosa.Analysis.Facts.Model.Rbf.total_workload_le_total_rbf'
      arr_seq H_arrival_times_are_consistent H_arr_seq_is_a_set sched
      H_jobs_come_from_arrival_sequence ts tsk H_tsk_in_ts
      H_valid_job_cost H_all_jobs_from_taskset H_is_arrival_curve
      j ARR TSK t L
    -- h_wl_le_rbf : workload_of_jobs (hep_job · j) (arrivals in [t, t+L)) ≤ total_hep_rbf L
    -- Need: pi + workload ≤ L = pi + total_hep_rbf L
    calc priority_inversion_bound + workload_of_higher_or_equal_priority_jobs j (arrivals_between arr_seq t (t + L))
        ≤ priority_inversion_bound + total_hep_request_bound_function_FP ts tsk L := by
          exact Nat.add_le_add_left h_wl_le_rbf _
      _ = L := H_fixed_point.symm
  -- job_of_task predicate
  have h_job_task : Prosa.Model.Task.Concept.job_of_task tsk j = true := by
    simp [Prosa.Model.Task.Concept.job_of_task, TSK]
  -- Apply exists_busy_interval → get concrete busy interval
  have h_concrete := Prosa.Analysis.Facts.Busy_interval.Busy_interval.exists_busy_interval
    arr_seq H_arrival_times_are_consistent sched
    H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute
    H_completed_jobs_dont_execute tsk j ARR h_job_task POS
    H_work_conserving H_arr_seq_is_a_set
    H_priority_is_reflexive H_priority_is_transitive
    priority_inversion_bound h_pi_job L H_L_positive h_wl_bound POS
  obtain ⟨t1, t2, h_le_arr, h_arr_lt, h_bound, h_cbi⟩ := h_concrete
  -- Convert concrete BI to abstract BI via bridge lemma
  have h_fp_seq : Prosa.Model.Priority.Classes.policy_respects_sequential_tasks (Task := Task) (Job := Job) := by
    intro j1 j2 hSame _
    show hep_task (job_task (Task := Task) j1) (job_task j2) = true
    rw [hSame]
    exact H_priority_is_reflexive 0 j2
  have h_abi := (Prosa.Analysis.Abstract.Ideal_jlfp_rta.instantiated_busy_interval_equivalent_edf_busy_interval
    arr_seq H_arrival_times_are_consistent H_arr_seq_is_a_set sched
    H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute
    H_completed_jobs_dont_execute H_sequential_tasks
    H_priority_is_reflexive H_priority_is_transitive h_fp_seq
    j ARR t1 t2).mp h_cbi
  exact ⟨t1, t2, ⟨h_le_arr, h_arr_lt⟩, h_bound, h_abi⟩

include H_arrival_times_are_consistent H_arr_seq_is_a_set
  H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute
  H_completed_jobs_dont_execute H_work_conserving H_sequential_tasks
  H_valid_job_cost H_all_jobs_from_taskset
  H_valid_arrival_curve H_is_arrival_curve
  H_tsk_in_ts
  H_priority_is_reflexive H_priority_is_transitive
  H_priority_inversion_is_bounded in
theorem instantiated_task_interference_is_bounded :
    Prosa.Analysis.Abstract.Abstract_seq_rta.task_interference_is_bounded_by
      arr_seq sched tsk
      (Prosa.Analysis.Abstract.Ideal_jlfp_rta.interference sched)
      (Prosa.Analysis.Abstract.Ideal_jlfp_rta.interfering_workload arr_seq sched)
      (fun _ _ R => priority_inversion_bound + total_ohep_request_bound_function_FP ts tsk R) := by
  intro j R₀ t1 t2 ARR TSK HLT NCOMPL BUSY
  -- Step 1: Get job_cost j > 0 from NCOMPL
  have POS : job_cost j > 0 := by
    by_contra h; push_neg at h; apply NCOMPL
    unfold completed_by
    have : job_cost j = 0 := Nat.eq_zero_of_le_zero h
    rw [this]; exact Nat.zero_le _
  -- Step 2: Get concrete busy interval via bridge lemma
  have h_fp_seq : Prosa.Model.Priority.Classes.policy_respects_sequential_tasks (Task := Task) (Job := Job) := by
    intro j1 j2 hSame _
    show hep_task (job_task (Task := Task) j1) (job_task j2) = true
    rw [hSame]; exact H_priority_is_reflexive 0 j2
  have h_cbi : Prosa.Analysis.Definitions.Busy_interval.busy_interval arr_seq sched j t1 t2 :=
    (Prosa.Analysis.Abstract.Ideal_jlfp_rta.instantiated_busy_interval_equivalent_edf_busy_interval
      arr_seq H_arrival_times_are_consistent H_arr_seq_is_a_set sched
      H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute
      H_completed_jobs_dont_execute H_sequential_tasks
      H_priority_is_reflexive H_priority_is_transitive h_fp_seq j ARR t1 t2).mpr BUSY
  -- Step 3: Bound priority inversion via monotonicity + H_priority_inversion_is_bounded
  have h_pi_bound : Prosa.Analysis.Abstract.Ideal_jlfp_rta.cumulative_priority_inversion sched j t1 (t1 + R₀) ≤
      priority_inversion_bound := by
    have h_bip := h_cbi.1  -- concrete busy_interval_prefix for [t1, t2)
    have h_pi_full := H_priority_inversion_is_bounded j ARR TSK POS t1 t2 h_bip
    exact le_trans (by
      unfold Prosa.Analysis.Abstract.Ideal_jlfp_rta.cumulative_priority_inversion
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · exact Finset.Ico_subset_Ico_right (Nat.le_of_lt HLT)
      · intro _ _ _; exact Nat.zero_le _) h_pi_full
  -- Step 4: Task interference decomposition (equality from cumulative_task_interference_split)
  have h_arr_before : j ∈ Prosa.Behavior.Arrival_sequence.arrivals_before arr_seq t2 :=
    Prosa.Analysis.Facts.Behavior.Arrivals.arrived_between_implies_in_arrivals
      arr_seq H_arrival_times_are_consistent j 0 t2 ARR ⟨Nat.zero_le _, BUSY.1.1.2⟩
  have h_decomp : Prosa.Analysis.Abstract.Abstract_seq_rta.cumul_task_interference
      arr_seq sched tsk (Prosa.Analysis.Abstract.Ideal_jlfp_rta.interference sched) t2 t1 (t1 + R₀) =
      Prosa.Analysis.Abstract.Ideal_jlfp_rta.cumulative_priority_inversion sched j t1 (t1 + R₀) +
      Prosa.Analysis.Abstract.Ideal_jlfp_rta.cumulative_interference_from_hep_jobs_from_other_tasks
        (Task := Task) sched j t1 (t1 + R₀) :=
    Prosa.Analysis.Abstract.Ideal_jlfp_rta.cumulative_task_interference_split
      arr_seq H_arrival_times_are_consistent H_arr_seq_is_a_set sched
      H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute
      H_completed_jobs_dont_execute H_sequential_tasks
      H_priority_is_reflexive H_priority_is_transitive h_fp_seq
      tsk j t1 (t1 + R₀) t2 TSK h_arr_before NCOMPL
  -- Step 4b: Bound other-task interference
  have h_qt1 : Prosa.Analysis.Definitions.Busy_interval.quiet_time arr_seq sched j t1 :=
    h_cbi.1.2.1
  have h_interf_eq := Prosa.Analysis.Abstract.Ideal_jlfp_rta.instantiated_cumulative_interference_of_hep_tasks_equal_total_interference_of_hep_tasks (Task := Task)
    arr_seq H_arrival_times_are_consistent H_arr_seq_is_a_set sched
    H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute
    H_completed_jobs_dont_execute j t1 (t1 + R₀) h_qt1
  have h_other_bound : Prosa.Analysis.Abstract.Ideal_jlfp_rta.cumulative_interference_from_hep_jobs_from_other_tasks
      (Task := Task) sched j t1 (t1 + R₀) ≤
      total_ohep_request_bound_function_FP ts tsk R₀ := by
    rw [h_interf_eq]
    -- Goal: service_of_hep_jobs_from_other_tasks ≤ total_ohep_rbf
    -- service ≤ workload ≤ total_ohep_rbf
    calc _ ≤ Prosa.Model.Aggregate.Workload.workload_of_jobs
              (fun jhp => hep_job jhp j && (job_task (Task := Task) jhp != job_task j))
              (Prosa.Behavior.Arrival_sequence.arrivals_between arr_seq t1 (t1 + R₀)) := by
            apply Prosa.Analysis.Facts.Model.Service_of_jobs.service_of_jobs_le_workload
              arr_seq H_arrival_times_are_consistent sched
              H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute
              _ _ Prosa.Analysis.Facts.Model.Ideal_schedule.ideal_proc_model_provides_unit_service
         _ ≤ total_ohep_request_bound_function_FP ts tsk R₀ := by
            exact Prosa.Analysis.Facts.Model.Rbf.total_workload_le_total_rbf
              arr_seq H_arrival_times_are_consistent H_arr_seq_is_a_set sched
              H_jobs_come_from_arrival_sequence ts tsk H_tsk_in_ts
              H_valid_job_cost H_all_jobs_from_taskset H_is_arrival_curve
              j ARR TSK t1 R₀
  -- Step 5: Combine bounds
  calc Prosa.Analysis.Abstract.Abstract_seq_rta.cumul_task_interference
        arr_seq sched tsk (Prosa.Analysis.Abstract.Ideal_jlfp_rta.interference sched) t2 t1 (t1 + R₀)
      = Prosa.Analysis.Abstract.Ideal_jlfp_rta.cumulative_priority_inversion sched j t1 (t1 + R₀) +
        Prosa.Analysis.Abstract.Ideal_jlfp_rta.cumulative_interference_from_hep_jobs_from_other_tasks
          (Task := Task) sched j t1 (t1 + R₀) := h_decomp
    _ ≤ priority_inversion_bound + total_ohep_request_bound_function_FP ts tsk R₀ :=
        Nat.add_le_add h_pi_bound h_other_bound

section SolutionOfResponseTimeRecurrenceExists

variable (j : Job)
variable (H_j_arrives : arrives_in arr_seq j)
variable (H_job_of_tsk : job_task j = tsk)
variable (H_job_cost_positive : job_cost_positive j)

variable (A : duration)
variable (H_A_is_in_abstract_search_space :
  Prosa.Analysis.Abstract.Search_space.is_in_search_space tsk L
    (fun t A R => task_request_bound_function t (A + ε) - task_cost t
                  + (priority_inversion_bound + total_ohep_request_bound_function_FP ts tsk R)) A)

include H_j_arrives H_job_of_tsk H_job_cost_positive
  H_valid_job_cost H_valid_arrival_curve H_is_arrival_curve
  H_tsk_in_ts H_A_is_in_abstract_search_space H_L_positive
  H_arrival_times_are_consistent in
theorem A_is_in_concrete_search_space :
    (A < L) && (task_request_bound_function tsk A != task_request_bound_function tsk (A + ε)) = true := by
  rcases H_A_is_in_abstract_search_space with INSP | ⟨⟨POSA, LTL⟩, x, LTx, INSP2⟩
  · -- Case 1: A = 0
    subst INSP
    simp only [Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq]
    constructor
    · exact H_L_positive
    · -- task_rbf 0 ≠ task_rbf ε
      have h0 : task_request_bound_function tsk 0 = 0 :=
        Prosa.Analysis.Facts.Model.Rbf.task_rbf_0_zero arr_seq H_arrival_times_are_consistent tsk
          (H_valid_arrival_curve tsk H_tsk_in_ts) (H_is_arrival_curve tsk H_tsk_in_ts)
      have h1 : task_request_bound_function tsk 1 ≥ task_cost tsk :=
        Prosa.Analysis.Facts.Model.Rbf.task_rbf_1_ge_task_cost arr_seq H_arrival_times_are_consistent tsk
          (H_valid_arrival_curve tsk H_tsk_in_ts) (H_is_arrival_curve tsk H_tsk_in_ts)
          j H_j_arrives H_job_of_tsk
      have hvc : job_cost j ≤ task_cost tsk := by
        have := H_valid_job_cost j H_j_arrives
        simp [valid_job_cost, H_job_of_tsk] at this
        exact this
      have hjcp : job_cost j > 0 := H_job_cost_positive
      intro heq
      have h2 : task_request_bound_function tsk ε ≥ task_cost tsk := by
        show task_request_bound_function tsk 1 ≥ task_cost tsk
        exact h1
      have h3 : task_request_bound_function tsk 0 = task_request_bound_function tsk ε := heq
      rw [h0] at h3
      have hrbf0 : task_request_bound_function tsk ε = 0 := h3.symm
      rw [hrbf0] at h2
      have hcost0 : task_cost tsk = 0 := Nat.le_antisymm h2 (Nat.zero_le _)
      rw [hcost0] at hvc
      have hjc0 : job_cost j = 0 := Nat.le_antisymm hvc (Nat.zero_le _)
      rw [hjc0] at hjcp
      exact absurd hjcp (lt_irrefl 0)
  · -- Case 2: A > 0 ∧ A < L, ∃ x, ibf different
    simp only [Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq]
    constructor
    · exact LTL
    · -- Show task_rbf A ≠ task_rbf (A + ε) by contradiction
      intro EQ
      apply INSP2
      -- Need: ibf tsk (A - ε) x = ibf tsk A x
      show (fun t A_1 R =>
        task_request_bound_function t (A_1 + ε) - task_cost t +
          (priority_inversion_bound + total_ohep_request_bound_function_FP ts tsk R)) tsk (A - ε) x =
        (fun t A_1 R =>
          task_request_bound_function t (A_1 + ε) - task_cost t +
            (priority_inversion_bound + total_ohep_request_bound_function_FP ts tsk R)) tsk A x
      simp only
      have hAε : A - ε + ε = A := Nat.sub_add_cancel POSA
      rw [hAε, EQ]

include H_j_arrives H_job_of_tsk H_job_cost_positive
  H_valid_job_cost H_valid_arrival_curve H_is_arrival_curve
  H_tsk_in_ts H_A_is_in_abstract_search_space H_R_is_maximum H_L_positive
  H_arrival_times_are_consistent in
theorem correct_search_space :
    ∃ (F : duration),
      A + F = task_request_bound_function tsk (A + ε)
              - (task_cost tsk - task_run_to_completion_threshold tsk)
              + (priority_inversion_bound + total_ohep_request_bound_function_FP ts tsk (A + F)) ∧
      F + (task_cost tsk - task_run_to_completion_threshold tsk) ≤ R := by
  have hCSS : (A < L) && (task_request_bound_function tsk A != task_request_bound_function tsk (A + ε)) = true :=
    A_is_in_concrete_search_space arr_seq H_arrival_times_are_consistent
      H_valid_job_cost ts H_valid_arrival_curve H_is_arrival_curve tsk H_tsk_in_ts
      priority_inversion_bound L H_L_positive j H_j_arrives H_job_of_tsk H_job_cost_positive
      A H_A_is_in_abstract_search_space
  have FIX := H_R_is_maximum A hCSS
  obtain ⟨F, hFIX, hNEQ⟩ := FIX
  refine ⟨F, ?_, hNEQ⟩
  rw [Nat.add_comm priority_inversion_bound, Nat.add_assoc] at hFIX
  exact hFIX

end SolutionOfResponseTimeRecurrenceExists

end FillingOutHypothesesOfAbstractRTATheorem

include H_arrival_times_are_consistent H_arr_seq_is_a_set
  H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute
  H_completed_jobs_dont_execute H_work_conserving H_sequential_tasks
  H_valid_job_cost H_all_jobs_from_taskset
  H_valid_arrival_curve H_is_arrival_curve
  H_tsk_in_ts H_valid_preemption_model
  H_valid_run_to_completion_threshold H_priority_is_reflexive
  H_priority_is_transitive
  H_priority_inversion_is_bounded
  H_L_positive H_fixed_point H_R_is_maximum in
theorem uniprocessor_response_time_bound_fp :
    task_response_time_bound arr_seq sched tsk R := by
  intro js ARRs TSKs
  by_cases POS : job_cost js > 0
  · have h_wc : Prosa.Analysis.Abstract.Definitions.work_conserving arr_seq sched tsk
        (Prosa.Analysis.Abstract.Ideal_jlfp_rta.interference sched)
        (Prosa.Analysis.Abstract.Ideal_jlfp_rta.interfering_workload arr_seq sched) :=
      instantiated_i_and_w_are_consistent_with_schedule
        arr_seq H_arrival_times_are_consistent H_arr_seq_is_a_set sched
        H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute
        H_completed_jobs_dont_execute H_work_conserving H_sequential_tasks
        tsk H_priority_is_reflexive H_priority_is_transitive
    have h_seq : Prosa.Analysis.Abstract.Abstract_seq_rta.interference_and_workload_consistent_with_sequential_tasks
        arr_seq sched tsk
        (Prosa.Analysis.Abstract.Ideal_jlfp_rta.interference sched)
        (Prosa.Analysis.Abstract.Ideal_jlfp_rta.interfering_workload arr_seq sched) :=
      instantiated_interference_and_workload_consistent_with_sequential_tasks
        arr_seq H_arrival_times_are_consistent H_arr_seq_is_a_set sched
        H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute
        H_completed_jobs_dont_execute H_sequential_tasks
        tsk H_priority_is_reflexive H_priority_is_transitive
    have h_busy : Prosa.Analysis.Abstract.Definitions.busy_intervals_are_bounded_by arr_seq sched tsk
        (Prosa.Analysis.Abstract.Ideal_jlfp_rta.interference sched)
        (Prosa.Analysis.Abstract.Ideal_jlfp_rta.interfering_workload arr_seq sched) L :=
      instantiated_busy_intervals_are_bounded
        arr_seq H_arrival_times_are_consistent H_arr_seq_is_a_set sched
        H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute
        H_completed_jobs_dont_execute H_work_conserving H_sequential_tasks
        H_valid_job_cost ts H_all_jobs_from_taskset H_valid_arrival_curve
        H_is_arrival_curve tsk H_tsk_in_ts
        H_priority_is_reflexive H_priority_is_transitive
        priority_inversion_bound H_priority_inversion_is_bounded
        L H_L_positive H_fixed_point
    have h_tib : Prosa.Analysis.Abstract.Abstract_seq_rta.task_interference_is_bounded_by
        arr_seq sched tsk
        (Prosa.Analysis.Abstract.Ideal_jlfp_rta.interference sched)
        (Prosa.Analysis.Abstract.Ideal_jlfp_rta.interfering_workload arr_seq sched)
        (fun _ _ R₀ => priority_inversion_bound + total_ohep_request_bound_function_FP ts tsk R₀) :=
      instantiated_task_interference_is_bounded
        arr_seq H_arrival_times_are_consistent H_arr_seq_is_a_set sched
        H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute
        H_completed_jobs_dont_execute H_work_conserving H_sequential_tasks
        H_valid_job_cost ts H_all_jobs_from_taskset H_valid_arrival_curve
        H_is_arrival_curve tsk H_tsk_in_ts H_priority_is_reflexive H_priority_is_transitive
        priority_inversion_bound H_priority_inversion_is_bounded
    exact Prosa.Analysis.Abstract.Abstract_seq_rta.uniprocessor_response_time_bound_seq
      arr_seq H_arrival_times_are_consistent H_arr_seq_is_a_set sched
      H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute
      H_completed_jobs_dont_execute H_valid_job_cost ts tsk H_tsk_in_ts
      H_valid_preemption_model H_valid_run_to_completion_threshold
      H_valid_arrival_curve H_is_arrival_curve
      (Prosa.Analysis.Abstract.Ideal_jlfp_rta.interference sched)
      (Prosa.Analysis.Abstract.Ideal_jlfp_rta.interfering_workload arr_seq sched)
      h_wc H_sequential_tasks h_seq L h_busy
      (fun _ _ R₀ => priority_inversion_bound + total_ohep_request_bound_function_FP ts tsk R₀)
      h_tib R
      (fun A INSP => correct_search_space
        arr_seq H_arrival_times_are_consistent H_valid_job_cost ts
        H_valid_arrival_curve H_is_arrival_curve tsk H_tsk_in_ts
        priority_inversion_bound L H_L_positive R H_R_is_maximum
        js ARRs TSKs POS A INSP)
      js ARRs TSKs
  · simp only [not_lt, Nat.le_zero] at POS
    show completed_by sched js (job_arrival js + R)
    unfold completed_by; rw [POS]; exact Nat.zero_le _

end AbstractRTAforFPwithArrivalCurves

end Prosa.Results.Fixed_priority.Rta.Bounded_pi
