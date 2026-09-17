-- Translated from: ../rt-proofs/results/edf/rta/bounded_pi.v
import Prosa.Analysis.Facts.Edf
import Prosa.Model.Schedule.Priority_driven
import Prosa.Analysis.Facts.Busy_interval.Carry_in
import Prosa.Analysis.Definitions.Schedulability
import Prosa.Model.Priority.Edf
import Prosa.Model.Task.Absolute_deadline
import Prosa.Analysis.Abstract.Ideal_jlfp_rta
import Prosa.Model.Processor.Ideal
import Prosa.Model.Readiness.Basic
import Prosa.Analysis.Abstract.Abstract_seq_rta
import Prosa.Analysis.Definitions.Request_bound_function
import Prosa.Analysis.Definitions.Priority_inversion
import Prosa.Model.Schedule.Work_conserving
import Prosa.Util.Epsilon
import Prosa.Util.Sum
import Prosa.Analysis.Facts.Model.Workload
import Prosa.Analysis.Facts.Behavior.Arrivals

namespace Prosa.Results.Edf.Rta.Bounded_pi

open Prosa.Behavior.Job
open Prosa.Behavior.Time
open Prosa.Behavior.Schedule
open Prosa.Behavior.Service
open Prosa.Behavior.Arrival_sequence
open Prosa.Behavior.Ready
open Prosa.Model.Task.Concept
open Prosa.Model.Task.Absolute_deadline
open Prosa.Model.Task.Sequentiality
open Prosa.Model.Task.Arrivals
open Prosa.Model.Task.Arrival.Curves
open Prosa.Model.Processor.Ideal
open Prosa.Model.Priority.Classes
open Prosa.Model.Priority.Edf
open Prosa.Model.Preemption.Parameter
open Prosa.Model.Task.Preemption.Parameters
open Prosa.Model.Aggregate.Workload
open Prosa.Model.Aggregate.Service_of_jobs
open Prosa.Model.Schedule.Work_conserving
open Prosa.Analysis.Abstract.Definitions
open Prosa.Analysis.Abstract.Ideal_jlfp_rta
open Prosa.Analysis.Abstract.Abstract_seq_rta
open Prosa.Analysis.Abstract.Search_space
open Prosa.Analysis.Definitions.Schedulability
open Prosa.Analysis.Definitions.Job_properties
open Prosa.Analysis.Definitions.Request_bound_function
open Prosa.Analysis.Definitions.Priority_inversion
open Prosa.Analysis.Definitions.Busy_interval
open Prosa.Analysis.Definitions.Task_schedule
open Prosa.Analysis.Facts.Edf
open Prosa.Analysis.Facts.Busy_interval.Carry_in
open Prosa.Analysis.Facts.Behavior.Completion
open Prosa.Analysis.Facts.Model.Rbf
open Prosa.Analysis.Facts.Model.Task_arrivals
open Prosa.Analysis.Facts.Model.Workload
open Prosa.Analysis.Facts.Behavior.Arrivals
open Prosa.Util.Sum
open Prosa.Analysis.Facts.Model.Service_of_jobs
open Prosa.Util.Epsilon

section AbstractRTAforEDFwithArrivalCurves

variable {Task : TaskType}
variable [TaskCost Task]
variable [TaskDeadline Task]
variable [TaskRunToCompletionThreshold Task]

variable {Job : JobType}
variable [DecidableEq Job]
variable [JobTask Job Task]
variable [JobArrival Job]
variable [JobCost Job]
variable [JobPreemptable Job]

variable [DecidableEq Task]

set_option synthInstance.checkSynthOrder false in
noncomputable local instance : JobDeadline Job := job_deadline_from_task_deadline Job Task
attribute [local instance] pstate_instance
attribute [local instance] Prosa.Model.Readiness.Basic.basic_ready_instance
set_option synthInstance.checkSynthOrder false in
noncomputable local instance : JLFP_policy Job := EDF Job
set_option synthInstance.checkSynthOrder false in
noncomputable local instance : JLDP_policy Job := JLFP_to_JLDP Job

variable (arr_seq : arrival_sequence Job)
variable (H_arrival_times_are_consistent : consistent_arrival_times arr_seq)
variable (H_arr_seq_is_a_set : arrival_sequence_uniq arr_seq)

variable (sched : schedule (processor_state Job))
variable (H_jobs_come_from_arrival_sequence :
  jobs_come_from_arrival_sequence (Job := Job) sched arr_seq)

variable (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute (Job := Job) sched)
variable (H_completed_jobs_dont_execute : completed_jobs_dont_execute (Job := Job) sched)

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

noncomputable def bound_on_total_hep_workload
    (tsk : Task) [TaskDeadline Task] [TaskCost Task] [MaxArrivals Task]
    (ts : List Task) (A Δ : duration) : Nat :=
  (ts.filter (fun tsk_o => decide (tsk_o ≠ tsk))).map
    (fun tsk_o =>
      task_request_bound_function tsk_o
        (min ((A + ε) + task_deadline tsk - task_deadline tsk_o) Δ))
    |>.sum

def task_rbf_changes_at (tsk : Task) [TaskCost Task] [MaxArrivals Task]
    (A : duration) : Bool :=
  decide (task_request_bound_function tsk A ≠ task_request_bound_function tsk (A + ε))

def bound_on_total_hep_workload_changes_at
    (tsk : Task) [TaskDeadline Task] [TaskCost Task] [MaxArrivals Task]
    (ts : List Task) (A : duration) : Bool :=
  ts.any fun tsko =>
    decide (tsk ≠ tsko) &&
      decide (task_request_bound_function tsko (A + task_deadline tsk - task_deadline tsko) ≠
              task_request_bound_function tsko ((A + ε) + task_deadline tsk - task_deadline tsko))

def is_in_search_space_edf
    (tsk : Task) [TaskDeadline Task] [TaskCost Task] [MaxArrivals Task]
    (ts : List Task) (L : duration) (A : duration) : Bool :=
  decide (A < L) &&
    (task_rbf_changes_at tsk A || bound_on_total_hep_workload_changes_at tsk ts A)

variable (priority_inversion_bound : duration)
variable (H_priority_inversion_is_bounded :
  priority_inversion_is_bounded_by arr_seq sched tsk priority_inversion_bound)

variable (L : duration)
variable (H_L_positive : L > 0)
variable (H_fixed_point : L = total_request_bound_function ts L)

variable (R : duration)
variable (H_R_is_maximum :
  ∀ (A : duration),
    is_in_search_space_edf tsk ts L A = true →
    ∃ (F : duration),
      A + F = priority_inversion_bound
              + (task_request_bound_function tsk (A + ε) -
                  (task_cost tsk - task_run_to_completion_threshold tsk))
              + bound_on_total_hep_workload tsk ts A (A + F) ∧
      F + (task_cost tsk - task_run_to_completion_threshold tsk) ≤ R)

section FillingOutHypothesesOfAbstractRTATheorem

include H_arrival_times_are_consistent H_arr_seq_is_a_set
  H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute
  H_completed_jobs_dont_execute H_work_conserving H_sequential_tasks in
lemma instantiated_i_and_w_are_coherent_with_schedule :
    Prosa.Analysis.Abstract.Definitions.work_conserving arr_seq sched tsk
      (Prosa.Analysis.Abstract.Ideal_jlfp_rta.interference sched)
      (Prosa.Analysis.Abstract.Ideal_jlfp_rta.interfering_workload arr_seq sched) := by
  intro j t1 t2 t ARRj TSKj POSj ABI ⟨HLE, HLT⟩
  have h_refl : reflexive_priorities (Job := Job) := Prosa.Model.Priority.Edf.EDF_is_reflexive
  have h_trans : transitive_priorities (Job := Job) := Prosa.Model.Priority.Edf.EDF_is_transitive
  have h_edf_seq : Prosa.Model.Priority.Classes.policy_respects_sequential_tasks (Task := Task) (Job := Job) :=
    EDF_respects_sequential_tasks
  have h_cbi := (Prosa.Analysis.Abstract.Ideal_jlfp_rta.instantiated_busy_interval_equivalent_edf_busy_interval
    arr_seq H_arrival_times_are_consistent H_arr_seq_is_a_set sched
    H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute
    H_completed_jobs_dont_execute H_sequential_tasks
    h_refl h_trans h_edf_seq j ARRj t1 t2).mpr ABI
  have h_job_task : Prosa.Model.Task.Concept.job_of_task tsk j = true := by
    simp [Prosa.Model.Task.Concept.job_of_task, TSKj]
  have h_not_idle : ¬ Prosa.Model.Processor.Ideal.is_idle sched t :=
    Prosa.Analysis.Facts.Busy_interval.Busy_interval.not_quiet_implies_not_idle
      arr_seq H_arrival_times_are_consistent sched
      H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute
      H_completed_jobs_dont_execute tsk j ARRj h_job_task POSj
      H_work_conserving h_refl h_trans t1 t2 h_cbi.1 t ⟨HLE, HLT⟩
  have h_not_none : sched t ≠ none := by intro h_eq; exact h_not_idle h_eq
  obtain ⟨jhp, h_sched_eq⟩ := Option.ne_none_iff_exists'.mp h_not_none
  have h_interf_eq : Prosa.Analysis.Abstract.Ideal_jlfp_rta.interference sched j t =
      (!hep_job jhp j || (hep_job jhp j && (jhp != j))) := by
    unfold Prosa.Analysis.Abstract.Ideal_jlfp_rta.interference
      Prosa.Analysis.Definitions.Priority_inversion.is_priority_inversion
      Prosa.Analysis.Abstract.Ideal_jlfp_rta.is_interference_from_another_hep_job
    rw [h_sched_eq]; rfl
  constructor
  · intro NINT
    by_cases hjhp : jhp = j
    · subst hjhp
      rw [Prosa.Analysis.Facts.Model.Ideal_schedule.scheduled_at_def]
      simp [h_sched_eq]
    · exfalso; apply NINT; rw [h_interf_eq]
      have h_bne : (jhp != j) = true := by simp [bne_iff_ne, hjhp]
      cases h_hep : hep_job jhp j <;> simp [h_bne]
  · intro SCHED
    have hjhp_eq : jhp = j := by
      rw [Prosa.Analysis.Facts.Model.Ideal_schedule.scheduled_at_def] at SCHED
      have h := of_decide_eq_true SCHED
      exact Option.some.inj (h_sched_eq.symm.trans h)
    rw [h_interf_eq, hjhp_eq]
    have h1 : hep_job j j = true := by show hep_job_at 0 j j = true; exact h_refl 0 j
    have h2 : (j != j) = false := bne_self_eq_false j
    rw [h1, h2, Bool.and_false, Bool.not_true, Bool.false_or]
    exact Bool.false_ne_true

include H_arrival_times_are_consistent H_arr_seq_is_a_set
  H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute
  H_completed_jobs_dont_execute H_sequential_tasks in
lemma instantiated_interference_and_workload_consistent_with_sequential_tasks :
    interference_and_workload_consistent_with_sequential_tasks
      arr_seq sched tsk
      (Prosa.Analysis.Abstract.Ideal_jlfp_rta.interference sched)
      (Prosa.Analysis.Abstract.Ideal_jlfp_rta.interfering_workload arr_seq sched) := by
  intro j t1 t2 ARR TSK POS BUSY
  simp only [task_workload_between, task_workload, task_service_of_jobs_in]
  have h_refl : reflexive_priorities (Job := Job) := Prosa.Model.Priority.Edf.EDF_is_reflexive
  have h_trans : transitive_priorities (Job := Job) := Prosa.Model.Priority.Edf.EDF_is_transitive
  apply (Prosa.Analysis.Facts.Model.Service_of_jobs.all_jobs_have_completed_equiv_workload_eq_service
    arr_seq H_arrival_times_are_consistent sched H_jobs_come_from_arrival_sequence
    H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute
    (job_of_task tsk) 0 t1 t1).mp
  intro s ARRs TSKs
  have h_s_arrives : arrives_in arr_seq s :=
    Prosa.Analysis.Facts.Behavior.Arrivals.in_arrivals_implies_arrived
      arr_seq H_arrival_times_are_consistent s 0 t1 ARRs
  have h_s_before : arrived_before s t1 :=
    (Prosa.Analysis.Facts.Behavior.Arrivals.in_arrivals_implies_arrived_between
      arr_seq H_arrival_times_are_consistent s 0 t1 ARRs).2
  have h_job_task_s : job_task (Task := Task) s = tsk := by
    simp [Prosa.Model.Task.Concept.job_of_task] at TSKs; exact TSKs
  have h_hep : hep_job s j = true := by
    exact EDF_respects_sequential_tasks s j (h_job_task_s.trans TSK.symm)
      (le_trans (le_of_lt h_s_before) BUSY.1.1.1)
  have h_aqt := BUSY.1.2.1
  have h_edf_seq : Prosa.Model.Priority.Classes.policy_respects_sequential_tasks (Task := Task) (Job := Job) :=
    EDF_respects_sequential_tasks
  have h_cqt := Prosa.Analysis.Abstract.Ideal_jlfp_rta.quiet_time_ab_implies_quiet_time_cl
    arr_seq H_arrival_times_are_consistent H_arr_seq_is_a_set sched
    H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute
    H_completed_jobs_dont_execute H_sequential_tasks
    h_refl h_trans h_edf_seq j t1 h_aqt
  exact h_cqt s h_s_arrives h_hep h_s_before

include H_arrival_times_are_consistent H_arr_seq_is_a_set
  H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute
  H_completed_jobs_dont_execute H_work_conserving H_sequential_tasks
  H_L_positive H_fixed_point H_valid_job_cost H_is_arrival_curve
  H_tsk_in_ts H_all_jobs_from_taskset in
lemma instantiated_busy_intervals_are_bounded :
    busy_intervals_are_bounded_by arr_seq sched tsk
      (Prosa.Analysis.Abstract.Ideal_jlfp_rta.interference sched)
      (Prosa.Analysis.Abstract.Ideal_jlfp_rta.interfering_workload arr_seq sched) L := by
  intro j ARR TSK POS
  have h_refl : reflexive_priorities (Job := Job) := Prosa.Model.Priority.Edf.EDF_is_reflexive
  have h_trans : transitive_priorities (Job := Job) := Prosa.Model.Priority.Edf.EDF_is_transitive
  have h_edf_seq : Prosa.Model.Priority.Classes.policy_respects_sequential_tasks (Task := Task) (Job := Job) :=
    EDF_respects_sequential_tasks
  have h_wl_bound : ∀ t, workload_of_jobs (fun (_ : Job) => true) (arrivals_between arr_seq t (t + L)) ≤ L := by
    intro t
    letI : FP_policy Task := ⟨fun _ _ => true⟩
    calc workload_of_jobs (fun (_ : Job) => true) (arrivals_between arr_seq t (t + L))
        ≤ total_request_bound_function ts L :=
          Prosa.Analysis.Facts.Model.Rbf.total_workload_le_total_rbf''
            arr_seq H_arrival_times_are_consistent H_arr_seq_is_a_set sched
            H_jobs_come_from_arrival_sequence ts tsk H_tsk_in_ts
            H_valid_job_cost H_all_jobs_from_taskset H_is_arrival_curve
            j ARR TSK t L
      _ = L := H_fixed_point.symm
  have h_concrete := Prosa.Analysis.Facts.Busy_interval.Carry_in.exists_busy_interval_from_total_workload_bound
    arr_seq H_arrival_times_are_consistent sched
    H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute
    H_completed_jobs_dont_execute H_work_conserving H_arr_seq_is_a_set
    h_refl L H_L_positive h_wl_bound j ARR POS
  obtain ⟨t1, t2, hLE, hLT, hBound, h_cbi⟩ := h_concrete
  have h_abi := (Prosa.Analysis.Abstract.Ideal_jlfp_rta.instantiated_busy_interval_equivalent_edf_busy_interval
    arr_seq H_arrival_times_are_consistent H_arr_seq_is_a_set sched
    H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute
    H_completed_jobs_dont_execute H_sequential_tasks
    h_refl h_trans h_edf_seq j ARR t1 t2).mp h_cbi
  exact ⟨t1, t2, ⟨hLE, hLT⟩, hBound, h_abi⟩

section TaskInterferenceIsBoundedByIBF

section Inequalities

variable (j : Job)
variable (H_j_arrives : arrives_in arr_seq j)
variable (H_job_of_tsk : job_task j = tsk)
variable (H_job_cost_positive : job_cost_positive j)

variable (t1 t2 : duration)
variable (H_busy_interval :
  Prosa.Analysis.Abstract.Definitions.busy_interval sched
    (Prosa.Analysis.Abstract.Ideal_jlfp_rta.interference sched)
    (Prosa.Analysis.Abstract.Ideal_jlfp_rta.interfering_workload arr_seq sched) j t1 t2)

variable (Δ : duration)
variable (H_Δ_in_busy : t1 + Δ < t2)

include H_priority_inversion_is_bounded H_arrival_times_are_consistent H_arr_seq_is_a_set
  H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute
  H_completed_jobs_dont_execute H_sequential_tasks
  H_j_arrives H_job_of_tsk H_job_cost_positive H_busy_interval H_Δ_in_busy in
lemma cumulative_priority_inversion_is_bounded :
    Prosa.Analysis.Abstract.Ideal_jlfp_rta.cumulative_priority_inversion sched j t1 (t1 + Δ) ≤
      priority_inversion_bound := by
  have h_refl : reflexive_priorities (Job := Job) := Prosa.Model.Priority.Edf.EDF_is_reflexive
  have h_trans : transitive_priorities (Job := Job) := Prosa.Model.Priority.Edf.EDF_is_transitive
  have h_edf_seq : Prosa.Model.Priority.Classes.policy_respects_sequential_tasks (Task := Task) (Job := Job) :=
    EDF_respects_sequential_tasks
  have h_cbi : Prosa.Analysis.Definitions.Busy_interval.busy_interval arr_seq sched j t1 t2 :=
    (Prosa.Analysis.Abstract.Ideal_jlfp_rta.instantiated_busy_interval_equivalent_edf_busy_interval
      arr_seq H_arrival_times_are_consistent H_arr_seq_is_a_set sched
      H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute
      H_completed_jobs_dont_execute H_sequential_tasks
      h_refl h_trans h_edf_seq j H_j_arrives t1 t2).mpr H_busy_interval
  have h_bip := h_cbi.1
  have h_pi_full := H_priority_inversion_is_bounded j H_j_arrives H_job_of_tsk H_job_cost_positive t1 t2 h_bip
  exact le_trans (by
    unfold Prosa.Analysis.Abstract.Ideal_jlfp_rta.cumulative_priority_inversion
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · exact Finset.Ico_subset_Ico_right (Nat.le_of_lt H_Δ_in_busy)
    · intro _ _ _; exact Nat.zero_le _) h_pi_full

include H_arrival_times_are_consistent H_arr_seq_is_a_set
  H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute
  H_completed_jobs_dont_execute H_sequential_tasks
  H_j_arrives H_job_of_tsk H_job_cost_positive H_busy_interval H_Δ_in_busy in
lemma cumulative_interference_is_bounded_by_total_service :
    Prosa.Analysis.Abstract.Ideal_jlfp_rta.cumulative_interference_from_hep_jobs_from_other_tasks
      (Task := Task) sched j t1 (t1 + Δ) ≤
    service_of_jobs sched
      (fun jo => hep_job jo j && decide (job_task (Task := Task) jo ≠ tsk))
      (arrivals_between arr_seq t1 (t1 + Δ)) t1 (t1 + Δ) := by
  have h_refl : reflexive_priorities (Job := Job) := Prosa.Model.Priority.Edf.EDF_is_reflexive
  have h_trans : transitive_priorities (Job := Job) := Prosa.Model.Priority.Edf.EDF_is_transitive
  have h_edf_seq : Prosa.Model.Priority.Classes.policy_respects_sequential_tasks (Task := Task) (Job := Job) :=
    EDF_respects_sequential_tasks
  have h_cbi :=
    (Prosa.Analysis.Abstract.Ideal_jlfp_rta.instantiated_busy_interval_equivalent_edf_busy_interval
      arr_seq H_arrival_times_are_consistent H_arr_seq_is_a_set sched
      H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute
      H_completed_jobs_dont_execute H_sequential_tasks
      h_refl h_trans h_edf_seq j H_j_arrives t1 t2).mpr H_busy_interval
  have h_qt1 := h_cbi.1.2.1
  have h_eq := Prosa.Analysis.Abstract.Ideal_jlfp_rta.instantiated_cumulative_interference_of_hep_tasks_equal_total_interference_of_hep_tasks
    (Task := Task)
    arr_seq H_arrival_times_are_consistent H_arr_seq_is_a_set sched
    H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute
    H_completed_jobs_dont_execute j t1 (t1 + Δ) h_qt1
  rw [h_eq]
  show service_of_jobs sched
      (fun jhp => hep_job jhp j && (job_task (Task := Task) jhp != job_task (Task := Task) j))
      (arrivals_between arr_seq t1 (t1 + Δ)) t1 (t1 + Δ) ≤
    service_of_jobs sched
      (fun jo => hep_job jo j && decide (job_task (Task := Task) jo ≠ tsk))
      (arrivals_between arr_seq t1 (t1 + Δ)) t1 (t1 + Δ)
  have h_pred : (fun jhp : Job => hep_job jhp j && (job_task (Task := Task) jhp != job_task (Task := Task) j)) =
      (fun jo : Job => hep_job jo j && decide (job_task (Task := Task) jo ≠ tsk)) := by
    funext jo; congr 1; unfold bne; rw [H_job_of_tsk, beq_eq_decide]
    cases h : (decide (job_task (Task := Task) jo = tsk)) <;> simp [h]
  rw [h_pred]

include H_arrival_times_are_consistent H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute
  H_j_arrives H_job_of_tsk H_busy_interval H_Δ_in_busy in
lemma total_service_is_bounded_by_total_workload :
    service_of_jobs sched
      (fun jo => hep_job jo j && decide (job_task (Task := Task) jo ≠ tsk))
      (arrivals_between arr_seq t1 (t1 + Δ)) t1 (t1 + Δ) ≤
    workload_of_jobs
      (fun jo => hep_job jo j && decide (job_task (Task := Task) jo ≠ tsk))
      (arrivals_between arr_seq t1 (t1 + Δ)) := by
  exact Prosa.Analysis.Facts.Model.Service_of_jobs.service_of_jobs_le_workload
    arr_seq H_arrival_times_are_consistent sched
    H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute
    _ _ Prosa.Analysis.Facts.Model.Ideal_schedule.ideal_proc_model_provides_unit_service t1 (t1 + Δ)

include H_all_jobs_from_taskset H_arrival_times_are_consistent
  H_j_arrives H_job_of_tsk H_busy_interval in
lemma reorder_summation :
    workload_of_jobs
      (fun jo => hep_job jo j && decide (job_task (Task := Task) jo ≠ tsk))
      (arrivals_between arr_seq t1 (t1 + Δ)) ≤
    ((ts.filter (fun tsk_o => decide (tsk_o ≠ tsk))).map
      (fun tsk_o => workload_of_jobs
        (fun jo => hep_job jo j && decide (job_task (Task := Task) jo = tsk_o))
        (arrivals_between arr_seq t1 (t1 + Δ)))).sum := by
  simp only [workload_of_jobs]
  set jobs := arrivals_between arr_seq t1 (t1 + Δ)
  set P := fun jo : Job => hep_job jo j && decide (job_task (Task := Task) jo ≠ tsk)
  set tasks := ts.filter (fun tsk_o => decide (tsk_o ≠ tsk))
  -- Step 1: partition LHS by task
  apply le_trans (list_sum_le_partition_sum (jobs.filter P) tasks job_cost
    (fun jo => job_task (Task := Task) jo) ?_)
  -- Step 2: per-task double-filter ≤ per-task single-filter
  · apply leq_sum_seq
    intro tsk_o _ _
    apply List.Sublist.sum_le_sum
    · apply List.Sublist.map job_cost
      -- (jobs.filter P).filter (job_task · == tsk_o) <+ jobs.filter (hep · && decide(=tsk_o))
      rw [List.filter_filter]
      -- After filter_filter: jobs.filter (fun jo => (job_task jo == tsk_o) && P jo)
      -- Need this to be sublist of jobs.filter (hep · && decide(=tsk_o))
      suffices ∀ (l : List Job),
          (l.filter (fun jo => (job_task (Task := Task) jo == tsk_o) && P jo)).Sublist
          (l.filter (fun jo => hep_job jo j && decide (job_task (Task := Task) jo = tsk_o))) from
        this jobs
      intro l; induction l with
      | nil => exact List.Sublist.slnil
      | cons a l ih =>
        simp only [List.filter_cons]
        split
        · rename_i hp
          have hq : hep_job a j && decide (job_task (Task := Task) a = tsk_o) = true := by
            simp only [Bool.and_eq_true, decide_eq_true_eq, P] at hp ⊢
            exact ⟨hp.2.1, beq_iff_eq.mp hp.1⟩
          split
          · exact ih.cons₂ _
          · rename_i hn
            exfalso; apply hn
            simp only [Bool.and_eq_true, decide_eq_true_eq, P] at hp ⊢
            exact ⟨hp.2.1, beq_iff_eq.mp hp.1⟩
        · split
          · exact ih.cons _
          · exact ih
    · intro _ _; exact Nat.zero_le _
  -- Step 1 prerequisite: ∀ jo ∈ jobs.filter P, job_task jo ∈ tasks
  · intro jo hjo
    rw [List.mem_filter] at hjo ⊢
    simp only [P, Bool.and_eq_true, decide_eq_true_eq] at hjo
    constructor
    · exact H_all_jobs_from_taskset jo
        (in_arrivals_implies_arrived arr_seq H_arrival_times_are_consistent
          jo t1 (t1 + Δ) hjo.1)
    · simp only [decide_eq_true_eq]; exact hjo.2.2

section Case1

variable (tsk_o : Task)
variable (H_tsko_in_ts : tsk_o ∈ ts)
variable (H_neq : tsk_o ≠ tsk)
variable (H_Δ_le : Δ ≤ (job_arrival j - t1) + ε + task_deadline tsk - task_deadline tsk_o)

include H_arrival_times_are_consistent H_valid_job_cost H_is_arrival_curve
  H_j_arrives H_job_of_tsk H_busy_interval H_tsko_in_ts in
lemma workload_le_rbf :
    workload_of_jobs
      (fun jo => hep_job jo j && decide (job_task (Task := Task) jo = tsk_o))
      (arrivals_between arr_seq t1 (t1 + Δ)) ≤
    task_request_bound_function tsk_o Δ := by
  -- Step 1: Drop hep filter → workload with job_of_task tsk_o
  apply le_trans (b := workload_of_jobs (job_of_task tsk_o) (arrivals_between arr_seq t1 (t1 + Δ)))
  · simp only [workload_of_jobs]
    apply List.Sublist.sum_le_sum
    · apply List.Sublist.map job_cost
      suffices ∀ (l : List Job),
          (l.filter (fun jo => hep_job jo j && decide (job_task (Task := Task) jo = tsk_o))).Sublist
          (l.filter (fun jo => job_of_task tsk_o jo)) from
        this _
      intro l; induction l with
      | nil => exact List.Sublist.slnil
      | cons a l ih =>
        simp only [List.filter_cons]
        by_cases hp : (hep_job a j && decide (job_task (Task := Task) a = tsk_o)) = true
        · simp only [hp, ite_true]
          have : job_of_task tsk_o a = true := by
            simp only [Bool.and_eq_true, decide_eq_true_eq] at hp
            simp [job_of_task, beq_iff_eq, hp.2]
          simp only [this, ite_true]; exact ih.cons₂ _
        · simp only [Bool.not_eq_true] at hp; simp only [hp, ite_false]
          by_cases hq : job_of_task tsk_o a = true
          · simp only [hq, ite_true]; exact ih.cons _
          · simp only [Bool.not_eq_true] at hq; simp only [hq, ite_false]; exact ih
    · intro _ _; exact Nat.zero_le _
  -- Step 2: workload of tsk_o's jobs ≤ task_cost * number_of_arrivals ≤ task_rbf
  · simp only [workload_of_jobs, task_request_bound_function]
    apply le_trans (sum_majorant_constant _ _ _ (task_cost tsk_o) ?_)
    · apply Nat.mul_le_mul_left
      -- number_of_task_arrivals ≤ max_arrivals
      show (((arrivals_between arr_seq t1 (t1 + Δ)).filter
        (fun j => job_of_task tsk_o j)).length) ≤ max_arrivals tsk_o Δ
      have h_arr := H_is_arrival_curve tsk_o H_tsko_in_ts t1 (t1 + Δ) (Nat.le_add_right t1 Δ)
      simp only [number_of_task_arrivals, task_arrivals_between] at h_arr
      have : t1 + Δ - t1 = Δ := Nat.add_sub_cancel_left t1 Δ
      rw [this] at h_arr; exact h_arr
    · intro jo hjo hP
      simp only [job_of_task, beq_iff_eq] at hP
      have hjo_arr := in_arrivals_implies_arrived arr_seq H_arrival_times_are_consistent
        jo t1 (t1 + Δ) hjo
      have := H_valid_job_cost jo hjo_arr
      simp only [valid_job_cost, hP] at this; exact this

end Case1

section Case2

variable (tsk_o : Task)
variable (H_tsko_in_ts : tsk_o ∈ ts)
variable (H_neq : tsk_o ≠ tsk)
variable (H_Δ_ge : (job_arrival j - t1) + ε + task_deadline tsk - task_deadline tsk_o ≤ Δ)

include H_arrival_times_are_consistent H_arr_seq_is_a_set
  H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute
  H_completed_jobs_dont_execute H_sequential_tasks
  H_j_arrives H_job_of_tsk H_job_cost_positive H_busy_interval
  H_tsko_in_ts H_Δ_ge in
lemma total_workload_shorten_range :
    workload_of_jobs
      (fun jo => hep_job jo j && decide (job_task (Task := Task) jo = tsk_o))
      (arrivals_between arr_seq t1 (t1 + Δ)) ≤
    workload_of_jobs
      (fun jo => hep_job jo j && decide (job_task (Task := Task) jo = tsk_o))
      (arrivals_between arr_seq t1
        (t1 + ((job_arrival j - t1) + ε + task_deadline tsk - task_deadline tsk_o))) := by
  set V := (job_arrival j - t1) + ε + task_deadline tsk - task_deadline tsk_o with hV_def
  set P := fun jo : Job => hep_job jo j && decide (job_task (Task := Task) jo = tsk_o)
  by_cases hle : t1 + V ≤ t1 + Δ
  · -- Case: V ≤ Δ. Split arrivals at (t1 + V)
    rw [workload_of_jobs_cat arr_seq (t1 + V) t1 (t1 + Δ) P ⟨Nat.le_add_right t1 V, hle⟩]
    suffices h_zero : workload_of_jobs P (arrivals_between arr_seq (t1 + V) (t1 + Δ)) = 0 by
      rw [h_zero, add_zero]
    simp only [workload_of_jobs]
    apply List.sum_eq_zero
    intro c hc; rw [List.mem_map] at hc
    obtain ⟨jo, hjo_mem, rfl⟩ := hc
    rw [List.mem_filter] at hjo_mem
    simp only [P, Bool.and_eq_true, decide_eq_true_eq] at hjo_mem
    exfalso
    have hjo_ab := in_arrivals_implies_arrived_between arr_seq H_arrival_times_are_consistent
      jo (t1 + V) (t1 + Δ) hjo_mem.1
    have hjo_ge : job_arrival jo ≥ t1 + V := hjo_ab.1
    have hjo_hep := hjo_mem.2.1
    have hjt_tsko : job_task (Task := Task) jo = tsk_o := hjo_mem.2.2
    have hjt_tsk : job_task (Task := Task) j = tsk := by
      have h := H_job_of_tsk; simp only [job_of_task, beq_iff_eq] at h; exact h
    simp only [hep_job, EDF, Nat.ble_eq] at hjo_hep
    -- Unfold job_deadline (which is job_arrival + task_deadline(job_task)) via definitional equality
    change job_arrival jo + task_deadline (job_task (Task := Task) jo) ≤
        job_arrival j + task_deadline (job_task (Task := Task) j) at hjo_hep
    rw [hjt_tsko, hjt_tsk] at hjo_hep
    -- hjo_hep : job_arrival jo + task_deadline tsk_o ≤ job_arrival j + task_deadline tsk
    have ht1_le_ja : t1 ≤ job_arrival j := H_busy_interval.1.1.1
    by_cases h_dtsko : task_deadline tsk_o ≤ (job_arrival j - t1) + ε + task_deadline tsk
    · have hV_sub : V + task_deadline tsk_o = (job_arrival j - t1) + ε + task_deadline tsk := by
        simp only [hV_def]; exact Nat.sub_add_cancel h_dtsko
      have h_ge : job_arrival jo + task_deadline tsk_o ≥
          t1 + ((job_arrival j - t1) + ε + task_deadline tsk) := by
        calc job_arrival jo + task_deadline tsk_o
            ≥ (t1 + V) + task_deadline tsk_o := Nat.add_le_add_right hjo_ge _
          _ = t1 + (V + task_deadline tsk_o) := Nat.add_assoc t1 V _
          _ = t1 + ((job_arrival j - t1) + ε + task_deadline tsk) := by rw [hV_sub]
      have h_simpl : t1 + ((job_arrival j - t1) + ε + task_deadline tsk) =
          job_arrival j + ε + task_deadline tsk := by
        have h1 := Nat.sub_add_cancel ht1_le_ja
        conv_rhs => rw [← h1]
        simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
      rw [h_simpl] at h_ge
      -- h_ge : jo_arr + D_o ≥ ja + ε + D, hjo_hep : jo_arr + D_o ≤ ja + D
      have h_absurd := le_trans h_ge hjo_hep
      -- h_absurd : ja + ε + D ≤ ja + D, but ε ≥ 1 — contradiction
      simp [ε] at h_absurd
    · push_neg at h_dtsko
      -- D_tsk_o > (ja - t1) + ε + D_tsk, so V = 0
      have hV0 : V = 0 := by
        simp only [hV_def]; apply Nat.sub_eq_zero_of_le; exact le_of_lt h_dtsko
      rw [hV0, Nat.add_zero] at hjo_ge
      have h1 : t1 + task_deadline tsk_o ≤ job_arrival j + task_deadline tsk :=
        le_trans (Nat.add_le_add_right hjo_ge _) hjo_hep
      have h2 : task_deadline tsk_o > job_arrival j - t1 + ε + task_deadline tsk := h_dtsko
      set y := job_arrival j - t1
      have hy_eq : y + t1 = job_arrival j := Nat.sub_add_cancel ht1_le_ja
      simp [ε] at h2
      -- Construct explicit Nat contradiction
      have h3 : t1 + (y + 1 + task_deadline tsk) < t1 + task_deadline tsk_o :=
        Nat.add_lt_add_left h2 t1
      have h4 : t1 + (y + 1 + task_deadline tsk) = job_arrival j + 1 + task_deadline tsk := by
        rw [← hy_eq]; ring
      rw [h4] at h3
      -- h3 : ja + 1 + D < t1 + D_o, h1 : t1 + D_o ≤ ja + D
      exact absurd (le_trans (Nat.le_of_lt h3) h1) (by omega)
  · -- Case: Δ < V. LHS list is prefix of RHS list
    push_neg at hle
    simp only [workload_of_jobs]
    apply List.Sublist.sum_le_sum
    · apply List.Sublist.map job_cost; apply List.Sublist.filter
      have h_cat := arrivals_between_cat arr_seq t1 (t1 + Δ) (t1 + V)
        (Nat.le_add_right t1 Δ) (le_of_lt hle)
      rw [h_cat]; exact List.sublist_append_left _ _
    · intro _ _; exact Nat.zero_le _

include H_arrival_times_are_consistent H_valid_job_cost H_is_arrival_curve
  H_j_arrives H_job_of_tsk H_busy_interval H_tsko_in_ts in
lemma workload_le_rbf' :
    workload_of_jobs
      (fun jo => hep_job jo j && decide (job_task (Task := Task) jo = tsk_o))
      (arrivals_between arr_seq t1
        (t1 + ((job_arrival j - t1) + ε + task_deadline tsk - task_deadline tsk_o))) ≤
    task_request_bound_function tsk_o
      ((job_arrival j - t1) + ε + task_deadline tsk - task_deadline tsk_o) := by
  set V := (job_arrival j - t1) + ε + task_deadline tsk - task_deadline tsk_o
  -- Same structure as workload_le_rbf but with range V instead of Δ
  apply le_trans (b := workload_of_jobs (job_of_task tsk_o) (arrivals_between arr_seq t1 (t1 + V)))
  · simp only [workload_of_jobs]
    apply List.Sublist.sum_le_sum
    · apply List.Sublist.map job_cost
      suffices ∀ (l : List Job),
          (l.filter (fun jo => hep_job jo j && decide (job_task (Task := Task) jo = tsk_o))).Sublist
          (l.filter (fun jo => job_of_task tsk_o jo)) from this _
      intro l; induction l with
      | nil => exact List.Sublist.slnil
      | cons a l ih =>
        simp only [List.filter_cons]
        by_cases hp : (hep_job a j && decide (job_task (Task := Task) a = tsk_o)) = true
        · simp only [hp, ite_true]
          have : job_of_task tsk_o a = true := by
            simp only [Bool.and_eq_true, decide_eq_true_eq] at hp
            simp [job_of_task, beq_iff_eq, hp.2]
          simp only [this, ite_true]; exact ih.cons₂ _
        · simp only [Bool.not_eq_true] at hp; simp only [hp, ite_false]
          by_cases hq : job_of_task tsk_o a = true
          · simp only [hq, ite_true]; exact ih.cons _
          · simp only [Bool.not_eq_true] at hq; simp only [hq, ite_false]; exact ih
    · intro _ _; exact Nat.zero_le _
  · simp only [workload_of_jobs, task_request_bound_function]
    apply le_trans (sum_majorant_constant _ _ _ (task_cost tsk_o) ?_)
    · apply Nat.mul_le_mul_left
      show (((arrivals_between arr_seq t1 (t1 + V)).filter
        (fun j => job_of_task tsk_o j)).length) ≤ max_arrivals tsk_o V
      have h_arr := H_is_arrival_curve tsk_o H_tsko_in_ts t1 (t1 + V) (Nat.le_add_right t1 V)
      simp only [number_of_task_arrivals, task_arrivals_between] at h_arr
      have : t1 + V - t1 = V := Nat.add_sub_cancel_left t1 V
      rw [this] at h_arr; exact h_arr
    · intro jo hjo hP
      simp only [job_of_task, beq_iff_eq] at hP
      have hjo_arr := in_arrivals_implies_arrived arr_seq H_arrival_times_are_consistent
        jo t1 (t1 + V) hjo
      have := H_valid_job_cost jo hjo_arr
      simp only [valid_job_cost, hP] at this; exact this

end Case2

include H_arrival_times_are_consistent H_arr_seq_is_a_set
  H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute
  H_completed_jobs_dont_execute H_sequential_tasks
  H_valid_job_cost H_all_jobs_from_taskset H_is_arrival_curve
  H_j_arrives H_job_of_tsk H_job_cost_positive H_busy_interval H_Δ_in_busy in
theorem sum_of_workloads_is_at_most_bound_on_total_hep_workload :
    ((ts.filter (fun tsk_o => decide (tsk_o ≠ tsk))).map
      (fun tsk_o => workload_of_jobs
        (fun jo => hep_job jo j && decide (job_task (Task := Task) jo = tsk_o))
        (arrivals_between arr_seq t1 (t1 + Δ)))).sum ≤
    bound_on_total_hep_workload tsk ts (job_arrival j - t1) Δ := by
  simp only [bound_on_total_hep_workload]
  apply leq_sum_seq
  intro tsk_o h_tsko_in hP
  simp only [decide_eq_true_eq] at hP
  -- hP : tsk_o ≠ tsk, h_tsko_in : tsk_o ∈ ts
  by_cases hle : Δ ≤ (job_arrival j - t1 + ε) + task_deadline tsk - task_deadline tsk_o
  · -- Case 1: Δ ≤ V, min = Δ
    rw [min_eq_right hle]
    exact workload_le_rbf arr_seq H_arrival_times_are_consistent sched
      H_valid_job_cost ts H_is_arrival_curve tsk j H_j_arrives H_job_of_tsk
      t1 t2 H_busy_interval Δ tsk_o h_tsko_in
  · -- Case 2: V < Δ, min = V
    push_neg at hle
    rw [min_eq_left (le_of_lt hle)]
    exact le_trans
      (total_workload_shorten_range arr_seq H_arrival_times_are_consistent
        H_arr_seq_is_a_set sched H_jobs_come_from_arrival_sequence
        H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute
        H_sequential_tasks ts tsk j H_j_arrives H_job_of_tsk
        H_job_cost_positive t1 t2 H_busy_interval Δ tsk_o h_tsko_in
        (le_of_lt hle))
      (workload_le_rbf' arr_seq H_arrival_times_are_consistent sched
        H_valid_job_cost ts H_is_arrival_curve tsk j H_j_arrives H_job_of_tsk
        t1 t2 H_busy_interval tsk_o h_tsko_in)







end Inequalities

include H_arrival_times_are_consistent H_arr_seq_is_a_set
  H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute
  H_completed_jobs_dont_execute H_sequential_tasks
  H_valid_job_cost H_all_jobs_from_taskset H_is_arrival_curve
  H_priority_inversion_is_bounded in
theorem instantiated_task_interference_is_bounded :
    task_interference_is_bounded_by
      arr_seq sched tsk
      (Prosa.Analysis.Abstract.Ideal_jlfp_rta.interference sched)
      (Prosa.Analysis.Abstract.Ideal_jlfp_rta.interfering_workload arr_seq sched)
      (fun _ A R => priority_inversion_bound +
        bound_on_total_hep_workload tsk ts A R) := by
  intro j R₀ t1 t2 ARR TSK HLT NCOMPL BUSY
  have POS : job_cost j > 0 := by
    by_contra h; push_neg at h; apply NCOMPL
    unfold completed_by
    have : job_cost j = 0 := Nat.eq_zero_of_le_zero h
    rw [this]; exact Nat.zero_le _
  have h_pi_bound : Prosa.Analysis.Abstract.Ideal_jlfp_rta.cumulative_priority_inversion sched j t1 (t1 + R₀) ≤
      priority_inversion_bound :=
    cumulative_priority_inversion_is_bounded
      arr_seq H_arrival_times_are_consistent H_arr_seq_is_a_set sched
      H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute
      H_completed_jobs_dont_execute H_sequential_tasks
      tsk priority_inversion_bound H_priority_inversion_is_bounded
      j ARR TSK POS t1 t2 BUSY R₀ HLT
  have h_decomp : Prosa.Analysis.Abstract.Abstract_seq_rta.cumul_task_interference
      arr_seq sched tsk (Prosa.Analysis.Abstract.Ideal_jlfp_rta.interference sched) t2 t1 (t1 + R₀) ≤
      Prosa.Analysis.Abstract.Ideal_jlfp_rta.cumulative_priority_inversion sched j t1 (t1 + R₀) +
      Prosa.Analysis.Abstract.Ideal_jlfp_rta.cumulative_interference_from_hep_jobs_from_other_tasks
        (Task := Task) sched j t1 (t1 + R₀) := by
    have h_refl : reflexive_priorities (Job := Job) := Prosa.Model.Priority.Edf.EDF_is_reflexive
    have h_trans : transitive_priorities (Job := Job) := Prosa.Model.Priority.Edf.EDF_is_transitive
    have h_edf_seq : Prosa.Model.Priority.Classes.policy_respects_sequential_tasks (Task := Task) (Job := Job) :=
      EDF_respects_sequential_tasks
    have h_arr_before : j ∈ Prosa.Behavior.Arrival_sequence.arrivals_before arr_seq t2 :=
      Prosa.Analysis.Facts.Behavior.Arrivals.arrived_between_implies_in_arrivals
        arr_seq H_arrival_times_are_consistent j 0 t2 ARR ⟨Nat.zero_le _, BUSY.1.1.2⟩
    exact le_of_eq (Prosa.Analysis.Abstract.Ideal_jlfp_rta.cumulative_task_interference_split
      arr_seq H_arrival_times_are_consistent H_arr_seq_is_a_set sched
      H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute
      H_completed_jobs_dont_execute H_sequential_tasks
      h_refl h_trans h_edf_seq
      tsk j t1 (t1 + R₀) t2 TSK h_arr_before NCOMPL)
  have h_other_bound : Prosa.Analysis.Abstract.Ideal_jlfp_rta.cumulative_interference_from_hep_jobs_from_other_tasks
      (Task := Task) sched j t1 (t1 + R₀) ≤
      bound_on_total_hep_workload tsk ts (job_arrival j - t1) R₀ :=
    calc Prosa.Analysis.Abstract.Ideal_jlfp_rta.cumulative_interference_from_hep_jobs_from_other_tasks
          (Task := Task) sched j t1 (t1 + R₀)
        ≤ service_of_jobs sched
            (fun jo => hep_job jo j && decide (job_task (Task := Task) jo ≠ tsk))
            (arrivals_between arr_seq t1 (t1 + R₀)) t1 (t1 + R₀) :=
          cumulative_interference_is_bounded_by_total_service
            arr_seq H_arrival_times_are_consistent H_arr_seq_is_a_set sched
            H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute
            H_completed_jobs_dont_execute H_sequential_tasks
            tsk j ARR TSK POS t1 t2 BUSY R₀ HLT
      _ ≤ workload_of_jobs
            (fun jo => hep_job jo j && decide (job_task (Task := Task) jo ≠ tsk))
            (arrivals_between arr_seq t1 (t1 + R₀)) :=
          total_service_is_bounded_by_total_workload
            arr_seq H_arrival_times_are_consistent sched
            H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute
            tsk j ARR TSK t1 t2 BUSY R₀ HLT
      _ ≤ ((ts.filter (fun tsk_o => decide (tsk_o ≠ tsk))).map
            (fun tsk_o => workload_of_jobs
              (fun jo => hep_job jo j && decide (job_task (Task := Task) jo = tsk_o))
              (arrivals_between arr_seq t1 (t1 + R₀)))).sum :=
          reorder_summation
            arr_seq H_arrival_times_are_consistent sched ts H_all_jobs_from_taskset
            tsk j ARR TSK t1 t2 BUSY R₀
      _ ≤ bound_on_total_hep_workload tsk ts (job_arrival j - t1) R₀ :=
          sum_of_workloads_is_at_most_bound_on_total_hep_workload
            arr_seq H_arrival_times_are_consistent H_arr_seq_is_a_set sched
            H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute
            H_completed_jobs_dont_execute H_sequential_tasks
            H_valid_job_cost ts H_all_jobs_from_taskset H_is_arrival_curve
            tsk j ARR TSK POS t1 t2 BUSY R₀ HLT
  calc Prosa.Analysis.Abstract.Abstract_seq_rta.cumul_task_interference
        arr_seq sched tsk (Prosa.Analysis.Abstract.Ideal_jlfp_rta.interference sched) t2 t1 (t1 + R₀)
      ≤ Prosa.Analysis.Abstract.Ideal_jlfp_rta.cumulative_priority_inversion sched j t1 (t1 + R₀) +
        Prosa.Analysis.Abstract.Ideal_jlfp_rta.cumulative_interference_from_hep_jobs_from_other_tasks
          (Task := Task) sched j t1 (t1 + R₀) := h_decomp
    _ ≤ priority_inversion_bound + bound_on_total_hep_workload tsk ts (job_arrival j - t1) R₀ :=
        Nat.add_le_add h_pi_bound h_other_bound

end TaskInterferenceIsBoundedByIBF

section SolutionOfResponseTimeReccurenceExists

variable (j : Job)
variable (H_j_arrives : arrives_in arr_seq j)
variable (H_job_of_tsk : job_of_task tsk j = true)
variable (H_job_cost_positive : job_cost_positive j)

noncomputable def total_interference_bound_fn
    (tsk : Task) [TaskDeadline Task] [TaskCost Task] [MaxArrivals Task]
    [TaskRunToCompletionThreshold Task]
    (ts : List Task) (priority_inversion_bound : duration)
    (A Δ : duration) :=
  task_request_bound_function tsk (A + ε) - task_cost tsk +
    (priority_inversion_bound + bound_on_total_hep_workload tsk ts A Δ)

variable (A : duration)
variable (H_A_is_in_abstract_search_space :
  Prosa.Analysis.Abstract.Search_space.is_in_search_space tsk L
    (fun tsk' A' R' =>
      total_interference_bound_fn tsk' ts priority_inversion_bound A' R') A)

include H_arrival_times_are_consistent H_valid_job_cost
  H_valid_arrival_curve H_is_arrival_curve H_tsk_in_ts H_L_positive
  H_R_is_maximum j H_j_arrives H_job_of_tsk H_job_cost_positive
  H_A_is_in_abstract_search_space in
lemma A_is_in_concrete_search_space :
    is_in_search_space_edf tsk ts L A = true := by
  -- Helper: monotone function with f(a)=f(b) gives f(min(a,x))=f(min(b,x))
  have h_mono_min : ∀ (f : Nat → Nat) (a b x : Nat),
      (∀ u v : Nat, u ≤ v → f u ≤ f v) → a ≤ b → f a = f b →
      f (min a x) = f (min b x) := by
    intro f a b x hmon hab heq
    rcases le_or_gt a x with hax | hax
    · rcases le_or_gt b x with hbx | hbx
      · rw [min_eq_left hax, min_eq_left hbx, heq]
      · rw [min_eq_left hax, min_eq_right (le_of_lt hbx)]
        exact le_antisymm (hmon _ _ hax) (heq ▸ hmon _ _ (le_of_lt hbx))
    · rw [min_eq_right (le_of_lt hax), min_eq_right (le_trans (le_of_lt hax) hab)]
  rcases H_A_is_in_abstract_search_space with INSP | ⟨⟨POSA, LTL⟩, x, LTx, INSP2⟩
  · -- Case 1: A = 0
    subst INSP
    simp only [is_in_search_space_edf, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true]
    refine ⟨H_L_positive, Or.inl ?_⟩
    simp only [task_rbf_changes_at, decide_eq_true_eq]
    have h0 := task_rbf_0_zero arr_seq H_arrival_times_are_consistent tsk
      (H_valid_arrival_curve tsk H_tsk_in_ts) (H_is_arrival_curve tsk H_tsk_in_ts)
    have h_tsk_of_j : job_task (Task := Task) j = tsk := by
      have h := H_job_of_tsk; simp only [job_of_task, beq_iff_eq] at h; exact h
    have h1 := task_rbf_1_ge_task_cost arr_seq H_arrival_times_are_consistent tsk
      (H_valid_arrival_curve tsk H_tsk_in_ts) (H_is_arrival_curve tsk H_tsk_in_ts)
      j H_j_arrives h_tsk_of_j
    have hvc : job_cost j ≤ task_cost tsk := by
      have := H_valid_job_cost j H_j_arrives
      simp [valid_job_cost, h_tsk_of_j] at this; exact this
    have hjcp : job_cost j > 0 := H_job_cost_positive
    intro heq; simp [ε] at heq; rw [h0] at heq
    -- heq : 0 = task_request_bound_function tsk 1
    exact absurd (le_trans hvc (le_trans h1 (le_of_eq heq.symm))) (not_le_of_gt hjcp)
  · -- Case 2: 0 < A ∧ A < L, ∃ x, ibf differs at x
    simp only [is_in_search_space_edf, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true]
    refine ⟨LTL, ?_⟩
    -- By contradiction assume neither changes
    by_contra h_neg; push_neg at h_neg
    obtain ⟨h_norb, h_nohep⟩ := h_neg
    -- Convert ≠ true to = false
    have h_no_rbf_change : task_rbf_changes_at tsk A = false := by
      revert h_norb; cases task_rbf_changes_at tsk A <;> simp
    have h_no_hep_change : bound_on_total_hep_workload_changes_at tsk ts A = false := by
      revert h_nohep; cases bound_on_total_hep_workload_changes_at tsk ts A <;> simp
    -- Extract task_rbf equality
    have h_rbf_eq : task_request_bound_function tsk A = task_request_bound_function tsk (A + ε) := by
      unfold task_rbf_changes_at at h_no_rbf_change
      rw [decide_eq_false_iff_not, not_not] at h_no_rbf_change
      exact h_no_rbf_change
    -- Extract per-task hep_workload equality
    have h_no_hep_list : ∀ tsk_o ∈ ts, tsk ≠ tsk_o →
        task_request_bound_function tsk_o (A + task_deadline tsk - task_deadline tsk_o) =
        task_request_bound_function tsk_o ((A + ε) + task_deadline tsk - task_deadline tsk_o) := by
      intro tsk_o htsko_in hneq
      by_contra h_diff
      have : bound_on_total_hep_workload_changes_at tsk ts A = true := by
        simp only [bound_on_total_hep_workload_changes_at, List.any_eq_true,
          Bool.and_eq_true, decide_eq_true_eq]
        exact ⟨tsk_o, htsko_in, hneq, h_diff⟩
      simp [this] at h_no_hep_change
    -- Show ibf(A-ε, x) = ibf(A, x) contradicting INSP2
    apply INSP2
    show total_interference_bound_fn tsk ts priority_inversion_bound (A - ε) x =
      total_interference_bound_fn tsk ts priority_inversion_bound A x
    simp only [total_interference_bound_fn]
    have hAε : A - ε + ε = A := Nat.sub_add_cancel POSA
    rw [hAε, h_rbf_eq]
    -- Remaining: bound_on_total_hep_workload(A-ε, x) = bound_on_total_hep_workload(A, x)
    congr 1; congr 1
    simp only [bound_on_total_hep_workload, hAε]
    -- Per-task equality: strip .sum then use map_congr_left
    congr 1
    apply List.map_congr_left
    intro tsk_o htsk_o
    have hneq : tsk_o ≠ tsk := by
      rw [List.mem_filter] at htsk_o; exact of_decide_eq_true htsk_o.2
    have htsko_in : tsk_o ∈ ts := by
      rw [List.mem_filter] at htsk_o; exact htsk_o.1
    have h_eq_rbf := h_no_hep_list tsk_o htsko_in hneq.symm
    have hab : A + task_deadline tsk - task_deadline tsk_o ≤
               (A + ε) + task_deadline tsk - task_deadline tsk_o :=
      Nat.sub_le_sub_right (Nat.add_le_add_right (Nat.le_add_right A ε) _) _
    have h_rbf_mono : ∀ u v : Nat, u ≤ v →
        task_request_bound_function tsk_o u ≤ task_request_bound_function tsk_o v := by
      intro u v huv
      have := task_rbf_monotone arr_seq H_arrival_times_are_consistent tsk_o
        (H_valid_arrival_curve tsk_o htsko_in) (H_is_arrival_curve tsk_o htsko_in)
      simp only [Prosa.Util.Rel.monotone, Nat.ble_eq, decide_eq_true_eq] at this
      exact this u v huv
    exact h_mono_min _ _ _ x h_rbf_mono hab h_eq_rbf

include H_arrival_times_are_consistent H_valid_job_cost
  H_valid_arrival_curve H_is_arrival_curve H_tsk_in_ts H_L_positive
  H_R_is_maximum j H_j_arrives H_job_of_tsk H_job_cost_positive
  H_A_is_in_abstract_search_space in
theorem correct_search_space :
    ∃ F,
      A + F = task_request_bound_function tsk (A + ε) -
                (task_cost tsk - task_run_to_completion_threshold tsk) +
              (priority_inversion_bound +
                bound_on_total_hep_workload tsk ts A (A + F)) ∧
      F + (task_cost tsk - task_run_to_completion_threshold tsk) ≤ R := by
  have hCSS : is_in_search_space_edf tsk ts L A = true :=
    A_is_in_concrete_search_space arr_seq H_arrival_times_are_consistent
      H_valid_job_cost ts H_valid_arrival_curve H_is_arrival_curve tsk H_tsk_in_ts
      priority_inversion_bound L H_L_positive R H_R_is_maximum
      j H_j_arrives H_job_of_tsk H_job_cost_positive A H_A_is_in_abstract_search_space
  have FIX := H_R_is_maximum A hCSS
  obtain ⟨F, hFIX, hNEQ⟩ := FIX
  refine ⟨F, ?_, hNEQ⟩
  rw [Nat.add_comm priority_inversion_bound, Nat.add_assoc] at hFIX
  exact hFIX

end SolutionOfResponseTimeReccurenceExists

end FillingOutHypothesesOfAbstractRTATheorem

include H_arrival_times_are_consistent H_arr_seq_is_a_set
  H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute
  H_completed_jobs_dont_execute H_work_conserving H_sequential_tasks
  H_valid_job_cost H_all_jobs_from_taskset H_valid_arrival_curve H_is_arrival_curve
  H_tsk_in_ts H_valid_preemption_model H_valid_run_to_completion_threshold
  H_priority_inversion_is_bounded H_L_positive H_fixed_point H_R_is_maximum in
theorem uniprocessor_response_time_bound_edf :
    task_response_time_bound arr_seq sched tsk R := by
  intro js ARRs TSKs
  by_cases POS : job_cost js > 0
  · have h_wc : Prosa.Analysis.Abstract.Definitions.work_conserving arr_seq sched tsk
        (Prosa.Analysis.Abstract.Ideal_jlfp_rta.interference sched)
        (Prosa.Analysis.Abstract.Ideal_jlfp_rta.interfering_workload arr_seq sched) :=
      instantiated_i_and_w_are_coherent_with_schedule
        arr_seq H_arrival_times_are_consistent H_arr_seq_is_a_set sched
        H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute
        H_completed_jobs_dont_execute H_work_conserving H_sequential_tasks tsk
    have h_seq : Prosa.Analysis.Abstract.Abstract_seq_rta.interference_and_workload_consistent_with_sequential_tasks
        arr_seq sched tsk
        (Prosa.Analysis.Abstract.Ideal_jlfp_rta.interference sched)
        (Prosa.Analysis.Abstract.Ideal_jlfp_rta.interfering_workload arr_seq sched) :=
      instantiated_interference_and_workload_consistent_with_sequential_tasks
        arr_seq H_arrival_times_are_consistent H_arr_seq_is_a_set sched
        H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute
        H_completed_jobs_dont_execute H_sequential_tasks tsk
    have h_busy : Prosa.Analysis.Abstract.Definitions.busy_intervals_are_bounded_by arr_seq sched tsk
        (Prosa.Analysis.Abstract.Ideal_jlfp_rta.interference sched)
        (Prosa.Analysis.Abstract.Ideal_jlfp_rta.interfering_workload arr_seq sched) L :=
      instantiated_busy_intervals_are_bounded
        arr_seq H_arrival_times_are_consistent H_arr_seq_is_a_set sched
        H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute
        H_completed_jobs_dont_execute H_work_conserving H_sequential_tasks
        H_valid_job_cost ts H_all_jobs_from_taskset H_is_arrival_curve tsk H_tsk_in_ts
        L H_L_positive H_fixed_point
    have h_tib : Prosa.Analysis.Abstract.Abstract_seq_rta.task_interference_is_bounded_by
        arr_seq sched tsk
        (Prosa.Analysis.Abstract.Ideal_jlfp_rta.interference sched)
        (Prosa.Analysis.Abstract.Ideal_jlfp_rta.interfering_workload arr_seq sched)
        (fun _ A R₀ => priority_inversion_bound + bound_on_total_hep_workload tsk ts A R₀) :=
      instantiated_task_interference_is_bounded
        arr_seq H_arrival_times_are_consistent H_arr_seq_is_a_set sched
        H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute
        H_completed_jobs_dont_execute H_sequential_tasks
        H_valid_job_cost ts H_all_jobs_from_taskset H_is_arrival_curve
        tsk priority_inversion_bound H_priority_inversion_is_bounded
    exact Prosa.Analysis.Abstract.Abstract_seq_rta.uniprocessor_response_time_bound_seq
      arr_seq H_arrival_times_are_consistent H_arr_seq_is_a_set sched
      H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute
      H_completed_jobs_dont_execute H_valid_job_cost ts tsk H_tsk_in_ts
      H_valid_preemption_model H_valid_run_to_completion_threshold
      H_valid_arrival_curve H_is_arrival_curve
      (Prosa.Analysis.Abstract.Ideal_jlfp_rta.interference sched)
      (Prosa.Analysis.Abstract.Ideal_jlfp_rta.interfering_workload arr_seq sched)
      h_wc H_sequential_tasks h_seq L h_busy
      (fun _ A R₀ => priority_inversion_bound + bound_on_total_hep_workload tsk ts A R₀)
      h_tib R
      (fun A INSP => correct_search_space arr_seq H_arrival_times_are_consistent
        H_valid_job_cost ts H_valid_arrival_curve H_is_arrival_curve tsk H_tsk_in_ts
        priority_inversion_bound L H_L_positive R H_R_is_maximum
        js ARRs (by rw [job_of_task]; simp [TSKs]) POS A INSP)
      js ARRs TSKs
  · simp only [not_lt, Nat.le_zero] at POS
    show completed_by sched js (job_arrival js + R)
    unfold completed_by; rw [POS]; exact Nat.zero_le _

end AbstractRTAforEDFwithArrivalCurves

end Prosa.Results.Edf.Rta.Bounded_pi
