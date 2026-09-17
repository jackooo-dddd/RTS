-- Translated from: ../rt-proofs/results/edf/rta/bounded_nps.v
import Prosa.Model.Priority.Edf
import Prosa.Analysis.Facts.Model.Rbf
import Prosa.Analysis.Facts.Model.Sequential
import Prosa.Results.Edf.Rta.Bounded_pi
import Prosa.Analysis.Facts.Busy_interval.Priority_inversion
import Prosa.Model.Processor.Ideal
import Prosa.Model.Readiness.Basic
import Prosa.Analysis.Definitions.Schedulability
import Prosa.Analysis.Definitions.Request_bound_function
import Prosa.Analysis.Definitions.Priority_inversion
import Prosa.Model.Task.Absolute_deadline
import Prosa.Model.Schedule.Priority_driven
import Prosa.Model.Schedule.Work_conserving
import Prosa.Util.Epsilon
import Prosa.Util.Minmax

namespace Prosa.Results.Edf.Rta.Bounded_nps

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
open Prosa.Model.Task.Arrival.Curves
open Prosa.Model.Readiness.Basic
open Prosa.Model.Schedule.Work_conserving
open Prosa.Model.Schedule.Priority_driven
open Prosa.Analysis.Definitions.Schedulability
open Prosa.Analysis.Definitions.Job_properties
open Prosa.Analysis.Definitions.Request_bound_function
open Prosa.Analysis.Definitions.Priority_inversion
open Prosa.Analysis.Facts.Busy_interval.Priority_inversion
open Prosa.Results.Edf.Rta.Bounded_pi
open Prosa.Analysis.Facts.Behavior.Arrivals
open Prosa.Util.Epsilon
open Prosa.Util.Minmax

section RTAforEDFwithBoundedNonpreemptiveSegmentsWithArrivalCurves

variable {Task : TaskType}
variable [TaskCost Task]
variable [TaskDeadline Task]
variable [TaskRunToCompletionThreshold Task]
variable [TaskMaxNonpreemptiveSegment Task]

variable {Job : JobType}
variable [DecidableEq Job]
variable [JobTask Job Task]
variable [JobArrival Job]
variable [JobCost Job]

variable [DecidableEq Task]

set_option synthInstance.checkSynthOrder false in
noncomputable local instance : JobDeadline Job := job_deadline_from_task_deadline Job Task
attribute [local instance] pstate_instance
attribute [local instance] basic_ready_instance
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

variable [JobPreemptable Job]

variable (H_valid_model_with_bounded_nonpreemptive_segments :
  valid_model_with_bounded_nonpreemptive_segments (Task := Task) arr_seq sched)

variable (H_sequential_tasks : sequential_tasks (Job := Job) (Task := Task) sched)

variable (H_work_conserving : work_conserving arr_seq sched)

variable (H_respects_policy : respects_policy_at_preemption_point arr_seq sched)

variable (ts : List Task)

variable (H_all_jobs_from_taskset : all_jobs_from_taskset arr_seq ts)

variable (H_valid_job_cost : arrivals_have_valid_job_costs (Task := Task) arr_seq)

variable [MaxArrivals Task]
variable (H_valid_arrival_curve : valid_taskset_arrival_curve ts max_arrivals)
variable (H_is_arrival_curve : taskset_respects_max_arrivals arr_seq ts)

variable (tsk : Task)
variable (H_tsk_in_ts : tsk ∈ ts)

variable (H_valid_preemption_model : valid_preemption_model arr_seq sched)

variable (H_valid_run_to_completion_threshold :
  valid_task_run_to_completion_threshold arr_seq tsk)

noncomputable def blocking_bound
    {Task : TaskType} [TaskDeadline Task] [TaskMaxNonpreemptiveSegment Task]
    [DecidableEq Task]
    (tsk : Task) (ts : List Task) : Nat :=
  bigMaxListCond ts
    (fun tsk_o => tsk_o ≠ tsk ∧ task_deadline tsk < task_deadline tsk_o)
    (fun tsk_o => task_max_nonpreemptive_segment tsk_o - ε)

section PriorityInversionIsBounded

include H_arrival_times_are_consistent H_valid_model_with_bounded_nonpreemptive_segments
  H_all_jobs_from_taskset in
lemma priority_inversion_is_bounded_by_blocking :
    ∀ (j : Job) (t : instant),
      arrives_in arr_seq j →
      job_task j = tsk →
      t ≤ job_arrival j →
      max_length_of_priority_inversion arr_seq j t ≤ blocking_bound tsk ts := by
  intro j t ARR TSK HTLE
  unfold max_length_of_priority_inversion blocking_bound
  rw [bigmax_leq_seqP]
  intro j' JINB NOTHEP
  have ARR' : arrives_in arr_seq j' := by
    unfold arrivals_before arrivals_between at JINB
    simp only [arrivals_at, Prosa.Util.Notation.bigCat, List.mem_flatten, List.mem_map] at JINB
    obtain ⟨l, ⟨i, _, rfl⟩, hj⟩ := JINB
    exact ⟨0 + i, hj⟩
  have RESP : job_respects_max_nonpreemptive_segment (Task := Task) j' :=
    (H_valid_model_with_bounded_nonpreemptive_segments.2 j' ARR').1
  have JT_IN : job_task (Task := Task) j' ∈ ts := H_all_jobs_from_taskset j' ARR'
  -- Key EDF step: derive blocking_bound filter condition for job_task j'
  have NOTHEP_TASK : (job_task (Task := Task) j') ≠ tsk ∧
      task_deadline tsk < task_deadline (job_task (Task := Task) j') := by
    constructor
    · -- job_task j' ≠ tsk: if job_task j' = tsk, then j' is hep to j
      intro h_eq
      apply NOTHEP
      -- j' arriving before t ≤ arr j means arr j' < arr j (since j' ∈ arrivals_before t)
      -- With same task (h_eq), job_deadline j' = arr j' + task_deadline tsk
      -- job_deadline j = arr j + task_deadline tsk
      -- Since arr j' ≤ arr j, job_deadline j' ≤ job_deadline j, so hep_job j' j
      simp only [hep_job, EDF, Nat.ble_eq]
      change job_arrival j' + task_deadline (job_task (Task := Task) j') ≤
          job_arrival j + task_deadline (job_task (Task := Task) j)
      rw [h_eq, TSK]
      have hj'_before := in_arrivals_implies_arrived_between arr_seq
        H_arrival_times_are_consistent j' 0 t JINB
      have : job_arrival j' < t := hj'_before.2
      exact Nat.add_le_add_right (le_trans (le_of_lt this) HTLE) _
    · -- task_deadline tsk < task_deadline (job_task j')
      -- From NOTHEP: ¬hep_job j' j, i.e., job_deadline j' > job_deadline j
      -- job_deadline j' = arr j' + deadline(task j'), job_deadline j = arr j + deadline tsk
      -- Since arr j' < arr j, we get deadline(task j') > deadline tsk + (arr j - arr j') > deadline tsk
      by_contra h_not
      push_neg at h_not
      apply NOTHEP
      simp only [hep_job, EDF, Nat.ble_eq]
      change job_arrival j' + task_deadline (job_task (Task := Task) j') ≤
          job_arrival j + task_deadline (job_task (Task := Task) j)
      rw [TSK]
      have hj'_before := in_arrivals_implies_arrived_between arr_seq
        H_arrival_times_are_consistent j' 0 t JINB
      have hj'_lt : job_arrival j' < t := hj'_before.2
      exact le_trans (Nat.add_le_add_left h_not _) (Nat.add_le_add_right (le_trans (le_of_lt hj'_lt) HTLE) _)
  calc job_max_nonpreemptive_segment j' - ε
      ≤ task_max_nonpreemptive_segment (job_task (Task := Task) j') - ε :=
        Nat.sub_le_sub_right RESP ε
    _ ≤ bigMaxListCond ts
          (fun tsk_o => tsk_o ≠ tsk ∧ task_deadline tsk < task_deadline tsk_o)
          (fun tsk_o => task_max_nonpreemptive_segment tsk_o - ε) :=
        leq_bigmax_cond_seq
          (fun tsk_o => tsk_o ≠ tsk ∧ task_deadline tsk < task_deadline tsk_o) ts
          (fun tsk_o => task_max_nonpreemptive_segment tsk_o - ε)
          (job_task (Task := Task) j') JT_IN NOTHEP_TASK

include H_arrival_times_are_consistent
  H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute
  H_completed_jobs_dont_execute
  H_valid_model_with_bounded_nonpreemptive_segments
  H_work_conserving H_respects_policy
  H_all_jobs_from_taskset in
lemma priority_inversion_is_bounded :
    priority_inversion_is_bounded_by arr_seq sched tsk (blocking_bound tsk ts) := by
  intro j ARR TSK POS t1 t2 PREF
  have HLT : t1 < t2 := PREF.1
  by_cases NEQ : t2 - t1 ≤ blocking_bound tsk ts
  · apply le_trans _ NEQ
    unfold cumulative_priority_inversion
    have hle1 : ∀ t, t ∈ Finset.Ico t1 t2 → (is_priority_inversion sched j t).toNat ≤ 1 := by
      intro t _
      unfold is_priority_inversion
      cases sched t with
      | none => simp
      | some s => cases h : hep_job s j <;> simp [h]
    calc ∑ t ∈ Finset.Ico t1 t2, (is_priority_inversion sched j t).toNat
        ≤ ∑ _t ∈ Finset.Ico t1 t2, 1 := Finset.sum_le_sum hle1
      _ = (Finset.Ico t1 t2).card := by simp
      _ = t2 - t1 := by simp
  · push_neg at NEQ
    have HBOUND_LT : t1 + blocking_bound tsk ts < t2 := by
      have h1 : t1 ≤ t2 := le_of_lt HLT
      rw [Nat.add_comm]
      exact Nat.lt_of_lt_of_le (Nat.add_lt_add_right NEQ t1) (le_of_eq (Nat.sub_add_cancel h1))
    have ⟨ppt, PPT, GE, LE⟩ := preemption_time_exists arr_seq H_arrival_times_are_consistent
      sched H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute
      H_completed_jobs_dont_execute
      (Prosa.Model.Priority.Edf.EDF_is_reflexive (Job := Job))
      (Prosa.Model.Priority.Edf.EDF_is_transitive (Job := Job))
      H_valid_model_with_bounded_nonpreemptive_segments H_work_conserving H_respects_policy
      j ARR POS t1 t2 PREF
    have PIBOUND := priority_inversion_is_bounded_by_blocking arr_seq
      H_arrival_times_are_consistent sched
      H_valid_model_with_bounded_nonpreemptive_segments ts H_all_jobs_from_taskset tsk j t1
      ARR TSK PREF.2.2.2.1
    have LE' : ppt ≤ t1 + blocking_bound tsk ts :=
      le_trans LE (Nat.add_le_add_left PIBOUND t1)
    have PPT_LT_T2 : ppt < t2 := Nat.lt_of_le_of_lt LE' HBOUND_LT
    have H_t1_le_ppt : t1 ≤ ppt := GE
    have PPT_BOUND : ppt - t1 ≤ blocking_bound tsk ts :=
      Nat.sub_le_of_le_add (show ppt ≤ blocking_bound tsk ts + t1 from Nat.add_comm t1 _ ▸ LE')
    unfold cumulative_priority_inversion
    rw [show Finset.Ico t1 t2 = Finset.Ico t1 ppt ∪ Finset.Ico ppt t2 from
      (Finset.Ico_union_Ico_eq_Ico H_t1_le_ppt (le_of_lt PPT_LT_T2)).symm]
    rw [Finset.sum_union (Finset.Ico_disjoint_Ico_consecutive t1 ppt t2)]
    suffices h1 : ∑ t ∈ Finset.Ico t1 ppt, (is_priority_inversion sched j t).toNat
        ≤ blocking_bound tsk ts by
      suffices h2 : ∑ t ∈ Finset.Ico ppt t2, (is_priority_inversion sched j t).toNat = 0 by
        rw [h2]; omega
      apply Finset.sum_eq_zero
      intro t ht
      simp only [Finset.mem_Ico] at ht
      unfold is_priority_inversion
      have ⟨j_hp, _, HP, SCHEDHP⟩ :=
        not_quiet_implies_exists_scheduled_hp_job arr_seq H_arrival_times_are_consistent
          sched H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute
          H_completed_jobs_dont_execute
          (Prosa.Model.Priority.Edf.EDF_is_reflexive (Job := Job))
          (Prosa.Model.Priority.Edf.EDF_is_transitive (Job := Job))
          H_valid_model_with_bounded_nonpreemptive_segments H_work_conserving H_respects_policy
          j ARR POS t1 t2 PREF (ppt - t1) ⟨ppt, PPT, GE, le_of_eq (Nat.add_sub_cancel' GE).symm⟩
          t (by refine ⟨?_, ht.2⟩; rw [Nat.add_sub_cancel' GE]; exact ht.1)
      cases hsched : sched t with
      | none =>
        exfalso
        rw [Prosa.Analysis.Facts.Model.Ideal_schedule.scheduled_at_def] at SCHEDHP
        simp [hsched] at SCHEDHP
      | some s =>
        have EQ : s = j_hp :=
          Prosa.Analysis.Facts.Model.Ideal_schedule.ideal_proc_model_is_a_uniprocessor_model
            s j_hp sched t
            (by rw [Prosa.Analysis.Facts.Model.Ideal_schedule.scheduled_at_def]; simp [hsched])
            SCHEDHP
        rw [EQ]; simp [HP]
    calc ∑ t ∈ Finset.Ico t1 ppt, (is_priority_inversion sched j t).toNat
        ≤ ∑ _t ∈ Finset.Ico t1 ppt, 1 := by
          apply Finset.sum_le_sum
          intro t _; unfold is_priority_inversion
          cases sched t with
          | none => simp
          | some s => cases h : hep_job s j <;> simp [h]
      _ = (Finset.Ico t1 ppt).card := by simp
      _ = ppt - t1 := by simp
      _ ≤ blocking_bound tsk ts := PPT_BOUND

end PriorityInversionIsBounded

section ResponseTimeBound

variable (L : duration)
variable (H_L_positive : L > 0)
variable (H_fixed_point : L = total_request_bound_function ts L)

variable (R : duration)
variable (H_R_is_maximum :
  ∀ (A : duration),
    is_in_search_space_edf tsk ts L A = true →
    ∃ (F : duration),
      A + F = blocking_bound tsk ts
              + (task_request_bound_function tsk (A + ε) -
                  (task_cost tsk - task_run_to_completion_threshold tsk))
              + bound_on_total_hep_workload tsk ts A (A + F) ∧
      F + (task_cost tsk - task_run_to_completion_threshold tsk) ≤ R)

include H_arrival_times_are_consistent H_arr_seq_is_a_set
  H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute
  H_completed_jobs_dont_execute
  H_valid_model_with_bounded_nonpreemptive_segments
  H_sequential_tasks H_work_conserving H_respects_policy
  H_all_jobs_from_taskset H_valid_job_cost
  H_valid_arrival_curve H_is_arrival_curve
  H_tsk_in_ts H_valid_preemption_model
  H_valid_run_to_completion_threshold
  H_L_positive H_fixed_point H_R_is_maximum in
theorem uniprocessor_response_time_bound_edf_with_bounded_nonpreemptive_segments :
    task_response_time_bound arr_seq sched tsk R := by
  exact Prosa.Results.Edf.Rta.Bounded_pi.uniprocessor_response_time_bound_edf
    arr_seq H_arrival_times_are_consistent H_arr_seq_is_a_set sched
    H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute
    H_completed_jobs_dont_execute H_work_conserving H_sequential_tasks
    H_valid_job_cost ts H_all_jobs_from_taskset H_valid_arrival_curve
    H_is_arrival_curve tsk H_tsk_in_ts H_valid_preemption_model
    H_valid_run_to_completion_threshold
    (blocking_bound tsk ts)
    (priority_inversion_is_bounded arr_seq H_arrival_times_are_consistent
      sched H_jobs_come_from_arrival_sequence
      H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute
      H_valid_model_with_bounded_nonpreemptive_segments H_work_conserving
      H_respects_policy ts H_all_jobs_from_taskset tsk)
    L H_L_positive H_fixed_point R H_R_is_maximum

end ResponseTimeBound

end RTAforEDFwithBoundedNonpreemptiveSegmentsWithArrivalCurves

end Prosa.Results.Edf.Rta.Bounded_nps
