-- Translated from: ../rt-proofs/results/fixed_priority/rta/bounded_nps.v
import Prosa.Analysis.Definitions.Schedulability
import Prosa.Analysis.Definitions.Request_bound_function
import Prosa.Analysis.Facts.Model.Sequential
import Prosa.Analysis.Facts.Busy_interval.Priority_inversion
import Prosa.Results.Fixed_priority.Rta.Bounded_pi
import Prosa.Model.Processor.Ideal
import Prosa.Model.Readiness.Basic
import Prosa.Model.Task.Arrival.Curves

namespace Prosa.Results.Fixed_priority.Rta.Bounded_nps

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
open Prosa.Model.Schedule.Work_conserving
open Prosa.Model.Schedule.Priority_driven
open Prosa.Analysis.Definitions.Priority_inversion
open Prosa.Analysis.Definitions.Job_properties
open Prosa.Analysis.Definitions.Schedulability
open Prosa.Analysis.Definitions.Request_bound_function
open Prosa.Analysis.Facts.Busy_interval.Priority_inversion
open Prosa.Util.Epsilon
open Prosa.Util.Minmax

section RTAforFPwithBoundedNonpreemptiveSegmentsWithArrivalCurves

variable {Task : TaskType}
variable [TaskCost Task]
variable [TaskRunToCompletionThreshold Task]
variable [TaskMaxNonpreemptiveSegment Task]
variable [DecidableEq Task]

variable {Job : JobType}
variable [DecidableEq Job]
variable [JobTask Job Task]
variable [JobArrival Job]
variable [JobCost Job]

variable (arr_seq : arrival_sequence Job)
variable (H_arrival_times_are_consistent : consistent_arrival_times arr_seq)
variable (H_arr_seq_is_a_set : arrival_sequence_uniq arr_seq)

attribute [local instance] pstate_instance

variable (sched : schedule (processor_state Job))
variable (H_jobs_come_from_arrival_sequence :
  jobs_come_from_arrival_sequence (Job := Job) sched arr_seq)

variable (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute (Job := Job) sched)
variable (H_completed_jobs_dont_execute : completed_jobs_dont_execute (Job := Job) sched)

variable [JobPreemptable Job]

variable (H_valid_model_with_bounded_nonpreemptive_segments :
  valid_model_with_bounded_nonpreemptive_segments (Task := Task) arr_seq sched)

variable [FP_policy Task]

set_option synthInstance.checkSynthOrder false in
noncomputable local instance : JLFP_policy Job := FP_to_JLFP Job Task
set_option synthInstance.checkSynthOrder false in
noncomputable local instance : JLDP_policy Job := JLFP_to_JLDP Job

variable (H_priority_is_reflexive : reflexive_priorities (Job := Job))
variable (H_priority_is_transitive : transitive_priorities (Job := Job))

variable (H_sequential_tasks : sequential_tasks (Job := Job) (Task := Task) sched)

variable (H_work_conserving : work_conserving arr_seq sched)

variable (H_respects_policy :
  respects_policy_at_preemption_point arr_seq sched)

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

noncomputable def blocking_bound : Nat :=
  bigMaxListCond ts
    (fun tsk_other => ¬(hep_task tsk_other tsk = true))
    (fun tsk_other => task_max_nonpreemptive_segment tsk_other - ε)

section PriorityInversionIsBounded

include H_valid_model_with_bounded_nonpreemptive_segments
  H_all_jobs_from_taskset in
theorem priority_inversion_is_bounded_by_blocking :
    ∀ j t,
      arrives_in arr_seq j →
      job_task j = tsk →
      max_length_of_priority_inversion arr_seq j t ≤ blocking_bound ts tsk := by
  intro j t ARR TSK
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
  have NOTHEP_TASK : ¬(hep_task (job_task (Task := Task) j') tsk = true) := by
    simp only [hep_job] at NOTHEP
    rw [TSK] at NOTHEP
    exact NOTHEP
  calc job_max_nonpreemptive_segment j' - ε
      ≤ task_max_nonpreemptive_segment (job_task (Task := Task) j') - ε :=
        Nat.sub_le_sub_right RESP ε
      _ ≤ bigMaxListCond ts (fun tsk_other => ¬(hep_task tsk_other tsk = true))
            (fun tsk_other => task_max_nonpreemptive_segment tsk_other - ε) :=
        leq_bigmax_cond_seq (fun tsk_other => ¬(hep_task tsk_other tsk = true)) ts
          (fun tsk_other => task_max_nonpreemptive_segment tsk_other - ε)
          (job_task (Task := Task) j') JT_IN NOTHEP_TASK

include H_arrival_times_are_consistent H_arr_seq_is_a_set
  H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute
  H_completed_jobs_dont_execute
  H_valid_model_with_bounded_nonpreemptive_segments
  H_priority_is_reflexive H_priority_is_transitive
  H_work_conserving H_respects_policy
  H_all_jobs_from_taskset in
theorem priority_inversion_is_bounded :
    priority_inversion_is_bounded_by
      arr_seq sched tsk (blocking_bound ts tsk) := by
  intro j ARR TSK POS t1 t2 PREF
  -- Extract t1 < t2 from PREF
  have HLT : t1 < t2 := PREF.1
  by_cases NEQ : t2 - t1 ≤ blocking_bound ts tsk
  · -- Case: t2 - t1 ≤ blocking_bound
    apply le_trans _ NEQ
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
  · -- Case: t2 - t1 > blocking_bound
    push_neg at NEQ
    -- NEQ : blocking_bound ts tsk < t2 - t1
    -- Since t1 < t2, we have t1 + blocking_bound < t2
    have HBOUND_LT : t1 + blocking_bound ts tsk < t2 := by
      have h1 : t1 ≤ t2 := le_of_lt HLT
      rw [Nat.add_comm]
      exact Nat.lt_of_lt_of_le (Nat.add_lt_add_right NEQ t1) (le_of_eq (Nat.sub_add_cancel h1))
    have ⟨ppt, PPT, GE, LE⟩ := preemption_time_exists arr_seq H_arrival_times_are_consistent
      sched H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute
      H_completed_jobs_dont_execute H_priority_is_reflexive H_priority_is_transitive
      H_valid_model_with_bounded_nonpreemptive_segments H_work_conserving H_respects_policy
      j ARR POS t1 t2 PREF
    have PIBOUND := priority_inversion_is_bounded_by_blocking arr_seq sched
      H_valid_model_with_bounded_nonpreemptive_segments ts H_all_jobs_from_taskset tsk j t1 ARR TSK
    have LE' : ppt ≤ t1 + blocking_bound ts tsk :=
      le_trans LE (Nat.add_le_add_left PIBOUND t1)
    have PPT_LT_T2 : ppt < t2 := Nat.lt_of_le_of_lt LE' HBOUND_LT
    have H_t1_le_ppt : t1 ≤ ppt := GE
    have PPT_BOUND : ppt - t1 ≤ blocking_bound ts tsk :=
      Nat.sub_le_of_le_add (show ppt ≤ blocking_bound ts tsk + t1 from Nat.add_comm t1 _ ▸ LE')
    unfold cumulative_priority_inversion
    rw [show Finset.Ico t1 t2 = Finset.Ico t1 ppt ∪ Finset.Ico ppt t2 from
      (Finset.Ico_union_Ico_eq_Ico H_t1_le_ppt (le_of_lt PPT_LT_T2)).symm]
    rw [Finset.sum_union (Finset.Ico_disjoint_Ico_consecutive t1 ppt t2)]
    suffices h1 : ∑ t ∈ Finset.Ico t1 ppt, (is_priority_inversion sched j t).toNat ≤ blocking_bound ts tsk by
      suffices h2 : ∑ t ∈ Finset.Ico ppt t2, (is_priority_inversion sched j t).toNat = 0 by
        rw [h2]; omega
      apply Finset.sum_eq_zero
      intro t ht
      simp only [Finset.mem_Ico] at ht
      unfold is_priority_inversion
      have ⟨j_hp, _, HP, SCHEDHP⟩ :=
        not_quiet_implies_exists_scheduled_hp_job arr_seq H_arrival_times_are_consistent
          sched H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute
          H_completed_jobs_dont_execute H_priority_is_reflexive H_priority_is_transitive
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
        rw [EQ]
        simp [HP]
    calc ∑ t ∈ Finset.Ico t1 ppt, (is_priority_inversion sched j t).toNat
        ≤ ∑ _t ∈ Finset.Ico t1 ppt, 1 := by
          apply Finset.sum_le_sum
          intro t _; unfold is_priority_inversion
          cases sched t with
          | none => simp
          | some s => cases h : hep_job s j <;> simp [h]
      _ = (Finset.Ico t1 ppt).card := by simp
      _ = ppt - t1 := by simp
      _ ≤ blocking_bound ts tsk := PPT_BOUND

end PriorityInversionIsBounded

section ResponseTimeBound

variable (L : duration)
variable (H_L_positive : L > 0)
variable (H_fixed_point : L = blocking_bound ts tsk + total_hep_request_bound_function_FP ts tsk L)

variable (R : duration)
variable (H_R_is_maximum :
  ∀ (A : duration),
    (A < L) && (task_request_bound_function tsk A != task_request_bound_function tsk (A + ε)) = true →
    ∃ (F : duration),
      A + F = blocking_bound ts tsk
              + (task_request_bound_function tsk (A + ε) - (task_cost tsk - task_run_to_completion_threshold tsk))
              + total_ohep_request_bound_function_FP ts tsk (A + F) ∧
      F + (task_cost tsk - task_run_to_completion_threshold tsk) ≤ R)

include H_arrival_times_are_consistent H_arr_seq_is_a_set
  H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute
  H_completed_jobs_dont_execute
  H_valid_model_with_bounded_nonpreemptive_segments
  H_priority_is_reflexive H_priority_is_transitive
  H_sequential_tasks H_work_conserving H_respects_policy
  H_all_jobs_from_taskset H_valid_job_cost
  H_valid_arrival_curve H_is_arrival_curve
  H_tsk_in_ts H_valid_preemption_model
  H_valid_run_to_completion_threshold
  H_L_positive H_fixed_point H_R_is_maximum in
theorem uniprocessor_response_time_bound_fp_with_bounded_nonpreemptive_segments :
    task_response_time_bound arr_seq sched tsk R := by
  exact Prosa.Results.Fixed_priority.Rta.Bounded_pi.uniprocessor_response_time_bound_fp
    arr_seq H_arrival_times_are_consistent H_arr_seq_is_a_set sched
    H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute
    H_completed_jobs_dont_execute H_work_conserving H_sequential_tasks
    H_valid_job_cost ts H_all_jobs_from_taskset H_valid_arrival_curve
    H_is_arrival_curve tsk H_tsk_in_ts H_valid_preemption_model
    H_valid_run_to_completion_threshold H_priority_is_reflexive
    H_priority_is_transitive
    (blocking_bound ts tsk)
    (priority_inversion_is_bounded arr_seq H_arrival_times_are_consistent
      H_arr_seq_is_a_set sched H_jobs_come_from_arrival_sequence
      H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute
      H_valid_model_with_bounded_nonpreemptive_segments H_priority_is_reflexive
      H_priority_is_transitive H_work_conserving H_respects_policy ts
      H_all_jobs_from_taskset tsk)
    L H_L_positive H_fixed_point R H_R_is_maximum

end ResponseTimeBound

end RTAforFPwithBoundedNonpreemptiveSegmentsWithArrivalCurves

end Prosa.Results.Fixed_priority.Rta.Bounded_nps
