-- Translated from: ../rt-proofs/analysis/facts/preemption/rtc_threshold/limited.v
import Prosa.Analysis.Facts.Preemption.Task.Limited
import Prosa.Analysis.Facts.Preemption.Rtc_threshold.Job_preemptable
import Prosa.Model.Preemption.Limited_preemptive
import Prosa.Model.Task.Preemption.Limited_preemptive

namespace Prosa.Analysis.Facts.Preemption.Rtc_threshold.Limited

open Prosa.Behavior.Job
open Prosa.Behavior.Time
open Prosa.Behavior.Service
open Prosa.Behavior.Schedule
open Prosa.Behavior.Arrival_sequence
open Prosa.Behavior.Ready
open Prosa.Model.Preemption.Parameter hiding distances job_preemption_points
open Prosa.Model.Preemption.Limited_preemptive
open Prosa.Model.Task.Preemption.Parameters
open Prosa.Model.Task.Preemption.Limited_preemptive
open Prosa.Model.Task.Concept
open Prosa.Model.Processor.Ideal
open Prosa.Model.Schedule.Limited_preemptive
open Prosa.Analysis.Facts.Preemption.Job.Limited
open Prosa.Analysis.Facts.Preemption.Rtc_threshold.Job_preemptable
open Prosa.Util.List
open Prosa.Util.Nondecreasing
open Prosa.Util.Epsilon

section TaskRTCThresholdLimitedPreemptions

variable {Task : TaskType}
variable [TaskCost Task]
variable [TaskPreemptionPoints Task]

variable {Job : JobType}
variable [JobTask Job Task]
variable [JobArrival Job]
variable [JobCost Job]
variable [DecidableEq Job]
variable [JobPreemptionPoints Job]

attribute [local instance] pstate_instance
attribute [local instance] limited_preemptions_model
attribute [local instance] limited_preemptions

variable (arr_seq : arrival_sequence Job)
variable (H_arrival_times_are_consistent : consistent_arrival_times arr_seq)

variable (sched : schedule (processor_state Job))
variable (H_schedule_respects_preemption_model :
    schedule_respects_preemption_model arr_seq sched)

variable (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute (Job := Job) sched)
variable (H_completed_jobs_dont_execute : completed_jobs_dont_execute (Job := Job) sched)

variable (ts : TaskSet Task)

variable (H_valid_job_cost :
    arrivals_have_valid_job_costs (Task := Task) arr_seq)

variable (H_valid_fixed_preemption_points_model :
    valid_fixed_preemption_points_model arr_seq ts)

variable (tsk : Task)
variable (H_tsk_in_ts : tsk ∈ ts)
variable (H_positive_cost : 0 < task_cost tsk)

include H_valid_fixed_preemption_points_model H_tsk_in_ts H_positive_cost in
theorem number_of_preemption_points_in_task_at_least_two :
    2 ≤ (task_preemption_points tsk).length := by
    obtain ⟨hbeg, hend, _⟩ := H_valid_fixed_preemption_points_model.2
    have h_first := hbeg tsk H_tsk_in_ts
    have h_last := hend tsk H_tsk_in_ts
    by_contra h
    push_neg at h
    have hlen : (task_preemption_points tsk).length ≤ 1 := by omega
    set pp := task_preemption_points tsk with hpp
    have h_eq : first0 pp = last0 pp := by
      rcases pp with _ | ⟨x, _ | ⟨y, t⟩⟩
      · simp [first0, last0, List.headD, List.getLastD]
      · simp [first0, last0, List.headD, List.getLastD]
      · simp at hlen
    have h12 := h_first.symm.trans h_eq
    have h13 := h12.trans h_last
    exact Nat.lt_irrefl 0 (h13.symm ▸ H_positive_cost)
private lemma nat_sub_pred_eq (a b : ℕ) (h1 : 1 ≤ b) (h2 : b ≤ a) :
    a - (b - 1) = a - b + 1 := by omega

include H_valid_fixed_preemption_points_model H_valid_job_cost
    H_tsk_in_ts H_positive_cost in
lemma limited_valid_task_run_to_completion_threshold :
    valid_task_run_to_completion_threshold arr_seq tsk := by
    constructor
    · exact Nat.sub_le _ _
    · intro j ARR TSK
      have LJ := H_valid_fixed_preemption_points_model.1
      obtain ⟨BEG_j, END_j, NDEC_j⟩ := H_valid_fixed_preemption_points_model.1
      obtain ⟨BEG_t, END_t, NDEC_t, T4, T5, T6⟩ := H_valid_fixed_preemption_points_model.2
      -- Parameter.distances and Nondecreasing.distances have identical definitions
      have hdist_eq : ∀ xs : List ℕ,
          Prosa.Model.Preemption.Parameter.distances xs = distances xs := fun _ => rfl
      rcases Nat.eq_zero_or_pos (job_cost j) with hzero | hpos
      · show job_cost j - (job_last_nonpreemptive_segment j - ε) ≤ _
        simp [hzero]
      · -- Model properties (about Limited_preemptive.job_preemption_points)
        have h_nd_j := NDEC_j j ARR
        have h_nd_t := NDEC_t tsk H_tsk_in_ts
        have h_end_j := END_j j ARR
        have h_end_t := END_t tsk H_tsk_in_ts
        have h_beg_j := BEG_j j ARR
        have h_ne_j : (job_preemption_points j) ≠ [] := by
          intro h; rw [h] at h_beg_j; exact List.not_mem_nil h_beg_j
        have h_len_j := number_of_preemption_points_at_least_two arr_seq LJ j ARR hpos
        have h_len_t := number_of_preemption_points_in_task_at_least_two
            arr_seq ts H_valid_fixed_preemption_points_model tsk H_tsk_in_ts H_positive_cost
        have h_len_eq : (job_preemption_points j).length =
            (task_preemption_points tsk).length := by
          have := T4 j ARR; rw [TSK] at this; exact this
        -- Distance domination
        have h_dom_dists : ∀ n,
            nthD (distances (job_preemption_points j)) n ≤
            nthD (distances (task_preemption_points tsk)) n := by
          intro n; simp only [nthD]
          have h := T5 j n ARR; rw [TSK] at h
          rw [← hdist_eq, ← hdist_eq]; exact h
        -- Sequence domination
        have h_first_jpp := nondec_seq_zero_first _ h_beg_j h_nd_j
        have h_first_tpp := BEG_t tsk H_tsk_in_ts
        have h_dom := domination_of_distances_implies_domination_of_seq
          (job_preemption_points j) (task_preemption_points tsk)
          (by rw [h_first_jpp, h_first_tpp])
          h_len_j h_len_t h_len_eq h_nd_j h_nd_t h_dom_dists
        -- Dedup properties
        have h_nd_dedup := nondecreasing_sequence_undup (job_preemption_points j) h_nd_j
        have h_last0_undup := last0_undup (job_preemption_points j) h_nd_j
        have h_last_mem_j : last0 (job_preemption_points j) ∈ job_preemption_points j := by
          obtain ⟨a, tl, hjpp⟩ := List.exists_cons_of_ne_nil h_ne_j
          rw [hjpp]; show (a :: tl).getLastD 0 ∈ a :: tl
          rw [List.getLastD_cons]; exact List.getLastD_mem_cons
        have h_dedup_len : 2 ≤ (job_preemption_points j).dedup.length :=
          subseq_leq_size [0, job_cost j] (job_preemption_points j).dedup
            (List.Nodup.cons (mt List.mem_singleton.mp (ne_of_gt hpos).symm) (List.nodup_singleton _))
            (by intro x hx; simp at hx
                rcases hx with rfl | rfl
                · exact List.mem_dedup.mpr h_beg_j
                · exact List.mem_dedup.mpr (by rw [← h_end_j]; exact h_last_mem_j))
        have h_dist_dedup_ne : distances (job_preemption_points j).dedup ≠ [] := by
          intro hempty
          have := size_of_seq_of_distances _ h_dedup_len; simp [hempty] at this; omega
        -- Bridge: relates Parameter.job_pp to Limited.job_pp
        have h_bridge := job_parameters_last_np_to_job_limited arr_seq LJ j ARR
        -- All elements of distances(dedup(jpp)) are positive
        have h_all_pos : ∀ x ∈ distances (job_preemption_points j).dedup, 0 < x := by
          intro x hx
          rw [← distances_positive_undup _ h_nd_j] at hx
          exact decide_eq_true_eq.mp (List.mem_filter.mp hx).2
        -- Positivity: job_last_np_seg > 0
        have h_J_pos : 0 < job_last_nonpreemptive_segment j := by
          unfold job_last_nonpreemptive_segment lengths_of_segments
          rw [hdist_eq, h_bridge, distances_positive_undup _ h_nd_j]
          have hmem : last0 (distances (job_preemption_points j).dedup) ∈
              distances (job_preemption_points j).dedup := by
            obtain ⟨d, dtl, hdists⟩ := List.exists_cons_of_ne_nil h_dist_dedup_ne
            rw [hdists]; show (d :: dtl).getLastD 0 ∈ d :: dtl
            rw [List.getLastD_cons]; exact List.getLastD_mem_cons
          exact h_all_pos _ hmem
        -- Bound: job_last_np_seg ≤ job_cost
        have h_J_le : job_last_nonpreemptive_segment j ≤ job_cost j := by
          unfold job_last_nonpreemptive_segment lengths_of_segments
          rw [hdist_eq, h_bridge, distances_positive_undup _ h_nd_j]
          exact Nat.le_trans (last_of_seq_le_max_of_seq _)
            (Nat.le_trans (max_distance_in_seq_le_last_element_of_seq _ h_nd_dedup)
              (le_of_eq (by rw [h_last0_undup]; exact h_end_j)))
        -- Positivity: task_last_np_seg > 0 (via T6)
        have h_T_pos : 0 < task_last_nonpr_segment tsk := by
          unfold task_last_nonpr_segment; rw [hdist_eq, last0_nth]; simp only [nthD]
          have h_dlen := size_of_seq_of_distances (task_preemption_points tsk) h_len_t
          have hlen_conv : (Prosa.Model.Preemption.Parameter.distances
              (task_preemption_points tsk)).length =
              (distances (task_preemption_points tsk)).length :=
            congrArg List.length (hdist_eq _)
          have h_T6 := T6 tsk ((distances (task_preemption_points tsk)).length - 1)
            H_tsk_in_ts (by omega)
          unfold ε at h_T6; omega
        -- Bound: task_last_np_seg ≤ task_cost
        have h_T_le : task_last_nonpr_segment tsk ≤ task_cost tsk := by
          unfold task_last_nonpr_segment; rw [hdist_eq]
          exact Nat.le_trans (last_of_seq_le_max_of_seq _)
            (Nat.le_trans (max_distance_in_seq_le_last_element_of_seq _ h_nd_t)
              (le_of_eq h_end_t))
        -- Main inequality
        show job_cost j - (job_last_nonpreemptive_segment j - ε) ≤
          task_cost tsk - (task_last_nonpr_segment tsk - ε)
        suffices h_core : job_cost j - job_last_nonpreemptive_segment j ≤
            task_cost tsk - task_last_nonpr_segment tsk by
          unfold ε
          rw [nat_sub_pred_eq _ _ h_J_pos h_J_le,
              nat_sub_pred_eq _ _ h_T_pos h_T_le]
          exact Nat.add_le_add_right h_core 1
        -- Unfold and bridge on LHS
        unfold job_last_nonpreemptive_segment lengths_of_segments task_last_nonpr_segment
        rw [hdist_eq, hdist_eq, h_bridge, distances_positive_undup _ h_nd_j]
        -- Goal: job_cost j - last0(dist(dedup(jpp))) ≤ task_cost tsk - last0(dist(tpp))
        have h_diff_dedup := last_seq_minus_last_distance_seq _ h_nd_dedup
        have h_diff_task := last_seq_minus_last_distance_seq _ h_nd_t
        rw [h_last0_undup, h_end_j] at h_diff_dedup
        rw [h_end_t] at h_diff_task
        have h_undup_le := undup_nth_le (job_preemption_points j) h_nd_j
        have h_dom_penult : nthD (job_preemption_points j)
            ((job_preemption_points j).length - 2) ≤
            nthD (task_preemption_points tsk)
              ((task_preemption_points tsk).length - 2) := by
          rw [h_len_eq]; exact h_dom _
        -- Chain: LHS = nthD(dedup,...) ≤ nthD(jpp,...) ≤ nthD(tpp,...) = RHS
        have h_chain := h_undup_le.trans h_dom_penult
        rw [← h_diff_dedup] at h_chain
        rw [← h_diff_task] at h_chain
        exact h_chain
end TaskRTCThresholdLimitedPreemptions

end Prosa.Analysis.Facts.Preemption.Rtc_threshold.Limited
