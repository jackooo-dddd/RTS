-- Translated from: ../rt-proofs/analysis/facts/preemption/task/floating.v
import Prosa.Analysis.Facts.Preemption.Job.Limited
import Prosa.Model.Preemption.Limited_preemptive
import Prosa.Model.Task.Preemption.Floating_nonpreemptive

namespace Prosa.Analysis.Facts.Preemption.Task.Floating

open Prosa.Behavior.Job
open Prosa.Behavior.Time
open Prosa.Behavior.Service
open Prosa.Behavior.Schedule
open Prosa.Behavior.Arrival_sequence
open Prosa.Behavior.Ready
open Prosa.Model.Processor.Ideal
open Prosa.Model.Preemption.Parameter
open Prosa.Model.Preemption.Limited_preemptive
open Prosa.Model.Schedule.Limited_preemptive
open Prosa.Model.Task.Concept
open Prosa.Model.Task.Preemption.Parameters
open Prosa.Model.Task.Preemption.Floating_nonpreemptive
open Prosa.Analysis.Facts.Preemption.Job.Limited
open Prosa.Util.List
open Prosa.Util.Nondecreasing
open Prosa.Util.Epsilon

section FloatingNonPreemptiveRegionsModel

variable {Task : TaskType}
variable [TaskCost Task]

variable {Job : JobType}
variable [JobTask Job Task]
variable [JobArrival Job]
variable [JobCost Job]
variable [DecidableEq Job]

variable [TaskMaxNonpreemptiveSegment Task]
variable [JobPreemptionPoints Job]

attribute [local instance] pstate_instance
attribute [local instance] limited_preemptions_model

variable (arr_seq : arrival_sequence Job)

variable (sched : schedule (processor_state Job))
variable (H_preemption_aware_schedule :
    schedule_respects_preemption_model arr_seq sched)

variable (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute (Job := Job) sched)
variable (H_completed_jobs_dont_execute : completed_jobs_dont_execute (Job := Job) sched)

variable (H_valid_model_with_floating_nonpreemptive_regions :
    valid_model_with_floating_nonpreemptive_regions (Task := Task) arr_seq)

include H_valid_model_with_floating_nonpreemptive_regions in
lemma floating_preemption_points_model_is_model_with_bounded_nonpreemptive_regions :
    model_with_bounded_nonpreemptive_segments (Task := Task) arr_seq := by
  intro j ARR
  have LIM := H_valid_model_with_floating_nonpreemptive_regions.1
  have MAX := H_valid_model_with_floating_nonpreemptive_regions.2
  have BEG := LIM.1
  have END_ := LIM.2.1
  have NDEC := LIM.2.2
  rcases Nat.eq_zero_or_pos (job_cost j) with ZERO | POS
  · -- Case: job_cost j = 0
    constructor
    · -- job_respects_max_nonpreemptive_segment
      unfold job_respects_max_nonpreemptive_segment job_max_nonpreemptive_segment
        lengths_of_segments
      unfold Prosa.Model.Preemption.Parameter.job_preemption_points
      simp only [job_preemptable]
      simp only [Prosa.Util.List.range, ZERO]
      norm_num
      simp [List.filter, BEG j ARR, Prosa.Model.Preemption.Parameter.distances, List.drop, List.zip]
      -- max0 [] = 0 ≤ anything
      simp [max0, List.foldl]
    · -- nonpreemptive_regions_have_bounded_length
      intro ρ ⟨_, hle⟩
      rw [ZERO] at hle
      have hρ0 : ρ = 0 := Nat.le_zero.mp hle
      subst hρ0
      refine ⟨0, Nat.le_refl 0, Nat.zero_le _, ?_⟩
      simp only [job_preemptable, decide_eq_true_eq]
      exact BEG j ARR
  · -- Case: job_cost j > 0
    constructor
    · exact MAX j ARR
    · -- nonpreemptive_regions_have_bounded_length
      intro ρ ⟨_, hle⟩
      by_cases hIN : ρ ∈ Prosa.Model.Preemption.Limited_preemptive.job_preemption_points j
      · -- ρ is a preemption point
        refine ⟨ρ, Nat.le_refl _, Nat.le_add_right ρ _, ?_⟩
        simp only [job_preemptable, decide_eq_true_eq]
        exact hIN
      · -- ρ is not a preemption point
        obtain ⟨n, hsize, hlt1, hlt2⟩ :=
          work_belongs_to_some_nonpreemptive_segment arr_seq LIM j ARR ρ hle hIN
        set pts := Prosa.Model.Preemption.Limited_preemptive.job_preemption_points j with hpts_def
        set ptr := nthD pts (n + 1) with hptr_def
        set ptl := nthD pts n with hptl_def
        refine ⟨ptr, Nat.le_of_lt hlt2, ?_, ?_⟩
        · -- ptr ≤ ρ + (job_max_nonpreemptive_segment j - ε)
          have hdist : ptr - ptl ≤ max0 (Prosa.Util.Nondecreasing.distances pts) :=
            distance_between_neighboring_elements_le_max_distance_in_seq pts n
          have hmax_eq : job_max_nonpreemptive_segment j =
            max0 (Prosa.Util.Nondecreasing.distances pts) := by
            show max0 (Prosa.Model.Preemption.Parameter.distances (Prosa.Model.Preemption.Parameter.job_preemption_points j)) = max0 (Prosa.Util.Nondecreasing.distances pts)
            simp only [Prosa.Model.Preemption.Parameter.distances, Prosa.Util.Nondecreasing.distances]
            exact job_parameters_max_np_to_job_limited arr_seq LIM j ARR
          have hmax_pos : 0 < max0 (Prosa.Util.Nondecreasing.distances pts) := by
            apply max_distance_in_nontrivial_seq_is_positive
            · exact NDEC j ARR
            · exact ⟨0, job_cost j, BEG j ARR, (END_ j ARR) ▸ job_cost_in_nonpreemptive_points arr_seq LIM j ARR, by omega⟩
          have hptl_le_ptr : ptl ≤ ptr := by
            exact (NDEC j ARR) n (n + 1) ⟨Nat.le_succ n, hsize⟩
          have hptr_le : ptr ≤ ptl + max0 (Prosa.Util.Nondecreasing.distances pts) := by
            omega
          -- ρ ≥ 1 since ρ ≠ 0 (0 ∈ preemption_points but ρ ∉ preemption_points)
          have hρ_pos : 0 < ρ := by
            rcases Nat.eq_zero_or_pos ρ with hρ0 | hρ_pos
            · exfalso; apply hIN; rw [hρ0]; exact BEG j ARR
            · exact hρ_pos
          have goal_proof : ptr ≤ ρ + (job_max_nonpreemptive_segment j - ε) := by
            unfold ε
            have h1 : ptl + 1 ≤ ρ := hlt1
            have h2 : ptr ≤ ptl + max0 (Prosa.Util.Nondecreasing.distances pts) := hptr_le
            have h3 : max0 (Prosa.Util.Nondecreasing.distances pts) = job_max_nonpreemptive_segment j := hmax_eq.symm
            rw [h3] at h2
            omega
          exact goal_proof
        · -- job_preemptable j ptr = true
          simp only [job_preemptable, decide_eq_true_eq]
          have hlen : n + 1 < pts.length := hsize
          rw [hptr_def]
          unfold nthD List.getD
          rw [List.getElem?_eq_getElem hlen]
          exact List.getElem_mem hlen

include H_valid_model_with_floating_nonpreemptive_regions
    H_preemption_aware_schedule H_completed_jobs_dont_execute in
theorem floating_preemption_points_model_is_valid_model_with_bounded_nonpreemptive_regions :
    valid_model_with_bounded_nonpreemptive_segments (Task := Task) arr_seq sched := by
  constructor
  · apply valid_fixed_preemption_points_model_lemma
    · exact H_preemption_aware_schedule
    · exact H_completed_jobs_dont_execute
    · exact H_valid_model_with_floating_nonpreemptive_regions.1
  · exact floating_preemption_points_model_is_model_with_bounded_nonpreemptive_regions arr_seq H_valid_model_with_floating_nonpreemptive_regions

end FloatingNonPreemptiveRegionsModel

end Prosa.Analysis.Facts.Preemption.Task.Floating
