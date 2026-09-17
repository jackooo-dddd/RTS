-- Translated from: ../rt-proofs/analysis/facts/preemption/task/limited.v
import Prosa.Analysis.Facts.Preemption.Job.Limited
import Prosa.Model.Preemption.Limited_preemptive
import Prosa.Model.Task.Preemption.Limited_preemptive

namespace Prosa.Analysis.Facts.Preemption.Task.Limited

open Prosa.Behavior.Job
open Prosa.Behavior.Time
open Prosa.Behavior.Service
open Prosa.Behavior.Schedule
open Prosa.Behavior.Arrival_sequence
open Prosa.Behavior.Ready
open Prosa.Model.Preemption.Parameter
open Prosa.Model.Preemption.Limited_preemptive
open Prosa.Model.Task.Preemption.Parameters
open Prosa.Model.Task.Preemption.Limited_preemptive
open Prosa.Model.Task.Concept
open Prosa.Model.Processor.Ideal
open Prosa.Model.Schedule.Limited_preemptive
open Prosa.Analysis.Facts.Preemption.Job.Limited
open Prosa.Util.List
open Prosa.Util.Nondecreasing
open Prosa.Util.Epsilon

section LimitedPreemptionsModel

variable {Task : TaskType}
variable [TaskCost Task]

variable {Job : JobType}
variable [JobTask Job Task]
variable [JobArrival Job]
variable [JobCost Job]
variable [DecidableEq Job]

variable [JobPreemptionPoints Job]
variable [TaskPreemptionPoints Task]

attribute [local instance] pstate_instance
attribute [local instance] limited_preemptions_model

variable (arr_seq : arrival_sequence Job)

variable (sched : schedule (processor_state Job))
variable (H_schedule_respects_preemption_model :
    schedule_respects_preemption_model arr_seq sched)

variable (H_jobs_must_arrive_to_execute :
    jobs_must_arrive_to_execute (Job := Job) sched)
variable (H_completed_jobs_dont_execute :
    completed_jobs_dont_execute (Job := Job) sched)

variable (ts : TaskSet Task)

variable (H_valid_fixed_preemption_points_model :
    valid_fixed_preemption_points_model arr_seq ts)

include H_valid_fixed_preemption_points_model H_schedule_respects_preemption_model H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute in
lemma fixed_preemption_points_model_is_model_with_bounded_nonpreemptive_regions :
    model_with_bounded_nonpreemptive_segments (Task := Task) arr_seq := by
  intro j ARR
  have LIM := H_valid_fixed_preemption_points_model.1
  have FIX := H_valid_fixed_preemption_points_model.2
  have BEG := LIM.1
  have END_ := LIM.2.1
  have NDEC := LIM.2.2
  have A1 := FIX.1
  have A2 := FIX.2.1
  have A3 := FIX.2.2.1
  have A4 := FIX.2.2.2.1
  have A5 := FIX.2.2.2.2.1
  have A6 := FIX.2.2.2.2.2
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
      simp [max0, List.foldl]
    · -- nonpreemptive_regions_have_bounded_length
      intro ρ ⟨_, hle⟩
      rw [ZERO] at hle
      have hρ0 : ρ = 0 := Nat.le_zero.mp hle
      subst hρ0
      refine ⟨0, Nat.le_refl 0, Nat.zero_le _, ?_⟩
      simp only [job_preemptable, limited_preemptions_model, decide_eq_true_eq]
      exact BEG j ARR
  · -- Case: job_cost j > 0
    constructor
    · -- job_respects_max_nonpreemptive_segment
      unfold job_respects_max_nonpreemptive_segment
      show job_max_nonpreemptive_segment j ≤ task_max_nonpreemptive_segment (job_task (Task := Task) j)
      unfold job_max_nonpreemptive_segment lengths_of_segments
      -- The goal has Parameter.distances. We need to bridge to Nondecreasing.distances
      -- to use job_parameters_max_np_to_job_limited.
      have hconv : max0 (Prosa.Model.Preemption.Parameter.distances (Prosa.Model.Preemption.Parameter.job_preemption_points j)) =
        max0 (Prosa.Util.Nondecreasing.distances (Prosa.Model.Preemption.Limited_preemptive.job_preemption_points j)) := by
        simp only [Prosa.Model.Preemption.Parameter.distances, Prosa.Util.Nondecreasing.distances]
        exact job_parameters_max_np_to_job_limited arr_seq LIM j ARR
      rw [hconv]
      change max0 (Prosa.Util.Nondecreasing.distances (Prosa.Model.Preemption.Limited_preemptive.job_preemption_points j))
        ≤ task_max_nonpr_segment (job_task (Task := Task) j)
      unfold task_max_nonpr_segment
      -- Prove max0 xs ≤ max0 ys inline, avoiding sorry'd max_of_dominating_seq
      -- Strategy: show every element of xs is ≤ max0 ys, then conclude max0 xs ≤ max0 ys
      have hdom : ∀ n, (Prosa.Util.Nondecreasing.distances (Prosa.Model.Preemption.Limited_preemptive.job_preemption_points j)).getD n 0
        ≤ (Prosa.Util.Nondecreasing.distances (task_preemption_points (job_task (Task := Task) j))).getD n 0 := by
        intro n; exact A5 j n ARR
      -- Inline proof: max0 xs ≤ max0 ys from pointwise domination
      -- Strategy: show ∀ x ∈ xs, x ≤ max0 ys, then use induction to conclude max0 xs ≤ max0 ys
      set xs := Prosa.Util.Nondecreasing.distances (Prosa.Model.Preemption.Limited_preemptive.job_preemption_points j)
      set ys := Prosa.Util.Nondecreasing.distances (task_preemption_points (job_task (Task := Task) j))
      -- First, show every element of xs is ≤ max0 ys
      have hall : ∀ x, x ∈ xs → x ≤ max0 ys := by
        intro x hx
        obtain ⟨n, hn_lt, hn_eq⟩ := List.getElem_of_mem hx
        have hx_eq : x = xs.getD n 0 := by
          simp only [List.getD, List.getElem?_eq_getElem hn_lt]
          exact hn_eq.symm
        rw [hx_eq]
        calc xs.getD n 0 ≤ ys.getD n 0 := hdom n
          _ ≤ max0 ys := by
              simp only [List.getD]
              rcases Nat.lt_or_ge n ys.length with hlt | hge
              · rw [List.getElem?_eq_getElem hlt]
                exact in_max0_le ys _ (List.getElem_mem hlt)
              · rw [List.getElem?_eq_none hge]
                exact Nat.zero_le _
      -- Now prove max0 xs ≤ max0 ys
      have max0_le_of_all_le : ∀ (zs : List ℕ) (b : ℕ), (∀ x, x ∈ zs → x ≤ b) → max0 zs ≤ b := by
        intro zs b hle
        induction zs with
        | nil => simp [max0, List.foldl]
        | cons a tl ih =>
          rw [max0_cons]
          apply Nat.max_le.mpr
          constructor
          · exact hle a (List.mem_cons_self ..)
          · exact ih (fun x hx => hle x (List.mem_cons_of_mem _ hx))
      exact max0_le_of_all_le xs (max0 ys) hall
    · -- nonpreemptive_regions_have_bounded_length
      intro ρ ⟨_, hle⟩
      by_cases hIN : ρ ∈ Prosa.Model.Preemption.Limited_preemptive.job_preemption_points j
      · -- ρ is a preemption point
        refine ⟨ρ, Nat.le_refl _, Nat.le_add_right ρ _, ?_⟩
        simp only [job_preemptable, limited_preemptions_model, decide_eq_true_eq]
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
          have hptl_le_ptr : ptl ≤ ptr :=
            (NDEC j ARR) n (n + 1) ⟨Nat.le_succ n, hsize⟩
          have hptr_le : ptr ≤ ptl + max0 (Prosa.Util.Nondecreasing.distances pts) := by
            omega
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
          simp only [job_preemptable, limited_preemptions_model, decide_eq_true_eq]
          have hlen : n + 1 < pts.length := hsize
          rw [hptr_def]
          unfold nthD List.getD
          rw [List.getElem?_eq_getElem hlen]
          exact List.getElem_mem hlen

include H_valid_fixed_preemption_points_model H_schedule_respects_preemption_model
    H_completed_jobs_dont_execute in
include H_schedule_respects_preemption_model H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_valid_fixed_preemption_points_model in
theorem fixed_preemption_points_model_is_valid_model_with_bounded_nonpreemptive_regions :
    valid_model_with_bounded_nonpreemptive_segments (Task := Task) arr_seq sched := by
  constructor
  · apply valid_fixed_preemption_points_model_lemma
    · exact H_schedule_respects_preemption_model
    · exact H_completed_jobs_dont_execute
    · exact H_valid_fixed_preemption_points_model.1
  · exact fixed_preemption_points_model_is_model_with_bounded_nonpreemptive_regions arr_seq sched
      H_schedule_respects_preemption_model H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute
      ts H_valid_fixed_preemption_points_model

end LimitedPreemptionsModel

end Prosa.Analysis.Facts.Preemption.Task.Limited
