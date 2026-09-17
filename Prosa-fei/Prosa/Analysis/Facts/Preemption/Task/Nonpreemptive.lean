-- Translated from: ../rt-proofs/analysis/facts/preemption/task/nonpreemptive.v
import Prosa.Analysis.Facts.Preemption.Job.Nonpreemptive
import Prosa.Model.Preemption.Fully_nonpreemptive
import Prosa.Model.Task.Preemption.Fully_nonpreemptive

namespace Prosa.Analysis.Facts.Preemption.Task.Nonpreemptive

open Prosa.Behavior.Job
open Prosa.Behavior.Time
open Prosa.Behavior.Service
open Prosa.Behavior.Schedule
open Prosa.Behavior.Arrival_sequence
open Prosa.Behavior.Ready
open Prosa.Model.Preemption.Parameter
open Prosa.Model.Task.Preemption.Parameters
open Prosa.Model.Task.Concept
open Prosa.Model.Processor.Ideal
open Prosa.Model.Schedule.Nonpreemptive
open Prosa.Analysis.Facts.Preemption.Job.Nonpreemptive
open Prosa.Util.Epsilon

section FullyNonPreemptiveModel

variable {Task : TaskType}
variable [TaskCost Task]
variable {Job : JobType}
variable [JobTask Job Task]
variable [JobArrival Job]
variable [JobCost Job]
variable [DecidableEq Job]

variable (arr_seq : arrival_sequence Job)
variable (H_arrival_times_are_consistent : consistent_arrival_times arr_seq)

attribute [local instance] pstate_instance
attribute [local instance] Prosa.Model.Preemption.Fully_nonpreemptive.fully_nonpreemptive_model
attribute [local instance] Prosa.Model.Task.Preemption.Fully_nonpreemptive.fully_nonpreemptive_model

variable (sched : schedule (processor_state Job))
variable (H_nonpreemptive_sched : nonpreemptive_schedule (Job := Job) sched)

variable (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute (Job := Job) sched)
variable (H_completed_jobs_dont_execute : completed_jobs_dont_execute (Job := Job) sched)

variable (H_valid_job_cost : arrivals_have_valid_job_costs (Task := Task) arr_seq)

include H_valid_job_cost in
lemma fully_nonpreemptive_model_is_model_with_bounded_nonpreemptive_regions :
    model_with_bounded_nonpreemptive_segments (Task := Task) arr_seq := by
  have hjc : ∀ j : Job, job_max_nonpreemptive_segment j = job_cost j := by
    intro j
    unfold job_max_nonpreemptive_segment lengths_of_segments distances job_preemption_points
    simp only [job_preemptable, Prosa.Model.Preemption.Fully_nonpreemptive.fully_nonpreemptive_model]
    unfold Prosa.Util.List.range
    by_cases hc : job_cost j = 0
    · simp only [hc, Prosa.Util.List.max0, Prosa.Model.Preemption.Parameter.distances,
        List.filter_cons, List.filter_nil, List.range'_succ, List.range'_zero,
        beq_self_eq_true, Bool.true_or, ite_true, List.drop, List.zip_nil_right,
        List.map_nil, List.foldl_nil, Nat.zero_add, Nat.add_zero, Nat.sub_zero]
    · have hpos : 0 < job_cost j := Nat.pos_of_ne_zero hc
      set n := job_cost j with hn_def
      -- Need: max0 (distances (filter (fun ρ => ρ == 0 || ρ == n) (List.range' 0 (n+1-0)))) = n
      -- Strategy: prove filter result = [0, n], then compute distances and max0.
      
      -- We prove this by directly computing the preemption points for the fully nonpreemptive model.
      -- The preemption points are [0, n] where n = job_cost j > 0.
      -- So distances = [n] and max0 [n] = n.
      -- We use a generalized helper lemma parametrized by ℕ to avoid issues with omega and `set`.
      
      have key : ∀ (c : ℕ), c > 0 →
        Prosa.Util.List.max0 (Prosa.Model.Preemption.Parameter.distances
          ((List.range' 0 (c + 1 - 0)).filter (fun ρ => (ρ == 0) || (ρ == c)))) = c := by
        intro c hc
        simp only [Nat.sub_zero]
        -- Helper: for x in range' s m with s ≥ 1 and s + m ≤ c, the filter is empty
        have filter_mid_empty : ∀ (m₀ s₀ : ℕ), s₀ ≥ 1 → s₀ + m₀ ≤ c →
            (List.range' s₀ m₀).filter (fun ρ => (ρ == 0) || (ρ == c)) = [] := by
          intro m₀ s₀ hs₀ hsm₀
          rw [List.filter_eq_nil_iff]
          intro x hx
          rw [List.mem_range'] at hx
          obtain ⟨k, hk_lt, rfl⟩ := hx
          simp only [Nat.one_mul, beq_iff_eq, Bool.or_eq_true]
          push_neg
          exact ⟨by omega, by omega⟩
        -- Split range' 0 (c+1) = 0 :: range' 1 c
        rw [List.range'_succ, List.filter_cons]
        simp only [beq_self_eq_true, Bool.true_or, ite_true, Nat.zero_add]
        -- Split range' 1 c = range' 1 (c-1) ++ [1 + 1*(c-1)]
        conv_lhs => rw [show c = (c - 1) + 1 from by omega]
        rw [List.range'_concat, List.filter_append, List.filter_cons, List.filter_nil]
        simp only [Nat.one_mul]
        have h1pc : 1 + (c - 1) = c := by omega
        have h1pc' : c - 1 + 1 = c := by omega
        rw [h1pc]
        simp only [h1pc', beq_self_eq_true, Bool.or_true, ite_true]
        rw [filter_mid_empty (c - 1) 1 (by omega) (by omega)]
        -- goal: max0 (distances (0 :: ([] ++ [c]))) = c
        unfold Prosa.Model.Preemption.Parameter.distances Prosa.Util.List.max0
        simp only [List.nil_append, List.drop, List.zip,
          List.zipWith, List.map, Nat.sub_zero,
          List.foldl]
        exact Nat.zero_max c
      -- Now apply key to n = job_cost j
      exact key n hpos
  intro j₀ hj₀
  constructor
  · -- job_respects_max_nonpreemptive_segment
    unfold job_respects_max_nonpreemptive_segment
    rw [hjc j₀]
    simp only [task_max_nonpreemptive_segment,
      Prosa.Model.Task.Preemption.Fully_nonpreemptive.fully_nonpreemptive_model]
    exact H_valid_job_cost j₀ hj₀
  · -- nonpreemptive_regions_have_bounded_length
    intro ρ ⟨_, hle⟩
    by_cases hρ : ρ = 0
    · -- Case ρ = 0: use pp = ρ (= 0)
      exact ⟨ρ, le_refl ρ, Nat.le_add_right ρ _, by
        subst hρ
        unfold job_preemptable Prosa.Model.Preemption.Fully_nonpreemptive.fully_nonpreemptive_model
        simp only [beq_self_eq_true, Bool.true_or]⟩
    · -- Case ρ > 0: use pp = job_cost j₀
      have hρ_pos : 0 < ρ := Nat.pos_of_ne_zero hρ
      refine ⟨job_cost j₀, hle, ?_, ?_⟩
      · -- job_cost j₀ ≤ ρ + (job_max_nonpreemptive_segment j₀ - ε)
        have hjc' : job_max_nonpreemptive_segment j₀ = job_cost j₀ := hjc j₀
        have hcost_pos : 0 < job_cost j₀ := Nat.lt_of_lt_of_le hρ_pos hle
        -- Rewrite max_nps to job_cost
        conv_rhs => rw [hjc']
        -- ε = 1, so job_cost j₀ - ε = job_cost j₀ - 1
        change job_cost j₀ ≤ ρ + (job_cost j₀ - 1)
        -- Explicit manual proof since omega can't see through the types
        have h1 : 1 ≤ job_cost j₀ := hcost_pos
        have h3 : 1 ≤ ρ := hρ_pos
        calc job_cost j₀ = job_cost j₀ - 1 + 1 := (Nat.sub_add_cancel h1).symm
          _ ≤ job_cost j₀ - 1 + ρ := Nat.add_le_add_left h3 _
          _ = ρ + (job_cost j₀ - 1) := Nat.add_comm _ _
      · -- job_preemptable j₀ (job_cost j₀)
        unfold job_preemptable Prosa.Model.Preemption.Fully_nonpreemptive.fully_nonpreemptive_model
        simp only [beq_self_eq_true, Bool.or_true]

include H_arrival_times_are_consistent H_nonpreemptive_sched
    H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_valid_job_cost in
theorem fully_nonpreemptive_model_is_valid_model_with_bounded_nonpreemptive_regions :
    valid_model_with_bounded_nonpreemptive_segments (Task := Task) arr_seq sched := by
  exact ⟨valid_fully_nonpreemptive_model arr_seq H_arrival_times_are_consistent sched
    H_nonpreemptive_sched H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute,
    fully_nonpreemptive_model_is_model_with_bounded_nonpreemptive_regions arr_seq H_valid_job_cost⟩

end FullyNonPreemptiveModel

end Prosa.Analysis.Facts.Preemption.Task.Nonpreemptive
