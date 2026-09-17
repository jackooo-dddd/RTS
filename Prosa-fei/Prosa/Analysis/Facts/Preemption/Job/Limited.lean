-- Translated from: ../rt-proofs/analysis/facts/preemption/job/limited.v
import Prosa.Model.Schedule.Limited_preemptive
import Prosa.Analysis.Definitions.Job_properties
import Prosa.Analysis.Facts.Behavior.All
import Prosa.Analysis.Facts.Model.Sequential
import Prosa.Analysis.Facts.Model.Ideal_schedule
import Prosa.Model.Preemption.Limited_preemptive

namespace Prosa.Analysis.Facts.Preemption.Job.Limited

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
open Prosa.Analysis.Definitions.Job_properties
open Prosa.Analysis.Facts.Model.Ideal_schedule
open Prosa.Util.List
open Prosa.Util.Nondecreasing
open Prosa.Util.Epsilon

section ModelWithLimitedPreemptions

variable {Task : TaskType}
variable [TaskCost Task]

variable {Job : JobType}
variable [JobTask Job Task]
variable [JobArrival Job]
variable [JobCost Job]
variable [DecidableEq Job]

variable [JobPreemptionPoints Job]

variable (arr_seq : arrival_sequence Job)

variable (sched : schedule (processor_state Job))
variable (H_schedule_respects_preemption_model :
    schedule_respects_preemption_model arr_seq sched)
variable (H_completed_jobs_dont_execute :
    completed_jobs_dont_execute (Job := Job) sched)
variable (H_valid_limited_preemptions_job_model :
    valid_limited_preemptions_job_model arr_seq)

attribute [local instance] pstate_instance
attribute [local instance] limited_preemptions_model

section AuxiliaryLemmas

variable (j : Job)
variable (H_j_arrives : arrives_in arr_seq j)

include H_valid_limited_preemptions_job_model H_j_arrives in
theorem zero_in_preemption_points :
    (0 : work) ∈ Prosa.Model.Preemption.Limited_preemptive.job_preemption_points j := by
  exact H_valid_limited_preemptions_job_model.1 j H_j_arrives

include H_valid_limited_preemptions_job_model H_j_arrives in
lemma zero_is_first_element :
    first0 (Prosa.Model.Preemption.Limited_preemptive.job_preemption_points j) = 0 := by
  apply nondec_seq_zero_first
  · exact H_valid_limited_preemptions_job_model.1 j H_j_arrives
  · exact H_valid_limited_preemptions_job_model.2.2 j H_j_arrives

include H_valid_limited_preemptions_job_model H_j_arrives in
lemma list_of_preemption_point_is_not_empty :
    0 < (Prosa.Model.Preemption.Limited_preemptive.job_preemption_points j).length := by
  exact List.length_pos_of_mem (H_valid_limited_preemptions_job_model.1 j H_j_arrives)

include H_valid_limited_preemptions_job_model H_j_arrives in
lemma job_cost_in_nonpreemptive_points :
    job_cost j ∈ Prosa.Model.Preemption.Limited_preemptive.job_preemption_points j := by
  have hend := H_valid_limited_preemptions_job_model.2.1 j H_j_arrives
  rw [← hend]
  -- Need: last0 xs ∈ xs for non-empty xs
  have hne : Prosa.Model.Preemption.Limited_preemptive.job_preemption_points j ≠ [] := by
    intro h
    have := H_valid_limited_preemptions_job_model.1 j H_j_arrives
    rw [h] at this; simp at this
  -- last0 xs = xs.getLastD 0 = xs.getLast hne for non-empty xs
  obtain ⟨a, as, hpts⟩ : ∃ a as, Prosa.Model.Preemption.Limited_preemptive.job_preemption_points j = a :: as := by
    match h : Prosa.Model.Preemption.Limited_preemptive.job_preemption_points j with
    | [] => exact absurd h hne
    | a :: as => exact ⟨a, as, rfl⟩
  rw [hpts]
  simp only [last0, List.getLastD, List.getLast?_cons]
  exact List.getLast_mem (by rw [← hpts]; exact hne)

include H_valid_limited_preemptions_job_model H_j_arrives in
theorem number_of_preemption_points_at_least_two :
    job_cost_positive j →
    2 ≤ (Prosa.Model.Preemption.Limited_preemptive.job_preemption_points j).length := by
  intro POS
  have h0 := H_valid_limited_preemptions_job_model.1 j H_j_arrives
  have hc : job_cost j ∈ Prosa.Model.Preemption.Limited_preemptive.job_preemption_points j :=
    job_cost_in_nonpreemptive_points arr_seq H_valid_limited_preemptions_job_model j H_j_arrives
  have hne : (0 : work) ≠ job_cost j := by unfold job_cost_positive at POS; unfold work at *; omega
  apply subseq_leq_size [0, job_cost j]
  · simp [List.nodup_cons, List.mem_singleton, hne, List.nodup_nil]
  · intro x hx; simp [List.mem_cons, List.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact h0
    · exact hc

include H_valid_limited_preemptions_job_model H_j_arrives in
lemma antidensity_of_preemption_points :
    ∀ (ρ : work),
      ρ ≤ job_cost j →
      ¬ (ρ ∈ Prosa.Model.Preemption.Limited_preemptive.job_preemption_points j) →
      first0 (Prosa.Model.Preemption.Limited_preemptive.job_preemption_points j) ≤ ρ ∧
      ρ < last0 (Prosa.Model.Preemption.Limited_preemptive.job_preemption_points j) := by
  intro ρ LE NotIN
  constructor
  · rw [zero_is_first_element arr_seq H_valid_limited_preemptions_job_model j H_j_arrives]
    exact Nat.zero_le _
  · rw [H_valid_limited_preemptions_job_model.2.1 j H_j_arrives]
    have hc : job_cost j ∈ Prosa.Model.Preemption.Limited_preemptive.job_preemption_points j :=
      job_cost_in_nonpreemptive_points arr_seq H_valid_limited_preemptions_job_model j H_j_arrives
    rcases Nat.eq_or_lt_of_le LE with heq | hlt
    · exfalso; exact NotIN (heq ▸ hc)
    · exact hlt

include H_valid_limited_preemptions_job_model H_j_arrives in
lemma work_belongs_to_some_nonpreemptive_segment :
    ∀ (ρ : work),
      ρ ≤ job_cost j →
      ¬ (ρ ∈ Prosa.Model.Preemption.Limited_preemptive.job_preemption_points j) →
      ∃ n,
        n + 1 < (Prosa.Model.Preemption.Limited_preemptive.job_preemption_points j).length ∧
        nthD (Prosa.Model.Preemption.Limited_preemptive.job_preemption_points j) n < ρ ∧
        ρ < nthD (Prosa.Model.Preemption.Limited_preemptive.job_preemption_points j) (n + 1) := by
  intro ρ LE NotIN
  -- If job_cost = 0, then ρ = 0 and 0 ∈ points, contradiction
  rcases Nat.eq_zero_or_pos (job_cost j) with ZERO | POS
  · exfalso; apply NotIN
    have : ρ = 0 := by unfold work at *; omega
    rw [this]; exact H_valid_limited_preemptions_job_model.1 j H_j_arrives
  · have h2 := number_of_preemption_points_at_least_two arr_seq H_valid_limited_preemptions_job_model j H_j_arrives POS
    have had := antidensity_of_preemption_points arr_seq H_valid_limited_preemptions_job_model j H_j_arrives ρ LE NotIN
    obtain ⟨n, hsize, hle, hlt⟩ := belonging_to_segment_of_seq_is_total
      (Prosa.Model.Preemption.Limited_preemptive.job_preemption_points j) ρ h2 had
    refine ⟨n, hsize, ?_, hlt⟩
    rcases Nat.eq_or_lt_of_le hle with heq | hgt
    · exfalso; apply NotIN
      have hlen : n < (Prosa.Model.Preemption.Limited_preemptive.job_preemption_points j).length := by omega
      have hmem : nthD (Prosa.Model.Preemption.Limited_preemptive.job_preemption_points j) n ∈
        Prosa.Model.Preemption.Limited_preemptive.job_preemption_points j := by
        unfold nthD List.getD
        rw [List.getElem?_eq_getElem hlen]
        exact List.getElem_mem hlen
      rw [heq] at hmem; exact hmem
    · exact hgt

include H_valid_limited_preemptions_job_model H_j_arrives in
lemma job_parameters_last_np_to_job_limited :
    last0 (Prosa.Util.Nondecreasing.distances (Prosa.Model.Preemption.Parameter.job_preemption_points j)) =
    last0 ((Prosa.Util.Nondecreasing.distances (Prosa.Model.Preemption.Limited_preemptive.job_preemption_points j)).filter (· > 0)) := by
  -- Parameter.job_preemption_points = (range 0 (job_cost j)).filter (job_preemptable j)
  -- With limited_preemptions_model, job_preemptable j ρ = decide (ρ ∈ Limited.job_preemption_points j)
  -- range 0 (job_cost j) = index_iota 0 (job_cost j + 1) since range a b = range' a (b+1-a)
  -- So Parameter.job_preemption_points j = (index_iota 0 (job_cost j + 1)).filter (· ∈ Limited.job_preemption_points j)
  -- By distances_iota_filtered, distances of that = (distances (Limited.job_preemption_points j)).filter (· > 0)
  -- So last0 of both sides are equal.
  have hA1 := H_valid_limited_preemptions_job_model.1
  have hA2 := H_valid_limited_preemptions_job_model.2.1
  have hA3 := H_valid_limited_preemptions_job_model.2.2
  -- Show that Parameter.job_preemption_points j = (index_iota 0 (job_cost j + 1)).filter (· ∈ Limited.job_preemption_points j)
  have hnd := hA3 j H_j_arrives
  have hlast := hA2 j H_j_arrives
  have hbounded : ∀ x, x ∈ Prosa.Model.Preemption.Limited_preemptive.job_preemption_points j → x ≤ job_cost j := by
    intro x hx
    exact last_is_max_in_nondecreasing_seq _ _ hnd hx |>.trans (by rw [hlast])
  -- Show parameter and filtered iota produce the same distances
  have hparam : Prosa.Util.Nondecreasing.distances (Prosa.Model.Preemption.Parameter.job_preemption_points j) =
    Prosa.Util.Nondecreasing.distances ((index_iota 0 (job_cost j + 1)).filter (· ∈ Prosa.Model.Preemption.Limited_preemptive.job_preemption_points j)) := by
    congr 1
  rw [hparam, distances_iota_filtered _ _ hbounded hnd]

include H_valid_limited_preemptions_job_model H_j_arrives in
lemma job_parameters_max_np_to_job_limited :
    max0 (Prosa.Util.Nondecreasing.distances (Prosa.Model.Preemption.Parameter.job_preemption_points j)) =
    max0 (Prosa.Util.Nondecreasing.distances (Prosa.Model.Preemption.Limited_preemptive.job_preemption_points j)) := by
  have hA1 := H_valid_limited_preemptions_job_model.1
  have hA2 := H_valid_limited_preemptions_job_model.2.1
  have hA3 := H_valid_limited_preemptions_job_model.2.2
  have hnd := hA3 j H_j_arrives
  have hlast := hA2 j H_j_arrives
  have hbounded : ∀ x, x ∈ Prosa.Model.Preemption.Limited_preemptive.job_preemption_points j → x ≤ job_cost j := by
    intro x hx
    exact last_is_max_in_nondecreasing_seq _ _ hnd hx |>.trans (by rw [hlast])
  have hparam : Prosa.Util.Nondecreasing.distances (Prosa.Model.Preemption.Parameter.job_preemption_points j) =
    Prosa.Util.Nondecreasing.distances ((index_iota 0 (job_cost j + 1)).filter (· ∈ Prosa.Model.Preemption.Limited_preemptive.job_preemption_points j)) := by
    congr 1
  rw [hparam, distances_iota_filtered _ _ hbounded hnd, max0_rem0]

end AuxiliaryLemmas

include H_schedule_respects_preemption_model H_completed_jobs_dont_execute
  H_valid_limited_preemptions_job_model in
lemma valid_fixed_preemption_points_model_lemma :
    valid_preemption_model arr_seq sched := by
  intro j ARR
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- job_cannot_become_nonpreemptive_before_execution
    show job_preemptable j 0 = true
    simp only [job_preemptable, limited_preemptions_model, decide_eq_true_eq]
    exact H_valid_limited_preemptions_job_model.1 j ARR
  · -- job_cannot_be_nonpreemptive_after_completion
    show job_preemptable j (job_cost j) = true
    simp only [job_preemptable, limited_preemptions_model, decide_eq_true_eq]
    exact job_cost_in_nonpreemptive_points arr_seq H_valid_limited_preemptions_job_model j ARR
  · -- not_preemptive_implies_scheduled
    intro t NPP
    exact H_schedule_respects_preemption_model j t ARR NPP
  · -- execution_starts_with_preemption_point
    intro prt NSCHED SCHED
    -- service doesn't change from prt to prt+1 since j is not scheduled at prt
    by_contra h
    -- h : ¬(job_preemptable j (service sched j (prt + 1)) = true)
    -- Since service sched j prt = service sched j (prt+1) (j not scheduled at prt),
    -- job_preemptable j (service sched j prt) is also not true
    have hsa : service_at sched j prt = 0 := by
      rw [service_at_is_scheduled_at]
      simp [NSCHED]
    have SERV : service sched j prt = service sched j (prt + 1) := by
      simp only [service, service_during]
      symm
      calc ∑ t ∈ Finset.Ico 0 (prt + 1), service_at sched j t
          = (∑ t ∈ Finset.Ico 0 prt, service_at sched j t) + service_at sched j prt := by
            rw [Finset.sum_Ico_succ_top (Nat.zero_le prt)]
        _ = ∑ t ∈ Finset.Ico 0 prt, service_at sched j t := by
            rw [hsa]; ring
    have h2 : ¬(job_preemptable j (service sched j prt) = true) := by
      rwa [SERV]
    have h_sched_prt : scheduled_at sched j prt = true :=
      H_schedule_respects_preemption_model j prt ARR h2
    rw [h_sched_prt] at NSCHED
    simp at NSCHED

end ModelWithLimitedPreemptions

end Prosa.Analysis.Facts.Preemption.Job.Limited
