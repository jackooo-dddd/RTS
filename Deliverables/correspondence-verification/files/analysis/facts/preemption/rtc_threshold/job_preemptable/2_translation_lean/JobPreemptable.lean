-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: analysis/facts/preemption/rtc_threshold/job_preemptable.v

import Prosa.Model.Job.Properties
import Prosa.Analysis.Facts.Behavior.All
import Prosa.Model.Task.Preemption.Parameters

namespace Prosa.Analysis.Facts.Preemption.RtcThreshold.JobPreemptable

open Prosa.Behavior.Arrival_sequence
open Prosa.Behavior.Job
open Prosa.Behavior.Schedule
open Prosa.Behavior.Service
open Prosa.Behavior.Time
open Prosa.Model.Job.Properties
open Prosa.Model.Preemption.Parameter
open Prosa.Analysis.Facts.Behavior.Service
open Prosa.Util.List
open Prosa.Util.Nondecreasing

/-! Representation notes: a Boolean in `Prop` position is `= true`; a single
comparison in `Prop` position is the Lean proposition; a chained
`a <= b < c` is `(decide (a ≤ b) && decide (b < c)) = true`;
`x \in s` is `decide (x ∈ s) = true`; `~~ b` is `!b`; `size` is `length`;
`[:: 0]` is `[0]`. Binder orders follow the elaborated types (the section
hypotheses appear only in the statements that use them). -/

section RunToCompletionThreshold

variable {Job : JobType} [DecidableEq Job] [JobCost Job] [JobPreemptable Job]

/-- LEAN_HELPER: the last element of `[0, c]` is `c`. -/
private theorem last0_range (c : Nat) : last0 (index_iota 0 (c + 1)) = c := by
  unfold index_iota
  rw [Nat.sub_zero, List.range'_concat, last0_cat _ _ (by simp)]
  simp [last0]

/-- LEAN_HELPER: `[0, c]` is not empty. -/
private theorem range_ne_nil (c : Nat) : index_iota 0 (c + 1) ≠ [] := by
  unfold index_iota; simp

/-- LEAN_HELPER: the preemption points are the filtered inclusive range. -/
private theorem pts_def (j : Job) :
    job_preemption_points j = (index_iota 0 (job_cost j + 1)).filter (fun ρ => job_preemptable j ρ) :=
  rfl

/-- A zero-cost job has the single preemption point `0`. -/
theorem preemption_points_of_zero_cost_job {PState : ProcessorState Job}
    (arr_seq : arrival_sequence Job) (sched : schedule PState) :
    valid_preemption_model arr_seq sched → ∀ j : Job, arrives_in arr_seq j →
      job_cost j = 0 → job_preemption_points j = [0] := by
  intro hv j harr hc
  have A1 := (hv j harr).1
  simp only [job_cannot_become_nonpreemptive_before_execution] at A1
  rw [pts_def, hc]
  simp [index_iota, A1]

/-- `0` is a preemption point of a job with positive cost. -/
theorem zero_in_preemption_points {PState : ProcessorState Job}
    (arr_seq : arrival_sequence Job) (sched : schedule PState) :
    valid_preemption_model arr_seq sched → ∀ j : Job, arrives_in arr_seq j →
      0 < job_cost j → decide (0 ∈ job_preemption_points j) = true := by
  intro hv j harr _
  have A1 := (hv j harr).1
  simp only [job_cannot_become_nonpreemptive_before_execution] at A1
  rw [pts_def]
  simp [index_iota, List.mem_filter, List.mem_range'_1, A1]

/-- The job cost is a preemption point of a job with positive cost. -/
theorem job_cost_in_preemption_points {PState : ProcessorState Job}
    (arr_seq : arrival_sequence Job) (sched : schedule PState) :
    valid_preemption_model arr_seq sched → ∀ j : Job, arrives_in arr_seq j →
      0 < job_cost j → decide (job_cost j ∈ job_preemption_points j) = true := by
  intro hv j harr _
  have A2 := (hv j harr).2.1
  simp only [job_cannot_be_nonpreemptive_after_completion] at A2
  rw [pts_def]
  simp [index_iota, List.mem_filter, List.mem_range'_1, A2]

/-- A job with positive cost has at least two preemption points. -/
theorem size_of_preemption_points {PState : ProcessorState Job}
    (arr_seq : arrival_sequence Job) (sched : schedule PState) :
    valid_preemption_model arr_seq sched → ∀ j : Job, arrives_in arr_seq j →
      0 < job_cost j → 1 < (job_preemption_points j).length := by
  intro hv j harr hpos
  have h0 := zero_in_preemption_points arr_seq sched hv j harr hpos
  have hc := job_cost_in_preemption_points arr_seq sched hv j harr hpos
  simp only [decide_eq_true_eq] at h0 hc
  have hle := subseq_leq_size [0, job_cost j] (job_preemption_points j)
    (by simp; exact Nat.ne_of_lt hpos) (by intro x hx; simp at hx; rcases hx with rfl | rfl <;> assumption)
  exact hle

/-- The preemption points form a nondecreasing sequence. -/
theorem preemption_points_nondecreasing (j : Job) :
    nondecreasing_sequence (job_preemption_points j) :=
  increasing_implies_nondecreasing _
    (iota_is_increasing_sequence 0 (job_cost j + 1) (fun ρ => job_preemptable j ρ))

/-- The last preemption point is the job cost. -/
theorem job_cost_is_last_element_of_preemption_points {PState : ProcessorState Job}
    (arr_seq : arrival_sequence Job) (sched : schedule PState) :
    valid_preemption_model arr_seq sched → ∀ j : Job, arrives_in arr_seq j →
      job_cost j = last0 (job_preemption_points j) := by
  intro hv j harr
  have A2 := (hv j harr).2.1
  simp only [job_cannot_be_nonpreemptive_after_completion] at A2
  rw [pts_def]
  exact (last0_filter (job_cost j) _ _ (range_ne_nil _) (last0_range _) A2).symm

/-- LEAN_HELPER: the preemption points increase strictly. -/
private theorem pts_increasing (j : Job) (n1 n2 : Nat) (h : n1 < n2 ∧ n2 < (job_preemption_points j).length) :
    (job_preemption_points j).getD n1 0 < (job_preemption_points j).getD n2 0 :=
  (iota_is_increasing_sequence 0 (job_cost j + 1) (fun ρ => job_preemptable j ρ)) n1 n2 h

/-- LEAN_HELPER: consecutive distances in `getD` form. -/
private theorem distances_getD (xs : List Nat) (n : Nat) :
    (distances xs).getD n 0 = xs.getD (n + 1) 0 - xs.getD n 0 :=
  function_of_distances_is_correct xs n

/-- LEAN_HELPER: the last nonpreemptive segment is the difference of the last
two preemption points. -/
private theorem last_segment_eq {PState : ProcessorState Job}
    (arr_seq : arrival_sequence Job) (sched : schedule PState)
    (hv : valid_preemption_model arr_seq sched) (j : Job) (harr : arrives_in arr_seq j)
    (hpos : 0 < job_cost j) :
    job_last_nonpreemptive_segment j =
      (job_preemption_points j).getD ((job_preemption_points j).length - 1) 0 -
        (job_preemption_points j).getD ((job_preemption_points j).length - 2) 0 ∧
    (job_preemption_points j).getD ((job_preemption_points j).length - 2) 0 <
      (job_preemption_points j).getD ((job_preemption_points j).length - 1) 0 := by
  have hlen := size_of_preemption_points arr_seq sched hv j harr hpos
  have hd := size_of_seq_of_distances (job_preemption_points j) hlen
  have hinc := pts_increasing j ((job_preemption_points j).length - 2)
    ((job_preemption_points j).length - 1) ⟨by omega, by omega⟩
  refine ⟨?_, hinc⟩
  unfold job_last_nonpreemptive_segment lengths_of_segments
  rw [last0_nth, distances_getD]
  have e1 : (distances (job_preemption_points j)).length - 1 + 1 =
      (job_preemption_points j).length - 1 := by omega
  have e2 : (distances (job_preemption_points j)).length - 1 =
      (job_preemption_points j).length - 2 := by omega
  rw [e1, e2]

/-- The last nonpreemptive segment of a job with positive cost is positive. -/
theorem job_last_nonpreemptive_segment_positive {PState : ProcessorState Job}
    (arr_seq : arrival_sequence Job) (sched : schedule PState) :
    valid_preemption_model arr_seq sched → ∀ j : Job, arrives_in arr_seq j →
      job_cost_positive j = true → 0 < job_last_nonpreemptive_segment j := by
  intro hv j harr hcp
  have hpos : 0 < job_cost j := by simpa [job_cost_positive] using hcp
  obtain ⟨heq, hlt⟩ := last_segment_eq arr_seq sched hv j harr hpos
  rw [heq]
  exact Nat.sub_pos_of_lt hlt

/-- The longest nonpreemptive segment of a job with positive cost is positive. -/
theorem job_max_nonpreemptive_segment_positive {PState : ProcessorState Job}
    (arr_seq : arrival_sequence Job) (sched : schedule PState) :
    valid_preemption_model arr_seq sched → ∀ j : Job, arrives_in arr_seq j →
      job_cost_positive j = true → 0 < job_max_nonpreemptive_segment j := by
  intro hv j harr hcp
  exact Nat.lt_of_lt_of_le (job_last_nonpreemptive_segment_positive arr_seq sched hv j harr hcp)
    (last_of_seq_le_max_of_seq _)

/-- The longest nonpreemptive segment does not exceed the job cost. -/
theorem job_max_nonpreemptive_segment_le_job_cost {PState : ProcessorState Job}
    (arr_seq : arrival_sequence Job) (sched : schedule PState) :
    valid_preemption_model arr_seq sched → ∀ j : Job, arrives_in arr_seq j →
      job_max_nonpreemptive_segment j ≤ job_cost j := by
  intro hv j harr
  have h := max_distance_in_seq_le_last_element_of_seq _ (preemption_points_nondecreasing j)
  rw [← job_cost_is_last_element_of_preemption_points arr_seq sched hv j harr] at h
  exact h

/-- The last nonpreemptive segment does not exceed the job cost. -/
theorem job_last_nonpreemptive_segment_le_job_cost {PState : ProcessorState Job}
    (arr_seq : arrival_sequence Job) (sched : schedule PState) :
    valid_preemption_model arr_seq sched → ∀ j : Job, arrives_in arr_seq j →
      job_last_nonpreemptive_segment j ≤ job_cost j := by
  intro hv j harr
  exact Nat.le_trans (last_of_seq_le_max_of_seq _)
    (job_max_nonpreemptive_segment_le_job_cost arr_seq sched hv j harr)

/-- The run-to-completion threshold of a job with positive cost is positive. -/
theorem job_run_to_completion_threshold_positive {PState : ProcessorState Job}
    (arr_seq : arrival_sequence Job) (sched : schedule PState) :
    valid_preemption_model arr_seq sched → ∀ j : Job, arrives_in arr_seq j →
      job_cost_positive j = true → 0 < job_rtct j := by
  intro hv j harr hcp
  have N1 := job_last_nonpreemptive_segment_positive arr_seq sched hv j harr hcp
  have N2 := job_last_nonpreemptive_segment_le_job_cost arr_seq sched hv j harr
  unfold job_rtct; omega

/-- The run-to-completion threshold does not exceed the job cost. -/
theorem job_run_to_completion_threshold_le_job_cost (j : Job) : job_rtct j ≤ job_cost j := by
  unfold job_rtct; exact Nat.sub_le _ _

/-- A job cannot be preempted within its last nonpreemptive segment. -/
theorem job_cannot_be_preempted_within_last_segment {PState : ProcessorState Job}
    (arr_seq : arrival_sequence Job) (sched : schedule PState) :
    valid_preemption_model arr_seq sched → ∀ j : Job, arrives_in arr_seq j →
      ∀ ρ : duration, (decide (job_rtct j ≤ ρ) && decide (ρ < job_cost j)) = true →
        (!job_preemptable j ρ) = true := by
  intro hv j harr ρ h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨GE, LT⟩ := h
  have LT0 := LT
  have hpos : 0 < job_cost j := Nat.lt_of_le_of_lt (Nat.zero_le _) LT
  obtain ⟨heq, hlt⟩ := last_segment_eq arr_seq sched hv j harr hpos
  have hlast := job_cost_is_last_element_of_preemption_points arr_seq sched hv j harr
  rw [last0_nth] at hlast
  have hlen := size_of_preemption_points arr_seq sched hv j harr hpos
  unfold job_rtct at GE
  rw [heq, hlast] at GE
  rw [hlast] at LT
  have key : (job_preemption_points j).getD ((job_preemption_points j).length - 1) 0 -
      ((job_preemption_points j).getD ((job_preemption_points j).length - 1) 0 -
        (job_preemption_points j).getD ((job_preemption_points j).length - 2) 0 - 1) =
      (job_preemption_points j).getD ((job_preemption_points j).length - 2) 0 + 1 := by
    rw [Nat.sub_sub, Nat.sub_sub_self hlt]
  rw [key] at GE
  have hbelow : (job_preemption_points j).getD ((job_preemption_points j).length - 2) 0 < ρ :=
    Nat.lt_of_succ_le GE
  have e : (job_preemption_points j).length - 2 + 1 = (job_preemption_points j).length - 1 := by
    omega
  have habove : ρ < (job_preemption_points j).getD ((job_preemption_points j).length - 2 + 1) 0 := by
    rw [e]; exact LT
  have hnot := antidensity_of_nondecreasing_seq (job_preemption_points j) ρ
    ((job_preemption_points j).length - 2) (preemption_points_nondecreasing j) ⟨hbelow, habove⟩
  have hiff := conversion_preserves_equivalence j ρ (Nat.le_of_lt LT0)
  cases hp : job_preemptable j ρ with
  | false => rfl
  | true =>
    have := hiff.1 hp
    simp only [decide_eq_true_eq] at this
    exact absurd this hnot

/-- After reaching its run-to-completion threshold, a job is scheduled until
its completion. -/
theorem job_nonpreemptive_after_run_to_completion_threshold {PState : ProcessorState Job}
    (arr_seq : arrival_sequence Job) (sched : schedule PState) :
    valid_preemption_model arr_seq sched → ∀ j : Job, arrives_in arr_seq j →
      ∀ t t' : Nat, t ≤ t' → job_rtct j ≤ service sched j t →
        (!completed_by sched j t') = true → scheduled_at sched j t' = true := by
  intro hv j harr t t' hle hth hcom
  apply (hv j harr).2.2.1 t'
  apply job_cannot_be_preempted_within_last_segment arr_seq sched hv j harr
  simp only [completed_by, Bool.not_eq_true', decide_eq_false_iff_not] at hcom
  have hmono := service_monotonic sched j t t' hle
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨Nat.le_trans hth hmono, Nat.lt_of_not_le hcom⟩

end RunToCompletionThreshold

end Prosa.Analysis.Facts.Preemption.RtcThreshold.JobPreemptable
