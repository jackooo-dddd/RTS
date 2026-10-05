-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: analysis/facts/preemption/job/limited.v

import Prosa.Model.Job.Properties
import Prosa.Model.Schedule.LimitedPreemptive
import Prosa.Model.Preemption.LimitedPreemptive
import Prosa.Analysis.Facts.Behavior.Service

namespace Prosa.Analysis.Facts.Preemption.Job.Limited

open Prosa.Behavior.Arrival_sequence
open Prosa.Behavior.Job
open Prosa.Behavior.Schedule
open Prosa.Behavior.Service
open Prosa.Behavior.Time
open Prosa.Model.Job.Properties
open Prosa.Model.Preemption.Parameter
open Prosa.Model.Preemption.LimitedPreemptive
open Prosa.Model.Schedule.LimitedPreemptive
open Prosa.Analysis.Facts.Behavior.Service
open Prosa.Util.List
open Prosa.Util.Nondecreasing

/-! Platform facts for the model with limited preemptions.
Representation notes: the source enables the section-local
`limited_preemptive_job_model` instance with `#[local] Existing Instance`;
the statements pass the accepted Lean definition of the same name explicitly,
as the elaborated source types do. `x \in s` is `decide (x ∈ s) = true`,
`x \notin s` is `(!decide (x ∈ s)) = true`, `size` is `List.length`,
`nth 0 s n` is `s.getD n 0`, `a <= b < c` is a Boolean conjunction of
decides. Binder orders follow the elaborated types (the unused task context
is absent, as in the elaborated source). -/

section ModelWithLimitedPreemptions

variable {Job : JobType} [DecidableEq Job]

/-- `0` is a preemption point. -/
theorem zero_in_preemption_points [JobCost Job] [JobPreemptionPoints Job]
    (arr_seq : arrival_sequence Job) :
    valid_limited_preemptions_job_model arr_seq →
    ∀ j : Job, arrives_in arr_seq j → decide (0 ∈ job_preemptive_points j) = true :=
  fun h j hj => h.1 j hj

/-- The first preemption point is `0`. -/
theorem zero_is_first_element [JobCost Job] [JobPreemptionPoints Job]
    (arr_seq : arrival_sequence Job) :
    valid_limited_preemptions_job_model arr_seq →
    ∀ j : Job, arrives_in arr_seq j → first0 (job_preemptive_points j) = 0 := by
  intro h j hj
  exact nondec_seq_zero_first _ (of_decide_eq_true (h.1 j hj)) (h.2.2 j hj)

/-- The list of preemption points is not empty. -/
theorem list_of_preemption_point_is_not_empty [JobCost Job] [JobPreemptionPoints Job]
    (arr_seq : arrival_sequence Job) :
    valid_limited_preemptions_job_model arr_seq →
    ∀ j : Job, arrives_in arr_seq j → 0 < (job_preemptive_points j).length := by
  intro h j hj
  have h0 := of_decide_eq_true (h.1 j hj)
  exact List.length_pos_of_mem h0

/-- The cost of a job is a preemption point. -/
theorem job_cost_in_nonpreemptive_points [JobCost Job] [JobPreemptionPoints Job]
    (arr_seq : arrival_sequence Job) :
    valid_limited_preemptions_job_model arr_seq →
    ∀ j : Job, arrives_in arr_seq j → decide (job_cost j ∈ job_preemptive_points j) = true := by
  intro h j hj
  have hend := h.2.1 j hj
  have hne : job_preemptive_points j ≠ [] :=
    List.ne_nil_of_length_pos (list_of_preemption_point_is_not_empty arr_seq h j hj)
  rw [← hend]
  apply decide_eq_true
  unfold last0
  rw [List.getLastD_eq_getLast?, List.getLast?_eq_some_getLast hne]
  exact List.getLast_mem hne

/-- A job with positive cost has at least two preemption points. -/
theorem number_of_preemption_points_at_least_two [JobCost Job] [JobPreemptionPoints Job]
    (arr_seq : arrival_sequence Job) :
    valid_limited_preemptions_job_model arr_seq →
    ∀ j : Job, arrives_in arr_seq j → job_cost_positive j = true →
      1 < (job_preemptive_points j).length := by
  intro h j hj hpos
  unfold job_cost_positive at hpos
  have hp := of_decide_eq_true hpos
  have h0 := of_decide_eq_true (zero_in_preemption_points arr_seq h j hj)
  have hc := of_decide_eq_true (job_cost_in_nonpreemptive_points arr_seq h j hj)
  revert h0 hc
  cases job_preemptive_points j with
  | nil => intro h0; simp at h0
  | cons a t =>
    cases t with
    | nil =>
      intro h0 hc
      simp only [List.mem_singleton] at h0 hc
      omega'
    | cons b t' => intro _ _; simp

/-- Work outside the preemption points lies between the first and the last
point. -/
theorem antidensity_of_preemption_points [JobCost Job] [JobPreemptionPoints Job]
    (arr_seq : arrival_sequence Job) :
    valid_limited_preemptions_job_model arr_seq →
    ∀ j : Job, arrives_in arr_seq j →
    ∀ ρ : work, ρ ≤ job_cost j → (!decide (ρ ∈ job_preemptive_points j)) = true →
      (decide (first0 (job_preemptive_points j) ≤ ρ) &&
        decide (ρ < last0 (job_preemptive_points j))) = true := by
  intro h j hj ρ hle hnin
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨by rw [zero_is_first_element arr_seq h j hj]; exact Nat.zero_le _, ?_⟩
  rw [h.2.1 j hj]
  rcases Nat.lt_or_ge ρ (job_cost j) with hlt | hge
  · exact hlt
  · exfalso
    have heq : ρ = job_cost j := by omega'
    subst heq
    rw [job_cost_in_nonpreemptive_points arr_seq h j hj] at hnin
    exact absurd hnin (by decide)

/-- Work outside the preemption points lies strictly inside some
nonpreemptive segment. -/
theorem work_belongs_to_some_nonpreemptive_segment [JobCost Job] [JobPreemptionPoints Job]
    (arr_seq : arrival_sequence Job) :
    valid_limited_preemptions_job_model arr_seq →
    ∀ j : Job, arrives_in arr_seq j →
    ∀ ρ : work, ρ ≤ job_cost j → (!decide (ρ ∈ job_preemptive_points j)) = true →
      ∃ n : Nat, n + 1 < (job_preemptive_points j).length ∧
        (decide ((job_preemptive_points j).getD n 0 < ρ) &&
          decide (ρ < (job_preemptive_points j).getD (n + 1) 0)) = true := by
  intro h j hj ρ hle hnin
  rcases Nat.eq_zero_or_pos (job_cost j) with hz | hpos
  · exfalso
    have hρ : ρ = 0 := by omega'
    subst hρ
    rw [zero_in_preemption_points arr_seq h j hj] at hnin
    exact absurd hnin (by decide)
  have h2 := number_of_preemption_points_at_least_two arr_seq h j hj
    (by unfold job_cost_positive; exact decide_eq_true hpos)
  have hanti := antidensity_of_preemption_points arr_seq h j hj ρ hle hnin
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hanti
  obtain ⟨n, hsize, hn1, hn2⟩ := belonging_to_segment_of_seq_is_total _ ρ h2 hanti
  refine ⟨n, hsize, ?_⟩
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨?_, hn2⟩
  rcases Nat.lt_or_ge ((job_preemptive_points j).getD n 0) ρ with hlt | hge
  · exact hlt
  · exfalso
    have heq : (job_preemptive_points j).getD n 0 = ρ := Nat.le_antisymm hn1 hge
    have hmem : ρ ∈ job_preemptive_points j := by
      rw [← heq, List.getD_eq_getElem _ _ (by omega')]
      exact List.getElem_mem _
    rw [decide_eq_true hmem] at hnin
    exact absurd hnin (by decide)

/-- The last nonpreemptive segment of `job_preemption_points` is the last
nonempty segment of `job_preemptive_points`. -/
theorem job_parameters_last_np_to_job_limited [JobCost Job] [JobPreemptionPoints Job]
    (arr_seq : arrival_sequence Job) :
    valid_limited_preemptions_job_model arr_seq →
    ∀ j : Job, arrives_in arr_seq j →
      last0 (distances (@job_preemption_points Job _ _ limited_preemptive_job_model j)) =
        last0 ((distances (job_preemptive_points j)).filter (fun x => decide (0 < x))) := by
  intro h j hj
  have hd := distances_iota_filtered (job_preemptive_points j) (job_cost j)
    (fun x hx => by
      rw [← h.2.1 j hj]
      exact last_is_max_in_nondecreasing_seq _ x (h.2.2 j hj) hx)
    (h.2.2 j hj)
  have hpp : @job_preemption_points Job _ _ limited_preemptive_job_model j =
      (index_iota 0 (job_cost j + 1)).filter (· ∈ job_preemptive_points j) := rfl
  rw [hpp, hd]

/-- The maximum nonpreemptive segments of both representations coincide. -/
theorem job_parameters_max_np_to_job_limited [JobCost Job] [JobPreemptionPoints Job]
    (arr_seq : arrival_sequence Job) :
    valid_limited_preemptions_job_model arr_seq →
    ∀ j : Job, arrives_in arr_seq j →
      max0 (distances (@job_preemption_points Job _ _ limited_preemptive_job_model j)) =
        max0 (distances (job_preemptive_points j)) := by
  intro h j hj
  have hd := distances_iota_filtered (job_preemptive_points j) (job_cost j)
    (fun x hx => by
      rw [← h.2.1 j hj]
      exact last_is_max_in_nondecreasing_seq _ x (h.2.2 j hj) hx)
    (h.2.2 j hj)
  have hpp : @job_preemption_points Job _ _ limited_preemptive_job_model j =
      (index_iota 0 (job_cost j + 1)).filter (· ∈ job_preemptive_points j) := rfl
  rw [hpp, hd]
  exact max0_rem0 _

/-- The limited-preemptive job model is a valid preemption model. -/
theorem valid_fixed_preemption_points_model_lemma [JobCost Job] [JobPreemptionPoints Job]
    (arr_seq : arrival_sequence Job) {PState : ProcessorState Job} (sched : schedule PState) :
    @schedule_respects_preemption_model Job _ PState limited_preemptive_job_model arr_seq sched →
    valid_limited_preemptions_job_model arr_seq →
    @valid_preemption_model Job _ _ limited_preemptive_job_model PState arr_seq sched := by
  intro hresp h j hj
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact zero_in_preemption_points arr_seq h j hj
  · exact job_cost_in_nonpreemptive_points arr_seq h j hj
  · intro t hnp
    exact hresp j t hj hnp
  · intro t hns hs
    have hserv : service sched j (t + 1) = service sched j t := by
      rw [← service_last_plus_before sched j t, not_scheduled_implies_no_service sched j t hns, Nat.add_zero]
    rw [hserv]
    cases hp : @job_preemptable Job _ limited_preemptive_job_model j (service sched j t)
    · exfalso
      have := hresp j t hj (by rw [hp]; rfl)
      rw [this] at hns
      exact absurd hns (by decide)
    · rfl

end ModelWithLimitedPreemptions

end Prosa.Analysis.Facts.Preemption.Job.Limited
