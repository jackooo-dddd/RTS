-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: analysis/facts/preemption/job/preemptive.v

import Prosa.Model.Task.Preemption.Parameters
import Prosa.Model.Preemption.FullyPreemptive

namespace Prosa.Analysis.Facts.Preemption.Job.Preemptive

open Prosa.Behavior.Arrival_sequence
open Prosa.Behavior.Job
open Prosa.Behavior.Schedule
open Prosa.Model.Preemption.Parameter
open Prosa.Model.Preemption.FullyPreemptive
open Prosa.Util.List
open Prosa.Util.Nondecreasing

/-! Representation notes: the source enables the section-local
`fully_preemptive_job_model` instance with `#[local] Existing Instance`; the
statements below pass the accepted Lean definition of the same name
explicitly, as the elaborated source types do; `ε` is `1`; `a > b` is
`b < a`. Binder orders follow the elaborated types (unused section context is
absent). -/

/-- LEAN_HELPER: consecutive distances of an arithmetic range with step one. -/
private theorem distances_range'_ones (a m : Nat) :
    ∀ x, x ∈ distances (List.range' a m) → x = 1 := by
  induction m generalizing a with
  | zero => intro x hx; simp [distances] at hx
  | succ m ih =>
    cases m with
    | zero => intro x hx; simp [distances, List.range'] at hx
    | succ m =>
      intro x hx
      have hcons : distances (List.range' a (m + 2)) =
          (a + 1 - a) :: distances (List.range' (a + 1) (m + 1)) := by
        simp only [List.range'_succ]; rfl
      rw [hcons] at hx
      rcases List.mem_cons.mp hx with h | h
      · omega
      · exact ih (a + 1) x h

/-- LEAN_HELPER: the number of consecutive distances of a range. -/
private theorem distances_range'_length (a m : Nat) :
    (distances (List.range' a m)).length = m - 1 := by
  simp [distances, List.length_zip, List.length_range']

/-- The fully preemptive model is a valid preemption model. -/
theorem valid_fully_preemptive_model {Job : JobType} [DecidableEq Job] [JobCost Job]
    {PState : ProcessorState Job} (arr_seq : arrival_sequence Job) (sched : schedule PState) :
    @valid_preemption_model Job _ _ fully_preemptive_job_model PState arr_seq sched := by
  intro j _
  refine ⟨rfl, rfl, ?_, ?_⟩
  · intro t h; simp at h
  · intro t _ _; rfl

/-- A job of zero cost has a zero maximum nonpreemptive segment. -/
theorem job_max_nps_is_0 {Job : JobType} [DecidableEq Job] [JobCost Job] :
    ∀ j : Job, job_cost j = 0 →
      @job_max_nonpreemptive_segment Job _ _ fully_preemptive_job_model j = 0 := by
  intro j h
  have hp : ∀ a, @job_preemptable Job _ fully_preemptive_job_model j a = true := fun _ => rfl
  simp [job_max_nonpreemptive_segment, lengths_of_segments, job_preemption_points,
    hp, h, range, index_iota, distances, max0]

/-- A job of positive cost has a maximum nonpreemptive segment of one. -/
theorem job_max_nps_is_ε {Job : JobType} [DecidableEq Job] [JobCost Job] :
    ∀ j : Job, 0 < job_cost j →
      @job_max_nonpreemptive_segment Job _ _ fully_preemptive_job_model j = 1 := by
  intro j h
  have hp : ∀ a, @job_preemptable Job _ fully_preemptive_job_model j a = true := fun _ => rfl
  have hpts : @job_preemption_points Job _ _ fully_preemptive_job_model j =
      List.range' 0 (job_cost j + 1) := by
    simp [job_preemption_points, hp, range, index_iota]
  unfold job_max_nonpreemptive_segment lengths_of_segments
  rw [hpts]
  apply max0_of_uniform_set
  · rw [distances_range'_length]
    rw [Nat.add_sub_cancel]; exact h
  · exact distances_range'_ones 0 (job_cost j + 1)

end Prosa.Analysis.Facts.Preemption.Job.Preemptive
