-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: analysis/facts/preemption/rtc_threshold/nonpreemptive.v

import Prosa.Analysis.Facts.Preemption.Job.Nonpreemptive
import Prosa.Model.Task.Preemption.FullyNonpreemptive

namespace Prosa.Analysis.Facts.Preemption.RtcThreshold.Nonpreemptive

open Prosa.Behavior.Arrival_sequence
open Prosa.Behavior.Job
open Prosa.Behavior.Time
open Prosa.Model.Task.Concept
open Prosa.Model.Preemption.Parameter
open Prosa.Model.Preemption.FullyNonpreemptive
open Prosa.Model.Task.Preemption.Parameters
open Prosa.Model.Task.Preemption.FullyNonpreemptive
open Prosa.Analysis.Facts.Preemption.Job.Nonpreemptive

/-! Representation notes: the source enables the section-local
`fully_nonpreemptive_job_model` and `fully_nonpreemptive_rtc_threshold`
instances with `#[local] Existing Instance`; the statements pass the accepted
Lean definitions of the same names explicitly, as the elaborated source types
do; `ε` is `1`. Binder orders follow the elaborated types (unused section
context and hypotheses are absent, as in the elaborated source). -/

/-- A zero-cost job has run-to-completion threshold `0`. -/
theorem job_rtc_threshold_is_0 {Job : JobType} [DecidableEq Job] [JobCost Job] :
    ∀ j : Job, job_cost j = 0 → @job_rtct Job _ _ fully_nonpreemptive_job_model j = 0 := by
  intro j h
  unfold job_rtct
  rw [h]; exact Nat.zero_sub _

/-- A job with positive cost has run-to-completion threshold `ε`. -/
theorem «job_rtc_threshold_is_ε» {Job : JobType} [DecidableEq Job] [JobCost Job]
    (arr_seq : arrival_sequence Job) :
    ∀ j : Job, 0 < job_cost j → arrives_in arr_seq j →
      @job_rtct Job _ _ fully_nonpreemptive_job_model j = 1 := by
  intro j hpos _
  unfold job_rtct
  rw [job_last_nps_is_job_cost j]
  try dsimp only [work, duration, instant] at *
  omega

/-- The fully nonpreemptive run-to-completion threshold is valid. -/
theorem fully_nonpreemptive_valid_task_run_to_completion_threshold
    {Task : TaskType} [DecidableEq Task] [TaskCost Task] {Job : JobType} [DecidableEq Job]
    [JobTask Job Task] [JobCost Job] (arr_seq : arrival_sequence Job) (tsk : Task) :
    0 < task_cost tsk →
      @valid_task_run_to_completion_threshold Task _ _ Job _ _ _
        fully_nonpreemptive_job_model fully_nonpreemptive_rtc_threshold arr_seq tsk := by
  intro hpos
  refine ⟨?_, ?_⟩
  · show decide (1 ≤ task_cost tsk) = true
    exact decide_eq_true hpos
  · intro j harr _
    show @job_rtct Job _ _ fully_nonpreemptive_job_model j ≤ 1
    by_cases h : job_cost j = 0
    · rw [job_rtc_threshold_is_0 j h]; exact Nat.zero_le _
    · rw [«job_rtc_threshold_is_ε» arr_seq j (Nat.pos_of_ne_zero h) harr]

end Prosa.Analysis.Facts.Preemption.RtcThreshold.Nonpreemptive
