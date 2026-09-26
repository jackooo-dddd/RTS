-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: analysis/facts/preemption/rtc_threshold/preemptive.v

import Prosa.Analysis.Facts.Preemption.RtcThreshold.JobPreemptable
import Prosa.Model.Preemption.FullyPreemptive
import Prosa.Model.Task.Preemption.FullyPreemptive

namespace Prosa.Analysis.Facts.Preemption.RtcThreshold.Preemptive

open Prosa.Behavior.Arrival_sequence
open Prosa.Behavior.Job
open Prosa.Behavior.Time
open Prosa.Model.Task.Concept
open Prosa.Model.Preemption.Parameter
open Prosa.Model.Preemption.FullyPreemptive
open Prosa.Model.Task.Preemption.Parameters
open Prosa.Model.Task.Preemption.FullyPreemptive

/-! Representation notes: the source enables the section-local
`fully_preemptive_job_model`, `fully_preemptive_task_model` and
`fully_preemptive_rtc_threshold` instances with `#[local] Existing Instance`;
the statement passes the accepted Lean definitions of the same names
explicitly, as the elaborated source type does. Binder orders follow the
elaborated type. -/

/-- The fully preemptive run-to-completion threshold (the task cost) is valid
when all arriving jobs respect their task costs. -/
theorem fully_preemptive_valid_task_run_to_completion_threshold
    {Task : TaskType} [DecidableEq Task] [TaskCost Task] {Job : JobType} [DecidableEq Job]
    [JobTask Job Task] [JobCost Job] (arr_seq : arrival_sequence Job) :
    arrivals_have_valid_job_costs (Task := Task) arr_seq →
      ∀ tsk : Task,
        @valid_task_run_to_completion_threshold Task _ _ Job _ _ _
          fully_preemptive_job_model fully_preemptive_rtc_threshold arr_seq tsk := by
  intro hvalid tsk
  refine ⟨?_, ?_⟩
  · show decide (task_cost tsk ≤ task_cost tsk) = true
    exact decide_eq_true (Nat.le_refl _)
  · intro j harr htsk
    show @job_rtct Job _ _ fully_preemptive_job_model j ≤ task_cost tsk
    have hv := hvalid j harr
    simp only [valid_job_cost, decide_eq_true_eq] at hv
    simp only [job_of_task, decide_eq_true_eq] at htsk
    subst htsk
    unfold job_rtct
    try dsimp only [work, duration, instant] at *
    omega

end Prosa.Analysis.Facts.Preemption.RtcThreshold.Preemptive
