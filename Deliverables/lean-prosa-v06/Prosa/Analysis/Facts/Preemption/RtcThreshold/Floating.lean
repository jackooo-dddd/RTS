-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: analysis/facts/preemption/rtc_threshold/floating.v

import Prosa.Analysis.Facts.Preemption.Task.Floating
import Prosa.Analysis.Facts.Preemption.RtcThreshold.JobPreemptable
import Prosa.Model.Task.Preemption.FloatingNonpreemptive

namespace Prosa.Analysis.Facts.Preemption.RtcThreshold.Floating

open Prosa.Behavior.Arrival_sequence
open Prosa.Behavior.Job
open Prosa.Model.Task.Concept
open Prosa.Model.Preemption.Parameter
open Prosa.Model.Task.Preemption.Parameters
open Prosa.Model.Task.Preemption.FloatingNonpreemptive

/-! The run-to-completion threshold of the model with floating nonpreemptive
regions is valid. Binders follow the elaborated source type; the source's
section-local `floating_preemptive_rtc_threshold` instance is the accepted
Lean definition of the same name, passed explicitly. -/

section TaskRTCThresholdFloatingNonPreemptiveRegions

variable {Job : JobType} [DecidableEq Job]

/-- The floating run-to-completion threshold (the task cost) is valid. -/
theorem floating_preemptive_valid_task_run_to_completion_threshold {Task : TaskType} [DecidableEq Task]
    [TaskCost Task] [JobTask Job Task] [JobCost Job] [JobPreemptable Job]
    (arr_seq : arrival_sequence Job) :
    arrivals_have_valid_job_costs (Task := Task) arr_seq →
    ∀ tsk : Task,
      @valid_task_run_to_completion_threshold Task _ _ Job _ _ _ _ floating_preemptive_rtc_threshold
        arr_seq tsk := by
  intro hvalid tsk
  refine ⟨decide_eq_true (Nat.le_refl _), ?_⟩
  intro j hj htsk
  have hv := hvalid j hj
  unfold valid_job_cost at hv
  have hv' := of_decide_eq_true hv
  unfold job_of_task at htsk
  rw [of_decide_eq_true htsk] at hv'
  show job_rtct j ≤ task_cost tsk
  unfold job_rtct
  omega'

end TaskRTCThresholdFloatingNonPreemptiveRegions

end Prosa.Analysis.Facts.Preemption.RtcThreshold.Floating
