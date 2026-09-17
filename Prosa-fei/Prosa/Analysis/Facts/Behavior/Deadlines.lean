-- Translated from: ../rt-proofs/analysis/facts/behavior/deadlines.v
import Prosa.Analysis.Facts.Behavior.Completion

namespace Prosa.Analysis.Facts.Behavior.Deadlines

open Prosa.Behavior.Job
open Prosa.Behavior.Time
open Prosa.Behavior.Schedule
open Prosa.Behavior.Service
open Prosa.Behavior.Ready
open Prosa.Model.Processor.Platform_properties
open Prosa.Analysis.Facts.Behavior.Completion

section DeadlineFacts

variable {Job : JobType}
variable [JobCost Job]
variable [JobDeadline Job]
variable {PState : Type _}
variable [ProcessorState Job PState]

section IdealProgressSchedules

variable (sched : schedule PState)
variable (H_completed_jobs : completed_jobs_dont_execute (Job := Job) sched)
variable (H_scheduled_implies_serviced : ideal_progress_proc_model (Job := Job) PState)

include H_completed_jobs H_scheduled_implies_serviced in
theorem scheduled_at_implies_later_deadline :
    ∀ (j : Job) t,
      job_meets_deadline sched j →
      scheduled_at sched j t →
      t < job_deadline j := by
  intro j t hdeadline hsched
  by_contra hle
  push_neg at hle
  have hcomp : completed_by sched j t :=
    completion_monotonic sched j (job_deadline j) t hle hdeadline
  have hnotcomp : ¬ completed_by sched j t :=
    scheduled_implies_not_completed sched j H_completed_jobs H_scheduled_implies_serviced t hsched
  exact hnotcomp hcomp

end IdealProgressSchedules

section EqualProgress

variable (sched sched' : schedule PState)

theorem service_invariant_implies_deadline_met :
    ∀ (j : Job),
      service sched j (job_deadline j) = service sched' j (job_deadline j) →
      (job_meets_deadline sched j ↔ job_meets_deadline sched' j) := by
  intro j hservice
  show completed_by sched j (job_deadline j) ↔ completed_by sched' j (job_deadline j)
  show service sched j (job_deadline j) ≥ job_cost j ↔ service sched' j (job_deadline j) ≥ job_cost j
  exact Iff.intro (fun h => hservice ▸ h) (fun h => hservice ▸ h)

end EqualProgress

end DeadlineFacts

end Prosa.Analysis.Facts.Behavior.Deadlines
