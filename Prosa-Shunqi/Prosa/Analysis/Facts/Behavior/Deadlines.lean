-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: analysis/facts/behavior/deadlines.v

import Prosa.Analysis.Facts.Behavior.Completion

namespace Prosa.Analysis.Facts.Behavior.Deadlines

open Prosa.Behavior.Job
open Prosa.Behavior.Ready
open Prosa.Behavior.Schedule
open Prosa.Behavior.Service
open Prosa.Behavior.Time
open Prosa.Analysis.Facts.Behavior.Service
open Prosa.Analysis.Facts.Behavior.Completion

/-! Representation notes: a Boolean in `Prop` position is `= true`; `~~ b`
is `!b`; a single comparison is the Lean proposition; a chained comparison
is `(decide _ && decide _) = true`. Binder orders and hypothesis sets follow
the elaborated types (unused section hypotheses are absent). -/

section DeadlineFacts

variable {Job : JobType} [DecidableEq Job] [JobCost Job] [JobDeadline Job]
variable {PState : ProcessorState Job}

/-- An incomplete job whose deadline is met has a later deadline. -/
theorem incomplete_implies_later_deadline (sched : schedule PState) :
    ∀ (j : Job) (t : instant), job_meets_deadline sched j = true →
      (!completed_by sched j t) = true → t < job_deadline j := by
  intro j t hmet hinc
  refine Nat.lt_of_not_le (fun hle => ?_)
  have := incompletion_monotonic sched j (job_deadline j) t hle hinc
  unfold job_meets_deadline at hmet
  rw [hmet] at this
  exact Bool.false_ne_true this

/-- An incomplete job whose deadline is met is scheduled before its deadline. -/
theorem incomplete_implies_scheduled_later (sched : schedule PState) :
    ∀ (j : Job) (t : instant), job_meets_deadline sched j = true →
      (!completed_by sched j t) = true →
        ∃ t' : Nat, (decide (t ≤ t') && decide (t' < job_deadline j)) = true ∧
          scheduled_at sched j t' = true := by
  intro j t hmet hinc
  apply cumulative_service_implies_scheduled
  have hlt := incomplete_implies_later_deadline sched j t hmet hinc
  have hcat := service_cat sched j t (job_deadline j) (Nat.le_of_lt hlt)
  have hless := (less_service_than_cost_is_incomplete sched j t).2 hinc
  unfold job_meets_deadline completed_by at hmet
  have hdl := of_decide_eq_true hmet
  try dsimp only [instant, duration, work] at *
  omega

/-- Under completed-jobs-don't-execute, a scheduled job meeting its deadline
is scheduled before the deadline. -/
theorem scheduled_at_implies_later_deadline (sched : schedule PState) :
    completed_jobs_dont_execute sched →
      ∀ (j : Job) (t : instant), job_meets_deadline sched j = true →
        scheduled_at sched j t = true → t < job_deadline j := by
  intro hc j t hmet hs
  exact incomplete_implies_later_deadline sched j t hmet
    (scheduled_implies_not_completed sched j hc t hs)

/-- Equal service at the deadline implies equal deadline outcomes. -/
theorem service_invariant_implies_deadline_met (sched sched' : schedule PState) :
    ∀ j : Job, service sched j (job_deadline j) = service sched' j (job_deadline j) →
      (job_meets_deadline sched j = true ↔ job_meets_deadline sched' j = true) := by
  intro j h
  unfold job_meets_deadline completed_by
  rw [h]

end DeadlineFacts

end Prosa.Analysis.Facts.Behavior.Deadlines
