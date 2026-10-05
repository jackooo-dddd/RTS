-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: analysis/definitions/progress.v

import Prosa.Analysis.Facts.Behavior.Service

namespace Prosa.Analysis.Definitions.Progress

open Prosa.Behavior.Job
open Prosa.Behavior.Schedule
open Prosa.Behavior.Service
open Prosa.Behavior.Time
open Prosa.Analysis.Facts.Behavior.Service

/-! Representation notes: the Boolean comparisons `a < b` and `a == b` are
`decide (a < b)` and `decide (a = b)`; `~~ b` is `!b`; a Boolean in `Prop`
position is `= true`. The section's unused `JobCost` context is absent from
the elaborated types. -/

/-- The job has progressed between `t1` and `t2`: its service increased. -/
noncomputable def job_has_progressed {Job : JobType} [DecidableEq Job] {PState : ProcessorState Job}
    (sched : schedule PState) (j : Job) (t1 t2 : Nat) : Bool :=
  decide (service sched j t1 < service sched j t2)

/-- No progress between `t1` and `t2`: the service is unchanged. -/
noncomputable def no_progress {Job : JobType} [DecidableEq Job] {PState : ProcessorState Job}
    (sched : schedule PState) (j : Job) (t1 t2 : Nat) : Bool :=
  decide (service sched j t1 = service sched j t2)

/-- Not having progressed is equivalent to no progress (for `t1 ≤ t2`). -/
theorem no_progress_equiv {Job : JobType} [DecidableEq Job] {PState : ProcessorState Job}
    (sched : schedule PState) (j : Job) (t1 t2 : Nat) :
    t1 ≤ t2 →
      ((!job_has_progressed sched j t1 t2) = true ↔ no_progress sched j t1 t2 = true) := by
  intro hle
  have hmono := service_monotonic sched j t1 t2 hle
  simp only [job_has_progressed, no_progress, Bool.not_eq_eq_eq_not, Bool.not_true,
    decide_eq_false_iff_not, decide_eq_true_eq, Nat.not_lt]
  dsimp only [work] at hmono ⊢
  constructor <;> intro h <;> omega

/-- No progress during the `delta` time units preceding `t`. -/
noncomputable def no_progress_for {Job : JobType} [DecidableEq Job] {PState : ProcessorState Job}
    (sched : schedule PState) (j : Job) (t : instant) (delta : duration) : Bool :=
  no_progress sched j (t - delta) t

end Prosa.Analysis.Definitions.Progress
