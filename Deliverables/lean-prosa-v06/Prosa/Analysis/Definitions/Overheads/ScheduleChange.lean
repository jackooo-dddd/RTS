-- Authoritative source: Prosa v0.6, commit
-- 414e66760333eaa4ef78c685bcf53291c527a548
-- analysis/definitions/overheads/schedule_change.v

import Prosa.Model.Processor.Overheads
import Prosa.Util.List

namespace Prosa.Analysis.Definitions.Overheads.ScheduleChange

open Prosa.Behavior.Job
open Prosa.Behavior.Schedule
open Prosa.Behavior.Time
open Prosa.Model.Processor.Overheads
open Prosa.Util.List

universe u

/-- A schedule change at `t` means that the scheduled job differs from the
    immediately preceding instant, with predecessor saturating at zero. -/
def schedule_change {Job : JobType} [DecidableEq Job]
    (sched : schedule (processor_state Job)) (t : instant) : Bool :=
  decide (scheduled_job sched (Nat.pred t) ≠ scheduled_job sched t)

/-- Count schedule changes over the half-open interval `[t1, t2)`. -/
def number_schedule_changes {Job : JobType} [DecidableEq Job]
    (sched : schedule (processor_state Job)) (t1 t2 : instant) : Nat :=
  (index_iota t1 t2).countP (schedule_change sched)

/-- There are no changes strictly within `[t1, t2)`; the transition into
    `t1` is deliberately excluded. -/
def no_schedule_changes_during {Job : JobType} [DecidableEq Job]
    (sched : schedule (processor_state Job)) (t1 t2 : instant) : Bool :=
  decide (number_schedule_changes sched (t1 + 1) t2 = 0)

/-- The selected job (or idle state) is the same at every instant in the
    half-open interval `[t1, t2)`. -/
def scheduled_job_invariant {Job : JobType} [DecidableEq Job]
    (sched : schedule (processor_state Job)) (oj : Option Job)
    (t1 t2 : instant) : Bool :=
  (index_iota t1 t2).all (fun t => decide (scheduled_job sched t = oj))

end Prosa.Analysis.Definitions.Overheads.ScheduleChange
