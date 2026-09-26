-- Authoritative source: Prosa v0.6, commit
-- 414e66760333eaa4ef78c685bcf53291c527a548
-- analysis/facts/model/uniprocessor.v

import Prosa.Model.Processor.PlatformProperties
import Prosa.Util.Tactics

namespace Prosa.Analysis.Facts.Model.Uniprocessor

open Prosa.Behavior.Job
open Prosa.Behavior.Schedule
open Prosa.Behavior.Service
open Prosa.Model.Processor.PlatformProperties

section UniquenessOfTheScheduledJob

variable {Job : JobType} [DecidableEq Job]
variable {PState : ProcessorState Job}

/-- On a uniprocessor, if one job is scheduled then no other job is
scheduled at the same time. -/
theorem scheduled_job_at_neq (H_uni : uniprocessor_model PState)
    (sched : schedule PState) :
    ∀ (j j' : Job) (t : Prosa.Behavior.Time.instant),
      decide (j ≠ j') = true →
      scheduled_at sched j t = true →
      (!scheduled_at sched j' t) = true := by
  intro j j' t hneq hsched
  cases hsched' : scheduled_at sched j' t
  · rfl
  · exact absurd (H_uni j j' sched t hsched hsched') (of_decide_eq_true hneq)

end UniquenessOfTheScheduledJob

end Prosa.Analysis.Facts.Model.Uniprocessor
