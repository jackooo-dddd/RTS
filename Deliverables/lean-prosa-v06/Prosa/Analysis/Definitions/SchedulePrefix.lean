-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: analysis/definitions/schedule_prefix.v

import Prosa.Behavior.Ready
import Prosa.Util.Nat

namespace Prosa.Analysis.Definitions.SchedulePrefix

open Prosa.Behavior.Job
open Prosa.Behavior.Time
open Prosa.Behavior.Schedule
open Prosa.Behavior.Service

universe u v w

section PrefixDefinition

variable {Job : JobType} [DecidableEq Job]
variable {PState : ProcessorState Job}

/-- Two schedules have the same processor state before `horizon`. -/
def identical_prefix (sched sched' : schedule PState)
    (horizon : instant) : Prop :=
  ∀ t, t < horizon → sched t = sched' t

/-- Prefix-identical schedules agree on the Boolean scheduled-at observation. -/
theorem identical_prefix_scheduled_at
    (sched sched' : schedule PState) (h : instant)
    (hp : identical_prefix sched sched' h)
    (j : Job) (t : instant) (ht : t < h) :
    scheduled_at sched j t = scheduled_at sched' j t := by
  rw [scheduled_at, scheduled_at, hp t ht]

/-- Identical prefixes remain identical when the horizon is shortened. -/
theorem identical_prefix_inclusion
    (sched sched' : schedule PState) (h h' : instant)
    (hle : h' ≤ h) (hp : identical_prefix sched sched' h) :
    identical_prefix sched sched' h' := by
  intro t ht
  exact hp t (Nat.lt_of_lt_of_le ht hle)

end PrefixDefinition

end Prosa.Analysis.Definitions.SchedulePrefix
