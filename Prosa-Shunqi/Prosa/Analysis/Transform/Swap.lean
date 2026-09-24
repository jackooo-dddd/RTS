-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: analysis/transform/swap.v

import Prosa.Behavior.All

namespace Prosa.Analysis.Transform.Swap

open Prosa.Behavior.Job
open Prosa.Behavior.Schedule
open Prosa.Behavior.Time

universe u

section ReplaceAt

variable {Job : JobType} [DecidableEq Job]
variable {PState : ProcessorState Job}
variable (original_sched : schedule PState)
variable (t' : instant) (new_state : PState.State)

/-- Override the processor state at exactly `t'`. -/
def replace_at : schedule PState :=
  fun t => if t' == t then new_state else original_sched t

end ReplaceAt

section Swapped

variable {Job : JobType} [DecidableEq Job]
variable {PState : ProcessorState Job}
variable (original_sched : schedule PState)
variable (t1 t2 : instant)

/-- Exchange the two states returned by a schedule at `t1` and `t2`. -/
def swapped : schedule PState :=
  let s1 := original_sched t1
  let s2 := original_sched t2
  let replaced_s1 := replace_at original_sched t1 s2
  replace_at replaced_s1 t2 s1

end Swapped

end Prosa.Analysis.Transform.Swap
