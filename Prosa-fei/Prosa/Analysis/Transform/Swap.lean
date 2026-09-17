-- Translated from: ../rt-proofs/analysis/transform/swap.v
import Prosa.Behavior.All

namespace Prosa.Analysis.Transform.Swap

open Prosa.Behavior.Time
open Prosa.Behavior.Job
open Prosa.Behavior.Schedule

section ReplaceAt

variable {Job : JobType}
variable {PState : Type _} [DecidableEq PState]
variable [ProcessorState Job PState]

variable (original_sched : schedule PState)
variable (t' : instant)
variable (new_state : PState)

def replace_at (t : instant) : PState :=
  if t' == t then new_state else original_sched t

end ReplaceAt

section Swapped

variable {Job : JobType}
variable {PState : Type _} [DecidableEq PState]
variable [ProcessorState Job PState]

variable (original_sched : schedule PState)
variable (t1 t2 : instant)

def swapped : schedule PState :=
  let s1 := original_sched t1
  let s2 := original_sched t2
  let replaced_s1 := replace_at original_sched t1 s2
  replace_at replaced_s1 t2 s1

end Swapped

end Prosa.Analysis.Transform.Swap
