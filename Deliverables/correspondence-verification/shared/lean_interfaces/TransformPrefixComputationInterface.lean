import Prosa.Analysis.Transform.Prefix
import Validation.fixtures.translation_order.PreemptionParameterComputationInterface

/-!
Export root for `analysis/transform/prefix.v`: the production declarations,
the accepted preemption-parameter export root (Schedule closure), and
kernel-checked case equations for the structural recursion of `prefix_map`.
Every equation is proved in Lean and exported with its proof.
-/

namespace Prosa.Validation.TransformPrefixInterface

open Prosa.Behavior.Job
open Prosa.Behavior.Schedule
open Prosa.Behavior.Time
open Prosa.Analysis.Transform.Prefix

variable {Job : JobType} [DecidableEq Job] {PState : ProcessorState Job}

theorem production_prefix_map_zero (sched : schedule PState)
    (f : schedule PState → instant → schedule PState) :
    prefix_map sched f 0 = sched := rfl

theorem production_prefix_map_succ (sched : schedule PState)
    (f : schedule PState → instant → schedule PState) (t : Nat) :
    prefix_map sched f (Nat.succ t) = f (prefix_map sched f t) t := rfl

end Prosa.Validation.TransformPrefixInterface
