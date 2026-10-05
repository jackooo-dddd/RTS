import Prosa.Analysis.Facts.Transform.ReplaceAt
import Validation.fixtures.translation_order.FactsCompletionComputationInterface

/-!
Export root for `analysis/facts/transform/replace_at.v`: the production
declarations together with the accepted completion-facts export root
(Service / Schedule interfaces) and the accepted schedule transformation
`replace_at`.
-/

namespace Prosa.Validation.ReplaceAtInterface

open Prosa.Behavior.Job
open Prosa.Behavior.Schedule
open Prosa.Behavior.Time
open Prosa.Analysis.Transform.Swap

/-- Kernel-checked case equations for the body of `replace_at` (proved in
Lean and exported with their proofs). -/
theorem production_replace_at_same {Job : JobType} [DecidableEq Job] {PState : ProcessorState Job}
    (sched : schedule PState) (t' : instant) (ns : PState.State) (t : instant) (h : t = t') :
    replace_at sched t' ns t = ns := by
  subst h; simp [replace_at]

theorem production_replace_at_other {Job : JobType} [DecidableEq Job] {PState : ProcessorState Job}
    (sched : schedule PState) (t' : instant) (ns : PState.State) (t : instant) (h : ¬ t = t') :
    replace_at sched t' ns t = sched t := by
  have : (t' == t) = false := by simp [Ne.symm h]
  simp [replace_at, this]

end Prosa.Validation.ReplaceAtInterface
