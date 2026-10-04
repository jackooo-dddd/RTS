/-
Usage example for the exported Prosa v0.6 Lean library.

Original: Prosa v0.6 (commit 414e66760333eaa4ef78c685bcf53291c527a548),
file `analysis/facts/behavior/completion.v`, `Lemma completion_monotonic`:

  forall t t', t <= t' -> completed_by sched j t -> completed_by sched j t'.

"Once a job has completed, it stays completed."  We re-prove it here from the
definitions of `completed_by`/`service` and the lower-level lemma
`service_cat` (service up to `t'` = service up to `t` + service in `[t, t')`).
The library's own translation of this lemma lives in
`Prosa.Analysis.Facts.Behavior.Completion`, which this file deliberately does
not import, so it cannot be used here.
-/
import Prosa.Analysis.Facts.Behavior.Service

open Prosa.Behavior.Job Prosa.Behavior.Schedule Prosa.Behavior.Service
open Prosa.Analysis.Facts.Behavior.Service

namespace RTSExample

/-- For any job type with costs, any processor model, schedule and job:
if `j` has completed by `t` and `t ≤ t'`, then `j` has completed by `t'`.
(Parameters as in the v0.6 section `CompletionFacts`; the unused section
context `JobArrival` is not part of the elaborated lemma.) -/
theorem completion_monotonic {Job : JobType} [DecidableEq Job] [JobCost Job]
    {PState : ProcessorState Job} (sched : schedule PState) (j : Job) :
    ∀ t t' : Nat, t ≤ t' →
      completed_by sched j t = true → completed_by sched j t' = true := by
  intro t t' hle hdone
  -- `completed_by sched j t` is the Boolean test `job_cost j ≤ service sched j t`.
  simp only [completed_by, decide_eq_true_eq] at hdone ⊢
  -- Split the service up to `t'` at `t`; the extra service is a natural number.
  rw [← service_cat sched j t t' hle]
  exact Nat.le_add_right_of_le hdone

end RTSExample

#print axioms RTSExample.completion_monotonic
