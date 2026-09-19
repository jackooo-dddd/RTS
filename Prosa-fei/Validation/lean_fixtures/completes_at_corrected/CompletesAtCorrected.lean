import Prosa.Behavior.Service

namespace Prosa.Validation.CompletesAt

open Prosa.Behavior.Job
open Prosa.Behavior.Schedule
open Prosa.Behavior.Service
open Prosa.Behavior.Time

/-!
This validation-only fixture supplies a completely concrete zero-cost job and
processor state.  `production_completes_at_zero` deliberately calls the frozen
production declaration.  `completes_at_corrected` differs only by restoring the
source's explicit zero-time branch.
-/

instance unitProcessorState : ProcessorState Unit Unit where
  Core := Unit
  Core_fintype := inferInstance
  Core_deceq := inferInstance
  scheduled_on _ _ _ := false
  service_in _ _ := 0
  service_implies_scheduled := by
    intro _ _ _
    rfl

instance unitJobCost : JobCost Unit where
  job_cost _ := 0

instance unitJobDeadline : JobDeadline Unit where
  job_deadline _ := 0

instance unitJobArrival : JobArrival Unit where
  job_arrival _ := 0

def unitSchedule : schedule Unit := fun _ => ()

def production_completes_at_zero : Prop :=
  completes_at unitSchedule () 0

noncomputable def completes_at_corrected
    {Job : JobType} {PState : Type _}
    [ProcessorState Job PState]
    (sched : schedule PState)
    [JobCost Job] [JobDeadline Job] [JobArrival Job]
    (j : Job) (t : instant) : Prop :=
  (¬ completed_by sched j (t - 1) ∨ t = 0) ∧ completed_by sched j t

def corrected_completes_at_zero : Prop :=
  completes_at_corrected unitSchedule () 0

def production_completes_at_zero_normal_form : Prop :=
  (¬ (0 : Nat) ≤ 0) ∧ (0 : Nat) ≤ 0

def corrected_completes_at_zero_normal_form : Prop :=
  (¬ (0 : Nat) ≤ 0 ∨ (0 : Nat) = 0) ∧ (0 : Nat) ≤ 0

-- These `rfl` checks force Lean itself to confirm the concrete normal forms
-- used by the Rocq-side counterexample; they contain no proof search.
theorem production_completes_at_zero_defeq :
    production_completes_at_zero = production_completes_at_zero_normal_form := rfl

theorem corrected_completes_at_zero_defeq :
    corrected_completes_at_zero = corrected_completes_at_zero_normal_form := rfl

end Prosa.Validation.CompletesAt
