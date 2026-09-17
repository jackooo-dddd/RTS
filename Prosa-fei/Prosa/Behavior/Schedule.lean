-- Translated from: ../rt-proofs/behavior/schedule.v
import Mathlib.Data.Fintype.Basic
import Prosa.Behavior.Arrival_sequence

namespace Prosa.Behavior.Schedule

open Prosa.Behavior.Job
open Prosa.Behavior.Time

class ProcessorState (Job : JobType) (State : Type _) where
  Core : Type
  Core_fintype : Fintype Core
  Core_deceq : DecidableEq Core
  scheduled_on : Job → State → Core → Bool
  service_in : Job → State → work
  service_implies_scheduled :
    ∀ j s, (¬ ∃ c : Core, scheduled_on j s c = true) → service_in j s = 0

namespace ProcessorState

variable {Job : JobType} {State : Type _} [ProcessorState Job State]

noncomputable def scheduled_in (j : Job) (s : State) : Bool :=
  have : Fintype (ProcessorState.Core Job State) := ProcessorState.Core_fintype
  have : DecidableEq (ProcessorState.Core Job State) := ProcessorState.Core_deceq
  decide (∃ c : ProcessorState.Core Job State, scheduled_on j s c = true)

end ProcessorState

def schedule (PState : Type _) := instant → PState

end Prosa.Behavior.Schedule
