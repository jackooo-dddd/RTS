-- Translated from: ../rt-proofs/model/processor/platform_properties.v
import Prosa.Behavior.All

namespace Prosa.Model.Processor.Platform_properties

open Prosa.Behavior.Job
open Prosa.Behavior.Time
open Prosa.Behavior.Schedule
open Prosa.Behavior.Service

section ProcessorModels

variable {Job : JobType}
variable (PState : Type _)
variable [ProcessorState Job PState]

def unit_service_proc_model :=
  ∀ (j : Job) (s : PState), ProcessorState.service_in j s ≤ 1

def ideal_progress_proc_model :=
  ∀ (j : Job) (s : PState), ProcessorState.scheduled_in j s = true → ProcessorState.service_in j s > 0

def uniprocessor_model :=
  ∀ (j1 j2 : Job) (s : schedule PState) (t : instant),
    scheduled_at s j1 t = true →
    scheduled_at s j2 t = true →
    j1 = j2

end ProcessorModels

end Prosa.Model.Processor.Platform_properties
