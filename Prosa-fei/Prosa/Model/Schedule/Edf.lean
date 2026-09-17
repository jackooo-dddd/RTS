-- Translated from: ../rt-proofs/model/schedule/edf.v
import Prosa.Behavior.All

namespace Prosa.Model.Schedule.Edf

open Prosa.Behavior.Job
open Prosa.Behavior.Time
open Prosa.Behavior.Schedule
open Prosa.Behavior.Service

section AlternativeDefinitionOfEDF

variable (Job : JobType) [JobCost Job] [JobDeadline Job] [JobArrival Job]
variable (PState : Type _) [ProcessorState Job PState]

def EDF_at (sched : schedule PState) (t : instant) : Prop :=
  ∀ (j : Job),
    scheduled_at sched j t →
    ∀ (t' : instant) (j' : Job),
      t ≤ t' →
      scheduled_at sched j' t' →
      job_arrival j' ≤ t →
      job_deadline j ≤ job_deadline j'

def EDF_schedule (sched : schedule PState) : Prop :=
  ∀ t, EDF_at Job PState sched t

end AlternativeDefinitionOfEDF

end Prosa.Model.Schedule.Edf
