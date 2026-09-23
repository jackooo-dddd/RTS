-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: analysis/definitions/sbf/average.v

import Prosa.Model.Processor.Supply

namespace Prosa.Analysis.Definitions.Sbf.Average

open Prosa.Behavior.Job
open Prosa.Behavior.Schedule
open Prosa.Behavior.Time
open Prosa.Model.Processor.Supply

section AverageResourceModel

variable {Job : JobType} [DecidableEq Job]
variable {PState : ProcessorState Job}

/-- The average-resource supply lower bound, including its unit-supply
    restriction. All subtraction is truncated natural subtraction. -/
noncomputable def average_resource_model
    (period allocation delay : duration) (sched : schedule PState) : Prop :=
  period ≥ allocation ∧
    ∀ t1 t2 : duration,
      supply_during sched t1 t2 ≥
        (((t2 - t1) - delay) * allocation) / period

end AverageResourceModel

section AverageResourceModelSBF

/-- The average-resource model's supply bound as a function of interval
    length. -/
def arm_sbf (period allocation delay delta : duration) : duration :=
  (((delta - delay) * allocation) / period)

end AverageResourceModelSBF

end Prosa.Analysis.Definitions.Sbf.Average
