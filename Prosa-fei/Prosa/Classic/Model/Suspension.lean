-- Translated from: ../rt-proofs/classic/model/suspension.v
import Prosa.Classic.Model.Arrival.Basic.Arrival_sequence
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace Prosa.Classic.Model.Suspension

open Prosa.Classic.Model.Time
open Prosa.Classic.Model.Arrival.Basic.Arrival_sequence

section SuspensionTimes

variable (Job : Type _) [DecidableEq Job]

def job_suspension := Job → Time → Duration

end SuspensionTimes

section TotalSuspensionTime

variable {Job : Type _} [DecidableEq Job]
variable (job_cost : Job → Time)
variable (next_suspension : job_suspension Job)
variable (j : Job)

noncomputable def total_suspension :=
  ∑ t ∈ Finset.range (job_cost j), next_suspension j t

end TotalSuspensionTime

section DynamicSuspensions

variable {Task : Type _} [DecidableEq Task]
variable {Job : Type _} [DecidableEq Job]
variable (job_cost : Job → Time)
variable (job_task : Job → Task)
variable (next_suspension : job_suspension Job)
variable (suspension_bound : Task → Duration)

def dynamic_suspension_model :=
  ∀ j, total_suspension job_cost next_suspension j ≤ suspension_bound (job_task j)

end DynamicSuspensions

end Prosa.Classic.Model.Suspension
