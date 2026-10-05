-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: model/processor/platform_properties.v

import Prosa.Behavior.All
import Prosa.Model.Processor.Supply

namespace Prosa.Model.Processor.PlatformProperties

open Prosa.Behavior.Job
open Prosa.Behavior.Schedule
open Prosa.Behavior.Service
open Prosa.Behavior.Time
open Prosa.Model.Processor.Supply

universe u v w

variable {Job : JobType} [DecidableEq Job]
variable (PState : ProcessorState Job)

/-- Every job receives at most one unit of service in each state. -/
noncomputable def unit_service_proc_model : Prop :=
  ∀ (j : Job) (s : PState.State), ProcessorState.service_in PState j s ≤ 1

/-- A scheduled job receives strictly positive service. -/
noncomputable def ideal_progress_proc_model : Prop :=
  ∀ (j : Job) (s : PState.State),
    ProcessorState.scheduled_in PState j s = true →
      0 < ProcessorState.service_in PState j s

/-- At any instant, two scheduled jobs must be equal. -/
def uniprocessor_model : Prop :=
  ∀ (j1 j2 : Job) (sched : schedule PState) (t : instant),
    scheduled_at sched j1 t = true →
    scheduled_at sched j2 t = true →
    j1 = j2

/-- Each state supplies at most one unit in total. -/
noncomputable def unit_supply_proc_model : Prop :=
  ∀ s : PState.State, ProcessorState.supply_in PState s ≤ 1

/-- Per-core service is bounded by supply, hence unit supply implies unit service. -/
theorem unit_supply_is_unit_service :
    unit_supply_proc_model PState → unit_service_proc_model PState := by
  intro hsupply j s
  have hservice : ProcessorState.service_in PState j s ≤
      ProcessorState.supply_in PState s := by
    unfold ProcessorState.service_in ProcessorState.supply_in
    apply Finset.sum_le_sum
    intro r _
    exact PState.service_on_le_supply_on j s r
  exact hservice.trans (hsupply s)

/-- A scheduled job consumes all supply at that instant. -/
noncomputable def fully_consuming_proc_model : Prop :=
  ∀ (j : Job) (sched : schedule PState) (t : instant),
    scheduled_at sched j t = true →
      service_at sched j t = supply_at sched t

end Prosa.Model.Processor.PlatformProperties
