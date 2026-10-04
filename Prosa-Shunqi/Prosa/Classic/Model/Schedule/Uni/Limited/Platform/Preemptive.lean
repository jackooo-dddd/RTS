-- Authoritative source:
-- ProsaBuddy classic Prosa (prosabuddy commit f692cb7479780cf6009493f373a309e13165201c)
-- source: classic/model/schedule/uni/limited/platform/preemptive.v
-- sha256: see Prosa-Shunqi/classic-prosa/comprehensive-classic/file_order.csv (rank 105)

import Prosa.Classic.Util.All
import Prosa.Classic.Model.Arrival.Basic.Job
import Prosa.Classic.Model.Arrival.Basic.Task
import Prosa.Classic.Model.Priority
import Prosa.Classic.Model.Arrival.Basic.TaskArrival
import Prosa.Classic.Model.Schedule.Uni.Schedule
import Prosa.Classic.Model.Schedule.Uni.Service
import Prosa.Classic.Model.Schedule.Uni.Basic.Platform
import Prosa.Classic.Model.Schedule.Uni.Limited.Platform.Definitions

/-!
The fully preemptive model as a limited-preemption platform (Rocq module `FullyPreemptivePlatform`).

Representation notes: `ε` is the v0.6 util notation for `1`; the section-local `Let`s `job_max_nps := ε` and
`task_max_nps := ε` are unfolded to `fun _ => ε`; `Require Export …limited.platform.definitions` is an `import`.
Binder lists follow the Rocq contract.
-/

set_option linter.unusedVariables false

namespace Prosa.Classic.Model.Schedule.Uni.Limited.Platform.Preemptive.FullyPreemptivePlatform

open Prosa.Classic.Model.Time.Time
open Prosa.Classic.Model.Arrival.Basic.ArrivalSequence.ArrivalSequence
open Prosa.Classic.Model.Schedule.Uni.Schedule.UniprocessorSchedule
open Prosa.Classic.Model.Schedule.Uni.Limited.Platform.Definitions.LimitedPreemptionPlatform
open Prosa.Util.Epsilon

universe u v

def can_be_preempted_for_fully_preemptive_model {Job : Type v} [DecidableEq Job] (j : Job) (progr : time) : Bool :=
  true

theorem fully_preemptive_model_is_correct {Job : Type v} [DecidableEq Job] (arr_seq : arrival_sequence Job)
    (sched : schedule Job) :
    correct_preemption_model arr_seq sched (can_be_preempted_for_fully_preemptive_model (Job := Job)) := by
  intro j _
  constructor
  · intro t CONTR; simp [can_be_preempted_for_fully_preemptive_model] at CONTR
  · intro t _ _; rfl

theorem fully_preemptive_model_is_model_with_bounded_nonpreemptive_regions {Task : Type u} [DecidableEq Task]
    {Job : Type v} [DecidableEq Job] (job_cost : Job → time) (job_task : Job → Task) (arr_seq : arrival_sequence Job) :
    model_with_bounded_nonpreemptive_segments job_cost job_task arr_seq
      (can_be_preempted_for_fully_preemptive_model (Job := Job)) (fun _ => ε) (fun _ => ε) := by
  intro j _
  refine ⟨rfl, rfl, fun _ => Nat.le_refl _, ?_⟩
  intro t _
  exact ⟨t, by simp, rfl⟩

end Prosa.Classic.Model.Schedule.Uni.Limited.Platform.Preemptive.FullyPreemptivePlatform
