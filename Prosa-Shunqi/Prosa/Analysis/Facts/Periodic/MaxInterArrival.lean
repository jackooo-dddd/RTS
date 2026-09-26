-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: analysis/facts/periodic/max_inter_arrival.v

import Prosa.Analysis.Facts.Periodic.ArrivalSeparation
import Prosa.Model.Task.Arrival.TaskMaxInterArrival

namespace Prosa.Analysis.Facts.Periodic.MaxInterArrival

open Prosa.Behavior.Arrival_sequence
open Prosa.Behavior.Job
open Prosa.Behavior.Time
open Prosa.Model.Task.Concept
open Prosa.Model.Task.Arrivals
open Prosa.Model.Task.Arrival.Periodic
open Prosa.Model.Task.Arrival.Task_max_inter_arrival

/-! Periodic tasks respect the maximum inter-arrival model. Binders follow the
elaborated source types. Representation: the source's global instance is a
Lean `instance` with the same name, found by instance resolution in the
statements, as in the elaborated source types; a Boolean in `Prop` position is
`= true`. -/

macro "omega'" : tactic => `(tactic| (try dsimp only [instant, duration, work] at *) <;> omega)

/-- The maximum inter-arrival time of a periodic task is its period. -/
instance max_inter_eq_period {Task : TaskType} [DecidableEq Task] [PeriodicModel Task] :
    TaskMaxInterArrival Task :=
  ⟨task_period⟩

theorem valid_period_is_valid_max_inter_arrival_time {Task : TaskType} [DecidableEq Task]
    [PeriodicModel Task] :
    ∀ tsk : Task, valid_period tsk = true → positive_task_max_inter_arrival_time tsk = true :=
  fun _ h => h

theorem periodic_model_respects_max_inter_arrival_model {Task : TaskType} [DecidableEq Task]
    [PeriodicModel Task] {Job : JobType} [DecidableEq Job] [JobTask Job Task] [JobArrival Job]
    (arr_seq : arrival_sequence Job) (tsk : Task) :
    valid_period tsk = true → respects_periodic_task_model arr_seq tsk →
      valid_task_max_inter_arrival_time arr_seq tsk := by
  intro hvalid hper
  refine ⟨hvalid, ?_⟩
  intro j harr htsk hidx
  obtain ⟨j', harr', hidx', htsk', hja⟩ := hper j harr hidx htsk
  refine ⟨j', ?_, harr', htsk', ?_⟩
  · intro e
    rw [← e] at hidx'
    omega
  · have hp : 0 < task_period tsk := of_decide_eq_true hvalid
    show (decide (job_arrival j' ≤ job_arrival j) &&
      decide (job_arrival j ≤ job_arrival j' + task_period tsk)) = true
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    rw [hja]
    constructor <;> omega'

end Prosa.Analysis.Facts.Periodic.MaxInterArrival
