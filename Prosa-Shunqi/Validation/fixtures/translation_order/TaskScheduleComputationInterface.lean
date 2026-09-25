import Prosa.Analysis.Definitions.TaskSchedule
import Validation.fixtures.translation_order.BigcatComputationInterface
import Validation.fixtures.translation_order.ScheduleComputationInterface
import Validation.fixtures.translation_order.ServiceComputationInterface

namespace Prosa.Validation.TaskScheduleInterface

open Prosa.Analysis.Definitions.TaskSchedule
open Prosa.Behavior.Arrival_sequence
open Prosa.Behavior.Job
open Prosa.Behavior.Schedule
open Prosa.Behavior.Time
open Prosa.Model.Task.Concept

universe u v w

/-- Source-shaped half-open sum, tied to the compiled production definition
by the whole-constant guard below. -/
noncomputable def taskServiceDuringProjection
    {Task : TaskType} [DecidableEq Task]
    {Job : JobType} [DecidableEq Job] [JobTask Job Task]
    {PState : ProcessorState Job}
    (arr_seq : arrival_sequence Job) (sched : schedule PState)
    (tsk : Task) (t1 t2 : instant) : work :=
  List.foldr Nat.add 0 <|
    (List.range' t1 (t2 - t1) 1).map fun t =>
      task_service_at arr_seq sched tsk t

noncomputable def taskServiceProjection
    {Task : TaskType} [DecidableEq Task]
    {Job : JobType} [DecidableEq Job] [JobTask Job Task]
    {PState : ProcessorState Job}
    (arr_seq : arrival_sequence Job) (sched : schedule PState)
    (tsk : Task) (t2 : instant) : work :=
  taskServiceDuringProjection arr_seq sched tsk 0 t2

theorem taskServiceDuringProjection_guard :
    @task_service_during = @taskServiceDuringProjection := rfl

theorem taskServiceProjection_guard :
    @task_service = @taskServiceProjection := rfl

/-- Actual `List.isEmpty` equations needed for the two nonempty tests. -/
theorem production_isEmpty_nil {T : Type u} :
    ([] : List T).isEmpty = true := rfl

theorem production_isEmpty_cons {T : Type u} (x : T) (xs : List T) :
    (x :: xs).isEmpty = false := rfl

end Prosa.Validation.TaskScheduleInterface
