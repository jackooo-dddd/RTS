-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: model/task/arrival/example.v

import Prosa.Model.Task.Arrival.Periodic
import Prosa.Model.Task.Arrival.PeriodicAsSporadic
import Prosa.Model.Task.Arrival.SporadicAsCurve
import Prosa.Model.Task.Arrival.CurveAsRbf

namespace Prosa.Model.Task.Arrival.Example

open Prosa.Behavior.Arrival_sequence
open Prosa.Behavior.Job
open Prosa.Model.Task.Concept
open Prosa.Model.Task.Arrival.Curves
open Prosa.Model.Task.Arrival.Sporadic
open Prosa.Model.Task.Arrival.Periodic
open Prosa.Model.Task.Arrival.PeriodicAsSporadic
open Prosa.Model.Task.Arrival.SporadicAsCurve
open Prosa.Model.Task.Arrival.CurveAsRbf
open Prosa.Model.Task.Arrival.RequestBoundFunctions

/-! Arrival-model conversion examples.

The source has no named declaration: its section states six anonymous `Goal`s, each closed by `by []`, i.e. by
type-class resolution of the conversion instances (`periodic_as_sporadic`, `MaxArrivalsSporadic`, `MaxArrivalsRBF`)
plus the `basic_rt_facts` hints of the conversion files. They are stated here as six theorems `goal_1` … `goal_6`, in
the source order and over the source section's inputs, so that each can be audited (`#print axioms`); an anonymous
Lean `example` cannot be. The instances are the accepted global Lean instances, resolved the same way; the hint
lemmas are applied explicitly. -/

section AutoArrivalModelConversion

variable {Task : TaskType} [DecidableEq Task] [PeriodicModel Task]
variable {Job : JobType} [DecidableEq Job] [JobArrival Job] [JobTask Job Task]
variable (ts : TaskSet Task) (arr_seq : arrival_sequence Job)

/-- Periodic tasks as sporadic tasks: valid minimum inter-arrival times. -/
theorem goal_1 (H_valid_periods : valid_periods ts) : valid_taskset_inter_arrival_times ts :=
  valid_periods_are_valid_inter_arrival_times ts H_valid_periods

/-- Periodic tasks as sporadic tasks: the arrival sequence respects the sporadic model. -/
theorem goal_2 (H_valid_arrival_sequence : valid_arrival_sequence arr_seq)
    (H_respects : taskset_respects_periodic_task_model arr_seq ts) (H_valid_periods : valid_periods ts) :
    taskset_respects_sporadic_task_model ts arr_seq :=
  periodic_task_sets_respect_sporadic_task_model arr_seq H_valid_arrival_sequence ts H_valid_periods H_respects

/-- Periodic tasks as arrival curves: valid arrival curves. -/
theorem goal_3 : valid_taskset_arrival_curve ts max_arrivals :=
  sporadic_task_sets_arrival_curve_valid ts

/-- Periodic tasks as arrival curves: the arrival sequence respects them. -/
theorem goal_4 (H_valid_arrival_sequence : valid_arrival_sequence arr_seq)
    (H_respects : taskset_respects_periodic_task_model arr_seq ts) (H_valid_periods : valid_periods ts) :
    taskset_respects_max_arrivals arr_seq ts :=
  sporadic_task_sets_respects_max_arrivals arr_seq H_valid_arrival_sequence ts
    (valid_periods_are_valid_inter_arrival_times ts H_valid_periods)
    (goal_2 ts arr_seq H_valid_arrival_sequence H_respects H_valid_periods)

variable [TaskCost Task] [JobCost Job]

/-- Periodic tasks as RBFs: valid request-bound functions. -/
theorem goal_5 : valid_taskset_request_bound_function ts (task_max_rbf max_arrivals) :=
  valid_taskset_arrival_curve_to_max_rbf ts (goal_3 ts)

/-- Periodic tasks as RBFs: the arrival sequence respects them. -/
theorem goal_6 (H_valid_arrival_sequence : valid_arrival_sequence arr_seq)
    (H_respects : taskset_respects_periodic_task_model arr_seq ts) (H_valid_periods : valid_periods ts)
    (H_valid_costs : jobs_have_valid_job_costs (Task := Task) (Job := Job)) :
    taskset_respects_max_request_bound arr_seq ts :=
  taskset_respects_arrival_curve_to_max_rbf ts arr_seq H_valid_costs
    (goal_4 ts arr_seq H_valid_arrival_sequence H_respects H_valid_periods)

end AutoArrivalModelConversion

end Prosa.Model.Task.Arrival.Example
