-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: model/composite/valid_task_arrival_sequence.v

import Prosa.Model.Task.Arrivals
import Prosa.Model.Task.Arrival.Curves

namespace Prosa.Model.Composite.ValidTaskArrivalSequence

open Prosa.Behavior.Arrival_sequence
open Prosa.Behavior.Job
open Prosa.Model.Task.Concept
open Prosa.Model.Task.Arrival.Curves

/-- An arrival sequence is a valid task arrival sequence for `ts`: it is a valid
arrival sequence, all arriving jobs have valid costs, all jobs come from `ts`,
the task set respects its maximum-arrival bounds, and `max_arrivals` is a
valid arrival curve for `ts`. -/
def valid_task_arrival_sequence {Task : TaskType} [DecidableEq Task] [TaskCost Task]
    [MaxArrivals Task] {Job : JobType} [DecidableEq Job] [JobTask Job Task]
    [JobCost Job] [JobArrival Job] (ts : List Task) (arr_seq : arrival_sequence Job) : Prop :=
  valid_arrival_sequence arr_seq ∧
  arrivals_have_valid_job_costs (Task := Task) arr_seq ∧
  all_jobs_from_taskset arr_seq ts ∧
  taskset_respects_max_arrivals arr_seq ts ∧
  valid_taskset_arrival_curve ts max_arrivals

theorem valid_task_arrival_sequence_valid_arrivals {Task : TaskType} [DecidableEq Task]
    [TaskCost Task] [MaxArrivals Task] {Job : JobType} [DecidableEq Job] [JobTask Job Task]
    [JobCost Job] [JobArrival Job] (ts : List Task) (arr_seq : arrival_sequence Job) :
    valid_task_arrival_sequence ts arr_seq → valid_arrival_sequence arr_seq :=
  fun h => h.1

theorem valid_task_arrival_sequence_valid_costs {Task : TaskType} [DecidableEq Task]
    [TaskCost Task] [MaxArrivals Task] {Job : JobType} [DecidableEq Job] [JobTask Job Task]
    [JobCost Job] [JobArrival Job] (ts : List Task) (arr_seq : arrival_sequence Job) :
    valid_task_arrival_sequence ts arr_seq → arrivals_have_valid_job_costs (Task := Task) arr_seq :=
  fun h => h.2.1

theorem valid_task_arrival_sequence_from_taskset {Task : TaskType} [DecidableEq Task]
    [TaskCost Task] [MaxArrivals Task] {Job : JobType} [DecidableEq Job] [JobTask Job Task]
    [JobCost Job] [JobArrival Job] (ts : List Task) (arr_seq : arrival_sequence Job) :
    valid_task_arrival_sequence ts arr_seq → all_jobs_from_taskset arr_seq ts :=
  fun h => h.2.2.1

theorem valid_task_arrival_sequence_respects_max {Task : TaskType} [DecidableEq Task]
    [TaskCost Task] [MaxArrivals Task] {Job : JobType} [DecidableEq Job] [JobTask Job Task]
    [JobCost Job] [JobArrival Job] (ts : List Task) (arr_seq : arrival_sequence Job) :
    valid_task_arrival_sequence ts arr_seq → taskset_respects_max_arrivals arr_seq ts :=
  fun h => h.2.2.2.1

theorem valid_task_arrival_sequence_valid_curve {Task : TaskType} [DecidableEq Task]
    [TaskCost Task] [MaxArrivals Task] {Job : JobType} [DecidableEq Job] [JobTask Job Task]
    [JobCost Job] [JobArrival Job] (ts : List Task) (arr_seq : arrival_sequence Job) :
    valid_task_arrival_sequence ts arr_seq → valid_taskset_arrival_curve ts max_arrivals :=
  fun h => h.2.2.2.2

end Prosa.Model.Composite.ValidTaskArrivalSequence
