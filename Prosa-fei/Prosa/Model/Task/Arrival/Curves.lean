-- Translated from: ../rt-proofs/model/task/arrival/curves.v
import Prosa.Util.Rel
import Prosa.Model.Task.Arrivals

namespace Prosa.Model.Task.Arrival.Curves

open Prosa.Behavior.Job
open Prosa.Behavior.Time
open Prosa.Behavior.Arrival_sequence
open Prosa.Model.Task.Concept
open Prosa.Model.Task.Arrivals
open Prosa.Util.Rel

class MaxArrivals (Task : TaskType) where
  max_arrivals : Task → duration → Nat

export MaxArrivals (max_arrivals)

class MinArrivals (Task : TaskType) where
  min_arrivals : Task → duration → Nat

export MinArrivals (min_arrivals)

class MinSeparation (Task : TaskType) where
  min_separation : Task → Nat → duration

export MinSeparation (min_separation)

class MaxSeparation (Task : TaskType) where
  max_separation : Task → Nat → duration

export MaxSeparation (max_separation)

section ArrivalCurves

variable {Task : TaskType}
variable {Job : JobType}
variable [JobTask Job Task]

variable (arr_seq : arrival_sequence Job)

section ArrivalCurves

variable [DecidableEq Task]

def valid_arrival_curve (tsk : Task) (num_arrivals : duration → Nat) :=
  num_arrivals 0 = 0 ∧
  monotone num_arrivals Nat.ble

def respects_max_arrivals (tsk : Task) (max_arrivals : duration → Nat) :=
  ∀ (t1 t2 : instant),
    t1 ≤ t2 →
    number_of_task_arrivals arr_seq tsk t1 t2 ≤ max_arrivals (t2 - t1)

def respects_min_arrivals (tsk : Task) (min_arrivals : duration → Nat) :=
  ∀ (t1 t2 : instant),
    t1 ≤ t2 →
    min_arrivals (t2 - t1) ≤ number_of_task_arrivals arr_seq tsk t1 t2

end ArrivalCurves

section SeparationBound

variable [DecidableEq Task]

def respects_min_separation (tsk : Task) (min_separation : Nat → duration) :=
  ∀ t1 t2,
    t1 ≤ t2 →
    min_separation (number_of_task_arrivals arr_seq tsk t1 t2) ≤ t2 - t1

def respects_max_separation (tsk : Task) (max_separation : Nat → duration) :=
  ∀ t1 t2,
    t1 ≤ t2 →
    t2 - t1 ≤ max_separation (number_of_task_arrivals arr_seq tsk t1 t2)

end SeparationBound

end ArrivalCurves

section ArrivalCurvesModel

variable {Task : TaskType}
variable {Job : JobType}
variable [DecidableEq Task]
variable [JobTask Job Task]

variable (arr_seq : arrival_sequence Job)

variable [MaxArrivals Task]
         [MinArrivals Task]
         [MaxSeparation Task]
         [MinSeparation Task]

variable (ts : TaskSet Task)

def valid_taskset_arrival_curve (arrivals : Task → duration → Nat) :=
  ∀ (tsk : Task), tsk ∈ ts → valid_arrival_curve tsk (arrivals tsk)

def taskset_respects_max_arrivals :=
  ∀ (tsk : Task), tsk ∈ ts → respects_max_arrivals arr_seq tsk (max_arrivals tsk)

def taskset_respects_min_arrivals :=
  ∀ (tsk : Task), tsk ∈ ts → respects_min_arrivals arr_seq tsk (min_arrivals tsk)

def taskset_respects_max_separation :=
  ∀ (tsk : Task), tsk ∈ ts → respects_max_separation arr_seq tsk (max_separation tsk)

def taskset_respects_min_separation :=
  ∀ (tsk : Task), tsk ∈ ts → respects_min_separation arr_seq tsk (min_separation tsk)

end ArrivalCurvesModel

end Prosa.Model.Task.Arrival.Curves
