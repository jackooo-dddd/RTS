-- Translated from: ../rt-proofs/classic/model/arrival/curves/bounds.v
import Prosa.Classic.Model.Arrival.Basic.Arrival_sequence
import Mathlib.Order.Monotone.Basic

namespace Prosa.Classic.Model.Arrival.Curves.Bounds

open Prosa.Classic.Model.Time
open Prosa.Classic.Model.Arrival.Basic.Arrival_sequence

namespace ArrivalCurves

section DefiningArrivalCurves

variable {Task : Type _} [DecidableEq Task]
variable {Job : Type _} [DecidableEq Job]
variable (job_task : Job → Task)
variable (arr_seq : arrival_sequence Job)

private def arrivals_of_tsk (tsk : Task) (t1 t2 : Time) : List Job :=
  (jobs_arrived_between arr_seq t1 t2).filter (fun j => decide (job_task j = tsk))

private def num_arrivals_of_tsk (tsk : Task) (t1 t2 : Time) : Nat :=
  (arrivals_of_tsk job_task arr_seq tsk t1 t2).length

section ArrivalBound

variable (max_arrivals : Task → Time → Nat)

def is_arrival_bound (tsk : Task) :=
  ∀ (t1 t2 : Time),
    t1 ≤ t2 →
    num_arrivals_of_tsk job_task arr_seq tsk t1 t2 ≤ max_arrivals tsk (t2 - t1)

def is_arrival_bound_for_taskset (ts : List Task) :=
  ∀ (tsk : Task), tsk ∈ ts → is_arrival_bound job_task arr_seq max_arrivals tsk

def zero_arrival_curve (tsk : Task) :=
  max_arrivals tsk 0 = 0

def monotonic_arrival_curve (tsk : Task) :=
  Monotone (max_arrivals tsk)

def proper_arrival_curve (tsk : Task) :=
  is_arrival_bound job_task arr_seq max_arrivals tsk ∧
  zero_arrival_curve max_arrivals tsk ∧
  monotonic_arrival_curve max_arrivals tsk

def family_of_proper_arrival_curves (ts : List Task) :=
  ∀ (tsk : Task), tsk ∈ ts → proper_arrival_curve job_task arr_seq max_arrivals tsk

end ArrivalBound

section SeparationBound

variable (min_length : Task → Nat → Time)

def is_separation_bound (tsk : Task) :=
  ∀ (t1 t2 : Time),
    t1 ≤ t2 →
    min_length tsk (num_arrivals_of_tsk job_task arr_seq tsk t1 t2) ≤ t2 - t1

end SeparationBound

end DefiningArrivalCurves

end ArrivalCurves

end Prosa.Classic.Model.Arrival.Curves.Bounds
