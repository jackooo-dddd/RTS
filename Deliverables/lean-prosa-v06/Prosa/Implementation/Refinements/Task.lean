-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: implementation/refinements/task.v

import Prosa.Implementation.Refinements.ArrivalBound
import Prosa.Implementation.Definitions.Task

/-! # Refinement of concrete tasks

A generic version of the concrete task (over a type `T` with the CoqEAL operation classes) and the refinements
relating it, at the binary numbers `N`, to the natural-number concrete task.

Representation (as in `Refinements`): Rocq cumulativity `Prop ≤ Type` is `PLift`; the source's `Type`-valued
`Global Instance`s are Lean definitions; the `Task`/`Job` aliases (the concrete types as `eqType`s) are the
accepted abbreviations; the source's `Local Instance`s and parsing-only notations are not public declarations. -/

set_option linter.dupNamespace false
set_option warn.classDefReducibility false

namespace Prosa.Implementation.Refinements.Task

open Prosa.Implementation.Refinements.Refinements
open Prosa.Implementation.Refinements.ArrivalBound
open Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve
open Prosa.Implementation.Definitions.ArrivalBound
open Prosa.Implementation.Definitions.Task

/-- The concrete task type. -/
abbrev Task : Type := concrete_task

/-- The concrete job type. -/
abbrev Job : Type := concrete_job

/-- A generic task. -/
structure task_T (T : Type) : Type where
  task_id_T : T
  task_cost_T : T
  task_arrival_T : task_arrivals_bound_T T
  task_deadline_T : T
  task_priority_T : T

open task_arrivals_bound_T

/-- Equality of generic tasks, attribute by attribute. -/
def task_eqdef_T {T : Type} [eq_of T] [eq_of (task_arrivals_bound_T T)] (t1 t2 : task_T T) : Bool :=
  eq_op (task_T.task_id_T t1) (task_T.task_id_T t2)
    && eq_op (task_T.task_cost_T t1) (task_T.task_cost_T t2)
    && eq_op (task_T.task_arrival_T t1) (task_T.task_arrival_T t2)
    && eq_op (task_T.task_deadline_T t1) (task_T.task_deadline_T t2)
    && eq_op (task_T.task_priority_T t1) (task_T.task_priority_T t2)

/-- A minimum inter-arrival time as an arrival-curve prefix. -/
def inter_arrival_to_extrapolated_arrival_curve_T {T : Type} [one_of T] (p : T) : T × List (T × T) :=
  (p, [(one_op, one_op)])

/-- The arrival-curve prefix of a generic task. -/
def get_extrapolated_arrival_curve_T {T : Type} [one_of T] (tsk : task_T T) : T × List (T × T) :=
  match task_T.task_arrival_T tsk with
  | Periodic_T p => inter_arrival_to_extrapolated_arrival_curve_T p
  | Sporadic_T m => inter_arrival_to_extrapolated_arrival_curve_T m
  | ArrivalPrefix_T steps => steps

/-- The generic maximum number of arrivals. -/
def ConcreteMaxArrivals_T {T : Type} [zero_of T] [one_of T] [add_of T] [mul_of T] [div_of T] [mod_of T]
    [leq_of T] (tsk : task_T T) (Δ : T) : T :=
  extrapolated_arrival_curve_T (get_extrapolated_arrival_curve_T tsk) Δ

/-- The generic request-bound function. -/
def task_rbf_T {T : Type} [zero_of T] [one_of T] [add_of T] [mul_of T] [div_of T] [mod_of T] [leq_of T]
    (tsk : task_T T) (Δ : T) : T :=
  mul_op (task_T.task_cost_T tsk) (ConcreteMaxArrivals_T tsk Δ)

/-- A valid generic arrival bound. -/
def valid_arrivals_T {T : Type} [zero_of T] [one_of T] [eq_of T] [leq_of T] [lt_of T] (tsk : task_T T) : Bool :=
  match task_T.task_arrival_T tsk with
  | Periodic_T p => leq_op one_op p
  | Sporadic_T m => leq_op one_op m
  | ArrivalPrefix_T ac_prefix_vec => valid_extrapolated_arrival_curve_T ac_prefix_vec

/-- The horizon of the arrival-curve prefix of a generic task. -/
def get_horizon_of_task_T {T : Type} [one_of T] (tsk : task_T T) : T :=
  horizon_of_T (get_extrapolated_arrival_curve_T tsk)

/-- The time steps of the arrival-curve prefix of a generic task. -/
def get_time_steps_of_task_T {T : Type} [one_of T] (tsk : task_T T) : List T :=
  time_steps_of_T (get_extrapolated_arrival_curve_T tsk)

/-- The time steps shifted by an offset. -/
def time_steps_with_offset_T {T : Type} [one_of T] [add_of T] (tsk : task_T T) (δ : T) : List T :=
  (get_time_steps_of_task_T tsk).map (fun t => add_op t δ)

/-- The time steps repeated for each offset. -/
def repeat_steps_with_offset_T {T : Type} [one_of T] [add_of T] (tsk : task_T T) (offsets : List T) : List T :=
  (offsets.map (time_steps_with_offset_T tsk)).flatten

/-- A binary generic task as a natural-number task. -/
def taskT_to_task (tsk : task_T N) : Task :=
  match tsk with
  | ⟨id, cost, arrival_bound, deadline, priority⟩ =>
    { task_id := nat_of_bin id, task_cost := nat_of_bin cost,
      task_arrival := task_abT_to_task_ab arrival_bound,
      task_deadline := nat_of_bin deadline, task_priority := nat_of_bin priority }

/-- Its graph relation. -/
def Rtask : Task → task_T N → Type := fun_hrel taskT_to_task

/-- A natural-number task as a binary generic task. -/
def task_to_taskT (tsk : Task) : task_T N :=
  match tsk with
  | ⟨id, cost, arrival_bound, deadline, priority⟩ =>
    { task_id_T := bin_of_nat id, task_cost_T := bin_of_nat cost,
      task_arrival_T := task_ab_to_task_abT arrival_bound,
      task_deadline_T := bin_of_nat deadline, task_priority_T := bin_of_nat priority }

/-! ### Refinements -/

/-- Refinement of the task constructor. -/
def refine_task :
    refines (hrespectful Rnat (hrespectful Rnat (hrespectful Rtask_ab (hrespectful Rnat (hrespectful Rnat Rtask)))))
      concrete_task.mk task_T.mk :=
  ⟨fun _ _ Ri _ _ Rc _ _ Rp _ _ Rd _ _ Rpr => ⟨by
    simp only [taskT_to_task, Rnat_eq Ri, Rnat_eq Rc, Rp.down, Rnat_eq Rd, Rnat_eq Rpr]⟩⟩

/-- Refinement of the task identifier. -/
def refine_task_id : refines (hrespectful Rtask Rnat) concrete_task.task_id task_T.task_id_T :=
  ⟨fun _ tsk h => Rnat_intro (by rw [← h.down]; cases tsk; rfl)⟩

/-- Refinement of the task cost. -/
def refine_task_cost : refines (hrespectful Rtask Rnat) concrete_task.task_cost task_T.task_cost_T :=
  ⟨fun _ tsk h => Rnat_intro (by rw [← h.down]; cases tsk; rfl)⟩

/-- Refinement of the task arrival bound. -/
def refine_task_arrival : refines (hrespectful Rtask Rtask_ab) concrete_task.task_arrival task_T.task_arrival_T :=
  ⟨fun _ tsk h => ⟨by rw [← h.down]; cases tsk; rfl⟩⟩

/-- Refinement of the task deadline. -/
def refine_task_deadline : refines (hrespectful Rtask Rnat) concrete_task.task_deadline task_T.task_deadline_T :=
  ⟨fun _ tsk h => Rnat_intro (by rw [← h.down]; cases tsk; rfl)⟩

/-- Refinement of the task priority. -/
def refine_task_priority : refines (hrespectful Rtask Rnat) concrete_task.task_priority task_T.task_priority_T :=
  ⟨fun _ tsk h => Rnat_intro (by rw [← h.down]; cases tsk; rfl)⟩

/-- Refinement of the `Periodic` constructor. -/
def refine_Periodic : refines (hrespectful Rnat Rtask_ab) task_arrivals_bound.Periodic Periodic_T :=
  ⟨fun _ _ Rt => ⟨by simp only [task_abT_to_task_ab, Rnat_eq Rt]⟩⟩

/-- Refinement of the `Sporadic` constructor. -/
def refine_Sporadic : refines (hrespectful Rnat Rtask_ab) task_arrivals_bound.Sporadic Sporadic_T :=
  ⟨fun _ _ Rt => ⟨by simp only [task_abT_to_task_ab, Rnat_eq Rt]⟩⟩

end Prosa.Implementation.Refinements.Task
