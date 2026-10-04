-- Authoritative source:
-- ProsaBuddy classic Prosa (prosabuddy commit f692cb7479780cf6009493f373a309e13165201c)
-- source: classic/model/arrival/curves/bounds.v
-- sha256: see Prosa-Shunqi/classic-prosa/comprehensive-classic/file_order.csv (rank 44)

import Prosa.Classic.Util.All
import Prosa.Classic.Model.Arrival.Basic.ArrivalSequence
import Prosa.Classic.Model.Arrival.Basic.TaskArrival
import Prosa.Util.Rel

/-!
Arrival curves and separation bounds (Rocq module `ArrivalCurves`).

Representation notes:
* `monotone leq (max_arrivals tsk)` is the v0.6 util relation `prosa.util.rel.monotone` (the source
  resolves `monotone` to it), i.e. `Prosa.Util.Rel.monotone (fun a b => decide (a ≤ b)) (max_arrivals tsk)`.
* `tsk \in ts` in proposition position is `tsk ∈ ts`; the section-local `Let`s `arrivals_of_tsk` and
  `num_arrivals_of_tsk` are unfolded.
-/

namespace Prosa.Classic.Model.Arrival.Curves.Bounds.ArrivalCurves

open Prosa.Classic.Model.Time.Time
open Prosa.Classic.Model.Arrival.Basic.ArrivalSequence.ArrivalSequence
open Prosa.Classic.Model.Arrival.Basic.TaskArrival.TaskArrival

universe u v

def is_arrival_bound {Task : Type u} [DecidableEq Task] {Job : Type v} [DecidableEq Job]
    (job_task : Job → Task) (arr_seq : arrival_sequence Job) (max_arrivals : Task → time → Nat)
    (tsk : Task) : Prop :=
  ∀ t1 t2 : time, t1 ≤ t2 → num_arrivals_of_task job_task arr_seq tsk t1 t2 ≤ max_arrivals tsk (t2 - t1)

def is_arrival_bound_for_taskset {Task : Type u} [DecidableEq Task] {Job : Type v} [DecidableEq Job]
    (job_task : Job → Task) (arr_seq : arrival_sequence Job) (max_arrivals : Task → time → Nat)
    (ts : List Task) : Prop :=
  ∀ tsk : Task, tsk ∈ ts → is_arrival_bound job_task arr_seq max_arrivals tsk

def zero_arrival_curve {Task : Type u} [DecidableEq Task] (max_arrivals : Task → time → Nat) (tsk : Task) :
    Prop :=
  max_arrivals tsk 0 = 0

def monotonic_arrival_curve {Task : Type u} [DecidableEq Task] (max_arrivals : Task → time → Nat)
    (tsk : Task) : Prop :=
  Prosa.Util.Rel.monotone (fun a b : Nat => decide (a ≤ b)) (max_arrivals tsk)

def proper_arrival_curve {Task : Type u} [DecidableEq Task] {Job : Type v} [DecidableEq Job]
    (job_task : Job → Task) (arr_seq : arrival_sequence Job) (max_arrivals : Task → time → Nat)
    (tsk : Task) : Prop :=
  is_arrival_bound job_task arr_seq max_arrivals tsk ∧
    zero_arrival_curve max_arrivals tsk ∧
    monotonic_arrival_curve max_arrivals tsk

def family_of_proper_arrival_curves {Task : Type u} [DecidableEq Task] {Job : Type v} [DecidableEq Job]
    (job_task : Job → Task) (arr_seq : arrival_sequence Job) (max_arrivals : Task → time → Nat)
    (ts : List Task) : Prop :=
  ∀ tsk : Task, tsk ∈ ts → proper_arrival_curve job_task arr_seq max_arrivals tsk

def is_separation_bound {Task : Type u} [DecidableEq Task] {Job : Type v} [DecidableEq Job]
    (job_task : Job → Task) (arr_seq : arrival_sequence Job) (min_length : Task → Nat → time)
    (tsk : Task) : Prop :=
  ∀ t1 t2 : time, t1 ≤ t2 → min_length tsk (num_arrivals_of_task job_task arr_seq tsk t1 t2) ≤ t2 - t1

end Prosa.Classic.Model.Arrival.Curves.Bounds.ArrivalCurves
