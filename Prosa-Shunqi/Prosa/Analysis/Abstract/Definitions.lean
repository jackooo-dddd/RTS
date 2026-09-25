-- Authoritative source: Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: analysis/abstract/definitions.v

import Mathlib.Algebra.BigOperators.Intervals
import Prosa.Model.Task.Concept

namespace Prosa.Analysis.Abstract.Definitions

open Prosa.Behavior.Arrival_sequence
open Prosa.Behavior.Job
open Prosa.Behavior.Schedule
open Prosa.Behavior.Service
open Prosa.Behavior.Time
open Prosa.Model.Task.Concept
open scoped BigOperators

universe u v w

/-- Boolean observation that a job incurs interference at an instant. -/
class Interference (Job : JobType) [DecidableEq Job] where
  interference : Job → instant → Bool

export Interference (interference)

/-- Interfering workload introduced for a job at an instant. -/
class InterferingWorkload (Job : JobType) [DecidableEq Job] where
  interfering_workload : Job → instant → duration

export InterferingWorkload (interfering_workload)

section AbstractRTADefinitions

variable {Job : JobType} [DecidableEq Job]
variable [Interference Job] [InterferingWorkload Job]

/-- Restrict interference by a Boolean condition. -/
def cond_interference (P : Job → instant → Bool) (j : Job) (t : instant) : Bool :=
  P j t && interference j t

/-- Cumulative conditional interference over the half-open interval. -/
noncomputable def cumul_cond_interference
    (P : Job → instant → Bool) (j : Job) (t1 t2 : instant) : Nat :=
  ∑ t ∈ Finset.Ico t1 t2, (cond_interference P j t).toNat

/-- Cumulative interference without an additional condition. -/
noncomputable def cumulative_interference (j : Job) (t1 t2 : instant) : Nat :=
  cumul_cond_interference (fun _ _ => true) j t1 t2

/-- Cumulative interfering workload over the same half-open interval. -/
noncomputable def cumulative_interfering_workload
    (j : Job) (t1 t2 : instant) : Nat :=
  ∑ t ∈ Finset.Ico t1 t2, interfering_workload j t

/-- The interference cannot exceed the workload that has appeared. -/
def no_speculative_execution : Prop :=
  ∀ (j : Job) (t : instant),
    cumulative_interference j 0 t ≤ cumulative_interfering_workload j 0 t

section BusyInterval

variable [JobArrival Job] [JobCost Job]
variable {PState : ProcessorState Job}
variable (sched : schedule PState)

/-- A Boolean quiet-time observation. It remains Boolean as in the source. -/
noncomputable def quiet_time (j : Job) (t : instant) : Bool :=
  decide (cumulative_interference j 0 t =
    cumulative_interfering_workload j 0 t) &&
    !pending_earlier_and_at sched j t

/-- The arrival lies in the interval, its start is quiet, and its interior
is not quiet. -/
def busy_interval_prefix (j : Job) (t1 t2 : instant) : Prop :=
  (t1 ≤ job_arrival j ∧ job_arrival j < t2) ∧
    quiet_time sched j t1 = true ∧
    (∀ t, t1 < t ∧ t < t2 → ¬ quiet_time sched j t = true)

/-- A busy-interval prefix whose endpoint is also quiet. -/
def busy_interval (j : Job) (t1 t2 : instant) : Prop :=
  busy_interval_prefix sched j t1 t2 ∧ quiet_time sched j t2 = true

/-- Busy intervals for the same job have unique endpoints. -/
theorem busy_interval_is_unique :
    ∀ (j : Job) (t1 t2 t1' t2' : instant),
      busy_interval sched j t1 t2 →
      busy_interval sched j t1' t2' →
      t1 = t1' ∧ t2 = t2' := by
  intro j t1 t2 t1' t2'
  rintro ⟨⟨⟨Hstart, Harrival⟩, Hquiet, HnotQuiet⟩, Hend⟩
  rintro ⟨⟨⟨Hstart', Harrival'⟩, Hquiet', HnotQuiet'⟩, Hend'⟩
  have Hleft : t1 = t1' := by
    by_contra Hne
    rcases Nat.lt_or_gt_of_ne Hne with Hlt | Hgt
    · exact HnotQuiet t1' ⟨Hlt, Nat.lt_of_le_of_lt Hstart' Harrival⟩ Hquiet'
    · exact HnotQuiet' t1 ⟨Hgt, Nat.lt_of_le_of_lt Hstart Harrival'⟩ Hquiet
  subst t1'
  refine ⟨rfl, ?_⟩
  by_contra Hne
  rcases Nat.lt_or_gt_of_ne Hne with Hlt | Hgt
  · exact HnotQuiet' t2 ⟨Nat.lt_of_le_of_lt Hstart Harrival, Hlt⟩ Hend
  · exact HnotQuiet t2' ⟨Nat.lt_of_le_of_lt Hstart' Harrival', Hgt⟩ Hend'

end BusyInterval

section BusyIntervalProperties

variable [JobArrival Job] [JobCost Job]
variable {PState : ProcessorState Job}
variable (arrSeq : arrival_sequence Job) (sched : schedule PState)

/-- Within a busy interval, a positive-cost arriving job either incurs
interference or receives service. -/
def work_conserving : Prop :=
  ∀ (j : Job) (t1 t2 t : instant),
    arrives_in arrSeq j →
    job_cost j > 0 →
    busy_interval_prefix sched j t1 t2 →
    t1 ≤ t ∧ t < t2 →
    (¬ interference j t = true ↔ receives_service_at sched j t = true)

variable {Task : TaskType} [DecidableEq Task] [JobTask Job Task]
variable (tsk : Task)

/-- Every relevant task job has a bounded busy interval. -/
def busy_intervals_are_bounded_by (L : duration) : Prop :=
  ∀ (j : Job),
    arrives_in arrSeq j →
    job_of_task tsk j = true →
    job_cost j > 0 →
    ∃ t1 t2,
      (t1 ≤ job_arrival j ∧ job_arrival j < t2) ∧
      t2 ≤ t1 + L ∧
      busy_interval sched j t1 t2

/-- A conditional interference-bound function for task `tsk`. -/
def cond_interference_is_bounded_by
    (IBF : duration → duration → work)
    (ParamSem : Job → Nat → Prop)
    (Cond : Job → instant → Bool) : Prop :=
  ∀ (t1 t2 Δ : instant) (j : Job),
    arrives_in arrSeq j →
    job_of_task tsk j = true →
    busy_interval sched j t1 t2 →
    t1 + Δ < t2 →
    (!completed_by sched j (t1 + Δ)) = true →
    ∀ X, ParamSem j X →
      cumul_cond_interference Cond j t1 (t1 + Δ) ≤ IBF X Δ

/-- The unconditional special case of a conditional interference bound. -/
def job_interference_is_bounded_by
    (IBF : duration → duration → work)
    (ParamSem : Job → Nat → Prop) : Prop :=
  cond_interference_is_bounded_by arrSeq sched tsk IBF ParamSem
    (fun _ _ => true)

end BusyIntervalProperties

end AbstractRTADefinitions

end Prosa.Analysis.Abstract.Definitions
