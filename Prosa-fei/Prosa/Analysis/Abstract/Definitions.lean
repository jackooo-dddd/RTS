-- Translated from: ../rt-proofs/analysis/abstract/definitions.v
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Prosa.Model.Task.Concept
import Prosa.Model.Processor.Ideal

namespace Prosa.Analysis.Abstract.Definitions

open Prosa.Behavior.Job
open Prosa.Behavior.Time
open Prosa.Behavior.Schedule
open Prosa.Behavior.Service
open Prosa.Behavior.Arrival_sequence
open Prosa.Model.Task.Concept
open Prosa.Model.Processor.Ideal

section AbstractRTADefinitions

section Definitions

variable {Job : JobType}
variable [DecidableEq Job]
variable {Task : TaskType}
variable [JobTask Job Task]
variable [JobArrival Job]
variable [JobCost Job]

variable (arr_seq : arrival_sequence Job)
variable (sched : schedule (processor_state Job))
variable (tsk : Task)
variable (interference : Job → instant → Bool)
variable (interfering_workload : Job → instant → duration)

noncomputable def cumul_interference (j : Job) (t1 t2 : instant) : Nat :=
  ∑ t ∈ Finset.Ico t1 t2, (interference j t).toNat

noncomputable def cumul_interfering_workload (j : Job) (t1 t2 : instant) : Nat :=
  ∑ t ∈ Finset.Ico t1 t2, interfering_workload j t

section BusyInterval

def quiet_time (j : Job) (t : instant) : Prop :=
  cumul_interference interference j 0 t = cumul_interfering_workload interfering_workload j 0 t ∧
  ¬ pending_earlier_and_at sched j t

def busy_interval_prefix (j : Job) (t1 t2 : instant) : Prop :=
  (t1 ≤ job_arrival j ∧ job_arrival j < t2) ∧
  quiet_time sched interference interfering_workload j t1 ∧
  (∀ t, t1 < t ∧ t < t2 → ¬ quiet_time sched interference interfering_workload j t)

def busy_interval (j : Job) (t1 t2 : instant) : Prop :=
  busy_interval_prefix sched interference interfering_workload j t1 t2 ∧
  quiet_time sched interference interfering_workload j t2

theorem busy_interval_is_unique :
    ∀ j t1 t2 t1' t2',
      busy_interval sched interference interfering_workload j t1 t2 →
      busy_interval sched interference interfering_workload j t1' t2' →
      t1 = t1' ∧ t2 = t2' := by
  intro j t1 t2 t1' t2' ⟨⟨⟨H1a, H1b⟩, QT1, NQ⟩, QT2⟩ ⟨⟨⟨H1a', H1b'⟩, QT1', NQ'⟩, QT2'⟩
  have EQ1 : t1 = t1' := by
    by_contra CONTR
    cases Nat.lt_or_gt_of_ne CONTR with
    | inl h => exact NQ t1' ⟨h, Nat.lt_of_le_of_lt H1a' H1b⟩ QT1'
    | inr h => exact NQ' t1 ⟨h, Nat.lt_of_le_of_lt H1a H1b'⟩ QT1
  subst EQ1
  refine ⟨rfl, ?_⟩
  by_contra CONTR
  cases Nat.lt_or_gt_of_ne CONTR with
  | inl h => exact NQ' t2 ⟨Nat.lt_of_le_of_lt H1a H1b, h⟩ QT2
  | inr h => exact NQ t2' ⟨Nat.lt_of_le_of_lt H1a' H1b', h⟩ QT2'

end BusyInterval

section BusyIntervalProperties

def work_conserving : Prop :=
  ∀ j t1 t2 t,
    arrives_in arr_seq j →
    job_task j = tsk →
    job_cost j > 0 →
    busy_interval sched interference interfering_workload j t1 t2 →
    t1 ≤ t ∧ t < t2 →
    (¬ (interference j t = true) ↔ scheduled_at sched j t = true)

def busy_intervals_are_bounded_by (L : duration) : Prop :=
  ∀ j,
    arrives_in arr_seq j →
    job_task j = tsk →
    job_cost j > 0 →
    ∃ t1 t2,
      (t1 ≤ job_arrival j ∧ job_arrival j < t2) ∧
      t2 ≤ t1 + L ∧
      busy_interval sched interference interfering_workload j t1 t2

def job_interference_is_bounded_by
    (interference_bound_function : Task → duration → duration → duration) : Prop :=
  ∀ t1 t2 delta j,
    arrives_in arr_seq j →
    job_task j = tsk →
    busy_interval sched interference interfering_workload j t1 t2 →
    t1 + delta < t2 →
    ¬ completed_by sched j (t1 + delta) →
    let offset := job_arrival j - t1
    cumul_interference interference j t1 (t1 + delta) ≤ interference_bound_function tsk offset delta

end BusyIntervalProperties

end Definitions

end AbstractRTADefinitions

end Prosa.Analysis.Abstract.Definitions
