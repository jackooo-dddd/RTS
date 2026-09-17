-- Translated from: ../rt-proofs/classic/model/schedule/uni/limited/abstract_RTA/definitions.v
import Prosa.Classic.Model.Arrival.Basic.Job
import Prosa.Classic.Model.Schedule.Uni.Schedule
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic

namespace Prosa.Classic.Model.Schedule.Uni.Limited.Abstract_RTA.Definitions

open Prosa.Classic.Model.Time
open Prosa.Classic.Model.Arrival.Basic.Job
open Prosa.Classic.Model.Arrival.Basic.Arrival_sequence
open Prosa.Classic.Model.Schedule.Uni.Schedule

section Definitions

variable {Task : Type _} [DecidableEq Task]
variable {Job : Type _} [DecidableEq Job]
variable (job_arrival : Job → Time)
variable (job_cost : Job → Time)
variable (job_task : Job → Task)
variable (arr_seq : arrival_sequence Job)
variable (sched : schedule Job)
variable (tsk : Task)

variable (interference : Job → Time → Bool)
variable (interfering_workload : Job → Time → Time)

def cumul_interference (j : Job) (t1 t2 : Time) : Nat :=
  ∑ t ∈ Finset.Ico t1 t2, (interference j t).toNat

def cumul_interfering_workload (j : Job) (t1 t2 : Time) : Nat :=
  ∑ t ∈ Finset.Ico t1 t2, interfering_workload j t

section BusyInterval

def quiet_time (j : Job) (t : Time) : Prop :=
  cumul_interference interference j 0 t = cumul_interfering_workload interfering_workload j 0 t ∧
  ¬ pending_earlier_and_at job_arrival job_cost sched j t

def busy_interval_prefix (j : Job) (t1 t2 : Time) : Prop :=
  t1 ≤ job_arrival j ∧ job_arrival j < t2 ∧
  quiet_time job_arrival job_cost sched interference interfering_workload j t1 ∧
  (∀ t, t1 < t → t < t2 → ¬ quiet_time job_arrival job_cost sched interference interfering_workload j t)

def busy_interval (j : Job) (t1 t2 : Time) : Prop :=
  busy_interval_prefix job_arrival job_cost sched interference interfering_workload j t1 t2 ∧
  quiet_time job_arrival job_cost sched interference interfering_workload j t2

theorem busy_interval_is_unique :
    ∀ j t1 t2 t1' t2',
      busy_interval job_arrival job_cost sched interference interfering_workload j t1 t2 →
      busy_interval job_arrival job_cost sched interference interfering_workload j t1' t2' →
      t1 = t1' ∧ t2 = t2' := by
  intro j t1 t2 t1' t2'
  intro ⟨⟨h1_le, h1_lt, hqt1, hnq1⟩, hqt2⟩
  intro ⟨⟨h1_le', h1_lt', hqt1', hnq1'⟩, hqt2'⟩
  have heq1 : t1 = t1' := by
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
    · exact hnq1 t1' hlt (Nat.lt_of_le_of_lt h1_le' h1_lt) hqt1'
    · exact hnq1' t1 hgt (Nat.lt_of_le_of_lt h1_le h1_lt') hqt1
  subst heq1
  have heq2 : t2 = t2' := by
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
    · exact hnq1' t2 (Nat.lt_of_le_of_lt h1_le h1_lt) hlt hqt2
    · exact hnq1 t2' (Nat.lt_of_le_of_lt h1_le h1_lt') hgt hqt2'
  exact ⟨rfl, heq2⟩

end BusyInterval

section BusyIntervalProperties

def work_conserving : Prop :=
  ∀ j t1 t2 t,
    arrives_in arr_seq j →
    job_task j = tsk →
    job_cost j > 0 →
    busy_interval job_arrival job_cost sched interference interfering_workload j t1 t2 →
    t1 ≤ t ∧ t < t2 →
    (¬ interference j t ↔ scheduled_at sched j t = true)

def busy_intervals_are_bounded_by (L : Time) : Prop :=
  ∀ j,
    arrives_in arr_seq j →
    job_task j = tsk →
    job_cost j > 0 →
    ∃ t1 t2,
      t1 ≤ job_arrival j ∧ job_arrival j < t2 ∧
      t2 ≤ t1 + L ∧
      busy_interval job_arrival job_cost sched interference interfering_workload j t1 t2

def job_interference_is_bounded_by (interference_bound_function : Task → Time → Time → Time) : Prop :=
  ∀ t1 t2 delta j,
    busy_interval job_arrival job_cost sched interference interfering_workload j t1 t2 →
    t1 + delta < t2 →
    arrives_in arr_seq j →
    job_task j = tsk →
    ¬ completed_by job_cost sched j (t1 + delta) →
    let offset := job_arrival j - t1
    cumul_interference interference j t1 (t1 + delta) ≤ interference_bound_function tsk offset delta

end BusyIntervalProperties

end Definitions

end Prosa.Classic.Model.Schedule.Uni.Limited.Abstract_RTA.Definitions
