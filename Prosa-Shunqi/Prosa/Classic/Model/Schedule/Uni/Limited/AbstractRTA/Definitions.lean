-- Authoritative source:
-- ProsaBuddy classic Prosa (prosabuddy commit f692cb7479780cf6009493f373a309e13165201c)
-- source: classic/model/schedule/uni/limited/abstract_RTA/definitions.v
-- sha256: see Prosa-Shunqi/classic-prosa/comprehensive-classic/file_order.csv (rank 54)

import Prosa.Classic.Util.All
import Prosa.Classic.Model.Arrival.Basic.Job
import Prosa.Classic.Model.Schedule.Uni.Schedule

/-!
Definitions of the abstract response-time analysis framework (Rocq module `AbstractRTADefinitions`).

Representation notes:
* `\sum_(a <= t < b) F t` is `∑ t ∈ Finset.Ico a b, F t`; a Boolean `interference j t` summed as a number is
  `(interference j t).toNat`.
* Boolean tests in proposition position are `= true`; chains `a <= x < b` / `a < x < b` in proposition position
  are `(decide (a ≤ x) && decide (x < b)) = true` / `(decide (a < x) && decide (x < b)) = true`; `~~ b` is
  `(!b) = true`.
* The section-local `Let`s (`job_scheduled_at`, `job_completed_by`, `job_pending_earlier_and_at`) are unfolded;
  the `let offset := …` inside `job_interference_is_bounded_by` is kept.
* Binder lists follow the Rocq contract: each definition takes exactly the section variables it uses.
-/

namespace Prosa.Classic.Model.Schedule.Uni.Limited.AbstractRTA.Definitions.AbstractRTADefinitions

open Prosa.Classic.Model.Time.Time
open Prosa.Classic.Model.Arrival.Basic.ArrivalSequence.ArrivalSequence
open Prosa.Classic.Model.Schedule.Uni.Schedule.UniprocessorSchedule

universe u v

local macro "omega'" : tactic =>
  `(tactic| ((try dsimp only [Prosa.Classic.Model.Time.Time.time,
    Prosa.Classic.Model.Time.Time.instant, Prosa.Classic.Model.Time.Time.duration] at *) <;>
    omega))

def cumul_interference {Job : Type v} [DecidableEq Job] (interference : Job → time → Bool) (j : Job)
    (t1 t2 : Nat) : Nat :=
  ∑ t ∈ Finset.Ico t1 t2, (interference j t).toNat

def cumul_interfering_workload {Job : Type v} [DecidableEq Job] (interfering_workload : Job → time → time)
    (j : Job) (t1 t2 : Nat) : Nat :=
  ∑ t ∈ Finset.Ico t1 t2, interfering_workload j t

def quiet_time {Job : Type v} [DecidableEq Job] (job_arrival job_cost : Job → time) (sched : schedule Job)
    (interference : Job → time → Bool) (interfering_workload : Job → time → time) (j : Job) (t : time) : Prop :=
  cumul_interference interference j 0 t = cumul_interfering_workload interfering_workload j 0 t ∧
    (!pending_earlier_and_at job_arrival job_cost sched j t) = true

def busy_interval_prefix {Job : Type v} [DecidableEq Job] (job_arrival job_cost : Job → time)
    (sched : schedule Job) (interference : Job → time → Bool) (interfering_workload : Job → time → time) (j : Job)
    (t1 t2 : time) : Prop :=
  (decide (t1 ≤ job_arrival j) && decide (job_arrival j < t2)) = true ∧
    quiet_time job_arrival job_cost sched interference interfering_workload j t1 ∧
    ∀ t, (decide (t1 < t) && decide (t < t2)) = true →
      ¬ quiet_time job_arrival job_cost sched interference interfering_workload j t

def busy_interval {Job : Type v} [DecidableEq Job] (job_arrival job_cost : Job → time) (sched : schedule Job)
    (interference : Job → time → Bool) (interfering_workload : Job → time → time) (j : Job) (t1 t2 : time) : Prop :=
  busy_interval_prefix job_arrival job_cost sched interference interfering_workload j t1 t2 ∧
    quiet_time job_arrival job_cost sched interference interfering_workload j t2

theorem busy_interval_is_unique {Job : Type v} [DecidableEq Job] (job_arrival job_cost : Job → time)
    (sched : schedule Job) (interference : Job → time → Bool) (interfering_workload : Job → time → time) :
    ∀ (j : Job) (t1 t2 t1' t2' : time),
      busy_interval job_arrival job_cost sched interference interfering_workload j t1 t2 →
      busy_interval job_arrival job_cost sched interference interfering_workload j t1' t2' →
      t1 = t1' ∧ t2 = t2' := by
  intro j t1 t2 t1' t2' BUSY BUSY'
  obtain ⟨⟨IN, QT1, NQ⟩, QT2⟩ := BUSY
  obtain ⟨⟨IN', QT1', NQ'⟩, QT2'⟩ := BUSY'
  simp only [Bool.and_eq_true, decide_eq_true_eq] at IN IN'
  have E1 : t1 = t1' := by
    rcases Nat.lt_trichotomy t1 t1' with LT | EQ | GT
    · exact absurd QT1' (NQ t1' (by simp; omega'))
    · exact EQ
    · exact absurd QT1 (NQ' t1 (by simp; omega'))
  subst E1
  refine ⟨rfl, ?_⟩
  rcases Nat.lt_trichotomy t2 t2' with LT | EQ | GT
  · exact absurd QT2 (NQ' t2 (by simp; omega'))
  · exact EQ
  · exact absurd QT2' (NQ t2' (by simp; omega'))

def work_conserving {Task : Type u} [DecidableEq Task] {Job : Type v} [DecidableEq Job]
    (job_arrival job_cost : Job → time) (job_task : Job → Task) (arr_seq : arrival_sequence Job)
    (sched : schedule Job) (tsk : Task) (interference : Job → time → Bool)
    (interfering_workload : Job → time → time) : Prop :=
  ∀ j t1 t2 t,
    arrives_in arr_seq j →
    job_task j = tsk →
    0 < job_cost j →
    busy_interval job_arrival job_cost sched interference interfering_workload j t1 t2 →
    (decide (t1 ≤ t) && decide (t < t2)) = true →
    (¬ interference j t = true ↔ scheduled_at sched j t = true)

def busy_intervals_are_bounded_by {Task : Type u} [DecidableEq Task] {Job : Type v} [DecidableEq Job]
    (job_arrival job_cost : Job → time) (job_task : Job → Task) (arr_seq : arrival_sequence Job)
    (sched : schedule Job) (tsk : Task) (interference : Job → time → Bool)
    (interfering_workload : Job → time → time) (L : Nat) : Prop :=
  ∀ j,
    arrives_in arr_seq j →
    job_task j = tsk →
    0 < job_cost j →
    ∃ t1 t2,
      (decide (t1 ≤ job_arrival j) && decide (job_arrival j < t2)) = true ∧
      t2 ≤ t1 + L ∧
      busy_interval job_arrival job_cost sched interference interfering_workload j t1 t2

def job_interference_is_bounded_by {Task : Type u} [DecidableEq Task] {Job : Type v} [DecidableEq Job]
    (job_arrival job_cost : Job → time) (job_task : Job → Task) (arr_seq : arrival_sequence Job)
    (sched : schedule Job) (tsk : Task) (interference : Job → time → Bool)
    (interfering_workload : Job → time → time) (interference_bound_function : Task → time → time → time) : Prop :=
  ∀ t1 t2 delta j,
    busy_interval job_arrival job_cost sched interference interfering_workload j t1 t2 →
    t1 + delta < t2 →
    arrives_in arr_seq j →
    job_task j = tsk →
    (!completed_by job_cost sched j (t1 + delta)) = true →
    let offset := job_arrival j - t1
    cumul_interference interference j t1 (t1 + delta) ≤ interference_bound_function tsk offset delta

end Prosa.Classic.Model.Schedule.Uni.Limited.AbstractRTA.Definitions.AbstractRTADefinitions
