-- Authoritative source:
-- ProsaBuddy classic Prosa (prosabuddy commit f692cb7479780cf6009493f373a309e13165201c)
-- source: classic/model/schedule/apa/constrained_deadlines.v
-- sha256: see Prosa-Shunqi/classic-prosa/casestudy-translation/file_order.csv (rank 41)

import Prosa.Classic.Model.Arrival.Basic.Job
import Prosa.Classic.Model.Arrival.Basic.Task
import Prosa.Classic.Model.Priority
import Prosa.Classic.Model.Arrival.Basic.TaskArrival
import Prosa.Classic.Model.Schedule.Global.Basic.Schedule
import Prosa.Classic.Model.Schedule.Apa.Interference
import Prosa.Classic.Model.Schedule.Apa.Affinity
import Prosa.Classic.Model.Schedule.Apa.Platform

/-!
Absence of multiple pending jobs of the same task under constrained deadlines, in
APA schedules (Rocq module `ConstrainedDeadlines`, `classic/model/schedule/apa`).

Unlike its global counterpart, this source file has no counting lemmas: it only
proves the uniqueness lemmas.  The section-local `Let hp_task_in alpha'` is
unfolded to `higher_priority_task_in alpha higher_eq_priority tsk alpha'` (with the
section `tsk`).  Binder lists follow the Rocq contract: as in the global file,
`scheduled_task_with_higher_eq_priority` takes the section `tsk` and `t` followed by its
own parameter `tsk`, named `tsk'` here; unlike the global file, that parameter is used,
in `hp_task_in (alpha tsk') tsk_other` (checked with `Print` in the official build:
`hp_task_in (alpha tsk0) tsk_other`).
-/

set_option linter.dupNamespace false

namespace Prosa.Classic.Model.Schedule.Apa.ConstrainedDeadlines.ConstrainedDeadlines

open Prosa.Classic.Model.Time.Time
open Prosa.Classic.Model.Arrival.Basic.ArrivalSequence.ArrivalSequence
open Prosa.Classic.Model.Arrival.Basic.Task.SporadicTaskset
open Prosa.Classic.Model.Arrival.Basic.Job.Job
open Prosa.Classic.Model.Arrival.Basic.TaskArrival.TaskArrival
open Prosa.Classic.Model.Priority.Priority
open Prosa.Classic.Model.Schedule.Global.Basic.Schedule.Schedule
open Prosa.Classic.Model.Schedule.Global.Basic.Schedule.ScheduleOfSporadicTask
open Prosa.Classic.Model.Schedule.Apa.Affinity.Affinity
open Prosa.Classic.Model.Schedule.Apa.Interference.Interference

universe u v

local macro "omega'" : tactic =>
  `(tactic| ((try dsimp only [Prosa.Classic.Model.Time.Time.time,
    Prosa.Classic.Model.Time.Time.instant, Prosa.Classic.Model.Time.Time.duration] at *) <;>
    omega))

/-- LEAN_HELPER: a pending job has arrived and is not completed. -/
private theorem pending_iff {Job : Type v} [DecidableEq Job] (job_arrival job_cost : Job → time)
    {num_cpus : Nat} (sched : schedule Job num_cpus) (j : Job) (t : time) :
    pending job_arrival job_cost sched j t = true ↔
      job_arrival j ≤ t ∧ completed job_cost sched j t = false := by
  simp [pending, has_arrived]

-- The contract abstracts `H_valid_task` and `H_job_of_tsk`, which this proof does not use.
set_option linter.unusedVariables false in
theorem platform_at_most_one_pending_job_of_each_task {sporadic_task : Type u}
    [DecidableEq sporadic_task] (task_cost task_period task_deadline : sporadic_task → time)
    {Job : Type v} [DecidableEq Job] (job_arrival job_cost : Job → time)
    (job_task : Job → sporadic_task) (arr_seq : arrival_sequence Job) {num_cpus : Nat}
    (sched : schedule Job num_cpus)
    (H_sporadic_tasks : sporadic_task_model task_period job_arrival job_task arr_seq)
    (tsk : sporadic_task)
    (H_valid_task : is_valid_sporadic_task task_cost task_period task_deadline tsk)
    (j : Job) (H_job_of_tsk : job_task j = tsk) (t : time)
    (H_all_previous_jobs_completed :
      ∀ (j_other : Job) (tsk_other : sporadic_task),
        arrives_in arr_seq j_other →
        job_task j_other = tsk_other →
        job_arrival j_other + task_period tsk_other ≤ t →
        completed job_cost sched j_other
          (job_arrival j_other + task_period (job_task j_other)) = true) :
    ∀ j1 j2 : Job,
      arrives_in arr_seq j1 →
      arrives_in arr_seq j2 →
      pending job_arrival job_cost sched j1 t = true →
      pending job_arrival job_cost sched j2 t = true →
      job_task j1 = job_task j2 →
      j1 = j2 := by
  intro j1 j2 ARR1 ARR2 PENDING1 PENDING2 SAMEtsk
  by_contra DIFF
  rw [pending_iff] at PENDING1 PENDING2
  obtain ⟨ARRIVED1, NOTCOMP1⟩ := PENDING1
  obtain ⟨ARRIVED2, NOTCOMP2⟩ := PENDING2
  rcases Nat.le_total (job_arrival j1) (job_arrival j2) with BEFORE1 | BEFORE2
  · have SPO := H_sporadic_tasks j1 j2 DIFF ARR1 ARR2 SAMEtsk BEFORE1
    have COMP1 := H_all_previous_jobs_completed j1 (job_task j1) ARR1 rfl
      (Nat.le_trans SPO ARRIVED2)
    have := completion_monotonic job_cost sched j1 _ t (Nat.le_trans SPO ARRIVED2) COMP1
    rw [this] at NOTCOMP1
    exact Bool.noConfusion NOTCOMP1
  · have SPO := H_sporadic_tasks j2 j1 (Ne.symm DIFF) ARR2 ARR1 SAMEtsk.symm BEFORE2
    have COMP2 := H_all_previous_jobs_completed j2 (job_task j2) ARR2 rfl
      (Nat.le_trans SPO ARRIVED1)
    have := completion_monotonic job_cost sched j2 _ t (Nat.le_trans SPO ARRIVED1) COMP2
    rw [this] at NOTCOMP2
    exact Bool.noConfusion NOTCOMP2

/-! ### Constrained deadlines under fixed-priority scheduling -/

def scheduled_task_with_higher_eq_priority {sporadic_task : Type u} {Job : Type v}
    [DecidableEq sporadic_task] [DecidableEq Job] (job_task : Job → sporadic_task)
    {num_cpus : Nat} (sched : schedule Job num_cpus)
    (alpha : task_affinity sporadic_task num_cpus) (higher_eq_priority : FP_policy sporadic_task)
    (tsk : sporadic_task) (t : time)
    (tsk' tsk_other : sporadic_task) : Bool :=
  task_is_scheduled job_task sched tsk_other t &&
    higher_priority_task_in alpha higher_eq_priority tsk (alpha tsk') tsk_other

theorem platform_fp_no_multiple_jobs_of_interfering_tasks {sporadic_task : Type u}
    [DecidableEq sporadic_task] (task_period : sporadic_task → time) {Job : Type v}
    [DecidableEq Job] (job_arrival job_cost : Job → time) (job_task : Job → sporadic_task)
    (arr_seq : arrival_sequence Job) {num_cpus : Nat} (sched : schedule Job num_cpus)
    (alpha : task_affinity sporadic_task num_cpus) (higher_eq_priority : FP_policy sporadic_task)
    (H_sporadic_tasks : sporadic_task_model task_period job_arrival job_task arr_seq)
    (tsk : sporadic_task) (t : time)
    (H_all_previous_jobs_completed :
      ∀ (j_other : Job) (tsk_other : sporadic_task),
        arrives_in arr_seq j_other →
        job_task j_other = tsk_other →
        higher_priority_task_in alpha higher_eq_priority tsk (alpha tsk) tsk_other = true →
        completed job_cost sched j_other (job_arrival j_other + task_period tsk_other) = true) :
    ∀ j1 j2 : Job,
      arrives_in arr_seq j1 →
      arrives_in arr_seq j2 →
      pending job_arrival job_cost sched j1 t = true →
      pending job_arrival job_cost sched j2 t = true →
      job_task j1 = job_task j2 →
      higher_priority_task_in alpha higher_eq_priority tsk (alpha tsk) (job_task j1) = true →
      j1 = j2 := by
  intro j1 j2 ARR1 ARR2 PENDING1 PENDING2 SAMEtsk INTERF
  by_contra DIFF
  rw [pending_iff] at PENDING1 PENDING2
  obtain ⟨ARRIVED1, NOTCOMP1⟩ := PENDING1
  obtain ⟨ARRIVED2, NOTCOMP2⟩ := PENDING2
  rcases Nat.le_total (job_arrival j1) (job_arrival j2) with BEFORE1 | BEFORE2
  · have SPO := H_sporadic_tasks j1 j2 DIFF ARR1 ARR2 SAMEtsk BEFORE1
    have COMP1 := H_all_previous_jobs_completed j1 (job_task j1) ARR1 rfl INTERF
    have := completion_monotonic job_cost sched j1 _ t (Nat.le_trans SPO ARRIVED2) COMP1
    rw [this] at NOTCOMP1
    exact Bool.noConfusion NOTCOMP1
  · have SPO := H_sporadic_tasks j2 j1 (Ne.symm DIFF) ARR2 ARR1 SAMEtsk.symm BEFORE2
    have COMP2 := H_all_previous_jobs_completed j2 (job_task j2) ARR2 rfl (SAMEtsk ▸ INTERF)
    have := completion_monotonic job_cost sched j2 _ t (Nat.le_trans SPO ARRIVED1) COMP2
    rw [this] at NOTCOMP2
    exact Bool.noConfusion NOTCOMP2

theorem platform_fp_no_multiple_jobs_of_tsk {sporadic_task : Type u}
    [DecidableEq sporadic_task] (task_cost task_period task_deadline : sporadic_task → time)
    {Job : Type v} [DecidableEq Job] (job_arrival job_cost : Job → time)
    (job_task : Job → sporadic_task) (arr_seq : arrival_sequence Job) {num_cpus : Nat}
    (sched : schedule Job num_cpus)
    (H_sporadic_tasks : sporadic_task_model task_period job_arrival job_task arr_seq)
    (tsk : sporadic_task)
    (H_valid_task : is_valid_sporadic_task task_cost task_period task_deadline tsk)
    (j : Job) (H_j_arrives : arrives_in arr_seq j) (H_job_of_tsk : job_task j = tsk) (t : time)
    (H_j_backlogged : backlogged job_arrival job_cost sched j t = true)
    (H_t_before_period : t < job_arrival j + task_period tsk)
    (H_all_previous_jobs_of_tsk_completed :
      ∀ j0 : Job,
        arrives_in arr_seq j0 →
        job_task j0 = tsk →
        job_arrival j0 < job_arrival j →
        completed job_cost sched j0 (job_arrival j0 + task_period tsk) = true) :
    ∀ j' : Job,
      arrives_in arr_seq j' →
      pending job_arrival job_cost sched j' t = true →
      job_task j' = tsk →
      j' = j := by
  intro j' ARR' PENDING' SAMEtsk
  by_contra DIFF
  have BACK := H_j_backlogged
  simp only [backlogged, Bool.and_eq_true] at BACK
  obtain ⟨PENDj, _⟩ := BACK
  rw [pending_iff] at PENDj PENDING'
  obtain ⟨ARRIVED, _⟩ := PENDj
  obtain ⟨ARRIVED', NOTCOMP'⟩ := PENDING'
  have PERIOD : 0 < task_period tsk := by
    have := H_valid_task.2.1
    simpa [task_period_positive] using this
  rcases Nat.le_total (job_arrival j') (job_arrival j) with BEFORE | BEFORE'
  · have SPO := H_sporadic_tasks j' j DIFF ARR' H_j_arrives (by rw [SAMEtsk, H_job_of_tsk])
      BEFORE
    rw [SAMEtsk] at SPO
    have COMP := H_all_previous_jobs_of_tsk_completed j' ARR' SAMEtsk (by omega')
    have := completion_monotonic job_cost sched j' _ t (Nat.le_trans SPO ARRIVED) COMP
    rw [this] at NOTCOMP'
    exact Bool.noConfusion NOTCOMP'
  · have SPO := H_sporadic_tasks j j' (Ne.symm DIFF) H_j_arrives ARR'
      (by rw [SAMEtsk, H_job_of_tsk]) BEFORE'
    rw [H_job_of_tsk] at SPO
    omega'

end Prosa.Classic.Model.Schedule.Apa.ConstrainedDeadlines.ConstrainedDeadlines
