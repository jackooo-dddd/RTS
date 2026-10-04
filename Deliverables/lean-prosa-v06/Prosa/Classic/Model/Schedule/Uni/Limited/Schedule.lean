-- Authoritative source:
-- ProsaBuddy classic Prosa (prosabuddy commit f692cb7479780cf6009493f373a309e13165201c)
-- source: classic/model/schedule/uni/limited/schedule.v
-- sha256: see Prosa-Shunqi/classic-prosa/comprehensive-classic/file_order.csv (rank 84)

import Prosa.Classic.Util.All
import Prosa.Classic.Model.Arrival.Basic.Job
import Prosa.Classic.Model.Schedule.Uni.Service
import Prosa.Classic.Model.Schedule.Uni.Schedule
import Prosa.Classic.Model.Schedule.Uni.Nonpreemptive.Schedule
import Prosa.Util.Epsilon

/-!
Lock-in service of jobs and tasks in limited-preemptive schedules. The source file declares no `Module`, so its
declarations live directly in the file namespace.

Representation notes:
* Boolean tests in proposition position are `= true`; `~~ b` is `(!b) = true`; `ε` is the v0.6 util notation
  for `1`.
* The section-local `Let job_lock_in_service` of the `FullyPreemptiveModel` / `FullyNonPreemptiveModel` sections
  is unfolded to `fun j => job_cost j` / `fun _ => ε`.
* The mid-section `Require Import …nonpreemptive.schedule` is a top-level `import` here.
* Binder lists follow the Rocq contract.
-/

set_option linter.dupNamespace false
set_option linter.unusedVariables false

namespace Prosa.Classic.Model.Schedule.Uni.Limited.Schedule

open Prosa.Classic.Model.Time.Time
open Prosa.Classic.Model.Arrival.Basic.ArrivalSequence.ArrivalSequence
open Prosa.Classic.Model.Arrival.Basic.Job.Job
open Prosa.Classic.Model.Schedule.Uni.Schedule.UniprocessorSchedule
open Prosa.Util.Epsilon

universe u v

local macro "omega'" : tactic =>
  `(tactic| ((try dsimp only [Prosa.Classic.Model.Time.Time.time,
    Prosa.Classic.Model.Time.Time.instant, Prosa.Classic.Model.Time.Time.duration] at *) <;>
    omega))

def job_lock_in_service_positive {Job : Type v} [DecidableEq Job] (job_cost : Job → time)
    (arr_seq : arrival_sequence Job) (job_lock_in_service : Job → time) : Prop :=
  ∀ j, arrives_in arr_seq j → job_cost_positive job_cost j = true → 0 < job_lock_in_service j

def job_lock_in_service_le_job_cost {Job : Type v} [DecidableEq Job] (job_cost : Job → time)
    (arr_seq : arrival_sequence Job) (job_lock_in_service : Job → time) : Prop :=
  ∀ j, arrives_in arr_seq j → job_cost_positive job_cost j = true → job_lock_in_service j ≤ job_cost j

def job_nonpreemptive_after_lock_in_service {Job : Type v} [DecidableEq Job] (job_cost : Job → time)
    (arr_seq : arrival_sequence Job) (sched : schedule Job) (job_lock_in_service : Job → time) : Prop :=
  ∀ j t t', arrives_in arr_seq j → t ≤ t' → job_lock_in_service j ≤ service sched j t →
    (!completed_by job_cost sched j t') = true → scheduled_at sched j t' = true

def proper_job_lock_in_service {Job : Type v} [DecidableEq Job] (job_cost : Job → time)
    (arr_seq : arrival_sequence Job) (sched : schedule Job) (job_lock_in_service : Job → time) : Prop :=
  job_lock_in_service_positive job_cost arr_seq job_lock_in_service ∧
  job_lock_in_service_le_job_cost job_cost arr_seq job_lock_in_service ∧
  job_nonpreemptive_after_lock_in_service job_cost arr_seq sched job_lock_in_service

def task_lock_in_service_le_task_cost {Task : Type u} [DecidableEq Task] (task_cost task_lock_in_service : Task → time)
    (tsk : Task) : Prop :=
  task_lock_in_service tsk ≤ task_cost tsk

def task_lock_in_service_bounds_job_lock_in_service {Task : Type u} [DecidableEq Task] {Job : Type v}
    [DecidableEq Job] (job_task : Job → Task) (arr_seq : arrival_sequence Job) (job_lock_in_service : Job → time)
    (task_lock_in_service : Task → time) (tsk : Task) : Prop :=
  ∀ j, arrives_in arr_seq j → job_task j = tsk → job_lock_in_service j ≤ task_lock_in_service tsk

def proper_task_lock_in_service {Task : Type u} [DecidableEq Task] (task_cost : Task → time) {Job : Type v}
    [DecidableEq Job] (job_task : Job → Task) (arr_seq : arrival_sequence Job) (job_lock_in_service : Job → time)
    (task_lock_in_service : Task → time) (tsk : Task) : Prop :=
  task_lock_in_service_le_task_cost task_cost task_lock_in_service tsk ∧
  task_lock_in_service_bounds_job_lock_in_service job_task arr_seq job_lock_in_service task_lock_in_service tsk

theorem job_nonpreemptive_after_lock_in_service_trivial {Job : Type v} [DecidableEq Job] (job_cost : Job → time)
    (arr_seq : arrival_sequence Job) (sched : schedule Job)
    (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched) :
    job_nonpreemptive_after_lock_in_service job_cost arr_seq sched (fun j => job_cost j) := by
  intro j t t' ARR LE SERV NCOMP
  exfalso
  have C := completion_monotonic job_cost sched j t t' LE (by simp only [completed_by, decide_eq_true_eq]; exact SERV)
  rw [C] at NCOMP
  exact Bool.noConfusion NCOMP

theorem property_last_segment_is_nonpreemptive_holds {Job : Type v} [DecidableEq Job] (job_cost : Job → time)
    (arr_seq : arrival_sequence Job) (sched : schedule Job)
    (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched)
    (H_is_nonpreemptive_schedule :
      Prosa.Classic.Model.Schedule.Uni.Nonpreemptive.Schedule.NonpreemptiveSchedule.is_nonpreemptive_schedule
        job_cost sched) :
    job_nonpreemptive_after_lock_in_service job_cost arr_seq sched (fun _ => ε) := by
  intro j t t' ARR LE NEQ NCOMPL
  have NEQ' : 1 ≤ service sched j t := NEQ
  have POS : service sched j t ≠ 0 := by omega'
  unfold service service_during at POS
  obtain ⟨ts, IN, SCHED⟩ := Finset.exists_ne_zero_of_sum_ne_zero POS
  rw [Finset.mem_Ico] at IN
  have SCHEDts : scheduled_at sched j ts = true := by
    unfold service_at at SCHED
    cases h : scheduled_at sched j ts
    · rw [h] at SCHED; simp at SCHED
    · rfl
  exact H_is_nonpreemptive_schedule j ts t' (by omega') SCHEDts NCOMPL

end Prosa.Classic.Model.Schedule.Uni.Limited.Schedule
