-- Authoritative source:
-- ProsaBuddy classic Prosa (prosabuddy commit f692cb7479780cf6009493f373a309e13165201c)
-- source: classic/model/schedule/global/jitter/schedule.v
-- sha256: see Prosa-Shunqi/classic-prosa/comprehensive-classic/file_order.csv (rank 47)

import Prosa.Classic.Util.All
import Prosa.Classic.Model.Arrival.Basic.Task
import Prosa.Classic.Model.Schedule.Global.Jitter.Job
import Prosa.Classic.Model.Arrival.Basic.ArrivalSequence
import Prosa.Classic.Model.Schedule.Global.Basic.Schedule

/-!
Global schedules with jitter (Rocq modules `ScheduleWithJitter`, which `Export`s the global basic schedule
module, and `ScheduleOfSporadicTaskWithJitter`).

Representation notes (as in the accepted global basic `classic/model/schedule/global/basic/schedule.v`):
* Boolean tests in proposition position are `= true`; `~~ b` in a Boolean expression is `!b`;
  `[exists cpu, P cpu]` is `(List.finRange num_cpus).any P`; `job_task j == tsk` is `decide (job_task j = tsk)`;
  `\sum_(a <= t < b) F t` is `∑ t ∈ Finset.Ico a b, F t`.
* `actual_arrival` returns `nat` in the source, hence `Nat` here.
* Binder lists follow the Rocq contract: each declaration takes exactly the section variables and hypotheses
  Rocq abstracts (e.g. `cumulative_service_le_task_cost` takes neither `arr_seq` nor `H_j_arrives`).
-/

set_option linter.dupNamespace false
set_option linter.unusedVariables false

namespace Prosa.Classic.Model.Schedule.Global.Jitter.Schedule

open Prosa.Classic.Model.Time.Time
open Prosa.Classic.Model.Arrival.Basic.ArrivalSequence.ArrivalSequence
open Prosa.Classic.Model.Schedule.Global.Basic.Schedule.Schedule

universe u v

local macro "omega'" : tactic =>
  `(tactic| ((try dsimp only [Prosa.Classic.Model.Time.Time.time,
    Prosa.Classic.Model.Time.Time.instant, Prosa.Classic.Model.Time.Time.duration] at *) <;>
    omega))

namespace ScheduleWithJitter

def actual_arrival {Job : Type u} [DecidableEq Job] (job_arrival job_jitter : Job → time) (j : Job) : Nat :=
  job_arrival j + job_jitter j

def jitter_has_passed {Job : Type u} [DecidableEq Job] (job_arrival job_jitter : Job → time) (j : Job)
    (t : time) : Bool :=
  decide (actual_arrival job_arrival job_jitter j ≤ t)

def actual_arrival_before {Job : Type u} [DecidableEq Job] (job_arrival job_jitter : Job → time) (j : Job)
    (t : time) : Bool :=
  decide (actual_arrival job_arrival job_jitter j < t)

def pending {Job : Type u} [DecidableEq Job] (job_arrival job_cost job_jitter : Job → time) {num_cpus : Nat}
    (sched : schedule Job num_cpus) (j : Job) (t : time) : Bool :=
  jitter_has_passed job_arrival job_jitter j t && !completed job_cost sched j t

def backlogged {Job : Type u} [DecidableEq Job] (job_arrival job_cost job_jitter : Job → time) {num_cpus : Nat}
    (sched : schedule Job num_cpus) (j : Job) (t : time) : Bool :=
  pending job_arrival job_cost job_jitter sched j t && !scheduled sched j t

def jobs_execute_after_jitter {Job : Type u} [DecidableEq Job] (job_arrival job_jitter : Job → time)
    {num_cpus : Nat} (sched : schedule Job num_cpus) : Prop :=
  ∀ j t, scheduled sched j t = true → jitter_has_passed job_arrival job_jitter j t = true

theorem scheduled_implies_pending {Job : Type u} [DecidableEq Job] (job_arrival job_cost job_jitter : Job → time)
    {num_cpus : Nat} (sched : schedule Job num_cpus)
    (H_jobs_execute_after_jitter : jobs_execute_after_jitter job_arrival job_jitter sched)
    (H_completed_jobs : completed_jobs_dont_execute job_cost sched) :
    ∀ j t, scheduled sched j t = true → pending job_arrival job_cost job_jitter sched j t = true := by
  intro j t SCHED
  have h1 := H_jobs_execute_after_jitter j t SCHED
  have h2 := completed_implies_not_scheduled job_cost sched j H_completed_jobs t
  cases hc : completed job_cost sched j t
  · simp [pending, h1, hc]
  · have := h2 hc; simp [SCHED] at this

theorem arrival_before_jitter {Job : Type u} [DecidableEq Job] (job_arrival job_jitter : Job → time)
    {num_cpus : Nat} (sched : schedule Job num_cpus)
    (H_jobs_execute_after_jitter : jobs_execute_after_jitter job_arrival job_jitter sched) :
    jobs_must_arrive_to_execute job_arrival sched := by
  intro j t SCHED
  have h := H_jobs_execute_after_jitter j t SCHED
  unfold jitter_has_passed actual_arrival at h
  simp only [has_arrived, decide_eq_true_eq] at h ⊢
  omega'

theorem service_before_jitter_zero {Job : Type u} [DecidableEq Job] (job_arrival job_jitter : Job → time)
    {num_cpus : Nat} (sched : schedule Job num_cpus)
    (H_jobs_execute_after_jitter : jobs_execute_after_jitter job_arrival job_jitter sched) :
    ∀ (j : Job) (t : Nat), t < job_arrival j + job_jitter j → service_at sched j t = 0 := by
  intro j t LT
  have h := not_scheduled_no_service sched j t
  cases hs : scheduled sched j t
  · rw [hs] at h; simpa using h.symm
  · have := H_jobs_execute_after_jitter j t hs
    unfold jitter_has_passed actual_arrival at this
    simp only [decide_eq_true_eq] at this
    omega'

theorem cumulative_service_before_jitter_zero {Job : Type u} [DecidableEq Job]
    (job_arrival job_jitter : Job → time) {num_cpus : Nat} (sched : schedule Job num_cpus)
    (H_jobs_execute_after_jitter : jobs_execute_after_jitter job_arrival job_jitter sched) :
    ∀ (j : Job) (t1 t2 : Nat), t2 ≤ job_arrival j + job_jitter j →
      ∑ t ∈ Finset.Ico t1 t2, service_at sched j t = 0 := by
  intro j t1 t2 LE
  apply Finset.sum_eq_zero
  intro t ht
  rw [Finset.mem_Ico] at ht
  exact service_before_jitter_zero job_arrival job_jitter sched H_jobs_execute_after_jitter j t (by omega')

end ScheduleWithJitter

namespace ScheduleOfSporadicTaskWithJitter

open Prosa.Classic.Model.Arrival.Basic.Job.Job

def task_scheduled_on {sporadic_task : Type u} {Job : Type v} [DecidableEq sporadic_task] [DecidableEq Job]
    (job_task : Job → sporadic_task) {num_cpus : Nat} (sched : schedule Job num_cpus) (tsk : sporadic_task)
    (cpu : processor num_cpus) (t : time) : Bool :=
  match sched cpu t with
  | some j => decide (job_task j = tsk)
  | none => false

def task_is_scheduled {sporadic_task : Type u} {Job : Type v} [DecidableEq sporadic_task] [DecidableEq Job]
    (job_task : Job → sporadic_task) {num_cpus : Nat} (sched : schedule Job num_cpus) (tsk : sporadic_task)
    (t : time) : Bool :=
  (List.finRange num_cpus).any (fun cpu => task_scheduled_on job_task sched tsk cpu t)

def jobs_of_task_scheduled_between {sporadic_task : Type u} {Job : Type v} [DecidableEq sporadic_task]
    [DecidableEq Job] (job_task : Job → sporadic_task) {num_cpus : Nat} (sched : schedule Job num_cpus)
    (tsk : sporadic_task) (t1 t2 : time) : List Job :=
  (jobs_scheduled_between sched t1 t2).filter (fun j => decide (job_task j = tsk))

def jobs_of_same_task_dont_execute_in_parallel {sporadic_task : Type u} {Job : Type v}
    [DecidableEq sporadic_task] [DecidableEq Job] (job_task : Job → sporadic_task) {num_cpus : Nat}
    (sched : schedule Job num_cpus) : Prop :=
  ∀ j j' t, job_task j = job_task j' → scheduled sched j t = true → scheduled sched j' t = true → j = j'

theorem cumulative_service_le_task_cost {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost task_deadline : sporadic_task → time) {Job : Type v} [DecidableEq Job]
    (job_cost job_deadline : Job → time) (job_task : Job → sporadic_task) {num_cpus : Nat}
    (sched : schedule Job num_cpus)
    (jobs_dont_execute_after_completion : completed_jobs_dont_execute job_cost sched)
    (tsk : sporadic_task) (j : Job) (H_job_of_task : job_task j = tsk)
    (valid_job : valid_sporadic_job task_cost task_deadline job_cost job_deadline job_task j) :
    ∀ t t' : time, service_during sched j t t' ≤ task_cost tsk := by
  intro t t'
  have h1 := cumulative_service_le_job_cost job_cost sched j jobs_dont_execute_after_completion t t'
  have h2 := valid_job.2.1
  simp only [job_cost_le_task_cost, decide_eq_true_eq] at h2
  rw [H_job_of_task] at h2
  exact Nat.le_trans h1 h2

end ScheduleOfSporadicTaskWithJitter

end Prosa.Classic.Model.Schedule.Global.Jitter.Schedule
