-- Authoritative source:
-- ProsaBuddy classic Prosa (prosabuddy commit f692cb7479780cf6009493f373a309e13165201c)
-- source: classic/model/schedule/uni/jitter/schedule.v
-- sha256: see Prosa-Shunqi/classic-prosa/comprehensive-classic/file_order.csv (rank 53)

import Prosa.Classic.Util.All
import Prosa.Classic.Model.Time
import Prosa.Classic.Model.Arrival.Basic.Task
import Prosa.Classic.Model.Arrival.Basic.Job
import Prosa.Classic.Model.Schedule.Uni.Schedule
import Prosa.Classic.Model.Arrival.Jitter.ArrivalSequence

/-!
Uniprocessor schedules with jitter (Rocq module `UniprocessorScheduleWithJitter`, which `Export`s
`ArrivalSequenceWithJitter` and `UniprocessorSchedule` and redefines `pending` and `backlogged`).

Representation notes: Boolean tests in proposition position are `= true`; `~~ b` in a Boolean expression is
`!b`; `\sum_(a <= t < b) F t` is `∑ t ∈ Finset.Ico a b, F t`; a Boolean chain `a <= x <= b` in proposition
position is `(decide (a ≤ x) && decide (x ≤ b)) = true`; the section-local `Let`s (`has_actually_arrived`,
`actual_job_arrival`) are unfolded. Binder lists follow the Rocq contract (e.g. `jitter_has_passed_implies_arrived`
takes neither `sched` nor the hypothesis).
-/

set_option linter.dupNamespace false
set_option linter.unusedVariables false

namespace Prosa.Classic.Model.Schedule.Uni.Jitter.Schedule.UniprocessorScheduleWithJitter

open Prosa.Classic.Model.Time.Time
open Prosa.Classic.Model.Arrival.Basic.ArrivalSequence.ArrivalSequence
open Prosa.Classic.Model.Arrival.Jitter.ArrivalSequence.ArrivalSequenceWithJitter
open Prosa.Classic.Model.Schedule.Uni.Schedule.UniprocessorSchedule hiding pending backlogged scheduled_implies_pending

universe u

local macro "omega'" : tactic =>
  `(tactic| ((try dsimp only [Prosa.Classic.Model.Time.Time.time,
    Prosa.Classic.Model.Time.Time.instant, Prosa.Classic.Model.Time.Time.duration] at *) <;>
    omega))

def pending {Job : Type u} [DecidableEq Job] (job_arrival job_cost job_jitter : Job → time) (sched : schedule Job)
    (j : Job) (t : time) : Bool :=
  jitter_has_passed job_arrival job_jitter j t && !completed_by job_cost sched j t

def backlogged {Job : Type u} [DecidableEq Job] (job_arrival job_cost job_jitter : Job → time)
    (sched : schedule Job) (j : Job) (t : time) : Bool :=
  pending job_arrival job_cost job_jitter sched j t && !scheduled_at sched j t

def jobs_execute_after_jitter {Job : Type u} [DecidableEq Job] (job_arrival job_jitter : Job → time)
    (sched : schedule Job) : Prop :=
  ∀ j t, scheduled_at sched j t = true → jitter_has_passed job_arrival job_jitter j t = true

theorem jobs_with_jitter_must_arrive_to_execute {Job : Type u} [DecidableEq Job]
    (job_arrival job_jitter : Job → time) (sched : schedule Job)
    (H_jobs_execute_after_jitter : jobs_execute_after_jitter job_arrival job_jitter sched) :
    jobs_must_arrive_to_execute job_arrival sched := by
  intro j t SCHED
  have h := H_jobs_execute_after_jitter j t SCHED
  unfold jitter_has_passed actual_arrival at h
  simp only [has_arrived, decide_eq_true_eq] at h ⊢
  omega'

theorem jitter_has_passed_implies_arrived {Job : Type u} [DecidableEq Job] (job_arrival job_jitter : Job → time)
    (j : Job) :
    ∀ t, jitter_has_passed job_arrival job_jitter j t = true → has_arrived job_arrival j t = true := by
  intro t PASS
  unfold jitter_has_passed actual_arrival at PASS
  simp only [has_arrived, decide_eq_true_eq] at PASS ⊢
  omega'

theorem service_before_jitter_is_zero {Job : Type u} [DecidableEq Job] (job_arrival job_jitter : Job → time)
    (sched : schedule Job) (H_jobs_execute_after_jitter : jobs_execute_after_jitter job_arrival job_jitter sched)
    (j : Job) :
    ∀ t : Nat, t < actual_arrival job_arrival job_jitter j → service_at sched j t = 0 := by
  intro t LT
  cases hs : scheduled_at sched j t
  · simp [service_at, hs]
  · have h := H_jobs_execute_after_jitter j t hs
    simp only [jitter_has_passed, decide_eq_true_eq] at h
    omega'

theorem cumulative_service_before_jitter_is_zero {Job : Type u} [DecidableEq Job]
    (job_arrival job_jitter : Job → time) (sched : schedule Job)
    (H_jobs_execute_after_jitter : jobs_execute_after_jitter job_arrival job_jitter sched) (j : Job) :
    ∀ t1 t2 : Nat, t2 ≤ actual_arrival job_arrival job_jitter j →
      ∑ i ∈ Finset.Ico t1 t2, service_at sched j i = 0 := by
  intro t1 t2 LE
  apply Finset.sum_eq_zero
  intro i hi
  rw [Finset.mem_Ico] at hi
  exact service_before_jitter_is_zero job_arrival job_jitter sched H_jobs_execute_after_jitter j i (by omega')

theorem ignore_service_before_jitter {Job : Type u} [DecidableEq Job] (job_arrival job_jitter : Job → time)
    (sched : schedule Job) (H_jobs_execute_after_jitter : jobs_execute_after_jitter job_arrival job_jitter sched)
    (j : Job) :
    ∀ t1 t2 : Nat,
      (decide (t1 ≤ actual_arrival job_arrival job_jitter j) &&
        decide (actual_arrival job_arrival job_jitter j ≤ t2)) = true →
      ∑ t ∈ Finset.Ico t1 t2, service_at sched j t =
        ∑ t ∈ Finset.Ico (actual_arrival job_arrival job_jitter j) t2, service_at sched j t := by
  intro t1 t2 H
  simp only [Bool.and_eq_true, decide_eq_true_eq] at H
  rw [← Finset.sum_Ico_consecutive _ H.1 H.2,
    cumulative_service_before_jitter_is_zero job_arrival job_jitter sched H_jobs_execute_after_jitter j t1
      (actual_arrival job_arrival job_jitter j) (Nat.le_refl _), Nat.zero_add]

theorem scheduled_implies_pending {Job : Type u} [DecidableEq Job] (job_arrival job_cost job_jitter : Job → time)
    (sched : schedule Job) (H_jobs_execute_after_jitter : jobs_execute_after_jitter job_arrival job_jitter sched)
    (H_completed_jobs : completed_jobs_dont_execute job_cost sched) (j : Job) :
    ∀ t, scheduled_at sched j t = true → pending job_arrival job_cost job_jitter sched j t = true := by
  intro t SCHED
  have h1 := H_jobs_execute_after_jitter j t SCHED
  have h2 := scheduled_implies_not_completed job_cost sched j H_completed_jobs t SCHED
  simp only [pending, h1, h2, Bool.true_and]

end Prosa.Classic.Model.Schedule.Uni.Jitter.Schedule.UniprocessorScheduleWithJitter
