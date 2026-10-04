-- Authoritative source:
-- ProsaBuddy classic Prosa (prosabuddy commit f692cb7479780cf6009493f373a309e13165201c)
-- source: classic/model/schedule/uni/nonpreemptive/platform.v
-- sha256: see Prosa-Shunqi/classic-prosa/comprehensive-classic/file_order.csv (rank 70)

import Prosa.Classic.Util.All
import Prosa.Classic.Model.Arrival.Basic.Task
import Prosa.Classic.Model.Arrival.Basic.Job
import Prosa.Classic.Model.Priority
import Prosa.Classic.Model.Arrival.Basic.TaskArrival
import Prosa.Classic.Model.Schedule.Uni.Schedule
import Prosa.Classic.Model.Schedule.Uni.Basic.Platform
import Prosa.Classic.Model.Schedule.Uni.Nonpreemptive.Schedule

/-!
Properties of the nonpreemptive uniprocessor platform (Rocq module `NonpreemptivePlatform`).

Representation notes:
* Boolean tests in proposition position are `= true`; the section-local `Let`s (`job_completed_by`,
  `job_scheduled_at`) are unfolded.
* `work_conserving` is, as in the source, `Platform.work_conserving job_cost` (partially applied): the source passes
  `job_cost` as the `job_arrival` argument of `Platform.work_conserving`, so the definition takes two cost
  functions (Rocq: `Arguments work_conserving {Job} (job_cost job_cost)`). This source oddity is kept; the second
  parameter is named `job_cost0` here because Lean binders need distinct names to be usable.
* Binder lists follow the Rocq contract.
-/

set_option linter.dupNamespace false
set_option linter.unusedVariables false

namespace Prosa.Classic.Model.Schedule.Uni.Nonpreemptive.Platform.NonpreemptivePlatform

open Prosa.Classic.Model.Time.Time
open Prosa.Classic.Model.Arrival.Basic.ArrivalSequence.ArrivalSequence
open Prosa.Classic.Model.Priority.Priority
open Prosa.Classic.Model.Schedule.Uni.Schedule.UniprocessorSchedule

universe u v

def is_preemption_point' {Job : Type v} [DecidableEq Job] (job_cost : Job → time) (sched : schedule Job)
    (t : time) : Prop :=
  t = 0 ∨ sched (t - 1) = none ∨
    ∃ j, scheduled_at sched j (t - 1) = true ∧ completed_by job_cost sched j t = true

def is_preemption_point {Job : Type v} [DecidableEq Job] (job_cost : Job → time) (sched : schedule Job)
    (t : time) : Prop :=
  t = 0 ∨ ∀ j, scheduled_at sched j (t - 1) = true → completed_by job_cost sched j t = true

theorem defitions_of_preemption_point_are_equal {Job : Type v} [DecidableEq Job] (job_cost : Job → time)
    (sched : schedule Job) :
    ∀ t, is_preemption_point job_cost sched t ↔ is_preemption_point' job_cost sched t := by
  intro t
  unfold is_preemption_point is_preemption_point'
  constructor
  · rintro (H | H)
    · exact Or.inl H
    · right
      cases hs : sched (t - 1) with
      | none => exact Or.inl rfl
      | some s =>
        right
        have SCHED : scheduled_at sched s (t - 1) = true := by simp [scheduled_at, hs]
        exact ⟨s, SCHED, H s SCHED⟩
  · rintro (H | H | ⟨j', H1, H2⟩)
    · exact Or.inl H
    · right; intro j H0
      simp [scheduled_at, H] at H0
    · right; intro j H0
      have EQ : j = j' := only_one_job_scheduled sched j j' (t - 1) H0 H1
      subst EQ; exact H2

def work_conserving {Job : Type v} [DecidableEq Job] (job_cost job_cost0 : Job → time)
    (arr_seq : arrival_sequence Job) (sched : schedule Job) : Prop :=
  Prosa.Classic.Model.Schedule.Uni.Basic.Platform.Platform.work_conserving job_cost job_cost0 arr_seq sched

def respects_FP_policy_at_preemption_point {sporadic_task : Type u} [DecidableEq sporadic_task]
    {Job : Type v} [DecidableEq Job] (job_arrival job_cost : Job → time) (job_task : Job → sporadic_task)
    (arr_seq : arrival_sequence Job) (sched : schedule Job) (higher_eq_priority : FP_policy sporadic_task) : Prop :=
  ∀ j j_hp t, arrives_in arr_seq j → backlogged job_arrival job_cost sched j t = true →
    scheduled_at sched j_hp t = true → is_preemption_point job_cost sched t →
    higher_eq_priority (job_task j_hp) (job_task j) = true

def respects_JLFP_policy_at_preemption_point {Job : Type v} [DecidableEq Job] (job_arrival job_cost : Job → time)
    (arr_seq : arrival_sequence Job) (sched : schedule Job) (higher_eq_priority : JLFP_policy Job) : Prop :=
  ∀ j j_hp t, arrives_in arr_seq j → backlogged job_arrival job_cost sched j t = true →
    scheduled_at sched j_hp t = true → is_preemption_point job_cost sched t →
    higher_eq_priority j_hp j = true

end Prosa.Classic.Model.Schedule.Uni.Nonpreemptive.Platform.NonpreemptivePlatform
