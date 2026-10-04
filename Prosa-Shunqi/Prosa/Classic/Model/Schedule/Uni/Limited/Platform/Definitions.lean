-- Authoritative source:
-- ProsaBuddy classic Prosa (prosabuddy commit f692cb7479780cf6009493f373a309e13165201c)
-- source: classic/model/schedule/uni/limited/platform/definitions.v
-- sha256: see Prosa-Shunqi/classic-prosa/comprehensive-classic/file_order.csv (rank 83)

import Prosa.Classic.Util.All
import Prosa.Classic.Model.Arrival.Basic.Job
import Prosa.Classic.Model.Arrival.Basic.Task
import Prosa.Classic.Model.Priority
import Prosa.Classic.Model.Arrival.Basic.TaskArrival
import Prosa.Classic.Model.Schedule.Uni.Schedule
import Prosa.Classic.Model.Schedule.Uni.Service
import Prosa.Classic.Model.Schedule.Uni.Basic.Platform
import Prosa.Classic.Model.Schedule.Uni.Nonpreemptive.Schedule
import Prosa.Util.Epsilon

/-!
Platform with limited preemptions (Rocq module `LimitedPreemptionPlatform`).

Representation notes:
* `preemption_time` is a Boolean (`if sched t is Some j then … else true` is a `match`).
* Boolean tests in proposition position are `= true`; `~~ b` is `(!b) = true`; Boolean chains `a <= x <= b` are
  `(decide (a ≤ x) && decide (x ≤ b)) = true`; `ε` is the v0.6 util notation for `1`; `t.+1` is `t + 1`.
* `work_conserving` is, as in the source, `Platform.work_conserving job_cost` (partially applied): the source passes
  `job_cost` as the `job_arrival` argument of `Platform.work_conserving`, so the definition takes two cost
  functions (Rocq: `Arguments work_conserving {Job} (job_cost job_cost)`). This source oddity is kept; the second
  parameter is named `job_cost0` because Lean binders need distinct names to be usable.
* The section-local `Let`s (`job_pending`, `job_completed_by`, `job_scheduled_at`) are unfolded.
* Binder lists follow the Rocq contract (e.g. `zero_is_pt` takes `H_model_with_bounded_np_segments` and
  `H_jobs_come_from_arrival_sequence` but not `H_correct_preemption_model`).
-/

set_option linter.unusedVariables false

namespace Prosa.Classic.Model.Schedule.Uni.Limited.Platform.Definitions.LimitedPreemptionPlatform

open Prosa.Classic.Model.Time.Time
open Prosa.Classic.Model.Arrival.Basic.ArrivalSequence.ArrivalSequence
open Prosa.Classic.Model.Priority.Priority
open Prosa.Classic.Model.Schedule.Uni.Schedule.UniprocessorSchedule
open Prosa.Util.Epsilon

universe u v

def preemption_time {Job : Type v} [DecidableEq Job] (sched : schedule Job) (can_be_preempted : Job → time → Bool)
    (t : time) : Bool :=
  match sched t with
  | some j => can_be_preempted j (service sched j t)
  | none => true

def not_preemptive_implies_scheduled {Job : Type v} [DecidableEq Job] (sched : schedule Job)
    (can_be_preempted : Job → time → Bool) (j : Job) : Prop :=
  ∀ t, (!can_be_preempted j (service sched j t)) = true → scheduled_at sched j t = true

def execution_starts_with_preemption_point {Job : Type v} [DecidableEq Job] (sched : schedule Job)
    (can_be_preempted : Job → time → Bool) (j : Job) : Prop :=
  ∀ prt, (!scheduled_at sched j prt) = true → scheduled_at sched j (prt + 1) = true →
    can_be_preempted j (service sched j (prt + 1)) = true

def correct_preemption_model {Job : Type v} [DecidableEq Job] (arr_seq : arrival_sequence Job)
    (sched : schedule Job) (can_be_preempted : Job → time → Bool) : Prop :=
  ∀ j, arrives_in arr_seq j →
    not_preemptive_implies_scheduled sched can_be_preempted j ∧
    execution_starts_with_preemption_point sched can_be_preempted j

def job_cannot_become_nonpreemptive_before_execution {Job : Type v} [DecidableEq Job]
    (can_be_preempted : Job → time → Bool) (j : Job) : Prop :=
  can_be_preempted j 0 = true

def job_cannot_be_nonpreemptive_after_completion {Job : Type v} [DecidableEq Job] (job_cost : Job → time)
    (can_be_preempted : Job → time → Bool) (j : Job) : Prop :=
  can_be_preempted j (job_cost j) = true

def job_max_nonpreemptive_segment_le_task_max_nonpreemptive_segment {Task : Type u} [DecidableEq Task]
    {Job : Type v} [DecidableEq Job] (job_task : Job → Task) (arr_seq : arrival_sequence Job)
    (job_max_nps : Job → time) (task_max_nps : Task → time) (j : Job) : Prop :=
  arrives_in arr_seq j → job_max_nps j ≤ task_max_nps (job_task j)

def nonpreemptive_regions_have_bounded_length {Job : Type v} [DecidableEq Job] (job_cost : Job → time)
    (can_be_preempted : Job → time → Bool) (job_max_nps : Job → time) (j : Job) : Prop :=
  ∀ progr, (decide (0 ≤ progr) && decide (progr ≤ job_cost j)) = true →
    ∃ preemption_point,
      (decide (progr ≤ preemption_point) && decide (preemption_point ≤ progr + (job_max_nps j - ε))) = true ∧
      can_be_preempted j preemption_point = true

def model_with_bounded_nonpreemptive_segments {Task : Type u} [DecidableEq Task] {Job : Type v} [DecidableEq Job]
    (job_cost : Job → time) (job_task : Job → Task) (arr_seq : arrival_sequence Job)
    (can_be_preempted : Job → time → Bool) (job_max_nps : Job → time) (task_max_nps : Task → time) : Prop :=
  ∀ j, arrives_in arr_seq j →
    job_cannot_become_nonpreemptive_before_execution can_be_preempted j ∧
    job_cannot_be_nonpreemptive_after_completion job_cost can_be_preempted j ∧
    job_max_nonpreemptive_segment_le_task_max_nonpreemptive_segment job_task arr_seq job_max_nps task_max_nps j ∧
    nonpreemptive_regions_have_bounded_length job_cost can_be_preempted job_max_nps j

theorem zero_is_pt {Task : Type u} [DecidableEq Task] {Job : Type v} [DecidableEq Job]
    (job_cost : Job → time) (job_task : Job → Task) (arr_seq : arrival_sequence Job) (sched : schedule Job)
    (can_be_preempted : Job → time → Bool) (job_max_nps : Job → time) (task_max_nps : Task → time)
    (H_model_with_bounded_np_segments :
      model_with_bounded_nonpreemptive_segments job_cost job_task arr_seq can_be_preempted job_max_nps task_max_nps)
    (H_jobs_come_from_arrival_sequence : jobs_come_from_arrival_sequence sched arr_seq) :
    preemption_time sched can_be_preempted 0 = true := by
  unfold preemption_time
  cases SCHED : sched 0 with
  | none => rfl
  | some j =>
    have ARR := H_jobs_come_from_arrival_sequence j 0 (by simp [scheduled_at, SCHED])
    have PP := (H_model_with_bounded_np_segments j ARR).1
    have Z : service sched j 0 = 0 := by simp [service, service_during]
    simp only [Z]
    exact PP

theorem first_moment_is_pt {Job : Type v} [DecidableEq Job] (arr_seq : arrival_sequence Job) (sched : schedule Job)
    (can_be_preempted : Job → time → Bool)
    (H_correct_preemption_model : correct_preemption_model arr_seq sched can_be_preempted) :
    ∀ (j : Job) (prt : time), arrives_in arr_seq j → (!scheduled_at sched j prt) = true →
      scheduled_at sched j (prt + 1) = true → preemption_time sched can_be_preempted (prt + 1) = true := by
  intro s pt ARR NSCHED SCHED
  unfold preemption_time
  have SCHED2 : sched (pt + 1) = some s := by simpa [scheduled_at] using SCHED
  rw [SCHED2]
  exact (H_correct_preemption_model s ARR).2 pt NSCHED SCHED

def work_conserving {Job : Type v} [DecidableEq Job] (job_cost job_cost0 : Job → time)
    (arr_seq : arrival_sequence Job) (sched : schedule Job) : Prop :=
  Prosa.Classic.Model.Schedule.Uni.Basic.Platform.Platform.work_conserving job_cost job_cost0 arr_seq sched

def respects_FP_policy_at_preemption_point {Task : Type u} [DecidableEq Task] {Job : Type v} [DecidableEq Job]
    (job_arrival job_cost : Job → time) (job_task : Job → Task) (arr_seq : arrival_sequence Job)
    (sched : schedule Job) (preemption_model : Job → time → Bool) (higher_eq_priority : FP_policy Task) : Prop :=
  ∀ j j_hp t, preemption_time sched preemption_model t = true → arrives_in arr_seq j →
    backlogged job_arrival job_cost sched j t = true → scheduled_at sched j_hp t = true →
    higher_eq_priority (job_task j_hp) (job_task j) = true

def respects_JLFP_policy_at_preemption_point {Job : Type v} [DecidableEq Job] (job_arrival job_cost : Job → time)
    (arr_seq : arrival_sequence Job) (sched : schedule Job) (preemption_model : Job → time → Bool)
    (higher_eq_priority : JLFP_policy Job) : Prop :=
  ∀ j j_hp t, preemption_time sched preemption_model t = true → arrives_in arr_seq j →
    backlogged job_arrival job_cost sched j t = true → scheduled_at sched j_hp t = true →
    higher_eq_priority j_hp j = true

end Prosa.Classic.Model.Schedule.Uni.Limited.Platform.Definitions.LimitedPreemptionPlatform
