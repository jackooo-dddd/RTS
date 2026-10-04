-- Authoritative source:
-- ProsaBuddy classic Prosa (prosabuddy commit f692cb7479780cf6009493f373a309e13165201c)
-- source: classic/model/schedule/global/jitter/platform.v
-- sha256: see Prosa-Shunqi/classic-prosa/comprehensive-classic/file_order.csv (rank 121)

import Prosa.Classic.Model.Arrival.Basic.Task
import Prosa.Classic.Model.Priority
import Prosa.Classic.Model.Arrival.Basic.TaskArrival
import Prosa.Classic.Model.Schedule.Global.Jitter.Job
import Prosa.Classic.Model.Schedule.Global.Jitter.Schedule
import Prosa.Classic.Model.Schedule.Global.Jitter.Interference

/-!
Platform properties of jitter-aware global schedules (Rocq module `Platform` of
`classic/model/schedule/global/jitter/platform.v`).

Representation notes (as in the accepted `classic/model/schedule/global/basic/platform.v`): Boolean predicates in
proposition position are `… = true`; `backlogged` is the jitter-aware `ScheduleWithJitter.backlogged` (the section-local
`Let job_is_backlogged` is unfolded). Binder lists follow the Rocq contract (`job_task` precedes `job_jitter` in
`respects_FP_policy`). Proofs are those of the basic module with the jitter-aware `backlogged`.
-/

set_option linter.dupNamespace false

namespace Prosa.Classic.Model.Schedule.Global.Jitter.Platform.Platform

open Prosa.Classic.Model.Time.Time
open Prosa.Classic.Model.Arrival.Basic.ArrivalSequence.ArrivalSequence
open Prosa.Classic.Model.Schedule.Global.Basic.Schedule.Schedule hiding backlogged
open Prosa.Classic.Model.Schedule.Global.Jitter.Schedule.ScheduleWithJitter (backlogged)
open Prosa.Classic.Model.Priority.Priority (FP_policy JLFP_policy JLDP_policy)
open Prosa.Classic.Util.Notation (make_sequence)
open BigOperators

universe u v

def work_conserving {Job : Type v} [DecidableEq Job] (job_arrival job_cost job_jitter : Job → time)
    (arr_seq : arrival_sequence Job) {num_cpus : Nat} (sched : schedule Job num_cpus) : Prop :=
  ∀ j t,
    arrives_in arr_seq j →
    backlogged job_arrival job_cost job_jitter sched j t = true →
    ∀ cpu, ∃ j_other, scheduled_on sched j_other cpu t = true

def work_conserving_count {Job : Type v} [DecidableEq Job] (job_arrival job_cost job_jitter : Job → time)
    (arr_seq : arrival_sequence Job) {num_cpus : Nat} (sched : schedule Job num_cpus) : Prop :=
  ∀ j t,
    arrives_in arr_seq j →
    backlogged job_arrival job_cost job_jitter sched j t = true →
    (jobs_scheduled_at sched t).length = num_cpus

def respects_FP_policy {sporadic_task : Type u} {Job : Type v} [DecidableEq sporadic_task]
    [DecidableEq Job] (job_arrival job_cost : Job → time) (job_task : Job → sporadic_task)
    (job_jitter : Job → time) (arr_seq : arrival_sequence Job) {num_cpus : Nat} (sched : schedule Job num_cpus)
    (higher_eq_priority : FP_policy sporadic_task) : Prop :=
  ∀ j j_hp t,
    arrives_in arr_seq j →
    backlogged job_arrival job_cost job_jitter sched j t = true →
    scheduled sched j_hp t = true →
    higher_eq_priority (job_task j_hp) (job_task j) = true

def respects_JLFP_policy {Job : Type v} [DecidableEq Job] (job_arrival job_cost job_jitter : Job → time)
    (arr_seq : arrival_sequence Job) {num_cpus : Nat} (sched : schedule Job num_cpus)
    (higher_eq_priority : JLFP_policy Job) : Prop :=
  ∀ j j_hp t,
    arrives_in arr_seq j →
    backlogged job_arrival job_cost job_jitter sched j t = true →
    scheduled sched j_hp t = true →
    higher_eq_priority j_hp j = true

def respects_JLDP_policy {Job : Type v} [DecidableEq Job] (job_arrival job_cost job_jitter : Job → time)
    (arr_seq : arrival_sequence Job) {num_cpus : Nat} (sched : schedule Job num_cpus)
    (higher_eq_priority : JLDP_policy Job) : Prop :=
  ∀ j j_hp t,
    arrives_in arr_seq j →
    backlogged job_arrival job_cost job_jitter sched j t = true →
    scheduled sched j_hp t = true →
    higher_eq_priority t j_hp j = true

/-- LEAN_HELPER: the number of scheduled jobs counts the busy processors, so it
equals `num_cpus` iff every processor is busy. -/
private theorem size_scheduled_eq_iff {Job : Type v} [DecidableEq Job] {num_cpus : Nat}
    (sched : schedule Job num_cpus) (t : time) :
    (jobs_scheduled_at sched t).length = num_cpus ↔ ∀ cpu, ∃ j, sched cpu t = some j := by
  have hsize : (jobs_scheduled_at sched t).length =
      ∑ cpu : Fin num_cpus, (make_sequence (sched cpu t)).length :=
    Prosa.Classic.Util.Bigcat.size_bigcat_ord num_cpus _
  have hle : ∀ cpu : Fin num_cpus, (make_sequence (sched cpu t)).length ≤ 1 := by
    intro cpu; unfold make_sequence; split <;> simp
  rw [hsize]
  constructor
  · intro H cpu
    by_contra hnone
    have h0 : (make_sequence (sched cpu t)).length < 1 := by
      cases hs : sched cpu t with
      | none => simp [make_sequence]
      | some k => exact absurd ⟨k, hs⟩ hnone
    have := Finset.sum_lt_sum (s := Finset.univ) (f := fun c => (make_sequence (sched c t)).length)
      (g := fun _ => 1) (fun c _ => hle c) ⟨cpu, Finset.mem_univ _, h0⟩
    rw [H, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, Nat.mul_one] at this
    exact Nat.lt_irrefl _ this
  · intro H
    calc ∑ cpu : Fin num_cpus, (make_sequence (sched cpu t)).length
        = ∑ _cpu : Fin num_cpus, 1 := by
          apply Finset.sum_congr rfl
          intro cpu _
          obtain ⟨k, hk⟩ := H cpu
          simp [make_sequence, hk]
      _ = num_cpus := by simp

theorem work_conserving_eq_work_conserving_count {Job : Type v} [DecidableEq Job]
    (job_arrival job_cost job_jitter : Job → time) (arr_seq : arrival_sequence Job) {num_cpus : Nat}
    (sched : schedule Job num_cpus) :
    work_conserving job_arrival job_cost job_jitter arr_seq sched ↔
      work_conserving_count job_arrival job_cost job_jitter arr_seq sched := by
  unfold work_conserving work_conserving_count
  simp only [size_scheduled_eq_iff, scheduled_on, decide_eq_true_eq]

end Prosa.Classic.Model.Schedule.Global.Jitter.Platform.Platform
