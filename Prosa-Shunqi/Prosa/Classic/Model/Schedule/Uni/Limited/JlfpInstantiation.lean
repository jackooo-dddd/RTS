-- Authoritative source:
-- ProsaBuddy classic Prosa (prosabuddy commit f692cb7479780cf6009493f373a309e13165201c)
-- source: classic/model/schedule/uni/limited/jlfp_instantiation.v
-- sha256: see Prosa-Shunqi/classic-prosa/comprehensive-classic/file_order.csv (rank 155)

import Prosa.Classic.Util.All
import Prosa.Classic.Model.Arrival.Basic.Job
import Prosa.Classic.Model.Arrival.Basic.TaskArrival
import Prosa.Classic.Model.Priority
import Prosa.Classic.Model.Schedule.Uni.Service
import Prosa.Classic.Model.Schedule.Uni.Workload
import Prosa.Classic.Model.Schedule.Uni.ScheduleOfTask
import Prosa.Classic.Model.Schedule.Uni.Limited.BusyInterval
import Prosa.Classic.Model.Schedule.Uni.Limited.AbstractRTA.Definitions
import Prosa.Classic.Model.Schedule.Uni.Limited.AbstractRTA.AbstractSeqRta

/-!
JLFP instantiation of interference and interfering workload for abstract RTA (Rocq module `JLFPInstantiation` of
`classic/model/schedule/uni/limited/jlfp_instantiation.v`).

Representation notes:
* `if sched t is Some jhp then … else false` is a `match`; a Boolean summed as a number is `Bool.toNat`;
  `\sum_(jhp <- s | P jhp) F jhp` is `Prosa.Util.Sum.sumFiltered s P F`; `\sum_(t1 <= t < t2) F t` is
  `∑ t ∈ Finset.Ico t1 t2, F t`; `j1 != j2` is `!decide (j1 = j2)`; `~~ b` is `(!b) = true`.
* The section-local `Let`s are unfolded: `another_job_with_higher_eq_priority j1 j2` is
  `higher_eq_priority j1 j2 && !decide (j1 = j2)`, `job_from_another_task_with_higher_eq_priority j1 j2` is
  `higher_eq_priority j1 j2 && !decide (job_task j1 = job_task j2)`, `is_priority_inversion` is the accepted
  `BusyIntervalJLFP.is_priority_inversion sched higher_eq_priority`, `quiet_time` is `BusyIntervalJLFP.quiet_time`,
  `cumulative_task_interference` is `AbstractSeqRTA.cumul_task_interference job_task arr_seq sched`, and the
  cumulative functions, workloads and services (`cumulative_priority_inversion`, …,
  `service_of_other_jobs_with_hep_priority`) are the corresponding sums.
* Binder lists follow the Rocq contract.
* The two service equivalences are proved through one per-instant lemma (the job scheduled at an instant of
  `[t1, t)` is counted once among the jobs arrived in `[t1, t)`, using the quiet time at `t1`); the Rocq proofs
  inline this argument by induction on the interval length.
-/

set_option linter.unusedVariables false

namespace Prosa.Classic.Model.Schedule.Uni.Limited.JlfpInstantiation.JLFPInstantiation

open Prosa.Classic.Model.Time.Time
open Prosa.Classic.Model.Arrival.Basic.ArrivalSequence.ArrivalSequence
open Prosa.Classic.Model.Arrival.Basic.Job.Job
open Prosa.Classic.Model.Arrival.Basic.TaskArrival.TaskArrival
open Prosa.Classic.Model.Priority.Priority
open Prosa.Classic.Model.Schedule.Uni.Schedule.UniprocessorSchedule
open Prosa.Classic.Model.Schedule.Uni.Service.Service
open Prosa.Classic.Model.Schedule.Uni.Workload.Workload
open Prosa.Classic.Model.Schedule.Uni.ScheduleOfTask.ScheduleOfTask
open Prosa.Util.Sum (sumFiltered)

namespace BusyIntervalJLFP
export Prosa.Classic.Model.Schedule.Uni.Limited.BusyInterval.BusyIntervalJLFP
  (is_priority_inversion quiet_time busy_interval busy_interval_prefix)
end BusyIntervalJLFP
namespace AbstractRTADefinitions
export Prosa.Classic.Model.Schedule.Uni.Limited.AbstractRTA.Definitions.AbstractRTADefinitions
  (quiet_time busy_interval busy_interval_prefix cumul_interference cumul_interfering_workload)
end AbstractRTADefinitions
namespace AbstractSeqRTA
export Prosa.Classic.Model.Schedule.Uni.Limited.AbstractRTA.AbstractSeqRta.AbstractSeqRTA
  (cumul_task_interference task_interference_received_before)
end AbstractSeqRTA

universe u v

local macro "omega'" : tactic =>
  `(tactic| ((try dsimp only [Prosa.Classic.Model.Time.Time.time,
    Prosa.Classic.Model.Time.Time.instant, Prosa.Classic.Model.Time.Time.duration] at *) <;>
    omega))

/-! ### Interference and interfering workload -/

def is_interference_from_another_job_with_higher_eq_priority {Job : Type v} [DecidableEq Job] (sched : schedule Job)
    (higher_eq_priority : JLFP_policy Job) (j : Job) (t : time) : Bool :=
  match sched t with
  | some jhp => higher_eq_priority jhp j && !decide (jhp = j)
  | none => false

def is_interference_from_another_task_with_higher_eq_priority {Task : Type u} [DecidableEq Task] {Job : Type v} [DecidableEq Job] (job_task : Job → Task) (sched : schedule Job)
    (higher_eq_priority : JLFP_policy Job) (j : Job) (t : time) : Bool :=
  match sched t with
  | some jhp => higher_eq_priority jhp j && !decide (job_task jhp = job_task j)
  | none => false

def interfering_workload_of_jobs_with_hep_priority {Job : Type v} [DecidableEq Job] (job_cost : Job → time) (arr_seq : arrival_sequence Job)
    (higher_eq_priority : JLFP_policy Job) (j : Job) (t : time) : Nat :=
  sumFiltered (jobs_arriving_at arr_seq t) (fun jhp => higher_eq_priority jhp j && !decide (jhp = j)) job_cost

def interference {Job : Type v} [DecidableEq Job] (sched : schedule Job) (higher_eq_priority : JLFP_policy Job) (j : Job) (t : time) : Bool :=
  BusyIntervalJLFP.is_priority_inversion sched higher_eq_priority j t || is_interference_from_another_job_with_higher_eq_priority sched higher_eq_priority j t

def interfering_workload {Job : Type v} [DecidableEq Job] (job_cost : Job → time) (arr_seq : arrival_sequence Job) (sched : schedule Job)
    (higher_eq_priority : JLFP_policy Job) (j : Job) (t : time) : Nat :=
  (BusyIntervalJLFP.is_priority_inversion sched higher_eq_priority j t).toNat + interfering_workload_of_jobs_with_hep_priority job_cost arr_seq higher_eq_priority j t

/-! ### Proof-local facts -/

private theorem sumFiltered_append {α : Type _} (l1 l2 : List α) (P : α → Bool) (F : α → Nat) :
    sumFiltered (l1 ++ l2) P F = sumFiltered l1 P F + sumFiltered l2 P F := by
  simp [sumFiltered, List.filter_append, List.map_append, List.sum_append]

private theorem sumFiltered_exchange {α : Type _} (l : List α) (P : α → Bool) (f : α → Nat → Nat) (t1 t2 : Nat) :
    sumFiltered l P (fun i => ∑ t ∈ Finset.Ico t1 t2, f i t) = ∑ t ∈ Finset.Ico t1 t2, sumFiltered l P (fun i => f i t) := by
  unfold sumFiltered
  induction (l.filter P) with
  | nil => simp
  | cons a l ih => simp only [List.map_cons, List.sum_cons, ih, Finset.sum_add_distrib]

private theorem arrivals_between_succ {Job : Type v} [DecidableEq Job] (arr_seq : arrival_sequence Job) (t1 t : Nat) (h : t1 ≤ t) :
    jobs_arrived_between arr_seq t1 (t + 1) = jobs_arrived_between arr_seq t1 t ++ jobs_arriving_at arr_seq t := by
  rw [job_arrived_between_cat arr_seq t1 t (t + 1) h (Nat.le_succ t)]
  congr 1
  simp [jobs_arrived_between, Prosa.Util.Notation.bigCat]

/-- LEAN_HELPER: in a duplicate-free list, the service at `x` of the retained jobs counts the scheduled job once. -/
private theorem sumFiltered_cons {{α : Type _}} (a : α) (L : List α) (P : α → Bool) (F : α → Nat) :
    sumFiltered (a :: L) P F = (if P a = true then F a else 0) + sumFiltered L P F := by
  unfold sumFiltered
  rw [List.filter_cons]
  split <;> simp

private theorem sumFiltered_service_at {Job : Type v} [DecidableEq Job] (sched : schedule Job) (x : time)
    (L : List Job) (hnd : L.Nodup) (P : Job → Bool) :
    sumFiltered L P (fun jo => service_at sched jo x) =
      (match sched x with | some s => decide (s ∈ L) && P s | none => false).toNat := by
  induction L with
  | nil => cases sched x <;> rfl
  | cons a L ih =>
    rw [List.nodup_cons] at hnd
    rw [sumFiltered_cons, ih hnd.2]
    cases hs : sched x with
    | none => simp [service_at, scheduled_at, hs]
    | some s =>
      simp only [service_at, scheduled_at, hs, Option.some.injEq, List.mem_cons]
      by_cases EQ : a = s
      · subst EQ
        have NIN := hnd.1
        cases hP : P a <;> simp [hP, NIN]
      · have NE : s ≠ a := fun h => EQ h.symm
        cases hP : P a <;> cases hm : decide (s ∈ L) <;> simp_all

/-- LEAN_HELPER: after a quiet time, the cumulative interference of a predicate that implies higher-or-equal
priority is the service of the retained jobs arrived in the interval. -/
private theorem cumul_pred_eq_service {Job : Type v} [DecidableEq Job] (job_arrival job_cost : Job → time) (arr_seq : arrival_sequence Job)
    (H_arrival_times_are_consistent : arrival_times_are_consistent job_arrival arr_seq)
    (H_arr_seq_is_a_set : arrival_sequence_is_a_set arr_seq)
    (sched : schedule Job) (H_jobs_come_from_arrival_sequence : jobs_come_from_arrival_sequence sched arr_seq)
    (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute job_arrival sched)
    (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched)
    (higher_eq_priority : JLFP_policy Job) (j : Job) (t1 t : time)
    (H_quiet_time : BusyIntervalJLFP.quiet_time job_arrival job_cost arr_seq sched higher_eq_priority j t1) (P : Job → Bool) (HP : ∀ s, P s = true → higher_eq_priority s j = true) :
    ∑ x ∈ Finset.Ico t1 t, (match sched x with | some s => P s | none => false).toNat =
      service_of_jobs sched (jobs_arrived_between arr_seq t1 t) P t1 t := by
  unfold service_of_jobs service_during
  rw [sumFiltered_exchange]
  apply Finset.sum_congr rfl
  intro x hx
  rw [Finset.mem_Ico] at hx
  rw [sumFiltered_service_at sched x _ (arrivals_uniq job_arrival arr_seq H_arrival_times_are_consistent
    H_arr_seq_is_a_set t1 t)]
  cases hs : sched x with
  | none => rfl
  | some s =>
    simp only
    cases hPs : P s
    · simp
    · have SCHED : scheduled_at sched s x = true := by simp [scheduled_at, hs]
      have ARRs := H_jobs_come_from_arrival_sequence s x SCHED
      have MUST := H_jobs_must_arrive_to_execute s x SCHED
      simp only [has_arrived, decide_eq_true_eq] at MUST
      have GE : t1 ≤ job_arrival s := by
        by_contra LT
        have C := H_quiet_time s ARRs (HP s hPs) (by simp [arrived_before]; omega')
        have C' := completion_monotonic job_cost sched s t1 x hx.1 C
        have := completed_implies_not_scheduled job_cost sched s H_completed_jobs_dont_execute x C'
        rw [SCHED] at this; exact Bool.noConfusion this
      have IN : s ∈ jobs_arrived_between arr_seq t1 t :=
        arrived_between_implies_in_arrivals job_arrival arr_seq H_arrival_times_are_consistent s t1 t ARRs
          (by simp only [arrived_between, Bool.and_eq_true, decide_eq_true_eq]; omega')
      simp [IN]

/-! ### Equivalences -/

theorem cumulative_interference_split {Job : Type v} [DecidableEq Job] (sched : schedule Job) (higher_eq_priority : JLFP_policy Job) :
    ∀ (j : Job) (t1 t2 : time),
      ∑ t ∈ Finset.Ico t1 t2, (interference sched higher_eq_priority j t).toNat =
        ∑ t ∈ Finset.Ico t1 t2, (BusyIntervalJLFP.is_priority_inversion sched higher_eq_priority j t).toNat + ∑ t ∈ Finset.Ico t1 t2, (is_interference_from_another_job_with_higher_eq_priority sched higher_eq_priority j t).toNat := by
  intro j t1 t2
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro t _
  unfold interference BusyIntervalJLFP.is_priority_inversion is_interference_from_another_job_with_higher_eq_priority
  cases sched t with
  | none => rfl
  | some s => cases h : higher_eq_priority s j <;> simp [h]

theorem cumulative_task_interference_split {Task : Type u} [DecidableEq Task] {Job : Type v} [DecidableEq Job] (job_arrival job_cost : Job → time) (job_task : Job → Task)
    (arr_seq : arrival_sequence Job) (sched : schedule Job)
    (H_sequential_jobs : sequential_jobs job_arrival job_cost sched job_task)
    (higher_eq_priority : JLFP_policy Job)
    (H_JLFP_respects_sequential_jobs : JLFP_respects_sequential_jobs job_task job_arrival higher_eq_priority)
    (tsk : Task) :
    ∀ (j : Job) (t1 t2 upp_t : time),
      job_task j = tsk →
      j ∈ jobs_arrived_before arr_seq upp_t →
      (!completed_by job_cost sched j t2) = true →
      AbstractSeqRTA.cumul_task_interference job_task arr_seq sched (interference sched higher_eq_priority) tsk upp_t t1 t2 =
        ∑ t ∈ Finset.Ico t1 t2, (BusyIntervalJLFP.is_priority_inversion sched higher_eq_priority j t).toNat + ∑ t ∈ Finset.Ico t1 t2, (is_interference_from_another_task_with_higher_eq_priority job_task sched higher_eq_priority j t).toNat := by
  intro j t1 t2 upp TSK ARR NCOMPL
  unfold AbstractSeqRTA.cumul_task_interference
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro t ht
  rw [Finset.mem_Ico] at ht
  have JIN : j ∈ arrivals_of_task_before job_task arr_seq tsk upp := by
    unfold arrivals_of_task_before arrivals_of_task_between
    rw [List.mem_filter]
    exact ⟨ARR, by simp [is_job_of_task, TSK]⟩
  unfold AbstractSeqRTA.task_interference_received_before task_scheduled_at
  cases hs : sched t with
  | none =>
    have NONE : ∀ x, (interference sched higher_eq_priority x t) = false := by
      intro x; simp [interference, BusyIntervalJLFP.is_priority_inversion,
        is_interference_from_another_job_with_higher_eq_priority, hs]
    simp [BusyIntervalJLFP.is_priority_inversion, is_interference_from_another_task_with_higher_eq_priority, hs, NONE]
  | some s =>
    by_cases STSK : job_task s = tsk
    · have HPs : higher_eq_priority s j = true := by
        cases COMP : completed_by job_cost sched j t
        · have ARRle := scheduler_executes_job_with_earliest_arrival job_arrival job_cost sched job_task
            H_sequential_jobs s j t (by simp [STSK, TSK]) (by simp [COMP]) (by simp [scheduled_at, hs])
          exact H_JLFP_respects_sequential_jobs s j (by simp [STSK, TSK]) ARRle
        · have := completion_monotonic job_cost sched j t t2 (Nat.le_of_lt ht.2) COMP
          rw [this] at NCOMPL; exact absurd NCOMPL (by simp)
      simp [BusyIntervalJLFP.is_priority_inversion, is_interference_from_another_task_with_higher_eq_priority, hs,
        STSK, HPs, TSK]
    · have INTj : (interference sched higher_eq_priority j t) = true := by
        have NE : s ≠ j := fun h => STSK (h ▸ TSK)
        cases hp : higher_eq_priority s j <;>
          simp [interference, BusyIntervalJLFP.is_priority_inversion,
            is_interference_from_another_job_with_higher_eq_priority, hs, hp, NE]
      have ANY : (arrivals_of_task_before job_task arr_seq tsk upp).any (fun x => interference sched higher_eq_priority x t) = true :=
        List.any_eq_true.mpr ⟨j, JIN, INTj⟩
      have NTj : job_task s ≠ job_task j := by rw [TSK]; exact STSK
      cases hp : higher_eq_priority s j <;>
        simp [BusyIntervalJLFP.is_priority_inversion, is_interference_from_another_task_with_higher_eq_priority, hs, hp,
          STSK, ANY, NTj]

theorem instantiated_cumulative_workload_of_hep_jobs_equal_total_workload_of_hep_jobs {Job : Type v} [DecidableEq Job] (job_cost : Job → time)
    (arr_seq : arrival_sequence Job) (higher_eq_priority : JLFP_policy Job) (t1 t2 : time) (j : Job) :
    ∑ t ∈ Finset.Ico t1 t2, interfering_workload_of_jobs_with_hep_priority job_cost arr_seq higher_eq_priority j t =
      workload_of_jobs job_cost (jobs_arrived_between arr_seq t1 t2) (fun jhp => higher_eq_priority jhp j && !decide (jhp = j)) := by
  rcases Nat.lt_or_ge t1 t2 with LT | GE
  · obtain ⟨k, rfl⟩ : ∃ k, t2 = t1 + k := ⟨t2 - t1, by omega'⟩
    induction k with
    | zero => simp [workload_of_jobs, sumFiltered, jobs_arrived_between, Prosa.Util.Notation.bigCat]
    | succ k ih =>
      rw [show t1 + (k + 1) = (t1 + k) + 1 by omega', Finset.sum_Ico_succ_top (by omega'),
        arrivals_between_succ arr_seq t1 (t1 + k) (by omega')]
      unfold workload_of_jobs at ih ⊢
      rw [sumFiltered_append]
      rcases Nat.eq_zero_or_pos k with hk | hk
      · subst hk
        simp [sumFiltered, jobs_arrived_between, Prosa.Util.Notation.bigCat,
          interfering_workload_of_jobs_with_hep_priority]
      · rw [ih (by omega')]
        rfl
  · rw [Finset.Ico_eq_empty_of_le GE]
    simp [workload_of_jobs, sumFiltered, jobs_arrived_between, Prosa.Util.Notation.bigCat, Nat.sub_eq_zero_of_le GE]

theorem instantiated_cumulative_interference_of_hep_jobs_equal_total_interference_of_hep_jobs {Job : Type v} [DecidableEq Job]
    (job_arrival job_cost : Job → time) (arr_seq : arrival_sequence Job) (H_arrival_times_are_consistent : arrival_times_are_consistent job_arrival arr_seq)
    (H_arr_seq_is_a_set : arrival_sequence_is_a_set arr_seq)
    (sched : schedule Job) (H_jobs_come_from_arrival_sequence : jobs_come_from_arrival_sequence sched arr_seq)
    (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute job_arrival sched)
    (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched)
    (higher_eq_priority : JLFP_policy Job) (j : Job) (t1 t : time) (H_quiet_time : BusyIntervalJLFP.quiet_time job_arrival job_cost arr_seq sched higher_eq_priority j t1) :
    ∑ x ∈ Finset.Ico t1 t, (is_interference_from_another_job_with_higher_eq_priority sched higher_eq_priority j x).toNat = service_of_jobs sched (jobs_arrived_between arr_seq t1 t) (fun jhp => higher_eq_priority jhp j && !decide (jhp = j)) t1 t :=
  cumul_pred_eq_service job_arrival job_cost arr_seq H_arrival_times_are_consistent H_arr_seq_is_a_set sched
    H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute higher_eq_priority j
    t1 t H_quiet_time _ (fun s h => by simp only [Bool.and_eq_true] at h; exact h.1)

theorem instantiated_cumulative_interference_of_hep_tasks_equal_total_interference_of_hep_tasks {Task : Type u} [DecidableEq Task] {Job : Type v} [DecidableEq Job]
    (job_arrival job_cost : Job → time) (job_task : Job → Task) (arr_seq : arrival_sequence Job) (H_arrival_times_are_consistent : arrival_times_are_consistent job_arrival arr_seq)
    (H_arr_seq_is_a_set : arrival_sequence_is_a_set arr_seq)
    (sched : schedule Job) (H_jobs_come_from_arrival_sequence : jobs_come_from_arrival_sequence sched arr_seq)
    (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute job_arrival sched)
    (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched)
    (higher_eq_priority : JLFP_policy Job) (j : Job) (t1 t : time) (H_quiet_time : BusyIntervalJLFP.quiet_time job_arrival job_cost arr_seq sched higher_eq_priority j t1) :
    ∑ x ∈ Finset.Ico t1 t, (is_interference_from_another_task_with_higher_eq_priority job_task sched higher_eq_priority j x).toNat = service_of_jobs sched (jobs_arrived_between arr_seq t1 t) (fun jhp => higher_eq_priority jhp j && !decide (job_task jhp = job_task j)) t1 t :=
  cumul_pred_eq_service job_arrival job_cost arr_seq H_arrival_times_are_consistent H_arr_seq_is_a_set sched
    H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute higher_eq_priority j
    t1 t H_quiet_time _ (fun s h => by simp only [Bool.and_eq_true] at h; exact h.1)

/-! ### Busy interval equivalence -/

/-- LEAN_HELPER: splitting off a retained element of a duplicate-free list from a filtered sum. -/
private theorem sumFiltered_split_self {{α : Type _}} [DecidableEq α] (L : List α) (P : α → Bool) (F : α → Nat) (a : α)
    (hnd : L.Nodup) :
    sumFiltered L P F = sumFiltered L (fun x => P x && !decide (x = a)) F + (if a ∈ L ∧ P a = true then F a else 0) := by
  induction L with
  | nil => simp [sumFiltered]
  | cons b L ih =>
    rw [List.nodup_cons] at hnd
    have IH := ih hnd.2
    rw [sumFiltered_cons, sumFiltered_cons]
    by_cases EQ : b = a
    · subst EQ
      have NIN := hnd.1
      have SAME : sumFiltered L (fun x => P x && !decide (x = b)) F = sumFiltered L P F := by
        unfold sumFiltered
        congr 2
        apply List.filter_congr
        intro x hx
        have : x ≠ b := fun h => NIN (h ▸ hx)
        simp [this]
      rw [SAME]
      cases hP : P b <;> simp [hP] <;> omega
    · have NE : ¬ (a = b) := fun h => EQ h.symm
      rw [IH]
      cases hP : P b <;> by_cases hIn : a ∈ L <;> simp [hP, EQ, NE, hIn] <;> omega

theorem instantiated_quiet_time_equivalent_edf_quiet_time {Task : Type u} [DecidableEq Task] {Job : Type v} [DecidableEq Job] (job_arrival job_cost : Job → time)
    (job_task : Job → Task) (arr_seq : arrival_sequence Job) (H_arrival_times_are_consistent : arrival_times_are_consistent job_arrival arr_seq)
    (H_arr_seq_is_a_set : arrival_sequence_is_a_set arr_seq)
    (sched : schedule Job) (H_jobs_come_from_arrival_sequence : jobs_come_from_arrival_sequence sched arr_seq)
    (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute job_arrival sched)
    (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched)
    (higher_eq_priority : JLFP_policy Job) (H_priority_is_reflexive : JLFP_is_reflexive higher_eq_priority) (j : Job)
    (H_j_arrives : arrives_in arr_seq j) (H_job_cost_positive : job_cost_positive job_cost j = true) :
    ∀ t, BusyIntervalJLFP.quiet_time job_arrival job_cost arr_seq sched higher_eq_priority j t ↔
      AbstractRTADefinitions.quiet_time job_arrival job_cost sched (interference sched higher_eq_priority) (interfering_workload job_cost arr_seq sched higher_eq_priority) j t := by
  have ZERO : BusyIntervalJLFP.quiet_time job_arrival job_cost arr_seq sched higher_eq_priority j 0 := by
    intro jhp _ _ AB; simp [arrived_before] at AB
  have IC1 := instantiated_cumulative_interference_of_hep_jobs_equal_total_interference_of_hep_jobs job_arrival
    job_cost arr_seq H_arrival_times_are_consistent H_arr_seq_is_a_set sched H_jobs_come_from_arrival_sequence
    H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute higher_eq_priority j 0
  have WL := instantiated_cumulative_workload_of_hep_jobs_equal_total_workload_of_hep_jobs job_cost arr_seq
    higher_eq_priority 0
  have SPLIT := cumulative_interference_split sched higher_eq_priority j 0
  have UNIQ := fun t => arrivals_uniq job_arrival arr_seq H_arrival_times_are_consistent H_arr_seq_is_a_set 0 t
  have EQUIV := fun t (P : Job → Bool) => all_jobs_have_completed_equiv_workload_eq_service job_arrival job_cost arr_seq
    H_arrival_times_are_consistent sched H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute P 0 t t
  intro t
  -- the abstract interference and interfering workload equations reduce to service/workload of other hep jobs
  have KEY : AbstractRTADefinitions.cumul_interference (interference sched higher_eq_priority) j 0 t =
      AbstractRTADefinitions.cumul_interfering_workload (interfering_workload job_cost arr_seq sched higher_eq_priority) j 0 t ↔
      service_of_jobs sched (jobs_arrived_between arr_seq 0 t) (fun jhp => higher_eq_priority jhp j && !decide (jhp = j)) 0 t =
        workload_of_jobs job_cost (jobs_arrived_between arr_seq 0 t) (fun jhp => higher_eq_priority jhp j && !decide (jhp = j)) := by
    have E1 : AbstractRTADefinitions.cumul_interference (interference sched higher_eq_priority) j 0 t =
        ∑ x ∈ Finset.Ico 0 t, (BusyIntervalJLFP.is_priority_inversion sched higher_eq_priority j x).toNat +
          service_of_jobs sched (jobs_arrived_between arr_seq 0 t)
            (fun jhp => higher_eq_priority jhp j && !decide (jhp = j)) 0 t := by
      unfold AbstractRTADefinitions.cumul_interference
      rw [SPLIT t, IC1 t ZERO]
    have E2 : AbstractRTADefinitions.cumul_interfering_workload (interfering_workload job_cost arr_seq sched higher_eq_priority) j 0 t =
        ∑ x ∈ Finset.Ico 0 t, (BusyIntervalJLFP.is_priority_inversion sched higher_eq_priority j x).toNat +
          workload_of_jobs job_cost (jobs_arrived_between arr_seq 0 t)
            (fun jhp => higher_eq_priority jhp j && !decide (jhp = j)) := by
      unfold AbstractRTADefinitions.cumul_interfering_workload interfering_workload
      rw [Finset.sum_add_distrib, WL t j]
    rw [E1, E2]
    omega
  constructor
  · intro QT
    refine ⟨KEY.mpr ?_, ?_⟩
    · exact ((EQUIV t _).mp (fun jo IN P => QT jo (in_arrivals_implies_arrived arr_seq jo 0 t IN)
        (by simp only [Bool.and_eq_true] at P; exact P.1)
        (by have := in_arrivals_implies_arrived_between job_arrival arr_seq H_arrival_times_are_consistent jo 0 t IN
            simp only [arrived_between, arrived_before, Bool.and_eq_true, decide_eq_true_eq] at this ⊢; omega'))).symm
    · simp only [pending_earlier_and_at, Bool.not_and, Bool.not_not, Bool.or_eq_true, Bool.not_eq_true']
      cases AB : arrived_before job_arrival j t
      · left; rfl
      · right; exact QT j H_j_arrives (H_priority_is_reflexive j) AB
  · intro ⟨EQ, NPEND⟩
    have SW := KEY.mp EQ
    -- the service and workload of all higher-or-equal-priority jobs (including `j`) coincide
    have ALL : workload_of_jobs job_cost (jobs_arrived_between arr_seq 0 t) (fun jhp => higher_eq_priority jhp j) =
        service_of_jobs sched (jobs_arrived_between arr_seq 0 t) (fun jhp => higher_eq_priority jhp j) 0 t := by
      unfold workload_of_jobs service_of_jobs at SW ⊢
      rw [sumFiltered_split_self _ _ _ j (UNIQ t), sumFiltered_split_self _ (fun jhp => higher_eq_priority jhp j) _ j (UNIQ t)]
      rw [SW]
      congr 1
      by_cases INj : j ∈ jobs_arrived_between arr_seq 0 t
      · simp only [INj, H_priority_is_reflexive j, and_self, if_true]
        simp only [pending_earlier_and_at, Bool.not_and, Bool.not_not, Bool.or_eq_true, Bool.not_eq_true'] at NPEND
        rcases NPEND with NAB | COMP
        · have := in_arrivals_implies_arrived_between job_arrival arr_seq H_arrival_times_are_consistent j 0 t INj
          simp only [arrived_between, Bool.and_eq_true, decide_eq_true_eq] at this
          simp only [arrived_before, decide_eq_false_iff_not, Nat.not_lt] at NAB
          omega'
        · have C1 := of_decide_eq_true COMP
          have C2 := cumulative_service_le_job_cost job_cost sched j H_completed_jobs_dont_execute 0 t
          unfold service at C1
          have : service_during sched j 0 t = job_cost j := by omega'
          rw [this]
      · simp [INj]
    intro jhp ARRhp HPhp AB
    exact (EQUIV t _).mpr ALL jhp
      (arrived_between_implies_in_arrivals job_arrival arr_seq H_arrival_times_are_consistent jhp 0 t ARRhp
        (by simp only [arrived_between, arrived_before, Bool.and_eq_true, decide_eq_true_eq] at AB ⊢; omega'))
      HPhp

theorem instantiated_busy_interval_equivalent_edf_busy_interval {Task : Type u} [DecidableEq Task] {Job : Type v} [DecidableEq Job] (job_arrival job_cost : Job → time)
    (job_task : Job → Task) (arr_seq : arrival_sequence Job) (H_arrival_times_are_consistent : arrival_times_are_consistent job_arrival arr_seq)
    (H_arr_seq_is_a_set : arrival_sequence_is_a_set arr_seq)
    (sched : schedule Job) (H_jobs_come_from_arrival_sequence : jobs_come_from_arrival_sequence sched arr_seq)
    (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute job_arrival sched)
    (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched)
    (higher_eq_priority : JLFP_policy Job) (H_priority_is_reflexive : JLFP_is_reflexive higher_eq_priority) (j : Job)
    (H_j_arrives : arrives_in arr_seq j) (H_job_cost_positive : job_cost_positive job_cost j = true) :
    ∀ t1 t2,
      BusyIntervalJLFP.busy_interval job_arrival job_cost arr_seq sched higher_eq_priority j t1 t2 ↔
        AbstractRTADefinitions.busy_interval job_arrival job_cost sched (interference sched higher_eq_priority) (interfering_workload job_cost arr_seq sched higher_eq_priority) j t1 t2 := by
  have QE := instantiated_quiet_time_equivalent_edf_quiet_time job_arrival job_cost job_task arr_seq
    H_arrival_times_are_consistent H_arr_seq_is_a_set sched H_jobs_come_from_arrival_sequence
    H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute higher_eq_priority H_priority_is_reflexive j
    H_j_arrives H_job_cost_positive
  intro t1 t2
  unfold BusyIntervalJLFP.busy_interval BusyIntervalJLFP.busy_interval_prefix AbstractRTADefinitions.busy_interval
    AbstractRTADefinitions.busy_interval_prefix
  constructor
  · rintro ⟨⟨LT, QT1, NQT, IN⟩, QT2⟩
    exact ⟨⟨IN, (QE t1).mp QT1, fun t h QT => NQT t h ((QE t).mpr QT)⟩, (QE t2).mp QT2⟩
  · rintro ⟨⟨IN, QT1, NQT⟩, QT2⟩
    have IN' := IN
    simp only [Bool.and_eq_true, decide_eq_true_eq] at IN'
    exact ⟨⟨by omega', (QE t1).mpr QT1, fun t h QT => NQT t h ((QE t).mp QT), IN⟩, (QE t2).mpr QT2⟩

end Prosa.Classic.Model.Schedule.Uni.Limited.JlfpInstantiation.JLFPInstantiation
