-- Authoritative source:
-- ProsaBuddy classic Prosa (prosabuddy commit f692cb7479780cf6009493f373a309e13165201c)
-- source: classic/implementation/uni/basic/tdma_rta_example.v
-- sha256: see Prosa-Shunqi/classic-prosa/comprehensive-classic/file_order.csv (rank 153)

import Prosa.Classic.Util.All
import Prosa.Classic.Util.FindSeq
import Prosa.Classic.Model.Arrival.Basic.Job
import Prosa.Classic.Model.Arrival.Basic.ArrivalSequence
import Prosa.Classic.Model.Schedule.Uni.Basic.PlatformTdma
import Prosa.Classic.Model.Arrival.Basic.Task
import Prosa.Classic.Model.PolicyTdma
import Prosa.Classic.Model.Schedule.Uni.Schedule
import Prosa.Classic.Model.Schedule.Uni.Schedulability
import Prosa.Classic.Model.Priority
import Prosa.Classic.Analysis.Uni.Basic.TdmaRtaTheory
import Prosa.Classic.Analysis.Uni.Basic.TdmaWcrtAnalysis
import Prosa.Classic.Implementation.Job
import Prosa.Classic.Implementation.Task
import Prosa.Classic.Implementation.ArrivalSequence
import Prosa.Classic.Implementation.Uni.Basic.ScheduleTdma

/-!
A TDMA response-time analysis example (Rocq module `ResponseTimeAnalysisExemple` of
`classic/implementation/uni/basic/tdma_rta_example.v`).

Representation notes:
* The section-local `Let`s that define the concrete example (`tsk1`, `tsk2`, `tsk3`, `time_slot1`, `time_slot2`,
  `time_slot3`, `ts`, `slot_seq`, `arr_seq`, `sched`) are kept as `LEAN_HELPER` definitions of the same names
  (`ts` is built with the `Program` obligation `ts_obligation_1` of the source, proved by `decide`); the other
  `Let`s (`job_in_time_slot`, `tdma_claimed_bound`, `tdma_valid_bound`, `no_deadline_missed_by`) are unfolded.
* Concrete jobs and tasks use the accepted `ConcreteJob`/`ConcreteTask` records, whose fields are the job and task
  parameter functions.
* `time_slot`: `find (fun tsk => tsk == task) s` is `List.findIdx (fun tsk => decide (tsk = task)) s` and
  `nth n s n` is `s.getD n n`; `slot_order task1 task2 := task_id task1 >= task_id task2` is the Boolean
  `decide (task2.task_id ≤ task1.task_id)`.
* `is_valid_tdma_bound` is Boolean in Rocq (`bound <= task_deadline tsk`) and a `Prop` in the accepted Lean
  translation, so `tdma_valid_bound tsk = true` is stated as `is_valid_tdma_bound concrete_task.task_deadline tsk …`.
* The Rocq source ends the proofs of `respects_TDMA_policy`, `valid_tdma_bounds`, `WCRT_le_period` and
  `ts_is_schedulable_by_tdma` with `Admitted`. These four statements are proved here (the WCRT values are
  8, 5 and 6 against deadlines 15, 5, 6 and periods 16, 8, 9; the TDMA policy follows from the FIFO order of the
  pending jobs and the uniqueness of the active slot). As Rocq keeps every section variable of an `Admitted`
  lemma, these lemmas take the unused section binder `{Job}`, as in the contract.
-/

set_option linter.unusedVariables false

namespace Prosa.Classic.Implementation.Uni.Basic.TdmaRtaExample.ResponseTimeAnalysisExemple

open Prosa.Classic.Model.Time.Time
open Prosa.Classic.Model.Arrival.Basic.ArrivalSequence.ArrivalSequence
open Prosa.Classic.Model.Arrival.Basic.Job.Job
open Prosa.Classic.Model.Arrival.Basic.Task.SporadicTaskset
open Prosa.Classic.Model.Schedule.Uni.Schedule.UniprocessorSchedule
open Prosa.Classic.Model.Schedule.Uni.Schedulability.Schedulability
open Prosa.Classic.Model.PolicyTdma.PolicyTDMA
open Prosa.Classic.Model.Schedule.Uni.Basic.PlatformTdma.Platform_TDMA
open Prosa.Classic.Analysis.Uni.Basic.TdmaRtaTheory.ResponseTimeAnalysisTDMA
open Prosa.Classic.Analysis.Uni.Basic.TdmaWcrtAnalysis.WCRT_OneJobTDMA (WCRT WCRT_formula)
open Prosa.Classic.Implementation.Job.ConcreteJob
open Prosa.Classic.Implementation.Task.ConcreteTask
open Prosa.Classic.Implementation.ArrivalSequence.ConcreteArrivalSequence
open Prosa.Classic.Implementation.Uni.Basic.ScheduleTdma.ConcreteSchedulerTDMA

universe v

local macro "omega'" : tactic =>
  `(tactic| ((try dsimp only [Prosa.Classic.Model.Time.Time.time,
    Prosa.Classic.Model.Time.Time.instant, Prosa.Classic.Model.Time.Time.duration] at *) <;>
    omega))

/-! ### The example (LEAN_HELPER definitions for the section `Let`s) -/

/-- LEAN_HELPER (Rocq `Let tsk1`). -/
def tsk1 : concrete_task := { task_id := 1, task_cost := 1, task_period := 16, task_deadline := 15 }
/-- LEAN_HELPER (Rocq `Let tsk2`). -/
def tsk2 : concrete_task := { task_id := 2, task_cost := 1, task_period := 8, task_deadline := 5 }
/-- LEAN_HELPER (Rocq `Let tsk3`). -/
def tsk3 : concrete_task := { task_id := 3, task_cost := 1, task_period := 9, task_deadline := 6 }

/-- LEAN_HELPER (Rocq `Let time_slot1`). -/
def time_slot1 : Nat := 1
/-- LEAN_HELPER (Rocq `Let time_slot2`). -/
def time_slot2 : Nat := 4
/-- LEAN_HELPER (Rocq `Let time_slot3`). -/
def time_slot3 : Nat := 3

theorem ts_obligation_1 : [tsk1, tsk2, tsk3].Nodup := by decide

/-- LEAN_HELPER (Rocq `Program Let ts := Build_set [:: tsk1; tsk2; tsk3] _`). -/
def ts : concrete_taskset := ⟨[tsk1, tsk2, tsk3], ts_obligation_1⟩

/-- LEAN_HELPER (Rocq `Let slot_seq`). -/
def slot_seq : List (concrete_task × Nat) := [(tsk1, time_slot1), (tsk2, time_slot2), (tsk3, time_slot3)]

theorem ts_has_valid_parameters :
    valid_sporadic_taskset concrete_task.task_cost concrete_task.task_period concrete_task.task_deadline ts.val := by
  intro tsk IN
  simp only [ts, List.mem_cons, List.not_mem_nil, or_false] at IN
  rcases IN with rfl | rfl | rfl <;> exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- LEAN_HELPER (Rocq `Let arr_seq`). -/
def arr_seq : arrival_sequence concrete_job := periodic_arrival_sequence ts

theorem job_arrival_times_are_consistent : arrival_times_are_consistent concrete_job.job_arrival arr_seq :=
  periodic_arrivals_are_consistent ts

def time_slot (task : concrete_task) : Nat :=
  if task ∈ slot_seq.map Prod.fst then
    (slot_seq.map Prod.snd).getD (List.findIdx (fun tsk => decide (tsk = task)) (slot_seq.map Prod.fst))
      (List.findIdx (fun tsk => decide (tsk = task)) (slot_seq.map Prod.fst))
  else 0

theorem valid_time_slots : ∀ tsk, tsk ∈ ts → is_valid_time_slot tsk time_slot = true := by
  intro tsk IN
  change tsk ∈ ts.val at IN
  simp only [ts, List.mem_cons, List.not_mem_nil, or_false] at IN
  rcases IN with rfl | rfl | rfl <;> decide

def slot_order (task1 task2 : concrete_task) : Bool :=
  decide (task2.task_id ≤ task1.task_id)

/-- LEAN_HELPER (Rocq `Let sched`). -/
def sched : schedule concrete_job :=
  scheduler_tdma concrete_job.job_arrival concrete_job.job_cost concrete_job.job_task arr_seq ts time_slot slot_order

theorem slot_order_total : slot_order_is_total_over_task_set ts slot_order := by
  intro x1 x2 _ _
  simp only [slot_order, decide_eq_true_eq]
  omega

theorem slot_order_transitive : slot_order_is_transitive slot_order := by
  intro y x z h1 h2
  simp only [slot_order, decide_eq_true_eq] at *
  omega

theorem slot_order_antisymmetric : slot_order_is_antisymmetric_over_task_set ts slot_order := by
  intro x1 x2 IN1 IN2 O1 O2
  simp only [ts, List.mem_cons, List.not_mem_nil, or_false] at IN1 IN2
  rcases IN1 with rfl | rfl | rfl <;> rcases IN2 with rfl | rfl | rfl <;> first | rfl | (exfalso; revert O1 O2; decide)

/-! ### The TDMA policy -/

/-- LEAN_HELPER: the head of a filtered list comes before any other retained element. -/
private theorem head_filter_findIdx_lt {{α : Type v}} [DecidableEq α] (p : α → Bool) :
    ∀ (L : List α) (y j : α), (L.filter p).head? = some y → j ∈ L → p j = true → j ≠ y →
      List.findIdx (fun x => decide (x = y)) L < List.findIdx (fun x => decide (x = j)) L := by
  intro L
  induction L with
  | nil => intro y j _ IN; simp at IN
  | cons a L ih =>
    intro y j HD IN Pj NE
    rw [List.filter_cons] at HD
    by_cases Pa : p a = true
    · rw [if_pos Pa, List.head?_cons, Option.some.injEq] at HD
      subst HD
      have hj : a ≠ j := fun h => NE h.symm
      simp [List.findIdx_cons, hj]
    · rw [if_neg Pa] at HD
      have haj : a ≠ j := by intro h; subst h; exact Pa Pj
      have hy : y ∈ L.filter p := List.mem_of_mem_head? HD
      have hay : a ≠ y := by
        intro h; subst h; exact Pa (List.mem_filter.mp hy).2
      have INj : j ∈ L := by
        rcases List.mem_cons.mp IN with h | h
        · exact absurd h.symm haj
        · exact h
      simp only [List.findIdx_cons, hay, haj, decide_false, cond_false]
      exact Nat.succ_lt_succ (ih y j HD INj Pj NE)

theorem respects_TDMA_policy {Job : Type v} [DecidableEq Job] :
    Respects_TDMA_policy concrete_job.job_arrival concrete_job.job_cost concrete_job.job_task arr_seq sched ts
      time_slot slot_order := by
  intro j t ARRJ
  have VALID := ts_has_valid_parameters
  have SET := periodic_arrivals_is_a_set ts VALID
  have FROMTS := periodic_arrivals_all_jobs_from_taskset ts
  set L := pending_jobs concrete_job.job_arrival concrete_job.job_cost arr_seq sched t with HL
  set p : concrete_job → Bool := fun job => Task_in_time_slot ts slot_order job.job_task time_slot t with HP
  have SCHEDeq : sched t = (L.filter p).head? := by
    show scheduler_tdma _ _ _ _ _ _ _ t = _
    rw [scheduler_uses_construction_function]
    rfl
  constructor
  · intro SCHED
    simp only [scheduled_at, decide_eq_true_eq] at SCHED
    rw [SCHEDeq] at SCHED
    exact (List.mem_filter.mp (List.mem_of_mem_head? SCHED)).2
  · intro BACK
    simp only [backlogged, Bool.and_eq_true, Bool.not_eq_true'] at BACK
    by_cases INSLOT : Task_in_time_slot ts slot_order j.job_task time_slot t = true
    · right
      have INL : j ∈ L := pending_job_in_penging_list concrete_job.job_arrival concrete_job.job_cost arr_seq
        job_arrival_times_are_consistent sched t j ARRJ BACK.1
      have INF : j ∈ L.filter p := List.mem_filter.mpr ⟨INL, INSLOT⟩
      obtain ⟨y, HD⟩ : ∃ y, (L.filter p).head? = some y := by
        cases h : (L.filter p) with
        | nil => rw [h] at INF; simp at INF
        | cons y ys => exact ⟨y, rfl⟩
      have SCHEDy : scheduled_at sched y t = true := by simp [scheduled_at, SCHEDeq, HD]
      have NE : j ≠ y := by
        intro h; subst h; rw [SCHEDy] at BACK; exact Bool.noConfusion BACK.2
      have INFy := List.mem_of_mem_head? HD
      have INLy : y ∈ L := (List.mem_filter.mp INFy).1
      have ARRy := pendinglist_jobs_in_arr_seq concrete_job.job_arrival concrete_job.job_cost arr_seq sched t y INLy
      have SLOTy : p y = true := (List.mem_filter.mp INFy).2
      have SAMEtsk : j.job_task = y.job_task :=
        task_in_time_slot_uniq ts slot_order time_slot slot_order_total slot_order_antisymmetric
          slot_order_transitive j.job_task y.job_task t (FROMTS j ARRJ)
          (by simpa [is_valid_time_slot] using valid_time_slots _ (FROMTS j ARRJ)) (FROMTS y ARRy)
          (by simpa [is_valid_time_slot] using valid_time_slots _ (FROMTS y ARRy)) INSLOT SLOTy
      have IDX := head_filter_findIdx_lt p L y j HD INL INSLOT NE
      have FIFO := respects_FIFO concrete_job.job_arrival concrete_job.job_cost arr_seq job_arrival_times_are_consistent
        sched t SET j y INL INLy IDX
      have SPO := periodic_arrivals_are_sporadic ts y j (fun h => NE h.symm) ARRy ARRJ SAMEtsk.symm FIFO
      have PER : 0 < y.job_task.task_period := by
        have := (VALID _ (FROMTS y ARRy)).2.1
        simpa [task_period_positive] using this
      exact ⟨y, ARRy, by omega', SAMEtsk, SCHEDy⟩
    · left; exact INSLOT

theorem job_cost_le_task_cost :
    ∀ j : concrete_job, arrives_in arr_seq j →
      job_cost_le_task_cost concrete_task.task_cost concrete_job.job_cost concrete_job.job_task j = true := by
  intro j ARR
  exact (periodic_arrivals_valid_job_parameters ts ts_has_valid_parameters j ARR).2.1

/-! ### Validity of the WCRT bounds and schedulability -/

theorem valid_tdma_bounds {Job : Type v} [DecidableEq Job] :
    ∀ tsk, tsk ∈ ts →
      is_valid_tdma_bound concrete_task.task_deadline tsk (WCRT concrete_task.task_cost time_slot ts tsk) := by
  intro tsk IN
  change tsk ∈ ts.val at IN
  simp only [ts, List.mem_cons, List.not_mem_nil, or_false] at IN
  unfold is_valid_tdma_bound
  rcases IN with rfl | rfl | rfl <;> decide

theorem WCRT_le_period {Job : Type v} [DecidableEq Job] :
    ∀ tsk, tsk ∈ ts → WCRT concrete_task.task_cost time_slot ts tsk ≤ concrete_task.task_period tsk := by
  intro tsk IN
  change tsk ∈ ts.val at IN
  simp only [ts, List.mem_cons, List.not_mem_nil, or_false] at IN
  rcases IN with rfl | rfl | rfl <;> decide

theorem ts_is_schedulable_by_tdma {Job : Type v} [DecidableEq Job] :
    ∀ tsk, tsk ∈ ts →
      task_misses_no_deadline concrete_job.job_arrival concrete_job.job_cost concrete_job.job_deadline
        concrete_job.job_task arr_seq sched tsk := by
  intro tsk IN
  have VALID := ts_has_valid_parameters
  exact taskset_schedulable_by_tdma concrete_task.task_cost concrete_task.task_period concrete_task.task_deadline
    concrete_job.job_arrival concrete_job.job_cost concrete_job.job_deadline concrete_job.job_task arr_seq
    job_arrival_times_are_consistent (periodic_arrivals_are_sporadic ts) sched
    (scheduler_jobs_must_arrive_to_execute concrete_job.job_arrival concrete_job.job_cost concrete_job.job_task arr_seq
      ts time_slot slot_order)
    (scheduler_completed_jobs_dont_execute concrete_job.job_arrival concrete_job.job_cost concrete_job.job_task arr_seq
      ts time_slot slot_order)
    time_slot slot_order ts tsk IN (WCRT_le_period (Job := Job) tsk IN) (respects_TDMA_policy (Job := Job))
    (valid_time_slots tsk IN) (periodic_arrivals_valid_job_parameters ts VALID) job_cost_le_task_cost
    (valid_tdma_bounds (Job := Job) tsk IN)

end Prosa.Classic.Implementation.Uni.Basic.TdmaRtaExample.ResponseTimeAnalysisExemple
