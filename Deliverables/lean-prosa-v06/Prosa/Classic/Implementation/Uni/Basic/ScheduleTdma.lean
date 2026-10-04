-- Authoritative source:
-- ProsaBuddy classic Prosa (prosabuddy commit f692cb7479780cf6009493f373a309e13165201c)
-- source: classic/implementation/uni/basic/schedule_tdma.v
-- sha256: see Prosa-Shunqi/classic-prosa/comprehensive-classic/file_order.csv (rank 136)

import Prosa.Classic.Util.All
import Prosa.Classic.Util.FindSeq
import Prosa.Classic.Model.Arrival.Basic.Job
import Prosa.Classic.Model.Arrival.Basic.ArrivalSequence
import Prosa.Classic.Model.Arrival.Basic.Task
import Prosa.Classic.Model.PolicyTdma
import Prosa.Classic.Model.Schedule.Uni.Schedule
import Prosa.Classic.Model.Schedule.Uni.Schedulability
import Prosa.Classic.Model.Priority
import Prosa.Classic.Model.Schedule.Uni.Transformation.Construction

/-!
A concrete uniprocessor TDMA scheduler (Rocq module `ConcreteSchedulerTDMA` of
`classic/implementation/uni/basic/schedule_tdma.v`).

Representation notes:
* `{set Task}` is the accepted `Prosa.Util.Seqset.set Task` (as in `PolicyTDMA`).
* `[seq j <- s | P j]` is `s.filter P`; `ohead s` is `s.head?`; MathComp's `find p s` is `List.findIdx p s`;
  `x == y` is `decide (x = y)`; `uniq s` in proposition position is `s.Nodup`.
* The section-local `Let`s (`is_pending`, `job_in_time_slot`, `empty_schedule`, `sched`) are unfolded.
* Binder lists follow the Rocq contract (the `Lemmas` section lemmas take the section hypothesis
  `H_arrival_times_are_consistent` only where the Rocq proof uses it).
-/

set_option linter.unusedVariables false

namespace Prosa.Classic.Implementation.Uni.Basic.ScheduleTdma.ConcreteSchedulerTDMA

open Prosa.Classic.Model.Time.Time
open Prosa.Classic.Model.Arrival.Basic.ArrivalSequence.ArrivalSequence
open Prosa.Classic.Model.Schedule.Uni.Schedule.UniprocessorSchedule
open Prosa.Classic.Model.PolicyTdma.PolicyTDMA
open Prosa.Classic.Model.Schedule.Uni.Transformation.Construction.ScheduleConstruction
open Prosa.Util.Seqset (set)

universe u v

local macro "omega'" : tactic =>
  `(tactic| ((try dsimp only [Prosa.Classic.Model.Time.Time.time,
    Prosa.Classic.Model.Time.Time.instant, Prosa.Classic.Model.Time.Time.duration] at *) <;>
    omega))

def pending_jobs {Job : Type v} [DecidableEq Job] (job_arrival job_cost : Job → time) (arr_seq : arrival_sequence Job) (sched : schedule Job)
    (t : time) : List Job :=
  (jobs_arrived_up_to arr_seq t).filter (fun j => pending job_arrival job_cost sched j t)

def job_to_schedule {Task : Type u} [DecidableEq Task] {Job : Type v} [DecidableEq Job] (job_arrival job_cost : Job → time) (job_task : Job → Task) (arr_seq : arrival_sequence Job) (ts : set Task)
    (time_slot : TDMA_slot Task) (slot_order : TDMA_slot_order Task) (sched : schedule Job) (t : time) : Option Job :=
  ((pending_jobs job_arrival job_cost arr_seq sched t).filter
    (fun job => Task_in_time_slot ts slot_order (job_task job) time_slot t)).head?

theorem pending_jobs_uniq {Job : Type v} [DecidableEq Job] (job_arrival job_cost : Job → time) (arr_seq : arrival_sequence Job)
    (H_arrival_times_are_consistent : arrival_times_are_consistent job_arrival arr_seq) (sched : schedule Job)
    (t : time) (arr_seq_is_a_set : arrival_sequence_is_a_set arr_seq) :
    (pending_jobs job_arrival job_cost arr_seq sched t).Nodup :=
  List.Nodup.filter _ (arrivals_uniq job_arrival arr_seq H_arrival_times_are_consistent arr_seq_is_a_set 0 (t + 1))

theorem respects_FIFO {Job : Type v} [DecidableEq Job] (job_arrival job_cost : Job → time) (arr_seq : arrival_sequence Job)
    (H_arrival_times_are_consistent : arrival_times_are_consistent job_arrival arr_seq) (sched : schedule Job)
    (t : time) (arr_seq_is_a_set : arrival_sequence_is_a_set arr_seq) :
    ∀ j j', j ∈ pending_jobs job_arrival job_cost arr_seq sched t → j' ∈ pending_jobs job_arrival job_cost arr_seq sched t →
      List.findIdx (fun job => decide (job = j')) (pending_jobs job_arrival job_cost arr_seq sched t) <
        List.findIdx (fun job => decide (job = j)) (pending_jobs job_arrival job_cost arr_seq sched t) →
      job_arrival j' ≤ job_arrival j := by
  intro j j' JIN J'IN LEQ
  have UNIQ := pending_jobs_uniq job_arrival job_cost arr_seq H_arrival_times_are_consistent sched t
    arr_seq_is_a_set
  by_contra GT
  have GT' : job_arrival j < job_arrival j' := by omega'
  have JIN' := JIN
  have J'IN' := J'IN
  unfold pending_jobs at JIN' J'IN'
  rw [List.mem_filter] at JIN' J'IN'
  have ARRj := in_arrivals_implies_arrived_between job_arrival arr_seq H_arrival_times_are_consistent j 0 (t + 1)
    JIN'.1
  have ARRj' := in_arrivals_implies_arrived_between job_arrival arr_seq H_arrival_times_are_consistent j' 0 (t + 1)
    J'IN'.1
  simp only [arrived_between, Bool.and_eq_true, decide_eq_true_eq] at ARRj ARRj'
  have SPLIT := job_arrived_between_cat arr_seq 0 (job_arrival j + 1) (t + 1) (Nat.zero_le _) (by omega')
  set A := (jobs_arrived_between arr_seq 0 (job_arrival j + 1)).filter
    (fun x => pending job_arrival job_cost sched x t) with HA
  set B := (jobs_arrived_between arr_seq (job_arrival j + 1) (t + 1)).filter
    (fun x => pending job_arrival job_cost sched x t) with HB
  have EQ : pending_jobs job_arrival job_cost arr_seq sched t = A ++ B := by
    unfold pending_jobs jobs_arrived_up_to
    rw [SPLIT, List.filter_append]
  have INA : j ∈ A := by
    rw [HA, List.mem_filter]
    refine ⟨?_, JIN'.2⟩
    exact arrived_between_implies_in_arrivals job_arrival arr_seq H_arrival_times_are_consistent j 0
      (job_arrival j + 1) (in_arrivals_implies_arrived arr_seq j 0 (t + 1) JIN'.1)
      (by simp only [arrived_between, Bool.and_eq_true, decide_eq_true_eq]; omega')
  have INB : j' ∈ B := by
    rw [HB, List.mem_filter]
    refine ⟨?_, J'IN'.2⟩
    exact arrived_between_implies_in_arrivals job_arrival arr_seq H_arrival_times_are_consistent j'
      (job_arrival j + 1) (t + 1) (in_arrivals_implies_arrived arr_seq j' 0 (t + 1) J'IN'.1)
      (by simp only [arrived_between, Bool.and_eq_true, decide_eq_true_eq]; omega')
  rw [EQ] at UNIQ LEQ
  have NOTA : j' ∉ A := fun h => List.disjoint_of_nodup_append UNIQ h INB
  have I1 : List.findIdx (fun job => decide (job = j)) A < A.length :=
    List.findIdx_lt_length_of_exists ⟨j, INA, by simp⟩
  have I2 : List.findIdx (fun job => decide (job = j')) A = A.length := by
    rw [List.findIdx_eq_length]
    intro x hx
    have NE : x ≠ j' := fun h => NOTA (h ▸ hx)
    simpa using NE
  rw [List.findIdx_append, List.findIdx_append, I2, if_pos I1] at LEQ
  simp only [Nat.lt_irrefl, if_false] at LEQ
  omega

theorem pending_job_in_penging_list {Job : Type v} [DecidableEq Job] (job_arrival job_cost : Job → time) (arr_seq : arrival_sequence Job)
    (H_arrival_times_are_consistent : arrival_times_are_consistent job_arrival arr_seq) (sched : schedule Job)
    (t : time) :
    ∀ j, arrives_in arr_seq j → pending job_arrival job_cost sched j t = true → j ∈ pending_jobs job_arrival job_cost arr_seq sched t := by
  intro j ARRJ PEN
  unfold pending_jobs
  rw [List.mem_filter]
  refine ⟨?_, PEN⟩
  have ARR := PEN
  simp only [pending, has_arrived, Bool.and_eq_true, decide_eq_true_eq] at ARR
  exact arrived_between_implies_in_arrivals job_arrival arr_seq H_arrival_times_are_consistent j 0 (t + 1) ARRJ
    (by simp only [arrived_between, Bool.and_eq_true, decide_eq_true_eq]; omega')

theorem pendinglist_jobs_in_arr_seq {Job : Type v} [DecidableEq Job] (job_arrival job_cost : Job → time) (arr_seq : arrival_sequence Job)
    (sched : schedule Job) (t : time) :
    ∀ j, j ∈ pending_jobs job_arrival job_cost arr_seq sched t → arrives_in arr_seq j := by
  intro j JIN
  unfold pending_jobs at JIN
  exact in_arrivals_implies_arrived arr_seq j 0 (t + 1) (List.mem_filter.mp JIN).1

def scheduler_tdma {Task : Type u} [DecidableEq Task] {Job : Type v} [DecidableEq Job] (job_arrival job_cost : Job → time) (job_task : Job → Task) (arr_seq : arrival_sequence Job) (ts : set Task)
    (time_slot : TDMA_slot Task) (slot_order : TDMA_slot_order Task) : schedule Job :=
  build_schedule_from_prefixes (job_to_schedule job_arrival job_cost job_task arr_seq ts time_slot slot_order) (fun _ => none)

theorem scheduler_depends_only_on_prefix {Task : Type u} [DecidableEq Task] {Job : Type v} [DecidableEq Job] (job_arrival job_cost : Job → time) (job_task : Job → Task) (arr_seq : arrival_sequence Job) (ts : set Task)
    (time_slot : TDMA_slot Task) (slot_order : TDMA_slot_order Task) :
    ∀ (sched1 sched2 : schedule Job) (t : Nat), (∀ t0, t0 < t → sched1 t0 = sched2 t0) →
      job_to_schedule job_arrival job_cost job_task arr_seq ts time_slot slot_order sched1 t = job_to_schedule job_arrival job_cost job_task arr_seq ts time_slot slot_order sched2 t := by
  intro sched1 sched2 t ALL
  have SERV : ∀ j, service sched1 j t = service sched2 j t := by
    intro j
    unfold service service_during
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mem_Ico] at hi
    simp only [service_at, scheduled_at, ALL i hi.2]
  unfold job_to_schedule pending_jobs
  simp only [pending, completed_by, SERV]

theorem scheduler_uses_construction_function {Task : Type u} [DecidableEq Task] {Job : Type v} [DecidableEq Job] (job_arrival job_cost : Job → time) (job_task : Job → Task) (arr_seq : arrival_sequence Job) (ts : set Task)
    (time_slot : TDMA_slot Task) (slot_order : TDMA_slot_order Task) :
    ∀ t, (scheduler_tdma job_arrival job_cost job_task arr_seq ts time_slot slot_order) t = job_to_schedule job_arrival job_cost job_task arr_seq ts time_slot slot_order (scheduler_tdma job_arrival job_cost job_task arr_seq ts time_slot slot_order) t := by
  intro t
  exact prefix_dependent_schedule_construction _ _ (scheduler_depends_only_on_prefix job_arrival job_cost job_task arr_seq ts time_slot slot_order) t

/-- LEAN_HELPER: a job scheduled by the TDMA scheduler is pending. -/
private theorem scheduled_pending {Task : Type u} [DecidableEq Task] {Job : Type v} [DecidableEq Job] (job_arrival job_cost : Job → time) (job_task : Job → Task) (arr_seq : arrival_sequence Job) (ts : set Task)
    (time_slot : TDMA_slot Task) (slot_order : TDMA_slot_order Task) (j : Job) (t : time) (SCHED : (scheduler_tdma job_arrival job_cost job_task arr_seq ts time_slot slot_order) t = some j) :
    pending job_arrival job_cost (scheduler_tdma job_arrival job_cost job_task arr_seq ts time_slot slot_order) j t = true := by
  rw [scheduler_uses_construction_function] at SCHED
  unfold job_to_schedule at SCHED
  have IN := List.mem_of_head? SCHED
  rw [List.mem_filter] at IN
  unfold pending_jobs at IN
  exact (List.mem_filter.mp IN.1).2

theorem scheduler_jobs_must_arrive_to_execute {Task : Type u} [DecidableEq Task] {Job : Type v} [DecidableEq Job] (job_arrival job_cost : Job → time) (job_task : Job → Task) (arr_seq : arrival_sequence Job) (ts : set Task)
    (time_slot : TDMA_slot Task) (slot_order : TDMA_slot_order Task) :
    jobs_must_arrive_to_execute job_arrival (scheduler_tdma job_arrival job_cost job_task arr_seq ts time_slot slot_order) := by
  intro j t SCHED
  simp only [scheduled_at, decide_eq_true_eq] at SCHED
  have PEND := scheduled_pending job_arrival job_cost job_task arr_seq ts time_slot slot_order j t SCHED
  simp only [pending, Bool.and_eq_true] at PEND
  exact PEND.1

theorem scheduler_completed_jobs_dont_execute {Task : Type u} [DecidableEq Task] {Job : Type v} [DecidableEq Job] (job_arrival job_cost : Job → time) (job_task : Job → Task) (arr_seq : arrival_sequence Job) (ts : set Task)
    (time_slot : TDMA_slot Task) (slot_order : TDMA_slot_order Task) :
    completed_jobs_dont_execute job_cost (scheduler_tdma job_arrival job_cost job_task arr_seq ts time_slot slot_order) := by
  intro j t
  induction t with
  | zero => simp [service, service_during]
  | succ t IHt =>
    have STEP : service (scheduler_tdma job_arrival job_cost job_task arr_seq ts time_slot slot_order) j (t + 1) = service (scheduler_tdma job_arrival job_cost job_task arr_seq ts time_slot slot_order) j t + service_at (scheduler_tdma job_arrival job_cost job_task arr_seq ts time_slot slot_order) j t := by
      unfold service service_during
      rw [Finset.sum_Ico_succ_top (Nat.zero_le _)]
    rw [STEP]
    rcases Nat.lt_or_ge (service (scheduler_tdma job_arrival job_cost job_task arr_seq ts time_slot slot_order) j t) (job_cost j) with LT | GE
    · have : service_at (scheduler_tdma job_arrival job_cost job_task arr_seq ts time_slot slot_order) j t ≤ 1 := by
        unfold service_at; cases scheduled_at _ j t <;> simp
      omega'
    · have NS : scheduled_at (scheduler_tdma job_arrival job_cost job_task arr_seq ts time_slot slot_order) j t = false := by
        cases hs : scheduled_at (scheduler_tdma job_arrival job_cost job_task arr_seq ts time_slot slot_order) j t
        · rfl
        · simp only [scheduled_at, decide_eq_true_eq] at hs
          have PEND := scheduled_pending job_arrival job_cost job_task arr_seq ts time_slot slot_order j t hs
          simp only [pending, completed_by, Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at PEND
          exact absurd GE PEND.2
      simp only [service_at, NS, Bool.toNat_false, Nat.add_zero]
      exact IHt

end Prosa.Classic.Implementation.Uni.Basic.ScheduleTdma.ConcreteSchedulerTDMA
