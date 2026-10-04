-- Authoritative source:
-- ProsaBuddy classic Prosa (prosabuddy commit f692cb7479780cf6009493f373a309e13165201c)
-- source: classic/model/schedule/uni/limited/abstract_RTA/abstract_seq_rta.v
-- sha256: see Prosa-Shunqi/classic-prosa/comprehensive-classic/file_order.csv (rank 140)

import Prosa.Classic.Util.All
import Prosa.Classic.Model.Arrival.Basic.Job
import Prosa.Classic.Model.Arrival.Basic.TaskArrival
import Prosa.Classic.Model.Schedule.Uni.Service
import Prosa.Classic.Model.Schedule.Uni.Workload
import Prosa.Classic.Model.Schedule.Uni.Schedule
import Prosa.Classic.Model.Schedule.Uni.ResponseTime
import Prosa.Classic.Model.Schedule.Uni.ScheduleOfTask
import Prosa.Classic.Model.Schedule.Uni.Limited.Rbf
import Prosa.Classic.Model.Schedule.Uni.Limited.Schedule
import Prosa.Classic.Model.Arrival.Curves.Bounds
import Prosa.Classic.Analysis.Uni.ArrivalCurves.WorkloadBound
import Prosa.Classic.Model.Schedule.Uni.Limited.AbstractRTA.Definitions
import Prosa.Classic.Model.Schedule.Uni.Limited.AbstractRTA.SufficientConditionForLockInService
import Prosa.Classic.Model.Schedule.Uni.Limited.AbstractRTA.ReductionOfSearchSpace
import Prosa.Classic.Model.Schedule.Uni.Limited.AbstractRTA.AbstractRta

/-!
Abstract response-time analysis with sequential jobs (Rocq module `AbstractSeqRTA` of
`classic/model/schedule/uni/limited/abstract_RTA/abstract_seq_rta.v`).

Representation notes:
* `~~ b` is `(!b) = true` in proposition position; `has p s` is `s.any p`; a Boolean summed as a number is
  `Bool.toNat`; `\sum_(t1 <= t < t2) F t` is `∑ t ∈ Finset.Ico t1 t2, F t`; `ε` is the accepted `Prosa.Util.Epsilon`
  notation (`1`).
* The section-local `Let`s (`job_pending_at`, `job_completed_by`, `arrivals_between`, `task_scheduled_at`,
  `response_time_bounded_by`, `task_rbf`, `work_conserving`, `busy_intervals_are_bounded_by`,
  `job_interference_is_bounded_by`, `busy_interval`, `task_workload_between`, `arrivals_of_task_before`,
  `task_service_between`, `cumul_interference`, `cumul_workload`, `cumul_task_interference`, `A`,
  `is_in_search_space`, `is_in_search_space_seq`) are unfolded. The `Let total_interference_bound tsk A Δ :=
  task_rbf (A + ε) - task_cost tsk + task_interference_bound_function tsk A Δ` (where `task_rbf` is fixed to the
  section task) is unfolded to the corresponding `fun`.
* Binder lists follow the Rocq contract.
* The proof of `bound_for_cumulative_job_interference_actual` follows the source's pointwise argument; the proof of
  `task_rbf_excl_tsk_bounds_task_workload_excl_j` bounds the workload of the other jobs of the task in
  `[t1, t1 + A + ε)` directly by `task_cost tsk * (number of arrivals - 1)` instead of splitting the interval at
  `t1 + A` as the source does (same statement).
-/

set_option linter.unusedVariables false

namespace Prosa.Classic.Model.Schedule.Uni.Limited.AbstractRTA.AbstractSeqRta.AbstractSeqRTA

open Prosa.Classic.Model.Time.Time
open Prosa.Classic.Model.Arrival.Basic.ArrivalSequence.ArrivalSequence
open Prosa.Classic.Model.Arrival.Basic.Job.Job
open Prosa.Classic.Model.Arrival.Basic.TaskArrival.TaskArrival
open Prosa.Classic.Model.Schedule.Uni.Schedule.UniprocessorSchedule
open Prosa.Classic.Model.Schedule.Uni.ResponseTime.ResponseTime
open Prosa.Classic.Model.Schedule.Uni.ScheduleOfTask.ScheduleOfTask
open Prosa.Classic.Model.Schedule.Uni.Workload.Workload
open Prosa.Classic.Model.Schedule.Uni.Service.Service
open Prosa.Classic.Model.Schedule.Uni.Limited.Schedule
open Prosa.Classic.Model.Arrival.Curves.Bounds.ArrivalCurves
open Prosa.Classic.Analysis.Uni.ArrivalCurves.WorkloadBound.MaxArrivalsWorkloadBound (task_request_bound_function)
open Prosa.Classic.Model.Schedule.Uni.Limited.AbstractRTA.Definitions.AbstractRTADefinitions
open Prosa.Classic.Model.Schedule.Uni.Limited.AbstractRTA.ReductionOfSearchSpace.AbstractRTAReduction
  (is_in_search_space)
open Prosa.Classic.Model.Schedule.Uni.Limited.AbstractRTA.AbstractRta.AbstractRTA (uniprocessor_response_time_bound)
open Prosa.Util.Sum (sumFiltered sum_majorant_constant leq_sum_seq)

universe u v

local macro "omega'" : tactic =>
  `(tactic| ((try dsimp only [Prosa.Classic.Model.Time.Time.time,
    Prosa.Classic.Model.Time.Time.instant, Prosa.Classic.Model.Time.Time.duration] at *) <;>
    omega))

/-! ### Definitions -/

def interference_and_workload_consistent_with_sequential_jobs {Task : Type u} [DecidableEq Task] {Job : Type v} [DecidableEq Job] (job_arrival job_cost : Job → time) (job_task : Job → Task) (arr_seq : arrival_sequence Job) (sched : schedule Job) (tsk : Task)
    (interference : Job → time → Bool) (interfering_workload : Job → time → time) : Prop :=
  ∀ j t1 t2,
    arrives_in arr_seq j →
    job_task j = tsk →
    0 < job_cost j →
    busy_interval job_arrival job_cost sched interference interfering_workload j t1 t2 →
    task_workload_between job_cost job_task arr_seq tsk 0 t1 = task_service_between job_task arr_seq sched tsk 0 t1

def task_interference_received_before {Task : Type u} [DecidableEq Task] {Job : Type v} [DecidableEq Job] (job_task : Job → Task) (arr_seq : arrival_sequence Job)
    (sched : schedule Job) (interference : Job → time → Bool) (tsk : Task) (upper_bound : time) (t : time) : Bool :=
  !task_scheduled_at job_task sched tsk t &&
    (arrivals_of_task_before job_task arr_seq tsk upper_bound).any (fun j => interference j t)

def cumul_task_interference {Task : Type u} [DecidableEq Task] {Job : Type v} [DecidableEq Job] (job_task : Job → Task) (arr_seq : arrival_sequence Job) (sched : schedule Job)
    (interference : Job → time → Bool) (tsk : Task) (upper_bound : time) (t1 t2 : Nat) : Nat :=
  ∑ t ∈ Finset.Ico t1 t2,
    (task_interference_received_before job_task arr_seq sched interference tsk upper_bound t).toNat

def task_interference_is_bounded_by {Task : Type u} [DecidableEq Task] {Job : Type v} [DecidableEq Job] (job_arrival job_cost : Job → time) (job_task : Job → Task) (arr_seq : arrival_sequence Job) (sched : schedule Job) (tsk : Task) (interference : Job → time → Bool) (interfering_workload : Job → time → time)
    (task_interference_bound_function : Task → time → time → time) : Prop :=
  ∀ j R t1 t2,
    arrives_in arr_seq j →
    job_task j = tsk →
    t1 + R < t2 →
    (!completed_by job_cost sched j (t1 + R)) = true →
    busy_interval job_arrival job_cost sched interference interfering_workload j t1 t2 →
    let offset := job_arrival j - t1
    cumul_task_interference job_task arr_seq sched interference tsk t2 t1 (t1 + R) ≤ task_interference_bound_function tsk offset R

/-! ### Proof-local facts -/

/-- LEAN_HELPER: the job of a busy interval arrives inside it. -/
private theorem busy_bounds {Job : Type v} [DecidableEq Job] (job_arrival job_cost : Job → time)
    (sched : schedule Job) (interference : Job → time → Bool) (interfering_workload : Job → time → time) (j : Job) (t1 t2 : time) (H : busy_interval job_arrival job_cost sched interference interfering_workload j t1 t2) :
    t1 ≤ job_arrival j ∧ job_arrival j < t2 := by
  obtain ⟨⟨IN, _, _⟩, _⟩ := H
  simp only [Bool.and_eq_true] at IN
  exact ⟨of_decide_eq_true IN.1, of_decide_eq_true IN.2⟩

/-- LEAN_HELPER: splitting off one retained element of a filtered sum. -/
private theorem sumFiltered_erase {I : Type v} [DecidableEq I] (l : List I) (P : I → Bool) (F : I → Nat) (x : I)
    (IN : x ∈ l) (Px : P x = true) : sumFiltered l P F = F x + sumFiltered (l.erase x) P F := by
  induction l with
  | nil => simp at IN
  | cons a l ih =>
    by_cases EQ : a = x
    · subst EQ
      simp [sumFiltered, List.erase_cons_head, Px]
    · have IN' : x ∈ l := by
        rcases List.mem_cons.mp IN with h | h
        · exact absurd h.symm EQ
        · exact h
      have hb : (a == x) = false := by simpa using EQ
      rw [List.erase_cons, hb]
      simp only [Bool.false_eq_true, ↓reduceIte]
      have := ih IN'
      unfold sumFiltered at this ⊢
      cases hP : P a <;> simp [List.filter_cons, hP, this] <;> omega'

/-- LEAN_HELPER: removing one retained element decreases the filtered length by one. -/
private theorem filter_length_erase {I : Type v} [DecidableEq I] (l : List I) (P : I → Bool) (x : I)
    (IN : x ∈ l) (Px : P x = true) : ((l.erase x).filter P).length + 1 = (l.filter P).length := by
  induction l with
  | nil => simp at IN
  | cons a l ih =>
    by_cases EQ : a = x
    · subst EQ
      simp [List.erase_cons_head, List.filter_cons, Px]
    · have IN' : x ∈ l := by
        rcases List.mem_cons.mp IN with h | h
        · exact absurd h.symm EQ
        · exact h
      have hb : (a == x) = false := by simpa using EQ
      rw [List.erase_cons, hb]
      simp only [Bool.false_eq_true, ↓reduceIte]
      have := ih IN'
      cases hP : P a <;> simp [List.filter_cons, hP] <;> omega'

/-- LEAN_HELPER: exchanging a filtered sum and a sum over time. -/
private theorem sumFiltered_exchange {I : Type v} (l : List I) (P : I → Bool) (f : I → Nat → Nat) (t1 t2 : Nat) :
    sumFiltered l P (fun i => ∑ t ∈ Finset.Ico t1 t2, f i t) =
      ∑ t ∈ Finset.Ico t1 t2, sumFiltered l P (fun i => f i t) := by
  unfold sumFiltered
  induction (l.filter P) with
  | nil => simp
  | cons a l ih => simp only [List.map_cons, List.sum_cons, ih, Finset.sum_add_distrib]

/-! ### Completion of jobs from the same task -/

theorem completed_before_beginning_of_busy_interval {Task : Type u} [DecidableEq Task] {Job : Type v} [DecidableEq Job] (job_arrival job_cost : Job → time) (job_task : Job → Task) (arr_seq : arrival_sequence Job)
    (H_arrival_times_are_consistent : arrival_times_are_consistent job_arrival arr_seq) (sched : schedule Job)
    (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute job_arrival sched)
    (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched) (tsk : Task) (interference : Job → time → Bool) (interfering_workload : Job → time → time)
    (H_interference_and_workload_consistent_with_sequential_jobs :
      interference_and_workload_consistent_with_sequential_jobs job_arrival job_cost job_task arr_seq sched tsk
        interference interfering_workload)
    (j1 j2 : Job) (H_j1_arrives : arrives_in arr_seq j1) (H_j2_arrives : arrives_in arr_seq j2)
    (H_j1_from_tsk : job_task j1 = tsk) (H_j2_from_tsk : job_task j2 = tsk)
    (H_j1_cost_positive : job_cost_positive job_cost j1 = true) (t1 t2 : time)
    (H_busy_interval : busy_interval job_arrival job_cost sched interference interfering_workload j1 t1 t2) :
    job_arrival j2 < t1 → completed_by job_cost sched j2 t1 = true := by
  intro JA
  rcases Nat.eq_zero_or_pos (job_cost j2) with ZERO | POS
  · simp [completed_by, ZERO]
  have SWEQ := H_interference_and_workload_consistent_with_sequential_jobs j1 t1 t2 H_j1_arrives H_j1_from_tsk
    (of_decide_eq_true H_j1_cost_positive) H_busy_interval
  unfold task_workload_between task_workload task_service_between task_service_of_jobs_received_in at SWEQ
  have ALL := (all_jobs_have_completed_equiv_workload_eq_service job_arrival job_cost arr_seq
    H_arrival_times_are_consistent sched H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute
    (fun j => decide (job_task j = tsk)) 0 t1 t1).mpr SWEQ
  apply ALL j2
  · exact arrived_between_implies_in_arrivals job_arrival arr_seq H_arrival_times_are_consistent j2 0 t1
      H_j2_arrives (by simp only [arrived_between, Bool.and_eq_true, decide_eq_true_eq]; omega')
  · simpa using H_j2_from_tsk

theorem arrives_after_beginning_of_busy_interval {Task : Type u} [DecidableEq Task] {Job : Type v} [DecidableEq Job] (job_arrival job_cost : Job → time) (job_task : Job → Task) (arr_seq : arrival_sequence Job)
    (H_arrival_times_are_consistent : arrival_times_are_consistent job_arrival arr_seq) (sched : schedule Job)
    (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute job_arrival sched)
    (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched) (tsk : Task) (interference : Job → time → Bool) (interfering_workload : Job → time → time)
    (H_interference_and_workload_consistent_with_sequential_jobs :
      interference_and_workload_consistent_with_sequential_jobs job_arrival job_cost job_task arr_seq sched tsk
        interference interfering_workload)
    (j1 j2 : Job) (H_j1_arrives : arrives_in arr_seq j1) (H_j2_arrives : arrives_in arr_seq j2)
    (H_j1_from_tsk : job_task j1 = tsk) (H_j2_from_tsk : job_task j2 = tsk)
    (H_j1_cost_positive : job_cost_positive job_cost j1 = true) (t1 t2 : time)
    (H_busy_interval : busy_interval job_arrival job_cost sched interference interfering_workload j1 t1 t2) :
    ∀ t : Nat, t1 ≤ t → pending job_arrival job_cost sched j2 t = true →
      arrived_between job_arrival j2 t1 (t + 1) = true := by
  intro t GE PEND
  simp only [pending, has_arrived, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at PEND
  simp only [arrived_between, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨?_, by omega'⟩
  by_contra LT
  have C := completed_before_beginning_of_busy_interval job_arrival job_cost job_task arr_seq
    H_arrival_times_are_consistent sched H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute tsk
    interference interfering_workload H_interference_and_workload_consistent_with_sequential_jobs j1 j2 H_j1_arrives
    H_j2_arrives H_j1_from_tsk H_j2_from_tsk H_j1_cost_positive t1 t2 H_busy_interval (by omega')
  have := completion_monotonic job_cost sched j2 t1 t GE C
  rw [this] at PEND; exact absurd PEND.2 (by simp)

/-! ### Bound on the cumulative job interference -/

theorem bound_for_cumulative_job_interference_actual {Task : Type u} [DecidableEq Task] {Job : Type v} [DecidableEq Job] (job_arrival job_cost : Job → time) (job_task : Job → Task) (arr_seq : arrival_sequence Job)
    (H_arrival_times_are_consistent : arrival_times_are_consistent job_arrival arr_seq) (sched : schedule Job)
    (H_jobs_come_from_arrival_sequence : jobs_come_from_arrival_sequence sched arr_seq)
    (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute job_arrival sched)
    (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched) (tsk : Task) (interference : Job → time → Bool) (interfering_workload : Job → time → time)
    (H_work_conserving : work_conserving job_arrival job_cost job_task arr_seq sched tsk interference interfering_workload)
    (H_sequential_jobs : sequential_jobs job_arrival job_cost sched job_task)
    (H_interference_and_workload_consistent_with_sequential_jobs :
      interference_and_workload_consistent_with_sequential_jobs job_arrival job_cost job_task arr_seq sched tsk
        interference interfering_workload)
    (j : Job) (H_j_arrives : arrives_in arr_seq j) (H_job_of_tsk : job_task j = tsk)
    (H_job_cost_positive : job_cost_positive job_cost j = true) (t1 t2 : time)
    (H_busy_interval : busy_interval job_arrival job_cost sched interference interfering_workload j t1 t2)
    (x : time) (H_inside_busy_interval : t1 + x < t2)
    (H_job_j_is_not_completed : (!completed_by job_cost sched j (t1 + x)) = true) :
    cumul_interference interference j t1 (t1 + x) ≤
      (task_workload_between job_cost job_task arr_seq tsk t1 (t1 + (job_arrival j - t1) + ε) - job_cost j) + cumul_task_interference job_task arr_seq sched interference tsk t2 t1 (t1 + x) := by
  obtain ⟨GEt1, LTt2⟩ := busy_bounds job_arrival job_cost sched interference interfering_workload j t1 t2
    H_busy_interval
  set J := jobs_arrived_between arr_seq t1 (t1 + (job_arrival j - t1) + ε) with HJ
  set P : Job → Bool := fun i => decide (job_task i = tsk) with HP
  have INJ : ∀ i, arrives_in arr_seq i → t1 ≤ job_arrival i → job_arrival i ≤ job_arrival j → i ∈ J := by
    intro i ARRi GE LE
    exact arrived_between_implies_in_arrivals job_arrival arr_seq H_arrival_times_are_consistent i t1 _ ARRi
      (by simp only [arrived_between, Bool.and_eq_true, decide_eq_true_eq]; omega')
  have jJ : j ∈ J := INJ j H_j_arrives GEt1 (Nat.le_refl _)
  have Pj : P j = true := by simp [HP, H_job_of_tsk]
  have NOTCOMP : ¬ job_cost j ≤ service sched j (t1 + x) := by
    simpa [completed_by] using H_job_j_is_not_completed
  -- `j` is among the jobs of the task arrived before `t2`
  have jTB : j ∈ arrivals_of_task_before job_task arr_seq tsk t2 := by
    unfold arrivals_of_task_before arrivals_of_task_between
    rw [List.mem_filter]
    refine ⟨arrived_between_implies_in_arrivals job_arrival arr_seq H_arrival_times_are_consistent j 0 t2
      H_j_arrives (by simp only [arrived_between, Bool.and_eq_true, decide_eq_true_eq]; omega'), ?_⟩
    simp [is_job_of_task, H_job_of_tsk]
  -- the pointwise inequality
  have POINT : ∀ t ∈ Finset.Ico t1 (t1 + x),
      (interference j t).toNat + service_at sched j t ≤
        sumFiltered J P (fun i => service_at sched i t) +
          (task_interference_received_before job_task arr_seq sched interference tsk t2 t).toNat := by
    intro t ht
    rw [Finset.mem_Ico] at ht
    have TI_of : task_scheduled_at job_task sched tsk t = false →
        (interference j t).toNat ≤
          (task_interference_received_before job_task arr_seq sched interference tsk t2 t).toNat := by
      intro NS
      cases hI : interference j t
      · simp
      · have : task_interference_received_before job_task arr_seq sched interference tsk t2 t = true := by
          simp only [task_interference_received_before, NS, Bool.not_false, Bool.true_and, List.any_eq_true]
          exact ⟨j, jTB, hI⟩
        rw [this]
    cases SCHEDt : sched t with
    | none =>
      have SA : service_at sched j t = 0 := by simp [service_at, scheduled_at, SCHEDt]
      have NS : task_scheduled_at job_task sched tsk t = false := by simp [task_scheduled_at, SCHEDt]
      have := TI_of NS
      omega'
    | some s =>
      by_cases TSK : job_task s = tsk
      · have NS : task_interference_received_before job_task arr_seq sched interference tsk t2 t = false := by
          simp [task_interference_received_before, task_scheduled_at, SCHEDt, TSK]
        rw [NS]
        by_cases EQ : s = j
        · subst EQ
          have SCHj : scheduled_at sched s t = true := by simp [scheduled_at, SCHEDt]
          have W := (H_work_conserving s t1 t2 t H_j_arrives H_job_of_tsk (of_decide_eq_true H_job_cost_positive)
            H_busy_interval (by simp only [Bool.and_eq_true, decide_eq_true_eq]; omega')).mpr SCHj
          have IF : interference s t = false := by simpa using W
          have E := sumFiltered_erase J P (fun i => service_at sched i t) s jJ Pj
          simp only [service_at, SCHj, IF, Bool.toNat_false, Bool.toNat_true] at E ⊢
          omega'
        · have SAj : service_at sched j t = 0 := by
            simp only [service_at, scheduled_at, SCHEDt, Option.some.injEq]
            simp [EQ]
          have SCHs : scheduled_at sched s t = true := by simp [scheduled_at, SCHEDt]
          have ARRs := H_jobs_come_from_arrival_sequence s t SCHs
          have PENDs := scheduled_implies_pending job_arrival job_cost sched H_jobs_must_arrive_to_execute
            H_completed_jobs_dont_execute s t SCHs
          have AFTER := arrives_after_beginning_of_busy_interval job_arrival job_cost job_task arr_seq
            H_arrival_times_are_consistent sched H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute tsk
            interference interfering_workload H_interference_and_workload_consistent_with_sequential_jobs j s
            H_j_arrives ARRs H_job_of_tsk TSK H_job_cost_positive t1 t2 H_busy_interval t ht.1 PENDs
          simp only [arrived_between, Bool.and_eq_true, decide_eq_true_eq] at AFTER
          have LEj : job_arrival s ≤ job_arrival j := by
            by_contra GT
            have C := H_sequential_jobs j s t (by simp [TSK, H_job_of_tsk]) (by omega') SCHs
            have C' := completion_monotonic job_cost sched j t (t1 + x) (by omega') C
            simp only [completed_by, decide_eq_true_eq] at C'
            exact NOTCOMP C'
          have sJ := INJ s ARRs AFTER.1 LEj
          have Ps : P s = true := by simp [HP, TSK]
          have E := sumFiltered_erase J P (fun i => service_at sched i t) s sJ Ps
          have SAs : service_at sched s t = 1 := by simp [service_at, SCHs]
          have : (interference j t).toNat ≤ 1 := by cases interference j t <;> simp
          rw [SAj]
          omega'
      · have SAj : service_at sched j t = 0 := by
          simp only [service_at, scheduled_at, SCHEDt, Option.some.injEq]
          have : s ≠ j := fun h => TSK (h ▸ H_job_of_tsk)
          simp [this]
        have NS : task_scheduled_at job_task sched tsk t = false := by simp [task_scheduled_at, SCHEDt, TSK]
        have := TI_of NS
        omega'
  have SUM := Finset.sum_le_sum POINT
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib] at SUM
  -- identify the sums
  have S_EQ : ∑ t ∈ Finset.Ico t1 (t1 + x), sumFiltered J P (fun i => service_at sched i t) =
      service_of_jobs sched J P t1 (t1 + x) := by
    unfold service_of_jobs service_during
    rw [sumFiltered_exchange]
  rw [S_EQ] at SUM
  have ES := sumFiltered_erase J P (fun i => service_during sched i t1 (t1 + x)) j jJ Pj
  have EW := sumFiltered_erase J P job_cost j jJ Pj
  have REST := service_of_jobs_le_workload job_cost sched (J.erase j) P H_completed_jobs_dont_execute t1 (t1 + x)
  unfold service_of_jobs at SUM REST
  unfold workload_of_jobs at REST
  have SD : ∑ t ∈ Finset.Ico t1 (t1 + x), service_at sched j t = service_during sched j t1 (t1 + x) := rfl
  rw [SD] at SUM
  have W_EQ : task_workload_between job_cost job_task arr_seq tsk t1 (t1 + (job_arrival j - t1) + ε) =
      sumFiltered J P job_cost := rfl
  have CI_EQ : cumul_interference interference j t1 (t1 + x) =
      ∑ t ∈ Finset.Ico t1 (t1 + x), (interference j t).toNat := rfl
  have CTI_EQ : cumul_task_interference job_task arr_seq sched interference tsk t2 t1 (t1 + x) =
      ∑ t ∈ Finset.Ico t1 (t1 + x),
        (task_interference_received_before job_task arr_seq sched interference tsk t2 t).toNat := rfl
  rw [W_EQ, CI_EQ, CTI_EQ]
  omega'

theorem task_rbf_excl_tsk_bounds_task_workload_excl_j {Task : Type u} [DecidableEq Task] (task_cost : Task → time)
    {Job : Type v} [DecidableEq Job] (job_arrival job_cost : Job → time) (job_task : Job → Task) (arr_seq : arrival_sequence Job)
    (H_arrival_times_are_consistent : arrival_times_are_consistent job_arrival arr_seq) (sched : schedule Job)
    (H_job_cost_le_task_cost : cost_of_jobs_from_arrival_sequence_le_task_cost task_cost job_cost job_task arr_seq)
    (ts : List Task) (max_arrivals : Task → time → Nat)
    (H_family_of_proper_arrival_curves : family_of_proper_arrival_curves job_task arr_seq max_arrivals ts) (tsk : Task)
    (H_tsk_in_ts : tsk ∈ ts) (interference : Job → time → Bool) (interfering_workload : Job → time → time)
    (j : Job) (H_j_arrives : arrives_in arr_seq j) (H_job_of_tsk : job_task j = tsk)
    (H_job_cost_positive : job_cost_positive job_cost j = true) (t1 t2 : time)
    (H_busy_interval : busy_interval job_arrival job_cost sched interference interfering_workload j t1 t2) :
    task_workload_between job_cost job_task arr_seq tsk t1 (t1 + (job_arrival j - t1) + ε) - job_cost j ≤ task_request_bound_function task_cost max_arrivals tsk ((job_arrival j - t1) + ε) - task_cost tsk := by
  obtain ⟨GEt1, LTt2⟩ := busy_bounds job_arrival job_cost sched interference interfering_workload j t1 t2
    H_busy_interval
  set J := jobs_arrived_between arr_seq t1 (t1 + (job_arrival j - t1) + ε) with HJ
  set P : Job → Bool := fun i => decide (job_task i = tsk) with HP
  have jJ : j ∈ J := arrived_between_implies_in_arrivals job_arrival arr_seq H_arrival_times_are_consistent j t1 _
    H_j_arrives (by simp only [arrived_between, Bool.and_eq_true, decide_eq_true_eq]; omega')
  have Pj : P j = true := by simp [HP, H_job_of_tsk]
  have EW := sumFiltered_erase J P job_cost j jJ Pj
  have LEN := filter_length_erase J P j jJ Pj
  have MAJ := sum_majorant_constant (J.erase j) P job_cost (task_cost tsk) (by
    intro i INi Pi
    have INi' : i ∈ J := List.mem_of_mem_erase INi
    have ARRi := in_arrivals_implies_arrived arr_seq i _ _ INi'
    have := of_decide_eq_true (H_job_cost_le_task_cost i ARRi)
    simp only [HP, decide_eq_true_eq] at Pi
    rw [Pi] at this; exact this)
  have ARRB := (H_family_of_proper_arrival_curves tsk H_tsk_in_ts).1 t1 (t1 + (job_arrival j - t1) + ε) (by omega')
  rw [show t1 + (job_arrival j - t1) + ε - t1 = job_arrival j - t1 + ε by omega'] at ARRB
  have NUM : num_arrivals_of_task job_task arr_seq tsk t1 (t1 + (job_arrival j - t1) + ε) = (J.filter P).length := by
    unfold num_arrivals_of_task arrivals_of_task_between
    rfl
  rw [NUM] at ARRB
  have W_EQ : task_workload_between job_cost job_task arr_seq tsk t1 (t1 + (job_arrival j - t1) + ε) =
      sumFiltered J P job_cost := rfl
  rw [W_EQ]
  unfold task_request_bound_function
  set N := (J.filter P).length with HN
  set M := max_arrivals tsk (job_arrival j - t1 + ε) with HM
  have H3 : task_cost tsk * N ≤ task_cost tsk * M := Nat.mul_le_mul_left _ ARRB
  have H2 : task_cost tsk * ((J.erase j).filter P).length + task_cost tsk = task_cost tsk * N := by
    rw [← LEN, Nat.mul_succ]
  omega'

theorem bound_for_cumulative_job_interference {Task : Type u} [DecidableEq Task] (task_cost : Task → time)
    {Job : Type v} [DecidableEq Job] (job_arrival job_cost : Job → time) (job_task : Job → Task) (arr_seq : arrival_sequence Job)
    (H_arrival_times_are_consistent : arrival_times_are_consistent job_arrival arr_seq) (sched : schedule Job)
    (H_jobs_come_from_arrival_sequence : jobs_come_from_arrival_sequence sched arr_seq)
    (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute job_arrival sched)
    (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched)
    (H_job_cost_le_task_cost : cost_of_jobs_from_arrival_sequence_le_task_cost task_cost job_cost job_task arr_seq)
    (ts : List Task) (max_arrivals : Task → time → Nat)
    (H_family_of_proper_arrival_curves : family_of_proper_arrival_curves job_task arr_seq max_arrivals ts) (tsk : Task)
    (H_tsk_in_ts : tsk ∈ ts) (interference : Job → time → Bool) (interfering_workload : Job → time → time)
    (H_work_conserving : work_conserving job_arrival job_cost job_task arr_seq sched tsk interference interfering_workload)
    (H_sequential_jobs : sequential_jobs job_arrival job_cost sched job_task)
    (H_interference_and_workload_consistent_with_sequential_jobs :
      interference_and_workload_consistent_with_sequential_jobs job_arrival job_cost job_task arr_seq sched tsk
        interference interfering_workload)
    (j : Job) (H_j_arrives : arrives_in arr_seq j) (H_job_of_tsk : job_task j = tsk)
    (H_job_cost_positive : job_cost_positive job_cost j = true) (t1 t2 : time)
    (H_busy_interval : busy_interval job_arrival job_cost sched interference interfering_workload j t1 t2)
    (x : time) (H_inside_busy_interval : t1 + x < t2)
    (H_job_j_is_not_completed : (!completed_by job_cost sched j (t1 + x)) = true) :
    cumul_interference interference j t1 (t1 + x) ≤
      (task_request_bound_function task_cost max_arrivals tsk ((job_arrival j - t1) + ε) - task_cost tsk) + cumul_task_interference job_task arr_seq sched interference tsk t2 t1 (t1 + x) := by
  have A1 := bound_for_cumulative_job_interference_actual job_arrival job_cost job_task arr_seq
    H_arrival_times_are_consistent sched H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute
    H_completed_jobs_dont_execute tsk interference interfering_workload H_work_conserving H_sequential_jobs
    H_interference_and_workload_consistent_with_sequential_jobs j H_j_arrives H_job_of_tsk H_job_cost_positive t1 t2
    H_busy_interval x H_inside_busy_interval H_job_j_is_not_completed
  have A2 := task_rbf_excl_tsk_bounds_task_workload_excl_j task_cost job_arrival job_cost job_task arr_seq
    H_arrival_times_are_consistent sched H_job_cost_le_task_cost ts max_arrivals H_family_of_proper_arrival_curves
    tsk H_tsk_in_ts interference interfering_workload j H_j_arrives H_job_of_tsk H_job_cost_positive t1 t2
    H_busy_interval
  omega'

/-! ### The response-time bound -/

theorem max_in_seq_hypothesis_implies_max_in_nonseq_hypothesis {Task : Type u} [DecidableEq Task]
    (task_cost : Task → time) {Job : Type v} [DecidableEq Job] (job_arrival job_cost : Job → time) (job_task : Job → Task) (arr_seq : arrival_sequence Job)
    (H_arrival_times_are_consistent : arrival_times_are_consistent job_arrival arr_seq) (sched : schedule Job)
    (ts : List Task) (max_arrivals : Task → time → Nat)
    (H_family_of_proper_arrival_curves : family_of_proper_arrival_curves job_task arr_seq max_arrivals ts) (tsk : Task)
    (H_tsk_in_ts : tsk ∈ ts)
    (job_lock_in_service : Job → time) (task_lock_in_service : Task → time)
    (H_proper_job_lock_in_service : proper_job_lock_in_service job_cost arr_seq sched job_lock_in_service)
    (H_proper_task_lock_in_service :
      proper_task_lock_in_service task_cost job_task arr_seq job_lock_in_service task_lock_in_service tsk)
    (L : time) (task_interference_bound_function : Task → time → time → time) (R : Nat)
    (H_R_is_maximum_seq : ∀ A, is_in_search_space tsk L (fun tsk0 A Δ => task_request_bound_function task_cost max_arrivals tsk (A + ε) - task_cost tsk0 + task_interference_bound_function tsk0 A Δ) A →
      ∃ F, A + F = (task_request_bound_function task_cost max_arrivals tsk (A + ε) - (task_cost tsk - task_lock_in_service tsk)) +
          task_interference_bound_function tsk A (A + F) ∧
        F + (task_cost tsk - task_lock_in_service tsk) ≤ R)
    (j : Job) (H_j_arrives : arrives_in arr_seq j) (H_job_of_tsk : job_task j = tsk) :
    ∀ A : Nat, is_in_search_space tsk L (fun tsk0 A Δ => task_request_bound_function task_cost max_arrivals tsk (A + ε) - task_cost tsk0 + task_interference_bound_function tsk0 A Δ) A →
      ∃ F, A + F = task_lock_in_service tsk +
          (task_request_bound_function task_cost max_arrivals tsk (A + ε) - task_cost tsk + task_interference_bound_function tsk A (A + F)) ∧
        F + (task_cost tsk - task_lock_in_service tsk) ≤ R := by
  intro A INSP
  obtain ⟨F, FIX, LE⟩ := H_R_is_maximum_seq A INSP
  refine ⟨F, ?_, LE⟩
  have PRT1 : task_lock_in_service tsk ≤ task_cost tsk := H_proper_task_lock_in_service.1
  have PROPER := H_family_of_proper_arrival_curves tsk H_tsk_in_ts
  have R1 := Prosa.Classic.Model.Schedule.Uni.Limited.Rbf.RBF.task_rbf_1_ge_task_cost task_cost job_arrival job_task
    arr_seq H_arrival_times_are_consistent tsk max_arrivals PROPER j H_j_arrives H_job_of_tsk
  have MONO := Prosa.Classic.Model.Schedule.Uni.Limited.Rbf.RBF.task_rbf_monotone task_cost job_task arr_seq tsk
    max_arrivals PROPER 1 (A + ε) (by simp)
  simp only [decide_eq_true_eq] at MONO
  omega'

theorem uniprocessor_response_time_bound_seq {Task : Type u} [DecidableEq Task] (task_cost : Task → time)
    {Job : Type v} [DecidableEq Job] (job_arrival job_cost : Job → time) (job_task : Job → Task) (arr_seq : arrival_sequence Job)
    (H_arrival_times_are_consistent : arrival_times_are_consistent job_arrival arr_seq) (sched : schedule Job)
    (H_jobs_come_from_arrival_sequence : jobs_come_from_arrival_sequence sched arr_seq)
    (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute job_arrival sched)
    (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched)
    (H_job_cost_le_task_cost : cost_of_jobs_from_arrival_sequence_le_task_cost task_cost job_cost job_task arr_seq)
    (ts : List Task) (max_arrivals : Task → time → Nat)
    (H_family_of_proper_arrival_curves : family_of_proper_arrival_curves job_task arr_seq max_arrivals ts) (tsk : Task)
    (H_tsk_in_ts : tsk ∈ ts)
    (job_lock_in_service : Job → time) (task_lock_in_service : Task → time)
    (H_proper_job_lock_in_service : proper_job_lock_in_service job_cost arr_seq sched job_lock_in_service)
    (H_proper_task_lock_in_service :
      proper_task_lock_in_service task_cost job_task arr_seq job_lock_in_service task_lock_in_service tsk)
    (interference : Job → time → Bool) (interfering_workload : Job → time → time)
    (H_work_conserving : work_conserving job_arrival job_cost job_task arr_seq sched tsk interference interfering_workload)
    (H_sequential_jobs : sequential_jobs job_arrival job_cost sched job_task)
    (H_interference_and_workload_consistent_with_sequential_jobs :
      interference_and_workload_consistent_with_sequential_jobs job_arrival job_cost job_task arr_seq sched tsk
        interference interfering_workload)
    (L : time)
    (H_busy_interval_exists :
      busy_intervals_are_bounded_by job_arrival job_cost job_task arr_seq sched tsk interference interfering_workload L)
    (task_interference_bound_function : Task → time → time → time)
    (H_task_interference_is_bounded : task_interference_is_bounded_by job_arrival job_cost job_task arr_seq sched tsk
      interference interfering_workload task_interference_bound_function)
    (R : Nat)
    (H_R_is_maximum_seq : ∀ A, is_in_search_space tsk L (fun tsk0 A Δ => task_request_bound_function task_cost max_arrivals tsk (A + ε) - task_cost tsk0 + task_interference_bound_function tsk0 A Δ) A →
      ∃ F, A + F = (task_request_bound_function task_cost max_arrivals tsk (A + ε) - (task_cost tsk - task_lock_in_service tsk)) +
          task_interference_bound_function tsk A (A + F) ∧
        F + (task_cost tsk - task_lock_in_service tsk) ≤ R) :
    is_response_time_bound_of_task job_arrival job_cost job_task arr_seq sched tsk R := by
  intro j ARR TSK
  apply uniprocessor_response_time_bound task_cost job_arrival job_cost job_task arr_seq sched
    H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_job_cost_le_task_cost tsk job_lock_in_service
    task_lock_in_service H_proper_job_lock_in_service H_proper_task_lock_in_service interference interfering_workload
    H_work_conserving L H_busy_interval_exists (fun tsk0 A Δ => task_request_bound_function task_cost max_arrivals tsk (A + ε) - task_cost tsk0 + task_interference_bound_function tsk0 A Δ) ?_ R
    (max_in_seq_hypothesis_implies_max_in_nonseq_hypothesis task_cost job_arrival job_cost job_task arr_seq
      H_arrival_times_are_consistent sched ts max_arrivals H_family_of_proper_arrival_curves tsk H_tsk_in_ts
      job_lock_in_service task_lock_in_service H_proper_job_lock_in_service H_proper_task_lock_in_service L
      task_interference_bound_function R H_R_is_maximum_seq j ARR TSK) j ARR TSK
  intro t1 t2 delta j' BUSY NEQ ARR' TSK' COMPL
  rcases Nat.eq_zero_or_pos (job_cost j') with ZERO | POS
  · exfalso
    simp [completed_by, ZERO] at COMPL
  have B1 := bound_for_cumulative_job_interference task_cost job_arrival job_cost job_task arr_seq
    H_arrival_times_are_consistent sched H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute
    H_completed_jobs_dont_execute H_job_cost_le_task_cost ts max_arrivals H_family_of_proper_arrival_curves tsk
    H_tsk_in_ts interference interfering_workload H_work_conserving H_sequential_jobs
    H_interference_and_workload_consistent_with_sequential_jobs j' ARR' TSK' (decide_eq_true POS) t1 t2 BUSY delta
    NEQ COMPL
  have B2 := H_task_interference_is_bounded j' delta t1 t2 ARR' TSK' NEQ COMPL BUSY
  simp only at B2 ⊢
  omega'

end Prosa.Classic.Model.Schedule.Uni.Limited.AbstractRTA.AbstractSeqRta.AbstractSeqRTA
