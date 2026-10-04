-- Authoritative source:
-- ProsaBuddy classic Prosa (prosabuddy commit f692cb7479780cf6009493f373a309e13165201c)
-- source: classic/model/schedule/uni/service.v
-- sha256: see Prosa-Shunqi/classic-prosa/comprehensive-classic/file_order.csv (rank 72)

import Prosa.Classic.Util.All
import Prosa.Classic.Model.Time
import Prosa.Classic.Model.Arrival.Basic.Task
import Prosa.Classic.Model.Arrival.Basic.Job
import Prosa.Classic.Model.Arrival.Basic.ArrivalSequence
import Prosa.Classic.Model.Priority
import Prosa.Classic.Model.Schedule.Uni.Schedule
import Prosa.Classic.Model.Schedule.Uni.Workload
import Prosa.Util.Sum
import Prosa.Util.UnitGrowth

/-!
Service received by sets of jobs in uniprocessor schedules (Rocq module `Service`).

Representation notes:
* `\sum_(j <- jobs | P j) F j` is `sumFiltered jobs P F` (v0.6 `Prosa.Util.Sum`); `predT` is `fun _ => true`;
  `uniq jobs` is `jobs.Nodup`; `j \in s` is `j ∈ s`.
* Boolean chains `a <= x < b` / `a <= x <= b` in proposition position are
  `(decide (a ≤ x) && decide (x < b)) = true` / `(decide (a ≤ x) && decide (x ≤ b)) = true`; other Boolean tests are
  `= true`.
* The section-local `Let`s (`of_higher_or_equal_priority`, `workload_of`, `of_task_tsk`, `job_completed_by`,
  `arrivals_between`, `jobs`) are unfolded.
* Binder lists follow the Rocq contract (e.g. `service_of_jobs_le_delta` takes `H_no_duplicate_jobs` but not
  `H_completed_jobs_dont_execute`; `service_of_jobs_cat_arrival_interval` takes no hypotheses).
-/

set_option linter.dupNamespace false
set_option linter.unusedVariables false

namespace Prosa.Classic.Model.Schedule.Uni.Service.Service

open Prosa.Classic.Model.Time.Time
open Prosa.Classic.Model.Arrival.Basic.ArrivalSequence.ArrivalSequence
open Prosa.Classic.Model.Priority.Priority
open Prosa.Classic.Model.Schedule.Uni.Schedule.UniprocessorSchedule
open Prosa.Classic.Model.Schedule.Uni.Workload.Workload
open Prosa.Util.Sum (sumFiltered)

universe u v

local macro "omega'" : tactic =>
  `(tactic| ((try dsimp only [Prosa.Classic.Model.Time.Time.time,
    Prosa.Classic.Model.Time.Time.instant, Prosa.Classic.Model.Time.Time.duration] at *) <;>
    omega))

def service_of_jobs {Job : Type u} [DecidableEq Job] (sched : schedule Job) (jobs : List Job) (P : Job → Bool)
    (t1 t2 : time) : Nat :=
  sumFiltered jobs P (fun j => service_during sched j t1 t2)

def service_of_higher_or_equal_priority_tasks {Job : Type u} [DecidableEq Job] (sched : schedule Job)
    (jobs : List Job) {Task : Type v} [DecidableEq Task] (job_task : Job → Task) (higher_eq_priority : FP_policy Task)
    (tsk : Task) (t1 t2 : time) : Nat :=
  service_of_jobs sched jobs (fun j => higher_eq_priority (job_task j) tsk) t1 t2

def service_of_higher_or_equal_priority_jobs {Job : Type u} [DecidableEq Job] (sched : schedule Job)
    (jobs : List Job) (higher_eq_priority : JLFP_policy Job) (j : Job) (t1 t2 : time) : Nat :=
  service_of_jobs sched jobs (fun j_hp => higher_eq_priority j_hp j) t1 t2

/-! ### Proof-local facts about filtered sums -/

private theorem sumFiltered_le {I : Type _} (l : List I) (P : I → Bool) (F G : I → Nat)
    (h : ∀ i ∈ l, P i = true → F i ≤ G i) : sumFiltered l P F ≤ sumFiltered l P G := by
  induction l with
  | nil => simp [sumFiltered]
  | cons a l ih =>
    have ih' := ih (fun i hi => h i (List.mem_cons_of_mem a hi))
    unfold sumFiltered at ih' ⊢
    cases hP : P a
    · simpa [List.filter_cons, hP] using ih'
    · simp only [List.filter_cons, hP, if_true, List.map_cons, List.sum_cons]
      exact Nat.add_le_add (h a List.mem_cons_self hP) ih'

private theorem sumFiltered_eq {I : Type _} (l : List I) (P : I → Bool) (F G : I → Nat)
    (h : ∀ i ∈ l, P i = true → F i = G i) : sumFiltered l P F = sumFiltered l P G :=
  Nat.le_antisymm (sumFiltered_le l P F G (fun i hi hp => (h i hi hp).le))
    (sumFiltered_le l P G F (fun i hi hp => (h i hi hp).ge))

private theorem sumFiltered_add {I : Type _} (l : List I) (P : I → Bool) (F G : I → Nat) :
    sumFiltered l P (fun i => F i + G i) = sumFiltered l P F + sumFiltered l P G := by
  unfold sumFiltered
  induction (l.filter P) with
  | nil => simp
  | cons a l ih => simp only [List.map_cons, List.sum_cons, ih]; omega

private theorem sumFiltered_append {I : Type _} (l1 l2 : List I) (P : I → Bool) (F : I → Nat) :
    sumFiltered (l1 ++ l2) P F = sumFiltered l1 P F + sumFiltered l2 P F := by
  simp [sumFiltered, List.filter_append]

private theorem sumFiltered_zero {I : Type _} (l : List I) (P : I → Bool) (F : I → Nat)
    (h : ∀ i ∈ l, P i = true → F i = 0) : sumFiltered l P F = 0 := by
  have := sumFiltered_eq l P F (fun _ => 0) h
  rw [this]; unfold sumFiltered; induction (l.filter P) <;> simp_all

private theorem sumFiltered_exchange {I : Type _} (l : List I) (P : I → Bool) (f : I → Nat → Nat) (t1 t2 : Nat) :
    sumFiltered l P (fun i => ∑ t ∈ Finset.Ico t1 t2, f i t) =
      ∑ t ∈ Finset.Ico t1 t2, sumFiltered l P (fun i => f i t) := by
  unfold sumFiltered
  induction (l.filter P) with
  | nil => simp
  | cons a l ih => simp only [List.map_cons, List.sum_cons, ih, Finset.sum_add_distrib]

/-- LEAN_HELPER: equal sums of pointwise-dominated terms are pointwise equal. -/
private theorem sumFiltered_eq_each {I : Type _} (l : List I) (P : I → Bool) (F G : I → Nat)
    (hle : ∀ i ∈ l, P i = true → F i ≤ G i) (heq : sumFiltered l P F = sumFiltered l P G) :
    ∀ i ∈ l, P i = true → F i = G i := by
  induction l with
  | nil => intro i hi; simp at hi
  | cons a l ih =>
    have hle' := fun i hi => hle i (List.mem_cons_of_mem a hi)
    have hs := sumFiltered_le l P F G hle'
    intro i hi hp
    cases hP : P a
    · have heq' : sumFiltered l P F = sumFiltered l P G := by
        simpa [sumFiltered, List.filter_cons, hP] using heq
      rcases List.mem_cons.mp hi with rfl | hi
      · rw [hP] at hp; exact absurd hp Bool.false_ne_true
      · exact ih hle' heq' i hi hp
    · have ha := hle a List.mem_cons_self hP
      have heq2 : F a + sumFiltered l P F = G a + sumFiltered l P G := by
        simpa [sumFiltered, List.filter_cons, hP] using heq
      rcases List.mem_cons.mp hi with rfl | hi
      · omega
      · exact ih hle' (by omega) i hi hp

/-- LEAN_HELPER: on a duplicate-free list, at most one job is served at any instant. -/
private theorem sum_service_at_le_one {Job : Type u} [DecidableEq Job] (sched : schedule Job) (t : Nat)
    (l : List Job) (hl : l.Nodup) : (l.map (fun j => service_at sched j t)).sum ≤ 1 := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.nodup_cons] at hl
    simp only [List.map_cons, List.sum_cons]
    by_cases hs : sched t = some a
    · have : (l.map (fun j => service_at sched j t)).sum = 0 := by
        apply List.sum_eq_zero
        intro x hx
        obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hx
        have hne : j ≠ a := fun h => hl.1 (h ▸ hj)
        simp [service_at, scheduled_at, hs, Ne.symm hne]
      rw [this]; simp [service_at, scheduled_at, hs]
    · have h0 : service_at sched a t = 0 := by simp [service_at, scheduled_at, hs]
      rw [h0, Nat.zero_add]; exact ih hl.2

private theorem sumFiltered_service_at_le_one {Job : Type u} [DecidableEq Job] (sched : schedule Job)
    (t : Nat) (l : List Job) (P : Job → Bool) (hl : l.Nodup) :
    sumFiltered l P (fun j => service_at sched j t) ≤ 1 :=
  sum_service_at_le_one sched t _ (hl.filter P)

/-- LEAN_HELPER: a sum over `[t1, t2)` of terms bounded by one is at most `t2 - t1`. -/
private theorem sum_le_one_le_delta (f : Nat → Nat) (t1 t2 : Nat) (h : ∀ t, f t ≤ 1) :
    ∑ t ∈ Finset.Ico t1 t2, f t ≤ t2 - t1 := by
  calc ∑ t ∈ Finset.Ico t1 t2, f t ≤ ∑ _t ∈ Finset.Ico t1 t2, (1 : Nat) := Finset.sum_le_sum (fun t _ => h t)
    _ = t2 - t1 := by simp

/-- LEAN_HELPER: a job arriving no earlier than `t1` has all its service in `[t1, t)`. -/
private theorem service_eq_service_during_from {Job : Type u} [DecidableEq Job] (job_arrival : Job → time)
    (sched : schedule Job) (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute job_arrival sched)
    (j : Job) (t1 t : Nat) (h : t1 ≤ job_arrival j) :
    service sched j t = service_during sched j t1 t := by
  unfold service service_during
  rcases Nat.le_total t t1 with hle | hle
  · rw [cumulative_service_before_job_arrival_zero job_arrival sched H_jobs_must_arrive_to_execute j 0 t
      (by omega'), Finset.Ico_eq_empty_of_le hle, Finset.sum_empty]
  · rw [← Finset.sum_Ico_consecutive _ (Nat.zero_le t1) hle,
      cumulative_service_before_job_arrival_zero job_arrival sched H_jobs_must_arrive_to_execute j 0 t1 h,
      Nat.zero_add]

/-! ### Lemmas -/

theorem service_of_jobs_le_workload {Job : Type u} [DecidableEq Job] (job_cost : Job → time)
    (sched : schedule Job) (jobs : List Job) (P : Job → Bool)
    (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched) :
    ∀ t1 t2 : time, service_of_jobs sched jobs P t1 t2 ≤ workload_of_jobs job_cost jobs P := by
  intro t1 t2
  exact sumFiltered_le _ _ _ _ (fun j _ _ =>
    cumulative_service_le_job_cost job_cost sched j H_completed_jobs_dont_execute t1 t2)

theorem service_of_jobs_le_delta {Job : Type u} [DecidableEq Job] (sched : schedule Job) (jobs : List Job)
    (P : Job → Bool) (H_no_duplicate_jobs : jobs.Nodup) :
    ∀ t1 t2 : time, service_of_jobs sched jobs P t1 t2 ≤ t2 - t1 := by
  intro t1 t2
  unfold service_of_jobs service_during
  rw [sumFiltered_exchange]
  exact sum_le_one_le_delta _ t1 t2 (fun t => sumFiltered_service_at_le_one sched t jobs P H_no_duplicate_jobs)

def task_service_of_jobs_received_in {Task : Type u} [DecidableEq Task] {Job : Type v} [DecidableEq Job]
    (job_task : Job → Task) (arr_seq : arrival_sequence Job) (sched : schedule Job) (tsk : Task)
    (ta1 ta2 t1 t2 : time) : Nat :=
  service_of_jobs sched (jobs_arrived_between arr_seq ta1 ta2) (fun j => decide (job_task j = tsk)) t1 t2

def task_service_between {Task : Type u} [DecidableEq Task] {Job : Type v} [DecidableEq Job]
    (job_task : Job → Task) (arr_seq : arrival_sequence Job) (sched : schedule Job) (tsk : Task)
    (t1 t2 : time) : Nat :=
  task_service_of_jobs_received_in job_task arr_seq sched tsk t1 t2 t1 t2

theorem service_monotonic {Job : Type u} [DecidableEq Job] (sched : schedule Job) :
    ∀ (j : Job) (t1 t2 : Nat), t1 ≤ t2 → service sched j t1 ≤ service sched j t2 := by
  intro j t1 t2 LE
  unfold service service_during
  rw [← Finset.sum_Ico_consecutive _ (Nat.zero_le t1) LE]
  exact Nat.le_add_right _ _

theorem service_during_cat {Job : Type u} [DecidableEq Job] (sched : schedule Job) :
    ∀ (j : Job) (t t1 t2 : Nat), (decide (t1 ≤ t) && decide (t ≤ t2)) = true →
      service_during sched j t1 t2 = service_during sched j t1 t + service_during sched j t t2 := by
  intro j t t1 t2 H
  simp only [Bool.and_eq_true, decide_eq_true_eq] at H
  unfold service_during
  rw [Finset.sum_Ico_consecutive _ H.1 H.2]

theorem incremental_service_during {Job : Type u} [DecidableEq Job] (sched : schedule Job) :
    ∀ (j : Job) (t1 t2 : time) (k : Nat), k < service_during sched j t1 t2 →
      ∃ t, (decide (t1 ≤ t) && decide (t < t2)) = true ∧ scheduled_at sched j t = true ∧
        service_during sched j t1 t = k := by
  intro j t1 t2 k SERV
  have LT : t1 < t2 := by
    by_contra hc
    unfold service_during at SERV
    rw [Finset.Ico_eq_empty_of_le (by omega'), Finset.sum_empty] at SERV
    omega
  have EX : ∃ d, k < service_during sched j t1 (t1 + d + 1) := ⟨t2 - t1 - 1, by
    have : t1 + (t2 - t1 - 1) + 1 = t2 := by omega'
    rw [this]; exact SERV⟩
  classical
  have hd0 := Nat.find_spec EX
  have hmin : ∀ m, m < Nat.find EX → ¬ k < service_during sched j t1 (t1 + m + 1) :=
    fun m h => Nat.find_min EX h
  have hd0le : Nat.find EX ≤ t2 - t1 - 1 := Nat.find_min' EX (by
    have : t1 + (t2 - t1 - 1) + 1 = t2 := by omega'
    rw [this]; exact SERV)
  generalize Nat.find EX = d0 at hd0 hmin hd0le
  have hstep : service_during sched j t1 (t1 + d0 + 1) =
      service_during sched j t1 (t1 + d0) + service_at sched j (t1 + d0) := by
    unfold service_during
    rw [Finset.sum_Ico_succ_top (by omega)]
  have hprev : service_during sched j t1 (t1 + d0) ≤ k := by
    rcases Nat.eq_zero_or_pos d0 with h0 | hpos
    · rw [h0]; unfold service_during; simp
    · have := hmin (d0 - 1) (by omega)
      have e : t1 + (d0 - 1) + 1 = t1 + d0 := by omega'
      rw [e] at this; omega'
  have hle1 : service_at sched j (t1 + d0) ≤ 1 := by
    unfold service_at; cases scheduled_at sched j (t1 + d0) <;> simp
  refine ⟨t1 + d0, ?_, ?_, ?_⟩
  · simp only [Bool.and_eq_true, decide_eq_true_eq]; constructor <;> omega'
  · have : service_at sched j (t1 + d0) = 1 := by omega'
    unfold service_at at this
    cases h : scheduled_at sched j (t1 + d0)
    · rw [h] at this; simp at this
    · rfl
  · omega'

theorem service_of_jobs_le_1 {Job : Type u} [DecidableEq Job] (job_arrival : Job → time)
    (arr_seq : arrival_sequence Job) (H_arrival_times_are_consistent : arrival_times_are_consistent job_arrival arr_seq)
    (H_arr_seq_is_a_set : arrival_sequence_is_a_set arr_seq) (sched : schedule Job) :
    ∀ (t1 t2 t : time) (P : Job → Bool),
      sumFiltered (jobs_arrived_between arr_seq t1 t2) P (fun j => service_at sched j t) ≤ 1 := by
  intro t1 t2 t P
  exact sumFiltered_service_at_le_one sched t _ P
    (arrivals_uniq job_arrival arr_seq H_arrival_times_are_consistent H_arr_seq_is_a_set t1 t2)

theorem total_service_of_jobs_le_delta {Job : Type u} [DecidableEq Job] (job_arrival : Job → time)
    (arr_seq : arrival_sequence Job) (H_arrival_times_are_consistent : arrival_times_are_consistent job_arrival arr_seq)
    (H_arr_seq_is_a_set : arrival_sequence_is_a_set arr_seq) (sched : schedule Job) :
    ∀ (t Δ : time) (P : Job → Bool),
      sumFiltered (jobs_arrived_between arr_seq t (t + Δ)) P (fun j => service_during sched j t (t + Δ)) ≤ Δ := by
  intro t Δ P
  unfold service_during
  rw [sumFiltered_exchange]
  have := sum_le_one_le_delta _ t (t + Δ) (fun x => service_of_jobs_le_1 job_arrival arr_seq
    H_arrival_times_are_consistent H_arr_seq_is_a_set sched t (t + Δ) x P)
  omega'

theorem low_service_implies_existence_of_idle_time {Job : Type u} [DecidableEq Job] (job_arrival : Job → time)
    (arr_seq : arrival_sequence Job) (H_arrival_times_are_consistent : arrival_times_are_consistent job_arrival arr_seq)
    (sched : schedule Job) (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute job_arrival sched)
    (H_jobs_come_from_arrival_sequence : jobs_come_from_arrival_sequence sched arr_seq) :
    ∀ t1 t2 : Nat, t1 ≤ t2 →
      service_of_jobs sched (jobs_arrived_between arr_seq 0 t2) (fun _ => true) t1 t2 < t2 - t1 →
      ∃ t, (decide (t1 ≤ t) && decide (t < t2)) = true ∧ is_idle sched t = true := by
  intro t1 t2 LE SERV
  unfold service_of_jobs service_during at SERV
  rw [sumFiltered_exchange] at SERV
  by_contra NONE
  push_neg at NONE
  apply absurd SERV
  apply Nat.not_lt.mpr
  calc t2 - t1 = ∑ _x ∈ Finset.Ico t1 t2, (1 : Nat) := by simp
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro x hx
      rw [Finset.mem_Ico] at hx
      have hni := NONE x (by simp only [Bool.and_eq_true, decide_eq_true_eq]; exact hx)
      cases hs : sched x with
      | none => simp [is_idle, hs] at hni
      | some s =>
        have SCHED : scheduled_at sched s x = true := by simp [scheduled_at, hs]
        have ARR := H_jobs_must_arrive_to_execute s x SCHED
        simp only [has_arrived, decide_eq_true_eq] at ARR
        have IN : s ∈ jobs_arrived_between arr_seq 0 t2 :=
          arrived_between_implies_in_arrivals job_arrival arr_seq H_arrival_times_are_consistent s 0 t2
            (H_jobs_come_from_arrival_sequence s x SCHED)
            (by simp only [arrived_between, Bool.and_eq_true, decide_eq_true_eq]; omega')
        have h1 : service_at sched s x = 1 := by simp [service_at, SCHED]
        have hle : service_at sched s x ≤ sumFiltered (jobs_arrived_between arr_seq 0 t2) (fun _ => true)
            (fun j => service_at sched j x) := by
          unfold sumFiltered
          rw [List.filter_true]
          exact List.le_sum_of_mem (List.mem_map_of_mem IN)
        omega'

theorem service_of_jobs_cat_scheduling_interval {Job : Type u} [DecidableEq Job] (job_arrival : Job → time)
    (arr_seq : arrival_sequence Job) (H_arrival_times_are_consistent : arrival_times_are_consistent job_arrival arr_seq)
    (sched : schedule Job) (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute job_arrival sched) :
    ∀ (P : Job → Bool) (t1 t2 t : Nat), (decide (t1 ≤ t) && decide (t ≤ t2)) = true →
      service_of_jobs sched (jobs_arrived_between arr_seq t1 t2) P t1 t2 =
        service_of_jobs sched (jobs_arrived_between arr_seq t1 t) P t1 t +
          service_of_jobs sched (jobs_arrived_between arr_seq t1 t) P t t2 +
          service_of_jobs sched (jobs_arrived_between arr_seq t t2) P t t2 := by
  intro P t1 t2 t H
  have H' := H
  simp only [Bool.and_eq_true, decide_eq_true_eq] at H'
  obtain ⟨GEt, LEt⟩ := H'
  unfold service_of_jobs
  rw [job_arrived_between_cat arr_seq t1 t t2 GEt LEt, sumFiltered_append]
  have hA : sumFiltered (jobs_arrived_between arr_seq t1 t) P (fun j => service_during sched j t1 t2) =
      sumFiltered (jobs_arrived_between arr_seq t1 t) P (fun j => service_during sched j t1 t) +
        sumFiltered (jobs_arrived_between arr_seq t1 t) P (fun j => service_during sched j t t2) := by
    rw [← sumFiltered_add]
    exact sumFiltered_eq _ _ _ _ (fun j _ _ => service_during_cat sched j t t1 t2 H)
  have hB : sumFiltered (jobs_arrived_between arr_seq t t2) P (fun j => service_during sched j t1 t2) =
      sumFiltered (jobs_arrived_between arr_seq t t2) P (fun j => service_during sched j t t2) := by
    apply sumFiltered_eq
    intro j hj _
    rw [service_during_cat sched j t t1 t2 H]
    have ARR := in_arrivals_implies_arrived_between job_arrival arr_seq H_arrival_times_are_consistent j t t2 hj
    simp only [arrived_between, Bool.and_eq_true, decide_eq_true_eq] at ARR
    unfold service_during
    rw [cumulative_service_before_job_arrival_zero job_arrival sched H_jobs_must_arrive_to_execute j t1 t ARR.1,
      Nat.zero_add]
  rw [hA, hB]

theorem service_of_jobs_cat_arrival_interval {Job : Type u} [DecidableEq Job] (arr_seq : arrival_sequence Job)
    (sched : schedule Job) :
    ∀ (P : Job → Bool) (t1 t2 t : Nat), (decide (t1 ≤ t) && decide (t ≤ t2)) = true →
      service_of_jobs sched (jobs_arrived_between arr_seq t1 t2) P t t2 =
        service_of_jobs sched (jobs_arrived_between arr_seq t1 t) P t t2 +
          service_of_jobs sched (jobs_arrived_between arr_seq t t2) P t t2 := by
  intro P t1 t2 t H
  simp only [Bool.and_eq_true, decide_eq_true_eq] at H
  unfold service_of_jobs
  rw [job_arrived_between_cat arr_seq t1 t t2 H.1 H.2, sumFiltered_append]

theorem workload_eq_service_impl_all_jobs_have_completed {Job : Type u} [DecidableEq Job]
    (job_arrival job_cost : Job → time) (arr_seq : arrival_sequence Job)
    (H_arrival_times_are_consistent : arrival_times_are_consistent job_arrival arr_seq) (sched : schedule Job)
    (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute job_arrival sched)
    (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched) (P : Job → Bool)
    (t1 t2 t_compl : time) :
    workload_of_jobs job_cost (jobs_arrived_between arr_seq t1 t2) P =
        service_of_jobs sched (jobs_arrived_between arr_seq t1 t2) P t1 t_compl →
      ∀ j, j ∈ jobs_arrived_between arr_seq t1 t2 → P j = true → completed_by job_cost sched j t_compl = true := by
  intro H j ARR Pj
  unfold workload_of_jobs service_of_jobs at H
  have EACH := sumFiltered_eq_each _ P _ _ (fun x _ _ =>
    cumulative_service_le_job_cost job_cost sched x H_completed_jobs_dont_execute t1 t_compl) H.symm j ARR Pj
  have A := in_arrivals_implies_arrived_between job_arrival arr_seq H_arrival_times_are_consistent j t1 t2 ARR
  simp only [arrived_between, Bool.and_eq_true, decide_eq_true_eq] at A
  simp only [completed_by, decide_eq_true_eq]
  rw [service_eq_service_during_from job_arrival sched H_jobs_must_arrive_to_execute j t1 t_compl A.1]
  omega'

theorem all_jobs_have_completed_impl_workload_eq_service {Job : Type u} [DecidableEq Job]
    (job_arrival job_cost : Job → time) (arr_seq : arrival_sequence Job)
    (H_arrival_times_are_consistent : arrival_times_are_consistent job_arrival arr_seq) (sched : schedule Job)
    (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute job_arrival sched)
    (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched) (P : Job → Bool)
    (t1 t2 t_compl : time) :
    (∀ j, j ∈ jobs_arrived_between arr_seq t1 t2 → P j = true → completed_by job_cost sched j t_compl = true) →
      workload_of_jobs job_cost (jobs_arrived_between arr_seq t1 t2) P =
        service_of_jobs sched (jobs_arrived_between arr_seq t1 t2) P t1 t_compl := by
  intro H
  unfold workload_of_jobs service_of_jobs
  apply sumFiltered_eq
  intro j ARR Pj
  have C := H j ARR Pj
  simp only [completed_by, decide_eq_true_eq] at C
  have A := in_arrivals_implies_arrived_between job_arrival arr_seq H_arrival_times_are_consistent j t1 t2 ARR
  simp only [arrived_between, Bool.and_eq_true, decide_eq_true_eq] at A
  rw [service_eq_service_during_from job_arrival sched H_jobs_must_arrive_to_execute j t1 t_compl A.1] at C
  have := cumulative_service_le_job_cost job_cost sched j H_completed_jobs_dont_execute t1 t_compl
  omega'

theorem all_jobs_have_completed_equiv_workload_eq_service {Job : Type u} [DecidableEq Job]
    (job_arrival job_cost : Job → time) (arr_seq : arrival_sequence Job)
    (H_arrival_times_are_consistent : arrival_times_are_consistent job_arrival arr_seq) (sched : schedule Job)
    (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute job_arrival sched)
    (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched) (P : Job → Bool)
    (t1 t2 t_compl : time) :
    (∀ j, j ∈ jobs_arrived_between arr_seq t1 t2 → P j = true → completed_by job_cost sched j t_compl = true) ↔
      workload_of_jobs job_cost (jobs_arrived_between arr_seq t1 t2) P =
        service_of_jobs sched (jobs_arrived_between arr_seq t1 t2) P t1 t_compl :=
  ⟨all_jobs_have_completed_impl_workload_eq_service job_arrival job_cost arr_seq H_arrival_times_are_consistent
      sched H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute P t1 t2 t_compl,
    workload_eq_service_impl_all_jobs_have_completed job_arrival job_cost arr_seq H_arrival_times_are_consistent
      sched H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute P t1 t2 t_compl⟩

end Prosa.Classic.Model.Schedule.Uni.Service.Service
