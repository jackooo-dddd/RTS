-- Authoritative source:
-- ProsaBuddy classic Prosa (prosabuddy commit f692cb7479780cf6009493f373a309e13165201c)
-- source: classic/analysis/global/parallel/interference_bound_edf.v
-- sha256: see Prosa-Shunqi/classic-prosa/comprehensive-classic/file_order.csv (rank 147)

import Prosa.Util.Sum
import Prosa.Classic.Util.DivMod
import Prosa.Classic.Util.Sum
import Prosa.Classic.Util.Sorting
import Prosa.Classic.Model.Arrival.Basic.Task
import Prosa.Classic.Model.Arrival.Basic.Job
import Prosa.Classic.Model.Arrival.Basic.TaskArrival
import Prosa.Classic.Model.Priority
import Prosa.Classic.Model.Schedule.Global.ResponseTime
import Prosa.Classic.Model.Schedule.Global.Workload
import Prosa.Classic.Model.Schedule.Global.Schedulability
import Prosa.Classic.Model.Schedule.Global.Basic.Schedule
import Prosa.Classic.Model.Schedule.Global.Basic.Platform
import Prosa.Classic.Model.Schedule.Global.Basic.Interference
import Prosa.Classic.Model.Schedule.Global.Basic.InterferenceEdf
import Prosa.Classic.Analysis.Global.Parallel.WorkloadBound
import Prosa.Classic.Analysis.Global.Parallel.InterferenceBound

/-!
Bertogna and Cirinei's EDF-specific interference bound for (potentially) parallel jobs and its safety proof (Rocq
module `InterferenceBoundEDF` of `classic/analysis/global/parallel/interference_bound_edf.v`).

Representation notes:
* The `let`s of `edf_specific_interference_bound` are inlined; `minn` is `min`; `div_ceil` is the classic
  `Prosa.Classic.Util.DivMod.div_ceil`.
* `\sum_((tsk_other, R_other) <- R_prev | other_task tsk_other) F` binds the pair by pattern matching and is
  `Prosa.Util.Sum.sumFiltered R_prev (fun (tsk_other, _R_other) => different_task tsk tsk_other)
  (fun (tsk_other, R_other) => F)`.
* The section-local `Let`s are unfolded in the statements exactly as in the accepted basic translation
  (`Prosa.Classic.Analysis.Global.Basic.InterferenceBoundEdf`), except that `n_k` is
  `div_ceil (task_deadline tsk_i + R_k - task_deadline tsk_k + 1) (task_period tsk_k)`; `x`, `interference_bound`,
  `t1`/`t2`, `D_i`/`D_k`/`p_k`, `interference_caused_by`, `interfering_jobs`, `sorted_jobs` (`mergeSort` by
  arrival time, MathComp's stable `sort`), `j_fst`/`j_lst`/`a_fst`/`a_lst` as there; the unused `Let`s
  (`no_deadline_is_missed_by_tsk`, `response_time_bounded_by`, `task_with_response_time`) are dropped.
* `\sum_(j <- s) F j` is `Prosa.Util.Sum.sumSeq s F`, `\sum_(j <- s | P j) F j` is `Prosa.Util.Sum.sumFiltered s P F`,
  `\sum_(a <= t < b) F t` is `∑ t ∈ Finset.Ico a b, F t`; `x != 0` in proposition position is
  `(!decide (x = 0)) = true`.
* The Rocq module re-exports `InterferenceBoundGeneric`.
* Binder lists follow the Rocq contract; in this file the arrival sequence is a `Context` (implicit `{arr_seq}`) and
  there is no sequential-jobs hypothesis.
* The lemmas shared with the basic file (job sequence simplification, first/last job facts, many periods in between,
  first job completed on time) reuse the accepted basic proofs with these changes; the single-job, slack, `n_k`
  coverage, multiple-jobs, main and monotonicity proofs follow the parallel source.
-/

set_option linter.dupNamespace false
set_option linter.unusedVariables false

namespace Prosa.Classic.Analysis.Global.Parallel.InterferenceBoundEdf.InterferenceBoundEDF

open Prosa.Classic.Model.Time.Time
open Prosa.Classic.Model.Arrival.Basic.ArrivalSequence.ArrivalSequence
open Prosa.Classic.Model.Arrival.Basic.Task.SporadicTaskset
open Prosa.Classic.Model.Arrival.Basic.Job.Job
open Prosa.Classic.Model.Arrival.Basic.TaskArrival.TaskArrival
open Prosa.Classic.Model.Priority.Priority
open Prosa.Classic.Model.Schedule.Global.Basic.Schedule.Schedule
open Prosa.Classic.Model.Schedule.Global.Basic.Schedule.ScheduleOfSporadicTask
open Prosa.Classic.Model.Schedule.Global.Basic.Platform.Platform
open Prosa.Classic.Model.Schedule.Global.Basic.Interference.Interference
open Prosa.Classic.Model.Schedule.Global.Basic.InterferenceEdf.InterferenceEDF
open Prosa.Classic.Model.Schedule.Global.ResponseTime.ResponseTime
open Prosa.Classic.Analysis.Global.Parallel.WorkloadBound.WorkloadBound
open Prosa.Classic.Util.DivMod (div_floor div_ceil ceil_neq0 leq_divceil2r)
open Prosa.Util.Sum (sumSeq sumFiltered)
open BigOperators

export Prosa.Classic.Analysis.Global.Parallel.InterferenceBound.InterferenceBoundGeneric
  (interference_bound_generic)

universe u v

local macro "omega'" : tactic =>
  `(tactic| ((try dsimp only [Prosa.Classic.Model.Time.Time.time,
    Prosa.Classic.Model.Time.Time.instant, Prosa.Classic.Model.Time.Time.duration] at *) <;>
    omega))

/-! ### Definitions -/

def edf_specific_interference_bound
    {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost : sporadic_task → time)
    (task_period : sporadic_task → time)
    (task_deadline : sporadic_task → time)
    (tsk : sporadic_task)
    (tsk_other : sporadic_task)
    (R_other : time) : Nat :=
  div_ceil (task_deadline tsk + R_other - task_deadline tsk_other + 1) (task_period tsk_other) *
    task_cost tsk_other

def interference_bound_edf
    {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost : sporadic_task → time)
    (task_period : sporadic_task → time)
    (task_deadline : sporadic_task → time)
    (tsk : sporadic_task)
    (delta : time)
    (tsk_R : sporadic_task × time) : Nat :=
  min (interference_bound_generic task_cost task_period delta tsk_R)
    (edf_specific_interference_bound task_cost task_period task_deadline tsk tsk_R.1 tsk_R.2)

def total_interference_bound_edf
    {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost : sporadic_task → time)
    (task_period : sporadic_task → time)
    (task_deadline : sporadic_task → time)
    (tsk : sporadic_task)
    (R_prev : List (sporadic_task × time))
    (delta : time) : Nat :=
  sumFiltered R_prev (fun (tsk_other, _R_other) => different_task tsk tsk_other)
    (fun (tsk_other, R_other) =>
      interference_bound_edf task_cost task_period task_deadline tsk delta (tsk_other, R_other))

/-! ### LEAN_HELPER lemmas -/

/-- LEAN_HELPER: a ceiling division multiplied back covers the dividend. -/
private theorem div_ceil_mul_ge (x y : Nat) (hy : 0 < y) : x ≤ div_ceil x y * y := by
  unfold div_ceil
  split
  · rename_i hd
    rw [Nat.div_mul_cancel hd]
  · have := Nat.div_add_mod x y
    have := Nat.mod_lt x hy
    rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm]
    omega


/-! ### LEAN_HELPER lemmas -/

/-- LEAN_HELPER: defaulted lookup inside the list. -/
private theorem getD_lt {α : Type _} {l : List α} {i : Nat} {d : α} (h : i < l.length) :
    l.getD i d = l[i] := by
  simp [List.getD_eq_getElem?_getD, h]

/-- LEAN_HELPER: a sum over a list as an indexed sum (MathComp `big_nth`). -/
private theorem sumSeq_getD {T : Type _} (l : List T) (F : T → Nat) (x0 : T) :
    sumSeq l F = ∑ i ∈ Finset.Ico 0 l.length, F (l.getD i x0) := by
  rw [← Finset.range_eq_Ico]
  induction l with
  | nil => simp [sumSeq]
  | cons a l ih =>
      unfold sumSeq at ih ⊢
      rw [List.map_cons, List.sum_cons, ih, List.length_cons, Finset.sum_range_succ']
      simp [Nat.add_comm]

/-- LEAN_HELPER: dropping the zero summands of a filtered sum. -/
private theorem sum_filter_ne_zero {α : Type _} (l : List α) (P : α → Bool) (f : α → Nat) :
    ((l.filter P).map f).sum = ((l.filter (fun x => P x && !decide (f x = 0))).map f).sum := by
  induction l with
  | nil => rfl
  | cons a l ih =>
      by_cases hP : P a = true
      · by_cases hf : f a = 0
        · simp [hP, hf, ih]
        · simp [hP, hf, ih]
      · simp [hP, ih]

/-- LEAN_HELPER: the sorted list has the same elements as the interfering jobs. -/
private theorem sorted_mem
    {sporadic_task : Type u} [DecidableEq sporadic_task]
    {Job : Type v} [DecidableEq Job]
    (job_arrival : Job → time)
    (job_cost : Job → time)
    (job_task : Job → sporadic_task)
    (num_cpus : Nat)
    (sched : schedule Job num_cpus)
    (j_i : Job)
    (tsk_k : sporadic_task)
    (delta : time)
    (j : Job) :
    j ∈ ((((jobs_scheduled_between sched (job_arrival j_i) (job_arrival j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost sched j_i (j') (job_arrival j_i) (job_arrival j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y))) ↔ j ∈ ((jobs_scheduled_between sched (job_arrival j_i) (job_arrival j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost sched j_i (j') (job_arrival j_i) (job_arrival j_i + delta) = 0))) :=
  List.mem_mergeSort

/-- LEAN_HELPER: the sorted list has no duplicates. -/
private theorem sorted_nodup
    {sporadic_task : Type u} [DecidableEq sporadic_task]
    {Job : Type v} [DecidableEq Job]
    (job_arrival : Job → time)
    (job_cost : Job → time)
    (job_task : Job → sporadic_task)
    (num_cpus : Nat)
    (sched : schedule Job num_cpus)
    (j_i : Job)
    (tsk_k : sporadic_task)
    (delta : time) :
    (((((jobs_scheduled_between sched (job_arrival j_i) (job_arrival j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost sched j_i (j') (job_arrival j_i) (job_arrival j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y)))).Nodup := by
  apply (List.mergeSort_perm _ _).nodup_iff.mpr
  exact (List.nodup_dedup _).filter _

/-- LEAN_HELPER: with sequential jobs, job interference in `[a, b)` is at most `b - a`. -/

private theorem interfering_job_arrives_before
    {Job : Type v} [DecidableEq Job]
    (job_arrival : Job → time)
    (job_cost : Job → time)
    (num_cpus : Nat)
    (sched : schedule Job num_cpus)
    (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute job_arrival sched)
    (j j' : Job) (a b : time)
    (NZ : (!decide (job_interference job_arrival job_cost sched j j' a b = 0)) = true) :
    job_arrival j' < b := by
  by_contra h
  have h0 := job_interference_le_service job_arrival job_cost sched j j' a b
  have hz := cumulative_service_before_job_arrival_zero job_arrival sched j'
    H_jobs_must_arrive_to_execute a b (by omega')
  unfold service_during at h0
  rw [hz] at h0
  simp only [Bool.not_eq_true', decide_eq_false_iff_not] at NZ
  omega'

/-! ### Simplifying the job sequence -/

theorem interference_bound_edf_use_another_definition
    {sporadic_task : Type u} [DecidableEq sporadic_task]
    {Job : Type v} [DecidableEq Job]
    (job_arrival : Job → time)
    (job_cost : Job → time)
    (job_task : Job → sporadic_task)
    (num_cpus : Nat)
    (sched : schedule Job num_cpus)
    (j_i : Job)
    (tsk_k : sporadic_task)
    (delta : time) :
    task_interference job_arrival job_cost job_task sched j_i tsk_k (job_arrival j_i) (job_arrival j_i + delta) ≤ sumFiltered (jobs_scheduled_between sched (job_arrival j_i) (job_arrival j_i + delta)) (fun j => decide (job_task j = tsk_k)) (fun j => job_interference job_arrival job_cost sched j_i (j) (job_arrival j_i) (job_arrival j_i + delta)) :=
  interference_le_interference_joblist job_arrival job_cost job_task sched j_i tsk_k _ _

theorem interference_bound_edf_simpl_by_filtering_interfering_jobs
    {sporadic_task : Type u} [DecidableEq sporadic_task]
    {Job : Type v} [DecidableEq Job]
    (job_arrival : Job → time)
    (job_cost : Job → time)
    (job_task : Job → sporadic_task)
    (num_cpus : Nat)
    (sched : schedule Job num_cpus)
    (j_i : Job)
    (tsk_k : sporadic_task)
    (delta : time) :
    sumFiltered (jobs_scheduled_between sched (job_arrival j_i) (job_arrival j_i + delta)) (fun j => decide (job_task j = tsk_k)) (fun j => job_interference job_arrival job_cost sched j_i (j) (job_arrival j_i) (job_arrival j_i + delta)) =
      sumSeq ((jobs_scheduled_between sched (job_arrival j_i) (job_arrival j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost sched j_i (j') (job_arrival j_i) (job_arrival j_i + delta) = 0))) (fun j => job_interference job_arrival job_cost sched j_i (j) (job_arrival j_i) (job_arrival j_i + delta)) := by
  unfold sumFiltered sumSeq
  exact sum_filter_ne_zero _ _ _

theorem interference_bound_edf_simpl_by_sorting_interfering_jobs
    {sporadic_task : Type u} [DecidableEq sporadic_task]
    {Job : Type v} [DecidableEq Job]
    (job_arrival : Job → time)
    (job_cost : Job → time)
    (job_task : Job → sporadic_task)
    (num_cpus : Nat)
    (sched : schedule Job num_cpus)
    (j_i : Job)
    (tsk_k : sporadic_task)
    (delta : time) :
    sumSeq ((jobs_scheduled_between sched (job_arrival j_i) (job_arrival j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost sched j_i (j') (job_arrival j_i) (job_arrival j_i + delta) = 0))) (fun j => job_interference job_arrival job_cost sched j_i (j) (job_arrival j_i) (job_arrival j_i + delta)) = sumSeq ((((jobs_scheduled_between sched (job_arrival j_i) (job_arrival j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost sched j_i (j') (job_arrival j_i) (job_arrival j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y))) (fun j => job_interference job_arrival job_cost sched j_i (j) (job_arrival j_i) (job_arrival j_i + delta)) := by
  unfold sumSeq
  exact ((List.mergeSort_perm _ _).map _).sum_eq.symm

theorem interference_bound_edf_job_in_same_sequence
    {sporadic_task : Type u} [DecidableEq sporadic_task]
    {Job : Type v} [DecidableEq Job]
    (job_arrival : Job → time)
    (job_cost : Job → time)
    (job_task : Job → sporadic_task)
    (num_cpus : Nat)
    (sched : schedule Job num_cpus)
    (j_i : Job)
    (tsk_k : sporadic_task)
    (delta : time)
    (j : Job) :
    decide (j ∈ ((jobs_scheduled_between sched (job_arrival j_i) (job_arrival j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost sched j_i (j') (job_arrival j_i) (job_arrival j_i + delta) = 0)))) = decide (j ∈ ((((jobs_scheduled_between sched (job_arrival j_i) (job_arrival j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost sched j_i (j') (job_arrival j_i) (job_arrival j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y)))) :=
  decide_eq_decide.mpr (sorted_mem job_arrival job_cost job_task num_cpus sched j_i tsk_k delta
    j).symm

theorem interference_bound_edf_all_jobs_from_tsk_k
    {sporadic_task : Type u} [DecidableEq sporadic_task]
    {Job : Type v} [DecidableEq Job]
    (job_arrival : Job → time)
    (job_cost : Job → time)
    (job_task : Job → sporadic_task)
    {arr_seq : arrival_sequence Job}
    (num_cpus : Nat)
    (sched : schedule Job num_cpus)
    (H_jobs_come_from_arrival_sequence : jobs_come_from_arrival_sequence sched arr_seq)
    (j_i : Job)
    (tsk_k : sporadic_task)
    (delta : time)
    (j : Job) :
    j ∈ ((((jobs_scheduled_between sched (job_arrival j_i) (job_arrival j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost sched j_i (j') (job_arrival j_i) (job_arrival j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y))) →
    arrives_in arr_seq j ∧
    job_task j = tsk_k ∧
    (!decide (job_interference job_arrival job_cost sched j_i (j) (job_arrival j_i) (job_arrival j_i + delta) = 0)) = true ∧
    j ∈ jobs_scheduled_between sched (job_arrival j_i) (job_arrival j_i + delta) := by
  intro IN
  rw [sorted_mem, List.mem_filter] at IN
  obtain ⟨INs, P⟩ := IN
  simp only [Bool.and_eq_true, decide_eq_true_eq] at P
  obtain ⟨TSK, NZ⟩ := P
  have IN2 := INs
  unfold jobs_scheduled_between at IN2
  rw [List.mem_dedup] at IN2
  obtain ⟨t, hmem, _, _⟩ := Prosa.Util.Bigcat.mem_bigcat_nat_exists _ _ _ _ IN2
  have SCHED : scheduled sched j t = true := by
    have := mem_scheduled_jobs_eq_scheduled sched j t
    rw [decide_eq_true hmem] at this
    exact this.symm
  exact ⟨H_jobs_come_from_arrival_sequence j t SCHED, TSK, NZ, INs⟩

theorem interference_bound_edf_jobs_ordered_by_arrival
    {sporadic_task : Type u} [DecidableEq sporadic_task]
    {Job : Type v} [DecidableEq Job]
    (job_arrival : Job → time)
    (job_cost : Job → time)
    (job_task : Job → sporadic_task)
    (num_cpus : Nat)
    (sched : schedule Job num_cpus)
    (j_i : Job)
    (tsk_k : sporadic_task)
    (delta : time)
    (i : Nat)
    (elem : Job) :
    i < (((((jobs_scheduled_between sched (job_arrival j_i) (job_arrival j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost sched j_i (j') (job_arrival j_i) (job_arrival j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y)))).length - 1 →
    job_arrival ((((((jobs_scheduled_between sched (job_arrival j_i) (job_arrival j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost sched j_i (j') (job_arrival j_i) (job_arrival j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y)))).getD i elem) ≤ job_arrival ((((((jobs_scheduled_between sched (job_arrival j_i) (job_arrival j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost sched j_i (j') (job_arrival j_i) (job_arrival j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y)))).getD (i + 1) elem) := by
  intro LT
  have hp : List.Pairwise (fun a b => decide (job_arrival a ≤ job_arrival b) = true) (((((jobs_scheduled_between sched (job_arrival j_i) (job_arrival j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost sched j_i (j') (job_arrival j_i) (job_arrival j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y)))) := by
    apply List.pairwise_mergeSort
    · intro a b c h1 h2; simp only [decide_eq_true_eq] at *; exact Nat.le_trans h1 h2
    · intro a b; simp only [Bool.or_eq_true, decide_eq_true_eq]; exact Nat.le_total _ _
  have h1 : i < (((((jobs_scheduled_between sched (job_arrival j_i) (job_arrival j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost sched j_i (j') (job_arrival j_i) (job_arrival j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y)))).length := by omega
  have h2 : i + 1 < (((((jobs_scheduled_between sched (job_arrival j_i) (job_arrival j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost sched j_i (j') (job_arrival j_i) (job_arrival j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y)))).length := by omega
  rw [getD_lt h1, getD_lt h2]
  have := List.pairwise_iff_getElem.mp hp i (i + 1) h1 h2 (Nat.lt_succ_self i)
  simpa using this

theorem interference_bound_edf_interference_le_task_cost
    {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost : sporadic_task → time)
    (task_deadline : sporadic_task → time)
    {Job : Type v} [DecidableEq Job]
    (job_arrival : Job → time)
    (job_cost : Job → time)
    (job_deadline : Job → time)
    (job_task : Job → sporadic_task)
    {arr_seq : arrival_sequence Job}
    (H_valid_job_parameters :
      ∀ j : Job, arrives_in arr_seq j →
        valid_sporadic_job task_cost task_deadline job_cost job_deadline job_task j)
    (num_cpus : Nat)
    (sched : schedule Job num_cpus)
    (H_jobs_come_from_arrival_sequence : jobs_come_from_arrival_sequence sched arr_seq)
    (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched)
    (j_i : Job)
    (tsk_k : sporadic_task)
    (delta : time)
    (j : Job) :
    j ∈ ((jobs_scheduled_between sched (job_arrival j_i) (job_arrival j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost sched j_i (j') (job_arrival j_i) (job_arrival j_i + delta) = 0))) → job_interference job_arrival job_cost sched j_i (j) (job_arrival j_i) (job_arrival j_i + delta) ≤ task_cost tsk_k := by
  intro IN
  obtain ⟨ARR, TSK, _, _⟩ := interference_bound_edf_all_jobs_from_tsk_k job_arrival job_cost
    job_task num_cpus sched H_jobs_come_from_arrival_sequence j_i tsk_k delta j
    ((sorted_mem job_arrival job_cost job_task num_cpus sched j_i tsk_k delta j).mpr IN)
  calc job_interference job_arrival job_cost sched j_i (j) (job_arrival j_i) (job_arrival j_i + delta)
      ≤ service_during sched j (job_arrival j_i) (job_arrival j_i + delta) :=
        job_interference_le_service job_arrival job_cost sched j_i j _ _
    _ ≤ task_cost tsk_k :=
        cumulative_service_le_task_cost task_cost task_deadline job_cost job_deadline job_task
          sched H_completed_jobs_dont_execute tsk_k j TSK (H_valid_job_parameters j ARR) _ _

/-! ### At most `n_k` jobs -/

theorem interference_bound_edf_holds_for_at_most_n_k_jobs
    {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost : sporadic_task → time)
    (task_period : sporadic_task → time)
    (task_deadline : sporadic_task → time)
    {Job : Type v} [DecidableEq Job]
    (job_arrival : Job → time)
    (job_cost : Job → time)
    (job_deadline : Job → time)
    (job_task : Job → sporadic_task)
    {arr_seq : arrival_sequence Job}
    (H_valid_job_parameters :
      ∀ j : Job, arrives_in arr_seq j →
        valid_sporadic_job task_cost task_deadline job_cost job_deadline job_task j)
    (num_cpus : Nat)
    (sched : schedule Job num_cpus)
    (H_jobs_come_from_arrival_sequence : jobs_come_from_arrival_sequence sched arr_seq)
    (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched)
    (tsk_i : sporadic_task)
    (j_i : Job)
    (tsk_k : sporadic_task)
    (R_k : time)
    (delta : time)
    (H_few_jobs : (((((jobs_scheduled_between sched (job_arrival j_i) (job_arrival j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost sched j_i (j') (job_arrival j_i) (job_arrival j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y)))).length ≤ div_ceil (task_deadline tsk_i + R_k - task_deadline tsk_k + 1) (task_period tsk_k)) :
    sumSeq ((((jobs_scheduled_between sched (job_arrival j_i) (job_arrival j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost sched j_i (j') (job_arrival j_i) (job_arrival j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y))) (fun j => job_interference job_arrival job_cost sched j_i (j) (job_arrival j_i) (job_arrival j_i + delta)) ≤ edf_specific_interference_bound task_cost task_period task_deadline tsk_i tsk_k R_k := by
  have hle : sumSeq ((((jobs_scheduled_between sched (job_arrival j_i) (job_arrival j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost sched j_i (j') (job_arrival j_i) (job_arrival j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y))) (fun j => job_interference job_arrival job_cost sched j_i (j) (job_arrival j_i) (job_arrival j_i + delta)) ≤ (((((jobs_scheduled_between sched (job_arrival j_i) (job_arrival j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost sched j_i (j') (job_arrival j_i) (job_arrival j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y)))).length * task_cost tsk_k := by
    unfold sumSeq
    have := List.sum_le_card_nsmul ((((((jobs_scheduled_between sched (job_arrival j_i) (job_arrival j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost sched j_i (j') (job_arrival j_i) (job_arrival j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y)))).map (fun j => job_interference job_arrival job_cost sched j_i (j) (job_arrival j_i) (job_arrival j_i + delta))) (task_cost tsk_k) (by
      intro y hy
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hy
      exact interference_bound_edf_interference_le_task_cost task_cost task_deadline job_arrival
        job_cost job_deadline job_task H_valid_job_parameters num_cpus sched
        H_jobs_come_from_arrival_sequence H_completed_jobs_dont_execute j_i tsk_k delta j
        ((sorted_mem job_arrival job_cost job_task num_cpus sched j_i tsk_k delta j).mp hj))
    simpa using this
  unfold edf_specific_interference_bound
  have := Nat.mul_le_mul_right (task_cost tsk_k) H_few_jobs
  omega'

/-! ### More than `n_k` jobs: the first job -/

theorem interference_bound_edf_at_least_one_job
    {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_period : sporadic_task → time)
    (task_deadline : sporadic_task → time)
    {Job : Type v} [DecidableEq Job]
    (job_arrival : Job → time)
    (job_cost : Job → time)
    (job_task : Job → sporadic_task)
    (num_cpus : Nat)
    (sched : schedule Job num_cpus)
    (tsk_i : sporadic_task)
    (j_i : Job)
    (tsk_k : sporadic_task)
    (R_k : time)
    (delta : time)
    (H_many_jobs : div_ceil (task_deadline tsk_i + R_k - task_deadline tsk_k + 1) (task_period tsk_k) < (((((jobs_scheduled_between sched (job_arrival j_i) (job_arrival j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost sched j_i (j') (job_arrival j_i) (job_arrival j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y)))).length) :
    0 < (((((jobs_scheduled_between sched (job_arrival j_i) (job_arrival j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost sched j_i (j') (job_arrival j_i) (job_arrival j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y)))).length := by
  omega

theorem interference_bound_edf_j_fst_is_job_of_tsk_k
    {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_period : sporadic_task → time)
    (task_deadline : sporadic_task → time)
    {Job : Type v} [DecidableEq Job]
    (job_arrival : Job → time)
    (job_cost : Job → time)
    (job_task : Job → sporadic_task)
    {arr_seq : arrival_sequence Job}
    (num_cpus : Nat)
    (sched : schedule Job num_cpus)
    (H_jobs_come_from_arrival_sequence : jobs_come_from_arrival_sequence sched arr_seq)
    (tsk_i : sporadic_task)
    (j_i : Job)
    (tsk_k : sporadic_task)
    (R_k : time)
    (delta : time)
    (H_many_jobs : div_ceil (task_deadline tsk_i + R_k - task_deadline tsk_k + 1) (task_period tsk_k) < (((((jobs_scheduled_between sched (job_arrival j_i) (job_arrival j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost sched j_i (j') (job_arrival j_i) (job_arrival j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y)))).length)
    (elem : Job) :
    arrives_in arr_seq ((((((jobs_scheduled_between sched (job_arrival j_i) (job_arrival j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost sched j_i (j') (job_arrival j_i) (job_arrival j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y)))).getD 0 elem) ∧
    job_task ((((((jobs_scheduled_between sched (job_arrival j_i) (job_arrival j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost sched j_i (j') (job_arrival j_i) (job_arrival j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y)))).getD 0 elem) = tsk_k ∧
    (!decide (job_interference job_arrival job_cost sched j_i (((((((jobs_scheduled_between sched (job_arrival j_i) (job_arrival j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost sched j_i (j') (job_arrival j_i) (job_arrival j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y)))).getD 0 elem)) (job_arrival j_i) (job_arrival j_i + delta) = 0)) = true ∧
    ((((((jobs_scheduled_between sched (job_arrival j_i) (job_arrival j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost sched j_i (j') (job_arrival j_i) (job_arrival j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y)))).getD 0 elem) ∈ jobs_scheduled_between sched (job_arrival j_i) (job_arrival j_i + delta) := by
  apply interference_bound_edf_all_jobs_from_tsk_k job_arrival job_cost job_task num_cpus
    sched H_jobs_come_from_arrival_sequence j_i tsk_k delta
  rw [getD_lt (by omega)]
  exact List.getElem_mem _

theorem interference_bound_edf_j_fst_deadline
    {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost : sporadic_task → time)
    (task_period : sporadic_task → time)
    (task_deadline : sporadic_task → time)
    {Job : Type v} [DecidableEq Job]
    (job_arrival : Job → time)
    (job_cost : Job → time)
    (job_deadline : Job → time)
    (job_task : Job → sporadic_task)
    {arr_seq : arrival_sequence Job}
    (H_valid_job_parameters :
      ∀ j : Job, arrives_in arr_seq j →
        valid_sporadic_job task_cost task_deadline job_cost job_deadline job_task j)
    (num_cpus : Nat)
    (sched : schedule Job num_cpus)
    (H_jobs_come_from_arrival_sequence : jobs_come_from_arrival_sequence sched arr_seq)
    (tsk_i : sporadic_task)
    (j_i : Job)
    (tsk_k : sporadic_task)
    (R_k : time)
    (delta : time)
    (H_many_jobs : div_ceil (task_deadline tsk_i + R_k - task_deadline tsk_k + 1) (task_period tsk_k) < (((((jobs_scheduled_between sched (job_arrival j_i) (job_arrival j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost sched j_i (j') (job_arrival j_i) (job_arrival j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y)))).length)
    (elem : Job) :
    job_deadline ((((((jobs_scheduled_between sched (job_arrival j_i) (job_arrival j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost sched j_i (j') (job_arrival j_i) (job_arrival j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y)))).getD 0 elem) = task_deadline tsk_k := by
  obtain ⟨ARR, TSK, _, _⟩ := interference_bound_edf_j_fst_is_job_of_tsk_k task_period
    task_deadline job_arrival job_cost job_task num_cpus sched
    H_jobs_come_from_arrival_sequence tsk_i j_i tsk_k R_k delta H_many_jobs elem
  have := (H_valid_job_parameters _ ARR).2.2
  simp only [job_deadline_eq_task_deadline] at this
  rw [this, TSK]

theorem interference_bound_edf_j_i_deadline
    {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost : sporadic_task → time)
    (task_deadline : sporadic_task → time)
    {Job : Type v} [DecidableEq Job]
    (job_cost : Job → time)
    (job_deadline : Job → time)
    (job_task : Job → sporadic_task)
    {arr_seq : arrival_sequence Job}
    (H_valid_job_parameters :
      ∀ j : Job, arrives_in arr_seq j →
        valid_sporadic_job task_cost task_deadline job_cost job_deadline job_task j)
    (tsk_i : sporadic_task)
    (j_i : Job)
    (H_j_i_arrives : arrives_in arr_seq j_i)
    (H_job_of_tsk_i : job_task j_i = tsk_i) :
    job_deadline j_i = task_deadline tsk_i := by
  have := (H_valid_job_parameters _ H_j_i_arrives).2.2
  simp only [job_deadline_eq_task_deadline] at this
  rw [this, H_job_of_tsk_i]

theorem interference_bound_edf_j_fst_completion_implies_rt_bound_inside_interval
    {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_period : sporadic_task → time)
    (task_deadline : sporadic_task → time)
    {Job : Type v} [DecidableEq Job]
    (job_arrival : Job → time)
    (job_cost : Job → time)
    (job_task : Job → sporadic_task)
    {arr_seq : arrival_sequence Job}
    (num_cpus : Nat)
    (sched : schedule Job num_cpus)
    (H_jobs_come_from_arrival_sequence : jobs_come_from_arrival_sequence sched arr_seq)
    (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched)
    (tsk_i : sporadic_task)
    (j_i : Job)
    (tsk_k : sporadic_task)
    (R_k : time)
    (delta : time)
    (H_many_jobs : div_ceil (task_deadline tsk_i + R_k - task_deadline tsk_k + 1) (task_period tsk_k) < (((((jobs_scheduled_between sched (job_arrival j_i) (job_arrival j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost sched j_i (j') (job_arrival j_i) (job_arrival j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y)))).length)
    (elem : Job) :
    completed job_cost sched ((((((jobs_scheduled_between sched (job_arrival j_i) (job_arrival j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost sched j_i (j') (job_arrival j_i) (job_arrival j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y)))).getD 0 elem) (job_arrival ((((((jobs_scheduled_between sched (job_arrival j_i) (job_arrival j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost sched j_i (j') (job_arrival j_i) (job_arrival j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y)))).getD 0 elem) + R_k) = true →
    job_arrival j_i ≤ job_arrival ((((((jobs_scheduled_between sched (job_arrival j_i) (job_arrival j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost sched j_i (j') (job_arrival j_i) (job_arrival j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y)))).getD 0 elem) + R_k := by
  intro RBOUND
  by_contra BUG
  obtain ⟨_, _, NZ, _⟩ := interference_bound_edf_j_fst_is_job_of_tsk_k task_period
    task_deadline job_arrival job_cost job_task num_cpus sched
    H_jobs_come_from_arrival_sequence tsk_i j_i tsk_k R_k delta H_many_jobs elem
  have h0 := job_interference_le_service job_arrival job_cost sched j_i ((((((jobs_scheduled_between sched (job_arrival j_i) (job_arrival j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost sched j_i (j') (job_arrival j_i) (job_arrival j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y)))).getD 0 elem) (job_arrival j_i)
    (job_arrival j_i + delta)
  have hz := cumulative_service_after_job_rt_zero job_arrival job_cost sched
    H_completed_jobs_dont_execute _ R_k RBOUND (job_arrival j_i) (job_arrival j_i + delta)
    (by omega')
  unfold service_during at h0
  rw [hz] at h0
  simp only [Bool.not_eq_true', decide_eq_false_iff_not] at NZ
  omega'

/-- LEAN_HELPER: under EDF, a job of `S` has a deadline no later than `j_i`'s. -/
private theorem sorted_job_deadline_le
    {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost : sporadic_task → time)
    (task_deadline : sporadic_task → time)
    {Job : Type v} [DecidableEq Job]
    (job_arrival : Job → time)
    (job_cost : Job → time)
    (job_deadline : Job → time)
    (job_task : Job → sporadic_task)
    {arr_seq : arrival_sequence Job}
    (H_valid_job_parameters :
      ∀ j : Job, arrives_in arr_seq j →
        valid_sporadic_job task_cost task_deadline job_cost job_deadline job_task j)
    (num_cpus : Nat)
    (sched : schedule Job num_cpus)
    (H_jobs_come_from_arrival_sequence : jobs_come_from_arrival_sequence sched arr_seq)
    (H_edf_scheduler :
      respects_JLFP_policy job_arrival job_cost arr_seq sched (EDF job_arrival job_deadline))
    (tsk_i : sporadic_task)
    (j_i : Job)
    (H_j_i_arrives : arrives_in arr_seq j_i)
    (H_job_of_tsk_i : job_task j_i = tsk_i)
    (tsk_k : sporadic_task)
    (delta : time)
    (j : Job) (IN : j ∈ ((((jobs_scheduled_between sched (job_arrival j_i) (job_arrival j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost sched j_i (j') (job_arrival j_i) (job_arrival j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y)))) :
    job_arrival j + task_deadline tsk_k ≤ job_arrival j_i + task_deadline tsk_i := by
  obtain ⟨ARR, TSK, NZ, _⟩ := interference_bound_edf_all_jobs_from_tsk_k job_arrival job_cost
    job_task num_cpus sched H_jobs_come_from_arrival_sequence j_i tsk_k delta j IN
  have LEdl := interference_under_edf_implies_shorter_deadlines job_arrival job_cost job_deadline
    num_cpus sched H_edf_scheduler j j_i _ _ ARR H_j_i_arrives NZ
  have hj := (H_valid_job_parameters _ ARR).2.2
  have hi := (H_valid_job_parameters _ H_j_i_arrives).2.2
  simp only [job_deadline_eq_task_deadline] at hj hi
  rw [hj, TSK, hi, H_job_of_tsk_i] at LEdl
  exact LEdl

/-! ### A single job -/


/-! ### A single job -/

theorem interference_bound_edf_holds_for_a_single_job
    {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost : sporadic_task → time)
    (task_period : sporadic_task → time)
    (task_deadline : sporadic_task → time)
    {Job : Type v} [DecidableEq Job]
    (job_arrival : Job → time)
    (job_cost : Job → time)
    (job_deadline : Job → time)
    (job_task : Job → sporadic_task)
    {arr_seq : arrival_sequence Job}
    (H_valid_job_parameters :
      ∀ j : Job, arrives_in arr_seq j →
        valid_sporadic_job task_cost task_deadline job_cost job_deadline job_task j)
    (num_cpus : Nat)
    (sched : schedule Job num_cpus)
    (H_jobs_come_from_arrival_sequence : jobs_come_from_arrival_sequence sched arr_seq)
    (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched)
    (ts : taskset_of sporadic_task)
    (H_valid_task_parameters :
      valid_sporadic_taskset task_cost task_period task_deadline ts.val)
    (tsk_i : sporadic_task)
    (H_tsk_i_in_task_set : tsk_i ∈ ts)
    (j_i : Job)
    (tsk_k : sporadic_task)
    (H_tsk_k_in_task_set : tsk_k ∈ ts)
    (R_k : time)
    (H_R_k_le_deadline : R_k ≤ task_deadline tsk_k)
    (delta : time)
    (elem : Job)
    (H_only_one_job : (((((jobs_scheduled_between sched (job_arrival j_i) (job_arrival j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost sched j_i (j') (job_arrival j_i) (job_arrival j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y)))).length = 1) :
    job_interference job_arrival job_cost sched j_i (((((((jobs_scheduled_between sched (job_arrival j_i) (job_arrival j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost sched j_i (j') (job_arrival j_i) (job_arrival j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y)))).getD 0 elem)) (job_arrival j_i) (job_arrival j_i + delta) ≤ edf_specific_interference_bound task_cost task_period task_deadline tsk_i tsk_k R_k := by
  have h0 : 0 < (((((jobs_scheduled_between sched (job_arrival j_i) (job_arrival j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost sched j_i (j') (job_arrival j_i) (job_arrival j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y)))).length := by omega
  have LE := interference_bound_edf_interference_le_task_cost task_cost task_deadline job_arrival job_cost
    job_deadline job_task H_valid_job_parameters num_cpus sched H_jobs_come_from_arrival_sequence
    H_completed_jobs_dont_execute j_i tsk_k delta ((((((jobs_scheduled_between sched (job_arrival j_i) (job_arrival j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost sched j_i (j') (job_arrival j_i) (job_arrival j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y)))).getD 0 elem)
    ((sorted_mem job_arrival job_cost job_task num_cpus sched j_i tsk_k delta _).mp
      (by rw [getD_lt h0]; exact List.getElem_mem _))
  have PER : 0 < task_period tsk_k := by
    have := (H_valid_task_parameters tsk_k H_tsk_k_in_task_set).2.1
    simpa [task_period_positive] using this
  have C := ceil_neq0 (task_deadline tsk_i + R_k - task_deadline tsk_k + 1) (task_period tsk_k) (by omega) PER
  unfold edf_specific_interference_bound
  calc job_interference job_arrival job_cost sched j_i (((((((jobs_scheduled_between sched (job_arrival j_i) (job_arrival j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost sched j_i (j') (job_arrival j_i) (job_arrival j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y)))).getD 0 elem)) (job_arrival j_i) (job_arrival j_i + delta)
      ≤ task_cost tsk_k := LE
    _ = 1 * task_cost tsk_k := (Nat.one_mul _).symm
    _ ≤ _ := Nat.mul_le_mul_right _ C

/-! ### Two or more jobs -/

theorem interference_bound_edf_j_lst_is_job_of_tsk_k
    {sporadic_task : Type u} [DecidableEq sporadic_task]
    {Job : Type v} [DecidableEq Job]
    (job_arrival : Job → time)
    (job_cost : Job → time)
    (job_task : Job → sporadic_task)
    {arr_seq : arrival_sequence Job}
    (num_cpus : Nat)
    (sched : schedule Job num_cpus)
    (H_jobs_come_from_arrival_sequence : jobs_come_from_arrival_sequence sched arr_seq)
    (j_i : Job)
    (tsk_k : sporadic_task)
    (delta : time)
    (elem : Job)
    (num_mid_jobs : Nat)
    (H_at_least_two_jobs : (((((jobs_scheduled_between sched (job_arrival j_i) (job_arrival j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost sched j_i (j') (job_arrival j_i) (job_arrival j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y)))).length = num_mid_jobs + 2) :
    arrives_in arr_seq ((((((jobs_scheduled_between sched (job_arrival j_i) (job_arrival j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost sched j_i (j') (job_arrival j_i) (job_arrival j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y)))).getD (num_mid_jobs + 1) elem) ∧
    job_task ((((((jobs_scheduled_between sched (job_arrival j_i) (job_arrival j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost sched j_i (j') (job_arrival j_i) (job_arrival j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y)))).getD (num_mid_jobs + 1) elem) = tsk_k ∧
    (!decide (job_interference job_arrival job_cost sched j_i (((((((jobs_scheduled_between sched (job_arrival j_i) (job_arrival j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost sched j_i (j') (job_arrival j_i) (job_arrival j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y)))).getD (num_mid_jobs + 1) elem)) (job_arrival j_i) (job_arrival j_i + delta) = 0)) = true ∧
    ((((((jobs_scheduled_between sched (job_arrival j_i) (job_arrival j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost sched j_i (j') (job_arrival j_i) (job_arrival j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y)))).getD (num_mid_jobs + 1) elem) ∈ jobs_scheduled_between sched (job_arrival j_i) (job_arrival j_i + delta) := by
  apply interference_bound_edf_all_jobs_from_tsk_k job_arrival job_cost job_task num_cpus
    sched H_jobs_come_from_arrival_sequence j_i tsk_k delta
  rw [getD_lt (by omega)]
  exact List.getElem_mem _

theorem interference_bound_edf_j_lst_deadline
    {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost : sporadic_task → time)
    (task_deadline : sporadic_task → time)
    {Job : Type v} [DecidableEq Job]
    (job_arrival : Job → time)
    (job_cost : Job → time)
    (job_deadline : Job → time)
    (job_task : Job → sporadic_task)
    {arr_seq : arrival_sequence Job}
    (H_valid_job_parameters :
      ∀ j : Job, arrives_in arr_seq j →
        valid_sporadic_job task_cost task_deadline job_cost job_deadline job_task j)
    (num_cpus : Nat)
    (sched : schedule Job num_cpus)
    (H_jobs_come_from_arrival_sequence : jobs_come_from_arrival_sequence sched arr_seq)
    (j_i : Job)
    (tsk_k : sporadic_task)
    (delta : time)
    (elem : Job)
    (num_mid_jobs : Nat)
    (H_at_least_two_jobs : (((((jobs_scheduled_between sched (job_arrival j_i) (job_arrival j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost sched j_i (j') (job_arrival j_i) (job_arrival j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y)))).length = num_mid_jobs + 2) :
    job_deadline ((((((jobs_scheduled_between sched (job_arrival j_i) (job_arrival j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost sched j_i (j') (job_arrival j_i) (job_arrival j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y)))).getD (num_mid_jobs + 1) elem) = task_deadline tsk_k := by
  obtain ⟨ARR, TSK, _, _⟩ := interference_bound_edf_j_lst_is_job_of_tsk_k job_arrival job_cost
    job_task num_cpus sched H_jobs_come_from_arrival_sequence j_i tsk_k delta elem
    num_mid_jobs H_at_least_two_jobs
  have := (H_valid_job_parameters _ ARR).2.2
  simp only [job_deadline_eq_task_deadline] at this
  rw [this, TSK]

theorem interference_bound_edf_j_fst_before_j_lst
    {sporadic_task : Type u} [DecidableEq sporadic_task]
    {Job : Type v} [DecidableEq Job]
    (job_arrival : Job → time)
    (job_cost : Job → time)
    (job_task : Job → sporadic_task)
    (num_cpus : Nat)
    (sched : schedule Job num_cpus)
    (j_i : Job)
    (tsk_k : sporadic_task)
    (delta : time)
    (elem : Job)
    (num_mid_jobs : Nat)
    (H_at_least_two_jobs : (((((jobs_scheduled_between sched (job_arrival j_i) (job_arrival j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost sched j_i (j') (job_arrival j_i) (job_arrival j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y)))).length = num_mid_jobs + 2) :
    job_arrival ((((((jobs_scheduled_between sched (job_arrival j_i) (job_arrival j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost sched j_i (j') (job_arrival j_i) (job_arrival j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y)))).getD 0 elem) ≤ job_arrival ((((((jobs_scheduled_between sched (job_arrival j_i) (job_arrival j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost sched j_i (j') (job_arrival j_i) (job_arrival j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y)))).getD (num_mid_jobs + 1) elem) := by
  have := Prosa.Classic.Util.Sorting.prev_le_next job_arrival (((((jobs_scheduled_between sched (job_arrival j_i) (job_arrival j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost sched j_i (j') (job_arrival j_i) (job_arrival j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y)))) elem 0 (num_mid_jobs + 1)
    (fun i hi => interference_bound_edf_jobs_ordered_by_arrival job_arrival job_cost job_task
      num_cpus sched j_i tsk_k delta i elem hi) (by omega)
  simpa using this

theorem interference_bound_edf_last_job_arrives_before_end_of_interval
    {sporadic_task : Type u} [DecidableEq sporadic_task]
    {Job : Type v} [DecidableEq Job]
    (job_arrival : Job → time)
    (job_cost : Job → time)
    (job_task : Job → sporadic_task)
    {arr_seq : arrival_sequence Job}
    (num_cpus : Nat)
    (sched : schedule Job num_cpus)
    (H_jobs_come_from_arrival_sequence : jobs_come_from_arrival_sequence sched arr_seq)
    (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute job_arrival sched)
    (j_i : Job)
    (tsk_k : sporadic_task)
    (delta : time)
    (elem : Job)
    (num_mid_jobs : Nat)
    (H_at_least_two_jobs : (((((jobs_scheduled_between sched (job_arrival j_i) (job_arrival j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost sched j_i (j') (job_arrival j_i) (job_arrival j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y)))).length = num_mid_jobs + 2) :
    job_arrival ((((((jobs_scheduled_between sched (job_arrival j_i) (job_arrival j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost sched j_i (j') (job_arrival j_i) (job_arrival j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y)))).getD (num_mid_jobs + 1) elem) < job_arrival j_i + delta := by
  obtain ⟨_, _, NZ, _⟩ := interference_bound_edf_j_lst_is_job_of_tsk_k job_arrival job_cost
    job_task num_cpus sched H_jobs_come_from_arrival_sequence j_i tsk_k delta elem
    num_mid_jobs H_at_least_two_jobs
  exact interfering_job_arrives_before job_arrival job_cost num_cpus sched
    H_jobs_must_arrive_to_execute j_i _ _ _ NZ

theorem interference_bound_edf_j_fst_completed_on_time
    {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_period : sporadic_task → time)
    (task_deadline : sporadic_task → time)
    {Job : Type v} [DecidableEq Job]
    (job_arrival : Job → time)
    (job_cost : Job → time)
    (job_task : Job → sporadic_task)
    {arr_seq : arrival_sequence Job}
    (H_sporadic_tasks : sporadic_task_model task_period job_arrival job_task arr_seq)
    (num_cpus : Nat)
    (sched : schedule Job num_cpus)
    (H_jobs_come_from_arrival_sequence : jobs_come_from_arrival_sequence sched arr_seq)
    (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute job_arrival sched)
    (ts : taskset_of sporadic_task)
    (H_constrained_deadlines :
      ∀ tsk : sporadic_task, tsk ∈ ts → task_deadline tsk ≤ task_period tsk)
    (tsk_i : sporadic_task)
    (j_i : Job)
    (tsk_k : sporadic_task)
    (H_tsk_k_in_task_set : tsk_k ∈ ts)
    (R_k : time)
    (H_R_k_le_deadline : R_k ≤ task_deadline tsk_k)
    (delta : time)
    (H_all_previous_jobs_completed_on_time :
      ∀ j_k : Job, arrives_in arr_seq j_k → job_task j_k = tsk_k →
        job_arrival j_k + R_k < job_arrival j_i + delta →
        completed job_cost sched j_k (job_arrival j_k + R_k) = true)
    (H_many_jobs : div_ceil (task_deadline tsk_i + R_k - task_deadline tsk_k + 1) (task_period tsk_k) < (((((jobs_scheduled_between sched (job_arrival j_i) (job_arrival j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost sched j_i (j') (job_arrival j_i) (job_arrival j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y)))).length)
    (elem : Job)
    (num_mid_jobs : Nat)
    (H_at_least_two_jobs : (((((jobs_scheduled_between sched (job_arrival j_i) (job_arrival j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost sched j_i (j') (job_arrival j_i) (job_arrival j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y)))).length = num_mid_jobs + 2) :
    completed job_cost sched ((((((jobs_scheduled_between sched (job_arrival j_i) (job_arrival j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost sched j_i (j') (job_arrival j_i) (job_arrival j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y)))).getD 0 elem) (job_arrival ((((((jobs_scheduled_between sched (job_arrival j_i) (job_arrival j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost sched j_i (j') (job_arrival j_i) (job_arrival j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y)))).getD 0 elem) + R_k) = true := by
  have h0 : 0 < (((((jobs_scheduled_between sched (job_arrival j_i) (job_arrival j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost sched j_i (j') (job_arrival j_i) (job_arrival j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y)))).length := by omega
  have h1 : 1 < (((((jobs_scheduled_between sched (job_arrival j_i) (job_arrival j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost sched j_i (j') (job_arrival j_i) (job_arrival j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y)))).length := by omega
  obtain ⟨FSTarr, FSTtsk, _, _⟩ := interference_bound_edf_all_jobs_from_tsk_k job_arrival
    job_cost job_task num_cpus sched H_jobs_come_from_arrival_sequence j_i tsk_k delta
    ((((((jobs_scheduled_between sched (job_arrival j_i) (job_arrival j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost sched j_i (j') (job_arrival j_i) (job_arrival j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y)))).getD 0 elem) (by rw [getD_lt h0]; exact List.getElem_mem _)
  obtain ⟨SNDarr, SNDtsk, SNDnz, _⟩ := interference_bound_edf_all_jobs_from_tsk_k job_arrival
    job_cost job_task num_cpus sched H_jobs_come_from_arrival_sequence j_i tsk_k delta
    ((((((jobs_scheduled_between sched (job_arrival j_i) (job_arrival j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost sched j_i (j') (job_arrival j_i) (job_arrival j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y)))).getD 1 elem) (by rw [getD_lt h1]; exact List.getElem_mem _)
  have SNDbefore := interfering_job_arrives_before job_arrival job_cost num_cpus sched
    H_jobs_must_arrive_to_execute j_i _ _ _ SNDnz
  have ORD := interference_bound_edf_jobs_ordered_by_arrival job_arrival job_cost job_task
    num_cpus sched j_i tsk_k delta 0 elem (by omega)
  have DIFF : ((((((jobs_scheduled_between sched (job_arrival j_i) (job_arrival j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost sched j_i (j') (job_arrival j_i) (job_arrival j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y)))).getD 0 elem) ≠ (((((jobs_scheduled_between sched (job_arrival j_i) (job_arrival j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost sched j_i (j') (job_arrival j_i) (job_arrival j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y)))).getD 1 elem := by
    rw [getD_lt h0, getD_lt h1]
    intro EQ
    have := (List.Nodup.getElem_inj_iff (sorted_nodup job_arrival job_cost job_task num_cpus
      sched j_i tsk_k delta)).mp EQ
    omega
  have SPO := H_sporadic_tasks _ _ DIFF FSTarr SNDarr (FSTtsk.trans SNDtsk.symm) ORD
  rw [FSTtsk] at SPO
  have hD := H_constrained_deadlines tsk_k H_tsk_k_in_task_set
  exact H_all_previous_jobs_completed_on_time _ FSTarr FSTtsk (by simp only [Nat.zero_add] at *; omega')

theorem interference_bound_edf_many_periods_in_between
    {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost : sporadic_task → time)
    (task_period : sporadic_task → time)
    (task_deadline : sporadic_task → time)
    {Job : Type v} [DecidableEq Job]
    (job_arrival : Job → time)
    (job_cost : Job → time)
    (job_deadline : Job → time)
    (job_task : Job → sporadic_task)
    {arr_seq : arrival_sequence Job}
    (H_sporadic_tasks : sporadic_task_model task_period job_arrival job_task arr_seq)
    (num_cpus : Nat)
    (sched : schedule Job num_cpus)
    (H_jobs_come_from_arrival_sequence : jobs_come_from_arrival_sequence sched arr_seq)
    (H_at_least_one_cpu : 0 < num_cpus)
    (ts : taskset_of sporadic_task)
    (tsk_i : sporadic_task)
    (H_tsk_i_in_task_set : tsk_i ∈ ts)
    (j_i : Job)
    (tsk_k : sporadic_task)
    (H_tsk_k_in_task_set : tsk_k ∈ ts)
    (R_k : time)
    (H_R_k_le_deadline : R_k ≤ task_deadline tsk_k)
    (delta : time)
    (H_delta_le_deadline : delta ≤ task_deadline tsk_i)
    (H_many_jobs : div_ceil (task_deadline tsk_i + R_k - task_deadline tsk_k + 1) (task_period tsk_k) < (((((jobs_scheduled_between sched (job_arrival j_i) (job_arrival j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost sched j_i (j') (job_arrival j_i) (job_arrival j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y)))).length)
    (elem : Job)
    (num_mid_jobs : Nat)
    (H_at_least_two_jobs : (((((jobs_scheduled_between sched (job_arrival j_i) (job_arrival j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost sched j_i (j') (job_arrival j_i) (job_arrival j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y)))).length = num_mid_jobs + 2) :
    (num_mid_jobs + 1) * task_period tsk_k ≤ job_arrival ((((((jobs_scheduled_between sched (job_arrival j_i) (job_arrival j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost sched j_i (j') (job_arrival j_i) (job_arrival j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y)))).getD (num_mid_jobs + 1) elem) - job_arrival ((((((jobs_scheduled_between sched (job_arrival j_i) (job_arrival j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost sched j_i (j') (job_arrival j_i) (job_arrival j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y)))).getD 0 elem) := by
  have hlen : (((((jobs_scheduled_between sched (job_arrival j_i) (job_arrival j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost sched j_i (j') (job_arrival j_i) (job_arrival j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y)))).length - 1 = num_mid_jobs + 1 := by omega
  have TEL := Prosa.Classic.Util.Sum.telescoping_sum Job job_arrival (((((jobs_scheduled_between sched (job_arrival j_i) (job_arrival j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost sched j_i (j') (job_arrival j_i) (job_arrival j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y)))) elem
    (fun i hi => interference_bound_edf_jobs_ordered_by_arrival job_arrival job_cost job_task
      num_cpus sched j_i tsk_k delta i elem hi)
  rw [hlen] at TEL
  rw [TEL]
  have hnd := sorted_nodup job_arrival job_cost job_task num_cpus sched j_i tsk_k delta
  calc (num_mid_jobs + 1) * task_period tsk_k
      = ∑ _i ∈ Finset.Ico 0 (num_mid_jobs + 1), task_period tsk_k := by simp
    _ ≤ _ := by
        apply Finset.sum_le_sum
        intro i hi
        rw [Finset.mem_Ico] at hi
        have h1 : i < (((((jobs_scheduled_between sched (job_arrival j_i) (job_arrival j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost sched j_i (j') (job_arrival j_i) (job_arrival j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y)))).length := by omega
        have h2 : i + 1 < (((((jobs_scheduled_between sched (job_arrival j_i) (job_arrival j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost sched j_i (j') (job_arrival j_i) (job_arrival j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y)))).length := by omega
        obtain ⟨CURarr, CURtsk, _, _⟩ := interference_bound_edf_all_jobs_from_tsk_k job_arrival
          job_cost job_task num_cpus sched H_jobs_come_from_arrival_sequence j_i tsk_k
          delta ((((((jobs_scheduled_between sched (job_arrival j_i) (job_arrival j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost sched j_i (j') (job_arrival j_i) (job_arrival j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y)))).getD i elem) (by rw [getD_lt h1]; exact List.getElem_mem _)
        obtain ⟨NEXTarr, NEXTtsk, _, _⟩ := interference_bound_edf_all_jobs_from_tsk_k job_arrival
          job_cost job_task num_cpus sched H_jobs_come_from_arrival_sequence j_i tsk_k
          delta ((((((jobs_scheduled_between sched (job_arrival j_i) (job_arrival j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost sched j_i (j') (job_arrival j_i) (job_arrival j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y)))).getD (i + 1) elem) (by rw [getD_lt h2]; exact List.getElem_mem _)
        have ARRle := interference_bound_edf_jobs_ordered_by_arrival job_arrival job_cost job_task
          num_cpus sched j_i tsk_k delta i elem (by omega)
        have DIFF : (((((jobs_scheduled_between sched (job_arrival j_i) (job_arrival j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost sched j_i (j') (job_arrival j_i) (job_arrival j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y)))).getD i elem ≠ (((((jobs_scheduled_between sched (job_arrival j_i) (job_arrival j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost sched j_i (j') (job_arrival j_i) (job_arrival j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y)))).getD (i + 1) elem := by
          rw [getD_lt h1, getD_lt h2]
          intro EQ
          have := (List.Nodup.getElem_inj_iff hnd).mp EQ
          omega
        have SPO := H_sporadic_tasks _ _ DIFF CURarr NEXTarr (CURtsk.trans NEXTtsk.symm) ARRle
        rw [CURtsk] at SPO
        omega'


theorem interference_bound_edf_slack_le_delta
    {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost : sporadic_task → time)
    (task_period : sporadic_task → time)
    (task_deadline : sporadic_task → time)
    {Job : Type v} [DecidableEq Job]
    (job_arrival : Job → time)
    (job_cost : Job → time)
    (job_deadline : Job → time)
    (job_task : Job → sporadic_task)
    {arr_seq : arrival_sequence Job}
    (H_sporadic_tasks : sporadic_task_model task_period job_arrival job_task arr_seq)
    (H_valid_job_parameters :
      ∀ j : Job, arrives_in arr_seq j →
        valid_sporadic_job task_cost task_deadline job_cost job_deadline job_task j)
    (num_cpus : Nat)
    (sched : schedule Job num_cpus)
    (H_jobs_come_from_arrival_sequence : jobs_come_from_arrival_sequence sched arr_seq)
    (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute job_arrival sched)
    (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched)
    (ts : taskset_of sporadic_task)
    (H_constrained_deadlines :
      ∀ tsk : sporadic_task, tsk ∈ ts → task_deadline tsk ≤ task_period tsk)
    (H_edf_scheduler :
      respects_JLFP_policy job_arrival job_cost arr_seq sched (EDF job_arrival job_deadline))
    (tsk_i : sporadic_task)
    (j_i : Job)
    (H_j_i_arrives : arrives_in arr_seq j_i)
    (H_job_of_tsk_i : job_task j_i = tsk_i)
    (tsk_k : sporadic_task)
    (H_tsk_k_in_task_set : tsk_k ∈ ts)
    (R_k : time)
    (H_R_k_le_deadline : R_k ≤ task_deadline tsk_k)
    (delta : time)
    (H_all_previous_jobs_completed_on_time :
      ∀ j_k : Job, arrives_in arr_seq j_k → job_task j_k = tsk_k →
        job_arrival j_k + R_k < job_arrival j_i + delta →
        completed job_cost sched j_k (job_arrival j_k + R_k) = true)
    (H_many_jobs : div_ceil (task_deadline tsk_i + R_k - task_deadline tsk_k + 1) (task_period tsk_k) < (((((jobs_scheduled_between sched (job_arrival j_i) (job_arrival j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost sched j_i (j') (job_arrival j_i) (job_arrival j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y)))).length)
    (elem : Job)
    (num_mid_jobs : Nat)
    (H_at_least_two_jobs : (((((jobs_scheduled_between sched (job_arrival j_i) (job_arrival j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost sched j_i (j') (job_arrival j_i) (job_arrival j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y)))).length = num_mid_jobs + 2) :
    task_deadline tsk_k - R_k ≤ task_deadline tsk_i := by
  have COMPL := interference_bound_edf_j_fst_completed_on_time task_period task_deadline job_arrival job_cost job_task
    H_sporadic_tasks num_cpus sched H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute ts
    H_constrained_deadlines tsk_i j_i tsk_k H_tsk_k_in_task_set R_k H_R_k_le_deadline delta
    H_all_previous_jobs_completed_on_time H_many_jobs elem num_mid_jobs H_at_least_two_jobs
  have AFTER := interference_bound_edf_j_fst_completion_implies_rt_bound_inside_interval task_period task_deadline
    job_arrival job_cost job_task num_cpus sched H_jobs_come_from_arrival_sequence H_completed_jobs_dont_execute
    tsk_i j_i tsk_k R_k delta H_many_jobs elem COMPL
  obtain ⟨ARR, TSK, NZ, _⟩ := interference_bound_edf_j_fst_is_job_of_tsk_k task_period task_deadline job_arrival
    job_cost job_task num_cpus sched H_jobs_come_from_arrival_sequence tsk_i j_i tsk_k R_k delta H_many_jobs elem
  have LEdl := interference_under_edf_implies_shorter_deadlines job_arrival job_cost job_deadline
    num_cpus sched H_edf_scheduler _ j_i _ _ ARR H_j_i_arrives NZ
  rw [interference_bound_edf_j_fst_deadline task_cost task_period task_deadline job_arrival job_cost job_deadline
      job_task H_valid_job_parameters num_cpus sched H_jobs_come_from_arrival_sequence tsk_i j_i tsk_k R_k delta
      H_many_jobs elem,
    interference_bound_edf_j_i_deadline task_cost task_deadline job_cost job_deadline job_task
      H_valid_job_parameters tsk_i j_i H_j_i_arrives H_job_of_tsk_i] at LEdl
  omega'

theorem interference_bound_edf_n_k_covers_all_jobs
    {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost : sporadic_task → time)
    (task_period : sporadic_task → time)
    (task_deadline : sporadic_task → time)
    {Job : Type v} [DecidableEq Job]
    (job_arrival : Job → time)
    (job_cost : Job → time)
    (job_deadline : Job → time)
    (job_task : Job → sporadic_task)
    {arr_seq : arrival_sequence Job}
    (H_sporadic_tasks : sporadic_task_model task_period job_arrival job_task arr_seq)
    (H_valid_job_parameters :
      ∀ j : Job, arrives_in arr_seq j →
        valid_sporadic_job task_cost task_deadline job_cost job_deadline job_task j)
    (num_cpus : Nat)
    (sched : schedule Job num_cpus)
    (H_jobs_come_from_arrival_sequence : jobs_come_from_arrival_sequence sched arr_seq)
    (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute job_arrival sched)
    (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched)
    (H_at_least_one_cpu : 0 < num_cpus)
    (ts : taskset_of sporadic_task)
    (H_valid_task_parameters :
      valid_sporadic_taskset task_cost task_period task_deadline ts.val)
    (H_constrained_deadlines :
      ∀ tsk : sporadic_task, tsk ∈ ts → task_deadline tsk ≤ task_period tsk)
    (H_edf_scheduler :
      respects_JLFP_policy job_arrival job_cost arr_seq sched (EDF job_arrival job_deadline))
    (tsk_i : sporadic_task)
    (H_tsk_i_in_task_set : tsk_i ∈ ts)
    (j_i : Job)
    (H_j_i_arrives : arrives_in arr_seq j_i)
    (H_job_of_tsk_i : job_task j_i = tsk_i)
    (tsk_k : sporadic_task)
    (H_tsk_k_in_task_set : tsk_k ∈ ts)
    (R_k : time)
    (H_R_k_le_deadline : R_k ≤ task_deadline tsk_k)
    (delta : time)
    (H_delta_le_deadline : delta ≤ task_deadline tsk_i)
    (H_all_previous_jobs_completed_on_time :
      ∀ j_k : Job, arrives_in arr_seq j_k → job_task j_k = tsk_k →
        job_arrival j_k + R_k < job_arrival j_i + delta →
        completed job_cost sched j_k (job_arrival j_k + R_k) = true)
    (H_many_jobs : div_ceil (task_deadline tsk_i + R_k - task_deadline tsk_k + 1) (task_period tsk_k) < (((((jobs_scheduled_between sched (job_arrival j_i) (job_arrival j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost sched j_i (j') (job_arrival j_i) (job_arrival j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y)))).length)
    (elem : Job)
    (num_mid_jobs : Nat)
    (H_at_least_two_jobs : (((((jobs_scheduled_between sched (job_arrival j_i) (job_arrival j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost sched j_i (j') (job_arrival j_i) (job_arrival j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y)))).length = num_mid_jobs + 2) :
    num_mid_jobs + 2 ≤ div_ceil (task_deadline tsk_i + R_k - task_deadline tsk_k + 1) (task_period tsk_k) := by
  by_contra LTnk
  have DIST := interference_bound_edf_many_periods_in_between task_cost task_period task_deadline job_arrival
    job_cost job_deadline job_task H_sporadic_tasks num_cpus sched H_jobs_come_from_arrival_sequence
    H_at_least_one_cpu ts tsk_i H_tsk_i_in_task_set j_i tsk_k H_tsk_k_in_task_set R_k H_R_k_le_deadline delta
    H_delta_le_deadline H_many_jobs elem num_mid_jobs H_at_least_two_jobs
  have SLACK := interference_bound_edf_slack_le_delta task_cost task_period task_deadline job_arrival job_cost
    job_deadline job_task H_sporadic_tasks H_valid_job_parameters num_cpus sched H_jobs_come_from_arrival_sequence
    H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute ts H_constrained_deadlines H_edf_scheduler tsk_i j_i
    H_j_i_arrives H_job_of_tsk_i tsk_k H_tsk_k_in_task_set R_k H_R_k_le_deadline delta
    H_all_previous_jobs_completed_on_time H_many_jobs elem num_mid_jobs H_at_least_two_jobs
  have COMPL := interference_bound_edf_j_fst_completed_on_time task_period task_deadline job_arrival job_cost job_task
    H_sporadic_tasks num_cpus sched H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute ts
    H_constrained_deadlines tsk_i j_i tsk_k H_tsk_k_in_task_set R_k H_R_k_le_deadline delta
    H_all_previous_jobs_completed_on_time H_many_jobs elem num_mid_jobs H_at_least_two_jobs
  have AFTER := interference_bound_edf_j_fst_completion_implies_rt_bound_inside_interval task_period task_deadline
    job_arrival job_cost job_task num_cpus sched H_jobs_come_from_arrival_sequence H_completed_jobs_dont_execute
    tsk_i j_i tsk_k R_k delta H_many_jobs elem COMPL
  have BEFORE := interference_bound_edf_j_fst_before_j_lst job_arrival job_cost job_task num_cpus sched j_i tsk_k
    delta elem num_mid_jobs H_at_least_two_jobs
  obtain ⟨ARRl, TSKl, NZl, _⟩ := interference_bound_edf_j_lst_is_job_of_tsk_k job_arrival job_cost job_task num_cpus
    sched H_jobs_come_from_arrival_sequence j_i tsk_k delta elem num_mid_jobs H_at_least_two_jobs
  have LEdl := interference_under_edf_implies_shorter_deadlines job_arrival job_cost job_deadline
    num_cpus sched H_edf_scheduler _ j_i _ _ ARRl H_j_i_arrives NZl
  rw [interference_bound_edf_j_lst_deadline task_cost task_deadline job_arrival job_cost job_deadline job_task
      H_valid_job_parameters num_cpus sched H_jobs_come_from_arrival_sequence j_i tsk_k delta elem num_mid_jobs
      H_at_least_two_jobs,
    interference_bound_edf_j_i_deadline task_cost task_deadline job_cost job_deadline job_task
      H_valid_job_parameters tsk_i j_i H_j_i_arrives H_job_of_tsk_i] at LEdl
  have PER : 0 < task_period tsk_k := by
    have := (H_valid_task_parameters tsk_k H_tsk_k_in_task_set).2.1
    simpa [task_period_positive] using this
  have CEIL := div_ceil_mul_ge (task_deadline tsk_i + R_k - task_deadline tsk_k + 1) (task_period tsk_k) PER
  have MUL : div_ceil (task_deadline tsk_i + R_k - task_deadline tsk_k + 1) (task_period tsk_k) * task_period tsk_k ≤ (num_mid_jobs + 1) * task_period tsk_k :=
    Nat.mul_le_mul_right _ (by omega)
  omega'

theorem interference_bound_edf_holds_for_multiple_jobs
    {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost : sporadic_task → time)
    (task_period : sporadic_task → time)
    (task_deadline : sporadic_task → time)
    {Job : Type v} [DecidableEq Job]
    (job_arrival : Job → time)
    (job_cost : Job → time)
    (job_deadline : Job → time)
    (job_task : Job → sporadic_task)
    {arr_seq : arrival_sequence Job}
    (H_sporadic_tasks : sporadic_task_model task_period job_arrival job_task arr_seq)
    (H_valid_job_parameters :
      ∀ j : Job, arrives_in arr_seq j →
        valid_sporadic_job task_cost task_deadline job_cost job_deadline job_task j)
    (num_cpus : Nat)
    (sched : schedule Job num_cpus)
    (H_jobs_come_from_arrival_sequence : jobs_come_from_arrival_sequence sched arr_seq)
    (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute job_arrival sched)
    (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched)
    (H_at_least_one_cpu : 0 < num_cpus)
    (ts : taskset_of sporadic_task)
    (H_valid_task_parameters :
      valid_sporadic_taskset task_cost task_period task_deadline ts.val)
    (H_constrained_deadlines :
      ∀ tsk : sporadic_task, tsk ∈ ts → task_deadline tsk ≤ task_period tsk)
    (H_edf_scheduler :
      respects_JLFP_policy job_arrival job_cost arr_seq sched (EDF job_arrival job_deadline))
    (tsk_i : sporadic_task)
    (H_tsk_i_in_task_set : tsk_i ∈ ts)
    (j_i : Job)
    (H_j_i_arrives : arrives_in arr_seq j_i)
    (H_job_of_tsk_i : job_task j_i = tsk_i)
    (tsk_k : sporadic_task)
    (H_tsk_k_in_task_set : tsk_k ∈ ts)
    (R_k : time)
    (H_R_k_le_deadline : R_k ≤ task_deadline tsk_k)
    (delta : time)
    (H_delta_le_deadline : delta ≤ task_deadline tsk_i)
    (H_all_previous_jobs_completed_on_time :
      ∀ j_k : Job, arrives_in arr_seq j_k → job_task j_k = tsk_k →
        job_arrival j_k + R_k < job_arrival j_i + delta →
        completed job_cost sched j_k (job_arrival j_k + R_k) = true)
    (H_many_jobs : div_ceil (task_deadline tsk_i + R_k - task_deadline tsk_k + 1) (task_period tsk_k) < (((((jobs_scheduled_between sched (job_arrival j_i) (job_arrival j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost sched j_i (j') (job_arrival j_i) (job_arrival j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y)))).length)
    (elem : Job)
    (num_mid_jobs : Nat)
    (H_at_least_two_jobs : (((((jobs_scheduled_between sched (job_arrival j_i) (job_arrival j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost sched j_i (j') (job_arrival j_i) (job_arrival j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y)))).length = num_mid_jobs + 2) :
    ∑ i ∈ Finset.Ico 0 (num_mid_jobs + 2), job_interference job_arrival job_cost sched j_i (((((((jobs_scheduled_between sched (job_arrival j_i) (job_arrival j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost sched j_i (j') (job_arrival j_i) (job_arrival j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y)))).getD i elem)) (job_arrival j_i) (job_arrival j_i + delta) ≤ edf_specific_interference_bound task_cost task_period task_deadline tsk_i tsk_k R_k := by
  have COVER := interference_bound_edf_n_k_covers_all_jobs task_cost task_period task_deadline job_arrival job_cost job_deadline job_task H_sporadic_tasks H_valid_job_parameters num_cpus sched H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_at_least_one_cpu ts H_valid_task_parameters H_constrained_deadlines H_edf_scheduler tsk_i H_tsk_i_in_task_set j_i H_j_i_arrives H_job_of_tsk_i tsk_k H_tsk_k_in_task_set R_k H_R_k_le_deadline delta H_delta_le_deadline H_all_previous_jobs_completed_on_time H_many_jobs elem num_mid_jobs
    H_at_least_two_jobs
  have EACH : ∀ i ∈ Finset.Ico 0 (num_mid_jobs + 2), job_interference job_arrival job_cost sched j_i (((((((jobs_scheduled_between sched (job_arrival j_i) (job_arrival j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost sched j_i (j') (job_arrival j_i) (job_arrival j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y)))).getD i elem)) (job_arrival j_i) (job_arrival j_i + delta) ≤ task_cost tsk_k := by
    intro i hi
    rw [Finset.mem_Ico] at hi
    have hl : i < (((((jobs_scheduled_between sched (job_arrival j_i) (job_arrival j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost sched j_i (j') (job_arrival j_i) (job_arrival j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y)))).length := by omega
    exact interference_bound_edf_interference_le_task_cost task_cost task_deadline job_arrival job_cost
      job_deadline job_task H_valid_job_parameters num_cpus sched H_jobs_come_from_arrival_sequence
      H_completed_jobs_dont_execute j_i tsk_k delta _
      ((sorted_mem job_arrival job_cost job_task num_cpus sched j_i tsk_k delta _).mp
        (by rw [getD_lt hl]; exact List.getElem_mem _))
  have SUM := Finset.sum_le_sum EACH
  simp only [Finset.sum_const, Nat.card_Ico, smul_eq_mul, Nat.sub_zero] at SUM
  unfold edf_specific_interference_bound
  have := Nat.mul_le_mul_right (task_cost tsk_k) COVER
  omega'

/-! ### The interference bound -/

theorem interference_bound_edf_bounds_interference
    {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost : sporadic_task → time)
    (task_period : sporadic_task → time)
    (task_deadline : sporadic_task → time)
    {Job : Type v} [DecidableEq Job]
    (job_arrival : Job → time)
    (job_cost : Job → time)
    (job_deadline : Job → time)
    (job_task : Job → sporadic_task)
    {arr_seq : arrival_sequence Job}
    (H_sporadic_tasks : sporadic_task_model task_period job_arrival job_task arr_seq)
    (H_valid_job_parameters :
      ∀ j : Job, arrives_in arr_seq j →
        valid_sporadic_job task_cost task_deadline job_cost job_deadline job_task j)
    (num_cpus : Nat)
    (sched : schedule Job num_cpus)
    (H_jobs_come_from_arrival_sequence : jobs_come_from_arrival_sequence sched arr_seq)
    (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute job_arrival sched)
    (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched)
    (H_at_least_one_cpu : 0 < num_cpus)
    (ts : taskset_of sporadic_task)
    (H_valid_task_parameters :
      valid_sporadic_taskset task_cost task_period task_deadline ts.val)
    (H_constrained_deadlines :
      ∀ tsk : sporadic_task, tsk ∈ ts → task_deadline tsk ≤ task_period tsk)
    (H_edf_scheduler :
      respects_JLFP_policy job_arrival job_cost arr_seq sched (EDF job_arrival job_deadline))
    (tsk_i : sporadic_task)
    (H_tsk_i_in_task_set : tsk_i ∈ ts)
    (j_i : Job)
    (H_j_i_arrives : arrives_in arr_seq j_i)
    (H_job_of_tsk_i : job_task j_i = tsk_i)
    (tsk_k : sporadic_task)
    (H_tsk_k_in_task_set : tsk_k ∈ ts)
    (R_k : time)
    (H_R_k_le_deadline : R_k ≤ task_deadline tsk_k)
    (delta : time)
    (H_delta_le_deadline : delta ≤ task_deadline tsk_i)
    (H_all_previous_jobs_completed_on_time :
      ∀ j_k : Job, arrives_in arr_seq j_k → job_task j_k = tsk_k →
        job_arrival j_k + R_k < job_arrival j_i + delta →
        completed job_cost sched j_k (job_arrival j_k + R_k) = true)
 :
    task_interference job_arrival job_cost job_task sched j_i tsk_k (job_arrival j_i) (job_arrival j_i + delta) ≤ edf_specific_interference_bound task_cost task_period task_deadline tsk_i tsk_k R_k := by
  have h1 := interference_bound_edf_use_another_definition job_arrival job_cost job_task num_cpus
    sched j_i tsk_k delta
  rw [interference_bound_edf_simpl_by_filtering_interfering_jobs job_arrival job_cost job_task
    num_cpus sched j_i tsk_k delta,
    interference_bound_edf_simpl_by_sorting_interfering_jobs job_arrival job_cost job_task
    num_cpus sched j_i tsk_k delta] at h1
  refine le_trans h1 ?_
  by_cases NUM : (((((jobs_scheduled_between sched (job_arrival j_i) (job_arrival j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost sched j_i (j') (job_arrival j_i) (job_arrival j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y)))).length ≤ div_ceil (task_deadline tsk_i + R_k - task_deadline tsk_k + 1) (task_period tsk_k)
  · exact interference_bound_edf_holds_for_at_most_n_k_jobs task_cost task_period task_deadline
      job_arrival job_cost job_deadline job_task H_valid_job_parameters num_cpus sched
      H_jobs_come_from_arrival_sequence H_completed_jobs_dont_execute tsk_i j_i tsk_k R_k delta NUM
  have NUM' : div_ceil (task_deadline tsk_i + R_k - task_deadline tsk_k + 1) (task_period tsk_k) < (((((jobs_scheduled_between sched (job_arrival j_i) (job_arrival j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost sched j_i (j') (job_arrival j_i) (job_arrival j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y)))).length := by omega
  obtain ⟨elem, _⟩ := List.exists_mem_of_length_pos (by omega : 0 < (((((jobs_scheduled_between sched (job_arrival j_i) (job_arrival j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost sched j_i (j') (job_arrival j_i) (job_arrival j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y)))).length)
  rw [sumSeq_getD _ _ elem]
  obtain hlen | ⟨num_mid_jobs, hlen⟩ :
      (((((jobs_scheduled_between sched (job_arrival j_i) (job_arrival j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost sched j_i (j') (job_arrival j_i) (job_arrival j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y)))).length = 1 ∨ ∃ m, (((((jobs_scheduled_between sched (job_arrival j_i) (job_arrival j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost sched j_i (j') (job_arrival j_i) (job_arrival j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y)))).length = m + 2 := by
    rcases h : (((((jobs_scheduled_between sched (job_arrival j_i) (job_arrival j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost sched j_i (j') (job_arrival j_i) (job_arrival j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y)))).length with _ | _ | m
    · omega
    · exact Or.inl rfl
    · exact Or.inr ⟨m, rfl⟩
  · rw [hlen, ← Finset.range_eq_Ico, Finset.sum_range_one]
    exact interference_bound_edf_holds_for_a_single_job task_cost task_period task_deadline
      job_arrival job_cost job_deadline job_task H_valid_job_parameters num_cpus sched
      H_jobs_come_from_arrival_sequence H_completed_jobs_dont_execute ts H_valid_task_parameters tsk_i
      H_tsk_i_in_task_set j_i tsk_k H_tsk_k_in_task_set R_k H_R_k_le_deadline delta elem hlen
  · rw [hlen]
    exact interference_bound_edf_holds_for_multiple_jobs task_cost task_period task_deadline job_arrival job_cost job_deadline job_task H_sporadic_tasks H_valid_job_parameters num_cpus sched H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_at_least_one_cpu ts H_valid_task_parameters H_constrained_deadlines H_edf_scheduler tsk_i H_tsk_i_in_task_set j_i H_j_i_arrives H_job_of_tsk_i tsk_k H_tsk_k_in_task_set R_k H_R_k_le_deadline delta H_delta_le_deadline H_all_previous_jobs_completed_on_time NUM' elem num_mid_jobs hlen

/-! ### Monotonicity of the EDF-specific bound -/

theorem interference_bound_edf_monotonic
    {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost : sporadic_task → time)
    (task_period : sporadic_task → time)
    (task_deadline : sporadic_task → time)
    (tsk : sporadic_task)
    (tsk_other : sporadic_task)
    (H_period_positive : 0 < task_period tsk_other)
    (delta : time)
    (delta' : time)
    (R : time)
    (R' : time)
    (H_delta_monotonic : delta ≤ delta')
    (H_response_time_monotonic : R ≤ R') :
    interference_bound_edf task_cost task_period task_deadline tsk delta (tsk_other, R) ≤
      interference_bound_edf task_cost task_period task_deadline tsk delta' (tsk_other, R') := by
  have hW := W_monotonic task_cost task_period tsk_other H_period_positive R R' H_response_time_monotonic delta delta'
    H_delta_monotonic
  unfold interference_bound_edf interference_bound_generic edf_specific_interference_bound
  apply min_le_min hW
  exact Nat.mul_le_mul_right _ (leq_divceil2r _ _ _ H_period_positive (by omega'))

end Prosa.Classic.Analysis.Global.Parallel.InterferenceBoundEdf.InterferenceBoundEDF
