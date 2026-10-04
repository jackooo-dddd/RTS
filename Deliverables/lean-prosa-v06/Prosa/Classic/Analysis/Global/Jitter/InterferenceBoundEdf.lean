-- Authoritative source:
-- ProsaBuddy classic Prosa (prosabuddy commit f692cb7479780cf6009493f373a309e13165201c)
-- source: classic/analysis/global/jitter/interference_bound_edf.v
-- sha256: see Prosa-Shunqi/classic-prosa/comprehensive-classic/file_order.csv (rank 161)

import Prosa.Util.Sum
import Prosa.Classic.Util.All
import Prosa.Classic.Model.Arrival.Basic.Task
import Prosa.Classic.Model.Priority
import Prosa.Classic.Model.Arrival.Basic.TaskArrival
import Prosa.Classic.Model.Schedule.Global.ResponseTime
import Prosa.Classic.Model.Schedule.Global.Workload
import Prosa.Classic.Model.Schedule.Global.Schedulability
import Prosa.Classic.Model.Schedule.Global.Jitter.Job
import Prosa.Classic.Model.Schedule.Global.Jitter.Schedule
import Prosa.Classic.Model.Schedule.Global.Jitter.Platform
import Prosa.Classic.Model.Schedule.Global.Jitter.Interference
import Prosa.Classic.Model.Schedule.Global.Jitter.InterferenceEdf
import Prosa.Classic.Analysis.Global.Jitter.WorkloadBound
import Prosa.Classic.Analysis.Global.Jitter.InterferenceBound

/-!
Bertogna and Cirinei's EDF-specific interference bound with release jitter and its safety proof (Rocq module
`InterferenceBoundEDFJitter` of `classic/analysis/global/jitter/interference_bound_edf.v`).

Representation notes (as in the accepted `classic/analysis/global/basic/interference_bound_edf.v` translation):
* The `let d_tsk := … in …` (and `j_other`) of `edf_specific_interference_bound` are inlined; `minn` is `min`,
  `m %% d` is `m % d`.
* The section-local `Let`s are unfolded in the statements: `t1`/`t2` are `job_arrival j_i + job_jitter j_i` /
  `job_arrival j_i + job_jitter j_i + delta`; `x` is the jitter-aware `task_interference … job_jitter sched j_i tsk_k
  t1 t2`; `interference_caused_by j' t1 t2` is `job_interference job_arrival job_cost job_jitter sched j_i j' t1 t2`;
  `a_i`, `D_i`, `D_k`, `p_k`, `J_i`, `J_k` are `job_arrival j_i`, `task_deadline tsk_i`, `task_deadline tsk_k`,
  `task_period tsk_k`, `task_jitter tsk_i`, `task_jitter tsk_k`; `interfering_jobs`/`sorted_jobs`/`j_fst`/`j_lst`
  are as in the basic translation (filter of `jobs_scheduled_between sched t1 t2`, `mergeSort` by arrival time,
  `getD` with the section variable `elem`).
* `\sum` notations are `Prosa.Util.Sum.sumSeq`/`sumFiltered`/`Finset` sums as in the basic translation.
* The Rocq module re-exports `InterferenceBoundJitter`.
* Binder lists follow the Rocq contract. The proofs follow the accepted basic translation, with the response-time
  bounds of the jobs of `tsk_k` shifted by the task jitter (`a_fst + J_k + R_k`), the interval start shifted by the
  job jitter, and `D_k - R_k` replaced by `D_k - R_k - J_k`; where the basic proof uses
  `jobs_must_arrive_to_execute`, it is obtained from `jobs_execute_after_jitter` (`arrival_before_jitter`).
-/

set_option linter.dupNamespace false
set_option linter.unusedVariables false

namespace Prosa.Classic.Analysis.Global.Jitter.InterferenceBoundEdf.InterferenceBoundEDFJitter

open Prosa.Classic.Model.Time.Time
open Prosa.Classic.Model.Arrival.Basic.ArrivalSequence.ArrivalSequence
open Prosa.Classic.Model.Arrival.Basic.Task.SporadicTaskset
open Prosa.Classic.Model.Arrival.Basic.Job.Job
open Prosa.Classic.Model.Arrival.Basic.TaskArrival.TaskArrival
open Prosa.Classic.Model.Priority.Priority
open Prosa.Classic.Model.Schedule.Global.Basic.Schedule.Schedule hiding pending backlogged scheduled_implies_pending
open Prosa.Classic.Model.Schedule.Global.Jitter.Job.JobWithJitter
open Prosa.Classic.Model.Schedule.Global.Jitter.Schedule.ScheduleWithJitter
open Prosa.Classic.Model.Schedule.Global.Jitter.Schedule.ScheduleOfSporadicTaskWithJitter
open Prosa.Classic.Model.Schedule.Global.Jitter.Platform.Platform
open Prosa.Classic.Model.Schedule.Global.Jitter.Interference.Interference
open Prosa.Classic.Model.Schedule.Global.Jitter.InterferenceEdf.InterferenceEDF
open Prosa.Classic.Model.Schedule.Global.ResponseTime.ResponseTime
open Prosa.Classic.Analysis.Global.Jitter.WorkloadBound.WorkloadBoundJitter
open Prosa.Classic.Util.DivMod (div_floor)
open Prosa.Util.Sum (sumSeq sumFiltered)
open BigOperators

export Prosa.Classic.Analysis.Global.Jitter.InterferenceBound.InterferenceBoundJitter
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
    (task_jitter : sporadic_task → time)
    (tsk : sporadic_task)
    (tsk_other : sporadic_task)
    (R_other : time) : Nat :=
  div_floor (task_deadline tsk) (task_period tsk_other) * task_cost tsk_other +
    min (task_cost tsk_other)
      (task_deadline tsk % task_period tsk_other - (task_deadline tsk_other - R_other - task_jitter tsk_other))

def interference_bound_edf
    {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost : sporadic_task → time)
    (task_period : sporadic_task → time)
    (task_deadline : sporadic_task → time)
    (task_jitter : sporadic_task → time)
    (tsk : sporadic_task)
    (delta : time)
    (tsk_R : sporadic_task × time) : Nat :=
  min (interference_bound_generic task_cost task_period task_jitter tsk delta tsk_R)
    (edf_specific_interference_bound task_cost task_period task_deadline task_jitter tsk tsk_R.1 tsk_R.2)

def total_interference_bound_edf
    {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost : sporadic_task → time)
    (task_period : sporadic_task → time)
    (task_deadline : sporadic_task → time)
    (task_jitter : sporadic_task → time)
    (tsk : sporadic_task)
    (R_prev : List (sporadic_task × time))
    (delta : time) : Nat :=
  sumFiltered R_prev (fun (tsk_other, _R_other) => different_task tsk tsk_other)
    (fun (tsk_other, R_other) =>
      interference_bound_edf task_cost task_period task_deadline task_jitter tsk delta (tsk_other, R_other))

/-! ### LEAN_HELPER lemmas -/

/-- LEAN_HELPER: defaulted lookup inside the list. -/
private theorem getD_lt
    {α : Type _}
    {l : List α}
    {i : Nat}
    {d : α}
    (h : i < l.length)
:
    l.getD i d = l[i] := by
  simp [List.getD_eq_getElem?_getD, h]

/-- LEAN_HELPER: a sum over a list as an indexed sum (MathComp `big_nth`). -/
private theorem sumSeq_getD
    {T : Type _}
    (l : List T)
    (F : T → Nat)
    (x0 : T)
:
    sumSeq l F = ∑ i ∈ Finset.Ico 0 l.length, F (l.getD i x0) := by
  rw [← Finset.range_eq_Ico]
  induction l with
  | nil => simp [sumSeq]
  | cons a l ih =>
      unfold sumSeq at ih ⊢
      rw [List.map_cons, List.sum_cons, ih, List.length_cons, Finset.sum_range_succ']
      simp [Nat.add_comm]

/-- LEAN_HELPER: dropping the zero summands of a filtered sum. -/
private theorem sum_filter_ne_zero
    {α : Type _}
    (l : List α)
    (P : α → Bool)
    (f : α → Nat)
:
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
    {sporadic_task : Type u}
    [DecidableEq sporadic_task]
    {Job : Type v}
    [DecidableEq Job]
    (job_arrival : Job → time)
    (job_cost : Job → time)
    (job_jitter : Job → time)
    (job_task : Job → sporadic_task)
    (num_cpus : Nat)
    (sched : schedule Job num_cpus)
    (j_i : Job)
    (tsk_k : sporadic_task)
    (delta : time)
    (j : Job)
:
    j ∈ ((((jobs_scheduled_between sched (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost job_jitter sched j_i (j') (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y))) ↔ j ∈ ((jobs_scheduled_between sched (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost job_jitter sched j_i (j') (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta) = 0))) :=
  List.mem_mergeSort

/-- LEAN_HELPER: the sorted list has no duplicates. -/
private theorem sorted_nodup
    {sporadic_task : Type u}
    [DecidableEq sporadic_task]
    {Job : Type v}
    [DecidableEq Job]
    (job_arrival : Job → time)
    (job_cost : Job → time)
    (job_jitter : Job → time)
    (job_task : Job → sporadic_task)
    (num_cpus : Nat)
    (sched : schedule Job num_cpus)
    (j_i : Job)
    (tsk_k : sporadic_task)
    (delta : time)
:
    (((((jobs_scheduled_between sched (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost job_jitter sched j_i (j') (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y)))).Nodup := by
  apply (List.mergeSort_perm _ _).nodup_iff.mpr
  exact (List.nodup_dedup _).filter _

/-- LEAN_HELPER: with sequential jobs, job interference in `[a, b)` is at most `b - a`. -/
private theorem job_interference_le_length
    {Job : Type v}
    [DecidableEq Job]
    (job_arrival : Job → time)
    (job_cost : Job → time)
    (job_jitter : Job → time)
    (num_cpus : Nat)
    (sched : schedule Job num_cpus)
    (H_sequential_jobs : sequential_jobs sched)
    (j j' : Job)
    (a b : time)
:
    job_interference job_arrival job_cost job_jitter sched j j' a b ≤ b - a := by
  by_cases h : a ≤ b
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
    have := job_interference_le_delta job_arrival job_cost job_jitter sched j H_sequential_jobs j' a d
    omega'
  · unfold job_interference
    rw [Finset.Ico_eq_empty_of_le (by omega')]
    simp

/-- LEAN_HELPER: a job that completes by `job_arrival j' + R` interferes at most until then. -/
private theorem job_interference_le_until_completion
    {Job : Type v}
    [DecidableEq Job]
    (job_arrival : Job → time)
    (job_cost : Job → time)
    (job_jitter : Job → time)
    (num_cpus : Nat)
    (sched : schedule Job num_cpus)
    (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched)
    (H_sequential_jobs : sequential_jobs sched)
    (j j' : Job)
    (R : time)
    (COMP : completed job_cost sched j' (job_arrival j' + R) = true)
    (a b : time)
:
    job_interference job_arrival job_cost job_jitter sched j j' a b ≤ job_arrival j' + R - a := by
  by_cases hb : b ≤ job_arrival j' + R
  · exact Nat.le_trans (job_interference_le_length job_arrival job_cost job_jitter num_cpus sched H_sequential_jobs j j' a b) (by omega')
  by_cases ha : job_arrival j' + R ≤ a
  · have h0 := job_interference_le_service job_arrival job_cost job_jitter sched j j' a b
    have hz := cumulative_service_after_job_rt_zero job_arrival job_cost sched
      H_completed_jobs_dont_execute j' R COMP a b ha
    unfold service_during at h0
    rw [hz] at h0
    omega'
  · have h1 : a ≤ job_arrival j' + R := by omega'
    have h2 : job_arrival j' + R ≤ b := by omega'
    have hsplit : job_interference job_arrival job_cost job_jitter sched j j' a b =
        job_interference job_arrival job_cost job_jitter sched j j' a (job_arrival j' + R) +
        job_interference job_arrival job_cost job_jitter sched j j' (job_arrival j' + R) b := by
      unfold job_interference
      exact (Finset.sum_Ico_consecutive _ h1 h2).symm
    have hA := job_interference_le_length job_arrival job_cost job_jitter num_cpus sched H_sequential_jobs j j' a (job_arrival j' + R)
    have h0 := job_interference_le_service job_arrival job_cost job_jitter sched j j'
      (job_arrival j' + R) b
    have hz := cumulative_service_after_job_rt_zero job_arrival job_cost sched
      H_completed_jobs_dont_execute j' R COMP (job_arrival j' + R) b (Nat.le_refl _)
    unfold service_during at h0
    rw [hz] at h0
    omega'

/-- LEAN_HELPER: a job that interferes in `[a, b)` arrives before `b`. -/
private theorem interfering_job_arrives_before
    {Job : Type v}
    [DecidableEq Job]
    (job_arrival : Job → time)
    (job_cost : Job → time)
    (job_jitter : Job → time)
    (num_cpus : Nat)
    (sched : schedule Job num_cpus)
    (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute job_arrival sched)
    (j j' : Job)
    (a b : time)
    (NZ : (!decide (job_interference job_arrival job_cost job_jitter sched j j' a b = 0)) = true)
:
    job_arrival j' < b := by
  by_contra h
  have h0 := job_interference_le_service job_arrival job_cost job_jitter sched j j' a b
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
    (job_jitter : Job → time)
    (num_cpus : Nat)
    (sched : schedule Job num_cpus)
    (j_i : Job)
    (tsk_k : sporadic_task)
    (delta : time)
:
    task_interference job_arrival job_cost job_task job_jitter sched j_i tsk_k (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta) ≤ sumFiltered (jobs_scheduled_between sched (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta)) (fun j => decide (job_task j = tsk_k)) (fun j => job_interference job_arrival job_cost job_jitter sched j_i (j) (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta)) :=
  interference_le_interference_joblist job_arrival job_cost job_task job_jitter sched j_i tsk_k _ _

theorem interference_bound_edf_simpl_by_filtering_interfering_jobs
    {sporadic_task : Type u} [DecidableEq sporadic_task]
    {Job : Type v} [DecidableEq Job]
    (job_arrival : Job → time)
    (job_cost : Job → time)
    (job_task : Job → sporadic_task)
    (job_jitter : Job → time)
    (num_cpus : Nat)
    (sched : schedule Job num_cpus)
    (j_i : Job)
    (tsk_k : sporadic_task)
    (delta : time)
:
    sumFiltered (jobs_scheduled_between sched (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta)) (fun j => decide (job_task j = tsk_k)) (fun j => job_interference job_arrival job_cost job_jitter sched j_i (j) (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta)) =
      sumSeq ((jobs_scheduled_between sched (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost job_jitter sched j_i (j') (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta) = 0))) (fun j => job_interference job_arrival job_cost job_jitter sched j_i (j) (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta)) := by
  unfold sumFiltered sumSeq
  exact sum_filter_ne_zero _ _ _

theorem interference_bound_edf_simpl_by_sorting_interfering_jobs
    {sporadic_task : Type u} [DecidableEq sporadic_task]
    {Job : Type v} [DecidableEq Job]
    (job_arrival : Job → time)
    (job_cost : Job → time)
    (job_task : Job → sporadic_task)
    (job_jitter : Job → time)
    (num_cpus : Nat)
    (sched : schedule Job num_cpus)
    (j_i : Job)
    (tsk_k : sporadic_task)
    (delta : time)
:
    sumSeq ((jobs_scheduled_between sched (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost job_jitter sched j_i (j') (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta) = 0))) (fun j => job_interference job_arrival job_cost job_jitter sched j_i (j) (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta)) = sumSeq ((((jobs_scheduled_between sched (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost job_jitter sched j_i (j') (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y))) (fun j => job_interference job_arrival job_cost job_jitter sched j_i (j) (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta)) := by
  unfold sumSeq
  exact ((List.mergeSort_perm _ _).map _).sum_eq.symm

theorem interference_bound_edf_job_in_same_sequence
    {sporadic_task : Type u} [DecidableEq sporadic_task]
    {Job : Type v} [DecidableEq Job]
    (job_arrival : Job → time)
    (job_cost : Job → time)
    (job_task : Job → sporadic_task)
    (job_jitter : Job → time)
    (num_cpus : Nat)
    (sched : schedule Job num_cpus)
    (j_i : Job)
    (tsk_k : sporadic_task)
    (delta : time)
    (j : Job)
:
    decide (j ∈ ((jobs_scheduled_between sched (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost job_jitter sched j_i (j') (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta) = 0)))) = decide (j ∈ ((((jobs_scheduled_between sched (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost job_jitter sched j_i (j') (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y)))) :=
  decide_eq_decide.mpr (sorted_mem job_arrival job_cost job_jitter job_task num_cpus sched j_i tsk_k delta j).symm

theorem interference_bound_edf_all_jobs_from_tsk_k
    {sporadic_task : Type u} [DecidableEq sporadic_task]
    {Job : Type v} [DecidableEq Job]
    (job_arrival : Job → time)
    (job_cost : Job → time)
    (job_task : Job → sporadic_task)
    (job_jitter : Job → time)
    {arr_seq : arrival_sequence Job}
    (num_cpus : Nat)
    (sched : schedule Job num_cpus)
    (H_jobs_come_from_arrival_sequence : jobs_come_from_arrival_sequence sched arr_seq)
    (j_i : Job)
    (tsk_k : sporadic_task)
    (delta : time)
    (j : Job)
:
    j ∈ ((((jobs_scheduled_between sched (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost job_jitter sched j_i (j') (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y))) →
    arrives_in arr_seq j ∧
    job_task j = tsk_k ∧
    (!decide (job_interference job_arrival job_cost job_jitter sched j_i (j) (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta) = 0)) = true ∧
    j ∈ jobs_scheduled_between sched (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta) := by
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
    (job_jitter : Job → time)
    (num_cpus : Nat)
    (sched : schedule Job num_cpus)
    (j_i : Job)
    (tsk_k : sporadic_task)
    (delta : time)
    (i : Nat)
    (elem : Job)
:
    i < (((((jobs_scheduled_between sched (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost job_jitter sched j_i (j') (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y)))).length - 1 →
    job_arrival ((((((jobs_scheduled_between sched (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost job_jitter sched j_i (j') (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y)))).getD i elem) ≤ job_arrival ((((((jobs_scheduled_between sched (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost job_jitter sched j_i (j') (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y)))).getD (i + 1) elem) := by
  intro LT
  have hp : List.Pairwise (fun a b => decide (job_arrival a ≤ job_arrival b) = true) (((((jobs_scheduled_between sched (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost job_jitter sched j_i (j') (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y)))) := by
    apply List.pairwise_mergeSort
    · intro a b c h1 h2; simp only [decide_eq_true_eq] at *; exact Nat.le_trans h1 h2
    · intro a b; simp only [Bool.or_eq_true, decide_eq_true_eq]; exact Nat.le_total _ _
  have h1 : i < (((((jobs_scheduled_between sched (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost job_jitter sched j_i (j') (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y)))).length := by omega
  have h2 : i + 1 < (((((jobs_scheduled_between sched (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost job_jitter sched j_i (j') (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y)))).length := by omega
  rw [getD_lt h1, getD_lt h2]
  have := List.pairwise_iff_getElem.mp hp i (i + 1) h1 h2 (Nat.lt_succ_self i)
  simpa using this

theorem interference_bound_edf_interference_le_task_cost
    {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost : sporadic_task → time)
    (task_deadline : sporadic_task → time)
    (task_jitter : sporadic_task → time)
    {Job : Type v} [DecidableEq Job]
    (job_arrival : Job → time)
    (job_cost : Job → time)
    (job_deadline : Job → time)
    (job_task : Job → sporadic_task)
    (job_jitter : Job → time)
    {arr_seq : arrival_sequence Job}
    (H_valid_job_parameters :
      ∀ j : Job, arrives_in arr_seq j →
        valid_sporadic_job_with_jitter task_cost task_deadline task_jitter job_cost job_deadline job_task job_jitter j)
    (num_cpus : Nat)
    (sched : schedule Job num_cpus)
    (H_jobs_come_from_arrival_sequence : jobs_come_from_arrival_sequence sched arr_seq)
    (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched)
    (j_i : Job)
    (tsk_k : sporadic_task)
    (delta : time)
    (j : Job)
:
    j ∈ ((jobs_scheduled_between sched (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost job_jitter sched j_i (j') (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta) = 0))) → job_interference job_arrival job_cost job_jitter sched j_i (j) (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta) ≤ task_cost tsk_k := by
  intro IN
  obtain ⟨ARR, TSK, _, _⟩ := interference_bound_edf_all_jobs_from_tsk_k job_arrival job_cost job_task job_jitter num_cpus sched H_jobs_come_from_arrival_sequence j_i tsk_k delta j
    ((sorted_mem job_arrival job_cost job_jitter job_task num_cpus sched j_i tsk_k delta j).mpr IN)
  calc job_interference job_arrival job_cost job_jitter sched j_i (j) (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta)
      ≤ service_during sched j (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta) :=
        job_interference_le_service job_arrival job_cost job_jitter sched j_i j _ _
    _ ≤ task_cost tsk_k :=
        cumulative_service_le_task_cost task_cost task_deadline job_cost job_deadline job_task
          sched H_completed_jobs_dont_execute tsk_k j TSK (H_valid_job_parameters j ARR).1 _ _

/-! ### At most `n_k` jobs -/

theorem interference_bound_edf_holds_for_at_most_n_k_jobs
    {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost : sporadic_task → time)
    (task_period : sporadic_task → time)
    (task_deadline : sporadic_task → time)
    (task_jitter : sporadic_task → time)
    {Job : Type v} [DecidableEq Job]
    (job_arrival : Job → time)
    (job_cost : Job → time)
    (job_deadline : Job → time)
    (job_task : Job → sporadic_task)
    (job_jitter : Job → time)
    {arr_seq : arrival_sequence Job}
    (H_valid_job_parameters :
      ∀ j : Job, arrives_in arr_seq j →
        valid_sporadic_job_with_jitter task_cost task_deadline task_jitter job_cost job_deadline job_task job_jitter j)
    (num_cpus : Nat)
    (sched : schedule Job num_cpus)
    (H_jobs_come_from_arrival_sequence : jobs_come_from_arrival_sequence sched arr_seq)
    (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched)
    (tsk_i : sporadic_task)
    (j_i : Job)
    (tsk_k : sporadic_task)
    (R_k : time)
    (delta : time)
    (H_few_jobs : (((((jobs_scheduled_between sched (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost job_jitter sched j_i (j') (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y)))).length ≤ div_floor (task_deadline tsk_i) (task_period tsk_k))
:
    sumSeq ((((jobs_scheduled_between sched (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost job_jitter sched j_i (j') (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y))) (fun j => job_interference job_arrival job_cost job_jitter sched j_i (j) (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta)) ≤ edf_specific_interference_bound task_cost task_period task_deadline task_jitter tsk_i tsk_k R_k := by
  have hle : sumSeq ((((jobs_scheduled_between sched (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost job_jitter sched j_i (j') (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y))) (fun j => job_interference job_arrival job_cost job_jitter sched j_i (j) (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta)) ≤ (((((jobs_scheduled_between sched (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost job_jitter sched j_i (j') (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y)))).length * task_cost tsk_k := by
    unfold sumSeq
    have := List.sum_le_card_nsmul ((((((jobs_scheduled_between sched (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost job_jitter sched j_i (j') (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y)))).map (fun j => job_interference job_arrival job_cost job_jitter sched j_i (j) (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta))) (task_cost tsk_k) (by
      intro y hy
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hy
      exact interference_bound_edf_interference_le_task_cost task_cost task_deadline task_jitter job_arrival job_cost job_deadline job_task job_jitter H_valid_job_parameters num_cpus sched H_jobs_come_from_arrival_sequence H_completed_jobs_dont_execute j_i tsk_k delta j
        ((sorted_mem job_arrival job_cost job_jitter job_task num_cpus sched j_i tsk_k delta j).mp hj))
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
    (job_jitter : Job → time)
    (num_cpus : Nat)
    (sched : schedule Job num_cpus)
    (tsk_i : sporadic_task)
    (j_i : Job)
    (tsk_k : sporadic_task)
    (delta : time)
    (H_many_jobs : div_floor (task_deadline tsk_i) (task_period tsk_k) < (((((jobs_scheduled_between sched (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost job_jitter sched j_i (j') (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y)))).length)
:
    0 < (((((jobs_scheduled_between sched (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost job_jitter sched j_i (j') (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y)))).length := by
  omega

theorem interference_bound_edf_j_fst_is_job_of_tsk_k
    {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_period : sporadic_task → time)
    (task_deadline : sporadic_task → time)
    {Job : Type v} [DecidableEq Job]
    (job_arrival : Job → time)
    (job_cost : Job → time)
    (job_task : Job → sporadic_task)
    (job_jitter : Job → time)
    {arr_seq : arrival_sequence Job}
    (num_cpus : Nat)
    (sched : schedule Job num_cpus)
    (H_jobs_come_from_arrival_sequence : jobs_come_from_arrival_sequence sched arr_seq)
    (tsk_i : sporadic_task)
    (j_i : Job)
    (tsk_k : sporadic_task)
    (delta : time)
    (H_many_jobs : div_floor (task_deadline tsk_i) (task_period tsk_k) < (((((jobs_scheduled_between sched (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost job_jitter sched j_i (j') (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y)))).length)
    (elem : Job)
:
    arrives_in arr_seq ((((((jobs_scheduled_between sched (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost job_jitter sched j_i (j') (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y)))).getD 0 elem) ∧
    job_task ((((((jobs_scheduled_between sched (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost job_jitter sched j_i (j') (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y)))).getD 0 elem) = tsk_k ∧
    (!decide (job_interference job_arrival job_cost job_jitter sched j_i (((((((jobs_scheduled_between sched (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost job_jitter sched j_i (j') (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y)))).getD 0 elem)) (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta) = 0)) = true ∧
    ((((((jobs_scheduled_between sched (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost job_jitter sched j_i (j') (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y)))).getD 0 elem) ∈ jobs_scheduled_between sched (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta) := by
  apply interference_bound_edf_all_jobs_from_tsk_k job_arrival job_cost job_task job_jitter num_cpus
    sched H_jobs_come_from_arrival_sequence j_i tsk_k delta
  rw [getD_lt (by omega)]
  exact List.getElem_mem _

theorem interference_bound_edf_j_fst_deadline
    {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost : sporadic_task → time)
    (task_period : sporadic_task → time)
    (task_deadline : sporadic_task → time)
    (task_jitter : sporadic_task → time)
    {Job : Type v} [DecidableEq Job]
    (job_arrival : Job → time)
    (job_cost : Job → time)
    (job_deadline : Job → time)
    (job_task : Job → sporadic_task)
    (job_jitter : Job → time)
    {arr_seq : arrival_sequence Job}
    (H_valid_job_parameters :
      ∀ j : Job, arrives_in arr_seq j →
        valid_sporadic_job_with_jitter task_cost task_deadline task_jitter job_cost job_deadline job_task job_jitter j)
    (num_cpus : Nat)
    (sched : schedule Job num_cpus)
    (H_jobs_come_from_arrival_sequence : jobs_come_from_arrival_sequence sched arr_seq)
    (tsk_i : sporadic_task)
    (j_i : Job)
    (tsk_k : sporadic_task)
    (delta : time)
    (H_many_jobs : div_floor (task_deadline tsk_i) (task_period tsk_k) < (((((jobs_scheduled_between sched (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost job_jitter sched j_i (j') (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y)))).length)
    (elem : Job)
:
    job_deadline ((((((jobs_scheduled_between sched (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost job_jitter sched j_i (j') (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y)))).getD 0 elem) = task_deadline tsk_k := by
  obtain ⟨ARR, TSK, _, _⟩ := interference_bound_edf_j_fst_is_job_of_tsk_k task_period task_deadline job_arrival job_cost job_task job_jitter num_cpus sched H_jobs_come_from_arrival_sequence tsk_i j_i tsk_k delta H_many_jobs elem
  have := (H_valid_job_parameters _ ARR).1.2.2
  simp only [job_deadline_eq_task_deadline] at this
  rw [this, TSK]

theorem interference_bound_edf_j_i_deadline
    {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost : sporadic_task → time)
    (task_deadline : sporadic_task → time)
    (task_jitter : sporadic_task → time)
    {Job : Type v} [DecidableEq Job]
    (job_cost : Job → time)
    (job_deadline : Job → time)
    (job_task : Job → sporadic_task)
    (job_jitter : Job → time)
    {arr_seq : arrival_sequence Job}
    (H_valid_job_parameters :
      ∀ j : Job, arrives_in arr_seq j →
        valid_sporadic_job_with_jitter task_cost task_deadline task_jitter job_cost job_deadline job_task job_jitter j)
    (tsk_i : sporadic_task)
    (j_i : Job)
    (H_j_i_arrives : arrives_in arr_seq j_i)
    (H_job_of_tsk_i : job_task j_i = tsk_i)
:
    job_deadline j_i = task_deadline tsk_i := by
  have := (H_valid_job_parameters _ H_j_i_arrives).1.2.2
  simp only [job_deadline_eq_task_deadline] at this
  rw [this, H_job_of_tsk_i]

theorem interference_bound_edf_j_fst_completion_implies_rt_bound_inside_interval
    {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_period : sporadic_task → time)
    (task_deadline : sporadic_task → time)
    (task_jitter : sporadic_task → time)
    {Job : Type v} [DecidableEq Job]
    (job_arrival : Job → time)
    (job_cost : Job → time)
    (job_task : Job → sporadic_task)
    (job_jitter : Job → time)
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
    (H_many_jobs : div_floor (task_deadline tsk_i) (task_period tsk_k) < (((((jobs_scheduled_between sched (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost job_jitter sched j_i (j') (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y)))).length)
    (elem : Job)
:
    completed job_cost sched ((((((jobs_scheduled_between sched (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost job_jitter sched j_i (j') (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y)))).getD 0 elem) (job_arrival ((((((jobs_scheduled_between sched (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost job_jitter sched j_i (j') (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y)))).getD 0 elem) + task_jitter tsk_k + R_k) = true →
    job_arrival j_i + job_jitter j_i ≤ job_arrival ((((((jobs_scheduled_between sched (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost job_jitter sched j_i (j') (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y)))).getD 0 elem) + task_jitter tsk_k + R_k := by
  intro RBOUND
  by_contra BUG
  obtain ⟨_, _, NZ, _⟩ := interference_bound_edf_j_fst_is_job_of_tsk_k task_period task_deadline job_arrival job_cost job_task job_jitter num_cpus sched H_jobs_come_from_arrival_sequence tsk_i j_i tsk_k delta H_many_jobs elem
  have h0 := job_interference_le_service job_arrival job_cost job_jitter sched j_i ((((((jobs_scheduled_between sched (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost job_jitter sched j_i (j') (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y)))).getD 0 elem) (job_arrival j_i + job_jitter j_i)
    (job_arrival j_i + job_jitter j_i + delta)
  have hz := cumulative_service_after_job_rt_zero job_arrival job_cost sched
    H_completed_jobs_dont_execute _ (task_jitter tsk_k + R_k) (by rw [← Nat.add_assoc]; exact RBOUND) (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta)
    (by omega')
  unfold service_during at h0
  rw [hz] at h0
  simp only [Bool.not_eq_true', decide_eq_false_iff_not] at NZ
  omega'

/-- LEAN_HELPER: under EDF, a job of `S` has a deadline no later than `j_i`'s. -/
private theorem sorted_job_deadline_le
    {sporadic_task : Type u}
    [DecidableEq sporadic_task]
    (task_cost : sporadic_task → time)
    (task_deadline : sporadic_task → time)
    (task_jitter : sporadic_task → time)
    {Job : Type v}
    [DecidableEq Job]
    (job_arrival : Job → time)
    (job_cost : Job → time)
    (job_deadline : Job → time)
    (job_task : Job → sporadic_task)
    (job_jitter : Job → time)
    (arr_seq : arrival_sequence Job)
    (H_valid_job_parameters :
      ∀ j : Job, arrives_in arr_seq j →
        valid_sporadic_job_with_jitter task_cost task_deadline task_jitter job_cost job_deadline job_task job_jitter j)
    (num_cpus : Nat)
    (sched : schedule Job num_cpus)
    (H_jobs_come_from_arrival_sequence : jobs_come_from_arrival_sequence sched arr_seq)
    (H_edf_policy :
      respects_JLFP_policy job_arrival job_cost job_jitter arr_seq sched (EDF job_arrival job_deadline))
    (tsk_i : sporadic_task)
    (j_i : Job)
    (H_j_i_arrives : arrives_in arr_seq j_i)
    (H_job_of_tsk_i : job_task j_i = tsk_i)
    (tsk_k : sporadic_task)
    (delta : time)
    (j : Job)
    (IN : j ∈ ((((jobs_scheduled_between sched (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost job_jitter sched j_i (j') (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y))))
:
    job_arrival j + task_deadline tsk_k ≤ job_arrival j_i + task_deadline tsk_i := by
  obtain ⟨ARR, TSK, NZ, _⟩ := interference_bound_edf_all_jobs_from_tsk_k job_arrival job_cost job_task job_jitter num_cpus sched H_jobs_come_from_arrival_sequence j_i tsk_k delta j IN
  have LEdl := interference_under_edf_implies_shorter_deadlines job_arrival job_cost job_deadline job_jitter
    arr_seq num_cpus sched H_edf_policy j j_i _ _ ARR H_j_i_arrives NZ
  have hj := (H_valid_job_parameters _ ARR).1.2.2
  have hi := (H_valid_job_parameters _ H_j_i_arrives).1.2.2
  simp only [job_deadline_eq_task_deadline] at hj hi
  rw [hj, TSK, hi, H_job_of_tsk_i] at LEdl
  exact LEdl

/-! ### A single job -/

theorem interference_bound_edf_simpl_when_there's_one_job
    {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost : sporadic_task → time)
    (task_period : sporadic_task → time)
    (task_deadline : sporadic_task → time)
    (task_jitter : sporadic_task → time)
    {Job : Type v} [DecidableEq Job]
    (job_arrival : Job → time)
    (job_cost : Job → time)
    (job_task : Job → sporadic_task)
    (job_jitter : Job → time)
    (num_cpus : Nat)
    (sched : schedule Job num_cpus)
    (ts : taskset_of sporadic_task)
    (H_valid_task_parameters :
      valid_sporadic_taskset task_cost task_period task_deadline ts.val)
    (tsk_i : sporadic_task)
    (j_i : Job)
    (tsk_k : sporadic_task)
    (H_tsk_k_in_task_set : tsk_k ∈ ts)
    (R_k : time)
    (delta : time)
    (H_many_jobs : div_floor (task_deadline tsk_i) (task_period tsk_k) < (((((jobs_scheduled_between sched (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost job_jitter sched j_i (j') (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y)))).length)
    (H_only_one_job : (((((jobs_scheduled_between sched (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost job_jitter sched j_i (j') (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y)))).length = 1)
:
    task_deadline tsk_i % task_period tsk_k - (task_deadline tsk_k - R_k - task_jitter tsk_k) =
      task_deadline tsk_i - (task_deadline tsk_k - R_k - task_jitter tsk_k) := by
  have hp : 0 < task_period tsk_k := by
    have := (H_valid_task_parameters tsk_k H_tsk_k_in_task_set).2.1
    simpa [task_period_positive] using this
  have hNK : task_deadline tsk_i / task_period tsk_k = 0 := by
    have : div_floor (task_deadline tsk_i) (task_period tsk_k) = 0 := by omega
    simpa [div_floor] using this
  have hlt : task_deadline tsk_i < task_period tsk_k := by
    by_contra h
    have := Nat.div_pos (Nat.le_of_not_lt h) hp
    omega'
  rw [Nat.mod_eq_of_lt hlt]

theorem interference_bound_edf_holds_for_single_job_that_completes_on_time
    {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost : sporadic_task → time)
    (task_period : sporadic_task → time)
    (task_deadline : sporadic_task → time)
    (task_jitter : sporadic_task → time)
    {Job : Type v} [DecidableEq Job]
    (job_arrival : Job → time)
    (job_cost : Job → time)
    (job_deadline : Job → time)
    (job_task : Job → sporadic_task)
    (job_jitter : Job → time)
    {arr_seq : arrival_sequence Job}
    (H_valid_job_parameters :
      ∀ j : Job, arrives_in arr_seq j →
        valid_sporadic_job_with_jitter task_cost task_deadline task_jitter job_cost job_deadline job_task job_jitter j)
    (num_cpus : Nat)
    (sched : schedule Job num_cpus)
    (H_jobs_come_from_arrival_sequence : jobs_come_from_arrival_sequence sched arr_seq)
    (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched)
    (H_sequential_jobs : sequential_jobs sched)
    (H_edf_policy :
      respects_JLFP_policy job_arrival job_cost job_jitter arr_seq sched (EDF job_arrival job_deadline))
    (tsk_i : sporadic_task)
    (j_i : Job)
    (H_j_i_arrives : arrives_in arr_seq j_i)
    (H_job_of_tsk_i : job_task j_i = tsk_i)
    (tsk_k : sporadic_task)
    (R_k : time)
    (H_R_k_le_deadline : task_jitter tsk_k + R_k ≤ task_deadline tsk_k)
    (delta : time)
    (H_many_jobs : div_floor (task_deadline tsk_i) (task_period tsk_k) < (((((jobs_scheduled_between sched (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost job_jitter sched j_i (j') (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y)))).length)
    (elem : Job)
    (H_j_fst_completed_by_rt_bound :
      completed job_cost sched ((((((jobs_scheduled_between sched (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost job_jitter sched j_i (j') (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y)))).getD 0 elem) (job_arrival ((((((jobs_scheduled_between sched (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost job_jitter sched j_i (j') (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y)))).getD 0 elem) + task_jitter tsk_k + R_k) = true)
:
    job_interference job_arrival job_cost job_jitter sched j_i ((((((jobs_scheduled_between sched (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost job_jitter sched j_i (j') (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y)))).getD 0 elem) (job_arrival j_i + job_jitter j_i)
        (job_arrival j_i + job_jitter j_i + delta) ≤
      task_deadline tsk_i - (task_deadline tsk_k - R_k - task_jitter tsk_k) := by
  have hle := job_interference_le_until_completion job_arrival job_cost job_jitter num_cpus sched H_completed_jobs_dont_execute H_sequential_jobs j_i ((((((jobs_scheduled_between sched (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost job_jitter sched j_i (j') (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y)))).getD 0 elem) (task_jitter tsk_k + R_k) (by rw [← Nat.add_assoc]; exact H_j_fst_completed_by_rt_bound) (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta)
  have hdl := sorted_job_deadline_le task_cost task_deadline task_jitter job_arrival job_cost job_deadline job_task job_jitter arr_seq H_valid_job_parameters num_cpus sched H_jobs_come_from_arrival_sequence H_edf_policy tsk_i j_i H_j_i_arrives H_job_of_tsk_i tsk_k delta ((((((jobs_scheduled_between sched (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost job_jitter sched j_i (j') (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y)))).getD 0 elem) (by rw [getD_lt (by omega)]; exact List.getElem_mem _)
  omega'

theorem interference_bound_edf_response_time_bound_of_j_fst_after_interval
    {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_period : sporadic_task → time)
    (task_deadline : sporadic_task → time)
    (task_jitter : sporadic_task → time)
    {Job : Type v} [DecidableEq Job]
    (job_arrival : Job → time)
    (job_cost : Job → time)
    (job_task : Job → sporadic_task)
    (job_jitter : Job → time)
    {arr_seq : arrival_sequence Job}
    (num_cpus : Nat)
    (sched : schedule Job num_cpus)
    (H_jobs_come_from_arrival_sequence : jobs_come_from_arrival_sequence sched arr_seq)
    (tsk_i : sporadic_task)
    (j_i : Job)
    (tsk_k : sporadic_task)
    (R_k : time)
    (delta : time)
    (H_all_previous_jobs_completed_on_time :
      ∀ j_k : Job, arrives_in arr_seq j_k → job_task j_k = tsk_k →
        job_arrival j_k + task_jitter tsk_k + R_k < job_arrival j_i + task_jitter tsk_i + delta →
        completed job_cost sched j_k (job_arrival j_k + task_jitter tsk_k + R_k) = true)
    (H_many_jobs : div_floor (task_deadline tsk_i) (task_period tsk_k) < (((((jobs_scheduled_between sched (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost job_jitter sched j_i (j') (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y)))).length)
    (elem : Job)
    (H_j_fst_not_complete_by_rt_bound :
      (!completed job_cost sched ((((((jobs_scheduled_between sched (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost job_jitter sched j_i (j') (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y)))).getD 0 elem) (job_arrival ((((((jobs_scheduled_between sched (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost job_jitter sched j_i (j') (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y)))).getD 0 elem) + task_jitter tsk_k + R_k)) = true)
:
    job_arrival j_i + task_jitter tsk_i + delta ≤ job_arrival ((((((jobs_scheduled_between sched (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost job_jitter sched j_i (j') (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y)))).getD 0 elem) + task_jitter tsk_k + R_k := by
  obtain ⟨ARR, TSK, _, _⟩ := interference_bound_edf_j_fst_is_job_of_tsk_k task_period task_deadline job_arrival job_cost job_task job_jitter num_cpus sched H_jobs_come_from_arrival_sequence tsk_i j_i tsk_k delta H_many_jobs elem
  by_contra LT
  have COMP := H_all_previous_jobs_completed_on_time _ ARR TSK (by omega')
  rw [COMP] at H_j_fst_not_complete_by_rt_bound
  exact Bool.noConfusion H_j_fst_not_complete_by_rt_bound

theorem interference_bound_edf_holds_for_single_job_with_big_slack
    {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost : sporadic_task → time)
    (task_period : sporadic_task → time)
    (task_deadline : sporadic_task → time)
    (task_jitter : sporadic_task → time)
    {Job : Type v} [DecidableEq Job]
    (job_arrival : Job → time)
    (job_cost : Job → time)
    (job_deadline : Job → time)
    (job_task : Job → sporadic_task)
    (job_jitter : Job → time)
    {arr_seq : arrival_sequence Job}
    (H_valid_job_parameters :
      ∀ j : Job, arrives_in arr_seq j →
        valid_sporadic_job_with_jitter task_cost task_deadline task_jitter job_cost job_deadline job_task job_jitter j)
    (num_cpus : Nat)
    (sched : schedule Job num_cpus)
    (H_jobs_come_from_arrival_sequence : jobs_come_from_arrival_sequence sched arr_seq)
    (H_edf_policy :
      respects_JLFP_policy job_arrival job_cost job_jitter arr_seq sched (EDF job_arrival job_deadline))
    (tsk_i : sporadic_task)
    (j_i : Job)
    (H_j_i_arrives : arrives_in arr_seq j_i)
    (H_job_of_tsk_i : job_task j_i = tsk_i)
    (tsk_k : sporadic_task)
    (R_k : time)
    (delta : time)
    (H_all_previous_jobs_completed_on_time :
      ∀ j_k : Job, arrives_in arr_seq j_k → job_task j_k = tsk_k →
        job_arrival j_k + task_jitter tsk_k + R_k < job_arrival j_i + task_jitter tsk_i + delta →
        completed job_cost sched j_k (job_arrival j_k + task_jitter tsk_k + R_k) = true)
    (H_many_jobs : div_floor (task_deadline tsk_i) (task_period tsk_k) < (((((jobs_scheduled_between sched (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost job_jitter sched j_i (j') (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y)))).length)
    (elem : Job)
    (H_j_fst_not_complete_by_rt_bound :
      (!completed job_cost sched ((((((jobs_scheduled_between sched (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost job_jitter sched j_i (j') (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y)))).getD 0 elem) (job_arrival ((((((jobs_scheduled_between sched (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost job_jitter sched j_i (j') (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y)))).getD 0 elem) + task_jitter tsk_k + R_k)) = true)
:
    task_deadline tsk_i < task_deadline tsk_k - R_k - task_jitter tsk_k →
    job_interference job_arrival job_cost job_jitter sched j_i (((((((jobs_scheduled_between sched (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost job_jitter sched j_i (j') (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y)))).getD 0 elem)) (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta) = 0 := by
  intro LTdk
  have AFTER := interference_bound_edf_response_time_bound_of_j_fst_after_interval task_period task_deadline task_jitter job_arrival job_cost job_task job_jitter num_cpus sched H_jobs_come_from_arrival_sequence tsk_i j_i tsk_k R_k delta H_all_previous_jobs_completed_on_time H_many_jobs elem H_j_fst_not_complete_by_rt_bound
  have hdl := sorted_job_deadline_le task_cost task_deadline task_jitter job_arrival job_cost job_deadline job_task job_jitter arr_seq H_valid_job_parameters num_cpus sched H_jobs_come_from_arrival_sequence H_edf_policy tsk_i j_i H_j_i_arrives H_job_of_tsk_i tsk_k delta ((((((jobs_scheduled_between sched (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost job_jitter sched j_i (j') (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y)))).getD 0 elem) (by rw [getD_lt (by omega)]; exact List.getElem_mem _)
  exfalso
  omega'

theorem interference_bound_edf_holds_for_single_job_with_small_slack
    {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost : sporadic_task → time)
    (task_period : sporadic_task → time)
    (task_deadline : sporadic_task → time)
    (task_jitter : sporadic_task → time)
    {Job : Type v} [DecidableEq Job]
    (job_arrival : Job → time)
    (job_cost : Job → time)
    (job_deadline : Job → time)
    (job_task : Job → sporadic_task)
    (job_jitter : Job → time)
    {arr_seq : arrival_sequence Job}
    (H_valid_job_parameters :
      ∀ j : Job, arrives_in arr_seq j →
        valid_sporadic_job_with_jitter task_cost task_deadline task_jitter job_cost job_deadline job_task job_jitter j)
    (num_cpus : Nat)
    (sched : schedule Job num_cpus)
    (H_jobs_come_from_arrival_sequence : jobs_come_from_arrival_sequence sched arr_seq)
    (H_sequential_jobs : sequential_jobs sched)
    (H_edf_policy :
      respects_JLFP_policy job_arrival job_cost job_jitter arr_seq sched (EDF job_arrival job_deadline))
    (tsk_i : sporadic_task)
    (j_i : Job)
    (H_j_i_arrives : arrives_in arr_seq j_i)
    (H_job_of_tsk_i : job_task j_i = tsk_i)
    (tsk_k : sporadic_task)
    (R_k : time)
    (H_R_k_le_deadline : task_jitter tsk_k + R_k ≤ task_deadline tsk_k)
    (delta : time)
    (H_all_previous_jobs_completed_on_time :
      ∀ j_k : Job, arrives_in arr_seq j_k → job_task j_k = tsk_k →
        job_arrival j_k + task_jitter tsk_k + R_k < job_arrival j_i + task_jitter tsk_i + delta →
        completed job_cost sched j_k (job_arrival j_k + task_jitter tsk_k + R_k) = true)
    (H_many_jobs : div_floor (task_deadline tsk_i) (task_period tsk_k) < (((((jobs_scheduled_between sched (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost job_jitter sched j_i (j') (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y)))).length)
    (elem : Job)
    (H_j_fst_not_complete_by_rt_bound :
      (!completed job_cost sched ((((((jobs_scheduled_between sched (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost job_jitter sched j_i (j') (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y)))).getD 0 elem) (job_arrival ((((((jobs_scheduled_between sched (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost job_jitter sched j_i (j') (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y)))).getD 0 elem) + task_jitter tsk_k + R_k)) = true)
:
    task_deadline tsk_k - R_k - task_jitter tsk_k ≤ task_deadline tsk_i →
    job_interference job_arrival job_cost job_jitter sched j_i (((((((jobs_scheduled_between sched (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost job_jitter sched j_i (j') (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y)))).getD 0 elem)) (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta) ≤ task_deadline tsk_i - (task_deadline tsk_k - R_k - task_jitter tsk_k) := by
  intro LEdk
  have AFTER := interference_bound_edf_response_time_bound_of_j_fst_after_interval task_period task_deadline task_jitter job_arrival job_cost job_task job_jitter num_cpus sched H_jobs_come_from_arrival_sequence tsk_i j_i tsk_k R_k delta H_all_previous_jobs_completed_on_time H_many_jobs elem H_j_fst_not_complete_by_rt_bound
  have hdl := sorted_job_deadline_le task_cost task_deadline task_jitter job_arrival job_cost job_deadline job_task job_jitter arr_seq H_valid_job_parameters num_cpus sched H_jobs_come_from_arrival_sequence H_edf_policy tsk_i j_i H_j_i_arrives H_job_of_tsk_i tsk_k delta ((((((jobs_scheduled_between sched (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost job_jitter sched j_i (j') (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y)))).getD 0 elem) (by rw [getD_lt (by omega)]; exact List.getElem_mem _)
  have hd := job_interference_le_delta job_arrival job_cost job_jitter sched j_i H_sequential_jobs ((((((jobs_scheduled_between sched (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost job_jitter sched j_i (j') (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y)))).getD 0 elem)
    (job_arrival j_i + job_jitter j_i) delta
  omega'

theorem interference_bound_edf_interference_of_j_fst_limited_by_slack
    {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost : sporadic_task → time)
    (task_period : sporadic_task → time)
    (task_deadline : sporadic_task → time)
    (task_jitter : sporadic_task → time)
    {Job : Type v} [DecidableEq Job]
    (job_arrival : Job → time)
    (job_cost : Job → time)
    (job_deadline : Job → time)
    (job_task : Job → sporadic_task)
    (job_jitter : Job → time)
    {arr_seq : arrival_sequence Job}
    (H_valid_job_parameters :
      ∀ j : Job, arrives_in arr_seq j →
        valid_sporadic_job_with_jitter task_cost task_deadline task_jitter job_cost job_deadline job_task job_jitter j)
    (num_cpus : Nat)
    (sched : schedule Job num_cpus)
    (H_jobs_come_from_arrival_sequence : jobs_come_from_arrival_sequence sched arr_seq)
    (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched)
    (H_sequential_jobs : sequential_jobs sched)
    (H_edf_policy :
      respects_JLFP_policy job_arrival job_cost job_jitter arr_seq sched (EDF job_arrival job_deadline))
    (tsk_i : sporadic_task)
    (j_i : Job)
    (H_j_i_arrives : arrives_in arr_seq j_i)
    (H_job_of_tsk_i : job_task j_i = tsk_i)
    (tsk_k : sporadic_task)
    (R_k : time)
    (H_R_k_le_deadline : task_jitter tsk_k + R_k ≤ task_deadline tsk_k)
    (delta : time)
    (H_all_previous_jobs_completed_on_time :
      ∀ j_k : Job, arrives_in arr_seq j_k → job_task j_k = tsk_k →
        job_arrival j_k + task_jitter tsk_k + R_k < job_arrival j_i + task_jitter tsk_i + delta →
        completed job_cost sched j_k (job_arrival j_k + task_jitter tsk_k + R_k) = true)
    (H_many_jobs : div_floor (task_deadline tsk_i) (task_period tsk_k) < (((((jobs_scheduled_between sched (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost job_jitter sched j_i (j') (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y)))).length)
    (elem : Job)
:
    job_interference job_arrival job_cost job_jitter sched j_i (((((((jobs_scheduled_between sched (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost job_jitter sched j_i (j') (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y)))).getD 0 elem)) (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta) ≤ task_deadline tsk_i - (task_deadline tsk_k - R_k - task_jitter tsk_k) := by
  cases COMP : completed job_cost sched ((((((jobs_scheduled_between sched (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost job_jitter sched j_i (j') (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y)))).getD 0 elem) (job_arrival ((((((jobs_scheduled_between sched (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost job_jitter sched j_i (j') (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y)))).getD 0 elem) + task_jitter tsk_k + R_k)
  · have NOTCOMP : (!completed job_cost sched ((((((jobs_scheduled_between sched (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost job_jitter sched j_i (j') (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y)))).getD 0 elem) (job_arrival ((((((jobs_scheduled_between sched (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost job_jitter sched j_i (j') (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y)))).getD 0 elem) + task_jitter tsk_k + R_k)) = true := by
      rw [COMP]; rfl
    by_cases LTdk : task_deadline tsk_i < task_deadline tsk_k - R_k - task_jitter tsk_k
    · rw [interference_bound_edf_holds_for_single_job_with_big_slack task_cost task_period task_deadline task_jitter job_arrival job_cost job_deadline job_task job_jitter H_valid_job_parameters num_cpus sched H_jobs_come_from_arrival_sequence H_edf_policy tsk_i j_i H_j_i_arrives H_job_of_tsk_i tsk_k R_k delta H_all_previous_jobs_completed_on_time H_many_jobs elem NOTCOMP LTdk]
      exact Nat.zero_le _
    · exact interference_bound_edf_holds_for_single_job_with_small_slack task_cost task_period task_deadline task_jitter job_arrival job_cost job_deadline job_task job_jitter H_valid_job_parameters num_cpus sched H_jobs_come_from_arrival_sequence H_sequential_jobs H_edf_policy tsk_i j_i H_j_i_arrives H_job_of_tsk_i tsk_k R_k H_R_k_le_deadline delta H_all_previous_jobs_completed_on_time H_many_jobs elem NOTCOMP (by omega')
  · exact interference_bound_edf_holds_for_single_job_that_completes_on_time task_cost task_period task_deadline task_jitter job_arrival job_cost job_deadline job_task job_jitter H_valid_job_parameters num_cpus sched H_jobs_come_from_arrival_sequence H_completed_jobs_dont_execute H_sequential_jobs H_edf_policy tsk_i j_i H_j_i_arrives H_job_of_tsk_i tsk_k R_k H_R_k_le_deadline delta H_many_jobs elem COMP

theorem interference_bound_edf_holds_for_a_single_job
    {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost : sporadic_task → time)
    (task_period : sporadic_task → time)
    (task_deadline : sporadic_task → time)
    (task_jitter : sporadic_task → time)
    {Job : Type v} [DecidableEq Job]
    (job_arrival : Job → time)
    (job_cost : Job → time)
    (job_deadline : Job → time)
    (job_task : Job → sporadic_task)
    (job_jitter : Job → time)
    {arr_seq : arrival_sequence Job}
    (H_valid_job_parameters :
      ∀ j : Job, arrives_in arr_seq j →
        valid_sporadic_job_with_jitter task_cost task_deadline task_jitter job_cost job_deadline job_task job_jitter j)
    (num_cpus : Nat)
    (sched : schedule Job num_cpus)
    (H_jobs_come_from_arrival_sequence : jobs_come_from_arrival_sequence sched arr_seq)
    (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched)
    (H_sequential_jobs : sequential_jobs sched)
    (ts : taskset_of sporadic_task)
    (H_valid_task_parameters :
      valid_sporadic_taskset task_cost task_period task_deadline ts.val)
    (H_edf_policy :
      respects_JLFP_policy job_arrival job_cost job_jitter arr_seq sched (EDF job_arrival job_deadline))
    (tsk_i : sporadic_task)
    (j_i : Job)
    (H_j_i_arrives : arrives_in arr_seq j_i)
    (H_job_of_tsk_i : job_task j_i = tsk_i)
    (tsk_k : sporadic_task)
    (H_tsk_k_in_task_set : tsk_k ∈ ts)
    (R_k : time)
    (H_R_k_le_deadline : task_jitter tsk_k + R_k ≤ task_deadline tsk_k)
    (delta : time)
    (H_all_previous_jobs_completed_on_time :
      ∀ j_k : Job, arrives_in arr_seq j_k → job_task j_k = tsk_k →
        job_arrival j_k + task_jitter tsk_k + R_k < job_arrival j_i + task_jitter tsk_i + delta →
        completed job_cost sched j_k (job_arrival j_k + task_jitter tsk_k + R_k) = true)
    (H_many_jobs : div_floor (task_deadline tsk_i) (task_period tsk_k) < (((((jobs_scheduled_between sched (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost job_jitter sched j_i (j') (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y)))).length)
    (elem : Job)
    (H_only_one_job : (((((jobs_scheduled_between sched (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost job_jitter sched j_i (j') (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y)))).length = 1)
:
    job_interference job_arrival job_cost job_jitter sched j_i (((((((jobs_scheduled_between sched (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost job_jitter sched j_i (j') (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y)))).getD 0 elem)) (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta) ≤ edf_specific_interference_bound task_cost task_period task_deadline task_jitter tsk_i tsk_k R_k := by
  have ONE := interference_bound_edf_simpl_when_there's_one_job task_cost task_period task_deadline task_jitter job_arrival job_cost job_task job_jitter num_cpus sched ts H_valid_task_parameters tsk_i j_i tsk_k H_tsk_k_in_task_set R_k delta H_many_jobs H_only_one_job
  have SLACK := interference_bound_edf_interference_of_j_fst_limited_by_slack task_cost task_period task_deadline task_jitter job_arrival job_cost job_deadline job_task job_jitter H_valid_job_parameters num_cpus sched H_jobs_come_from_arrival_sequence H_completed_jobs_dont_execute H_sequential_jobs H_edf_policy tsk_i j_i H_j_i_arrives H_job_of_tsk_i tsk_k R_k H_R_k_le_deadline delta H_all_previous_jobs_completed_on_time H_many_jobs elem
  have COST := interference_bound_edf_interference_le_task_cost task_cost task_deadline task_jitter job_arrival job_cost job_deadline job_task job_jitter H_valid_job_parameters num_cpus sched H_jobs_come_from_arrival_sequence H_completed_jobs_dont_execute j_i tsk_k delta ((((((jobs_scheduled_between sched (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost job_jitter sched j_i (j') (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y)))).getD 0 elem)
    ((sorted_mem job_arrival job_cost job_jitter job_task num_cpus sched j_i tsk_k delta _).mp
      (by rw [getD_lt (by omega)]; exact List.getElem_mem _))
  have hNK0 : div_floor (task_deadline tsk_i) (task_period tsk_k) = 0 := by omega
  unfold edf_specific_interference_bound
  rw [hNK0, Nat.zero_mul, Nat.zero_add, ONE]
  exact le_min COST SLACK

/-! ### Two or more jobs -/

theorem interference_bound_edf_j_lst_is_job_of_tsk_k
    {sporadic_task : Type u} [DecidableEq sporadic_task]
    {Job : Type v} [DecidableEq Job]
    (job_arrival : Job → time)
    (job_cost : Job → time)
    (job_task : Job → sporadic_task)
    (job_jitter : Job → time)
    {arr_seq : arrival_sequence Job}
    (num_cpus : Nat)
    (sched : schedule Job num_cpus)
    (H_jobs_come_from_arrival_sequence : jobs_come_from_arrival_sequence sched arr_seq)
    (j_i : Job)
    (tsk_k : sporadic_task)
    (delta : time)
    (elem : Job)
    (num_mid_jobs : Nat)
    (H_at_least_two_jobs : (((((jobs_scheduled_between sched (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost job_jitter sched j_i (j') (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y)))).length = num_mid_jobs + 2)
:
    arrives_in arr_seq ((((((jobs_scheduled_between sched (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost job_jitter sched j_i (j') (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y)))).getD (num_mid_jobs + 1) elem) ∧
    job_task ((((((jobs_scheduled_between sched (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost job_jitter sched j_i (j') (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y)))).getD (num_mid_jobs + 1) elem) = tsk_k ∧
    (!decide (job_interference job_arrival job_cost job_jitter sched j_i (((((((jobs_scheduled_between sched (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost job_jitter sched j_i (j') (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y)))).getD (num_mid_jobs + 1) elem)) (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta) = 0)) = true ∧
    ((((((jobs_scheduled_between sched (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost job_jitter sched j_i (j') (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y)))).getD (num_mid_jobs + 1) elem) ∈ jobs_scheduled_between sched (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta) := by
  apply interference_bound_edf_all_jobs_from_tsk_k job_arrival job_cost job_task job_jitter num_cpus
    sched H_jobs_come_from_arrival_sequence j_i tsk_k delta
  rw [getD_lt (by omega)]
  exact List.getElem_mem _

theorem interference_bound_edf_j_lst_deadline
    {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost : sporadic_task → time)
    (task_deadline : sporadic_task → time)
    (task_jitter : sporadic_task → time)
    {Job : Type v} [DecidableEq Job]
    (job_arrival : Job → time)
    (job_cost : Job → time)
    (job_deadline : Job → time)
    (job_task : Job → sporadic_task)
    (job_jitter : Job → time)
    {arr_seq : arrival_sequence Job}
    (H_valid_job_parameters :
      ∀ j : Job, arrives_in arr_seq j →
        valid_sporadic_job_with_jitter task_cost task_deadline task_jitter job_cost job_deadline job_task job_jitter j)
    (num_cpus : Nat)
    (sched : schedule Job num_cpus)
    (H_jobs_come_from_arrival_sequence : jobs_come_from_arrival_sequence sched arr_seq)
    (j_i : Job)
    (tsk_k : sporadic_task)
    (delta : time)
    (elem : Job)
    (num_mid_jobs : Nat)
    (H_at_least_two_jobs : (((((jobs_scheduled_between sched (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost job_jitter sched j_i (j') (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y)))).length = num_mid_jobs + 2)
:
    job_deadline ((((((jobs_scheduled_between sched (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost job_jitter sched j_i (j') (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y)))).getD (num_mid_jobs + 1) elem) = task_deadline tsk_k := by
  obtain ⟨ARR, TSK, _, _⟩ := interference_bound_edf_j_lst_is_job_of_tsk_k job_arrival job_cost job_task job_jitter num_cpus sched H_jobs_come_from_arrival_sequence j_i tsk_k delta elem num_mid_jobs H_at_least_two_jobs
  have := (H_valid_job_parameters _ ARR).1.2.2
  simp only [job_deadline_eq_task_deadline] at this
  rw [this, TSK]

theorem interference_bound_edf_j_fst_before_j_lst
    {sporadic_task : Type u} [DecidableEq sporadic_task]
    {Job : Type v} [DecidableEq Job]
    (job_arrival : Job → time)
    (job_cost : Job → time)
    (job_task : Job → sporadic_task)
    (job_jitter : Job → time)
    (num_cpus : Nat)
    (sched : schedule Job num_cpus)
    (j_i : Job)
    (tsk_k : sporadic_task)
    (delta : time)
    (elem : Job)
    (num_mid_jobs : Nat)
    (H_at_least_two_jobs : (((((jobs_scheduled_between sched (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost job_jitter sched j_i (j') (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y)))).length = num_mid_jobs + 2)
:
    job_arrival ((((((jobs_scheduled_between sched (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost job_jitter sched j_i (j') (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y)))).getD 0 elem) ≤ job_arrival ((((((jobs_scheduled_between sched (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost job_jitter sched j_i (j') (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y)))).getD (num_mid_jobs + 1) elem) := by
  have := Prosa.Classic.Util.Sorting.prev_le_next job_arrival (((((jobs_scheduled_between sched (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost job_jitter sched j_i (j') (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y)))) elem 0 (num_mid_jobs + 1)
    (fun i hi => interference_bound_edf_jobs_ordered_by_arrival job_arrival job_cost job_task job_jitter num_cpus sched j_i tsk_k delta i elem hi) (by omega)
  simpa using this

theorem interference_bound_edf_last_job_arrives_before_end_of_interval
    {sporadic_task : Type u} [DecidableEq sporadic_task]
    {Job : Type v} [DecidableEq Job]
    (job_arrival : Job → time)
    (job_cost : Job → time)
    (job_task : Job → sporadic_task)
    (job_jitter : Job → time)
    {arr_seq : arrival_sequence Job}
    (num_cpus : Nat)
    (sched : schedule Job num_cpus)
    (H_jobs_come_from_arrival_sequence : jobs_come_from_arrival_sequence sched arr_seq)
    (H_jobs_execute_after_jitter : jobs_execute_after_jitter job_arrival job_jitter sched)
    (j_i : Job)
    (tsk_k : sporadic_task)
    (delta : time)
    (elem : Job)
    (num_mid_jobs : Nat)
    (H_at_least_two_jobs : (((((jobs_scheduled_between sched (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost job_jitter sched j_i (j') (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y)))).length = num_mid_jobs + 2)
:
    job_arrival ((((((jobs_scheduled_between sched (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost job_jitter sched j_i (j') (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y)))).getD (num_mid_jobs + 1) elem) < job_arrival j_i + job_jitter j_i + delta := by
  have H_jobs_must_arrive_to_execute :=
    arrival_before_jitter job_arrival job_jitter sched H_jobs_execute_after_jitter
  obtain ⟨_, _, NZ, _⟩ := interference_bound_edf_j_lst_is_job_of_tsk_k job_arrival job_cost job_task job_jitter num_cpus sched H_jobs_come_from_arrival_sequence j_i tsk_k delta elem num_mid_jobs H_at_least_two_jobs
  exact interfering_job_arrives_before job_arrival job_cost job_jitter num_cpus sched H_jobs_must_arrive_to_execute j_i _ _ _ NZ

theorem interference_bound_edf_j_fst_completed_on_time
    {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost : sporadic_task → time)
    (task_period : sporadic_task → time)
    (task_deadline : sporadic_task → time)
    (task_jitter : sporadic_task → time)
    {Job : Type v} [DecidableEq Job]
    (job_arrival : Job → time)
    (job_cost : Job → time)
    (job_deadline : Job → time)
    (job_task : Job → sporadic_task)
    (job_jitter : Job → time)
    {arr_seq : arrival_sequence Job}
    (H_sporadic_tasks : sporadic_task_model task_period job_arrival job_task arr_seq)
    (H_valid_job_parameters :
      ∀ j : Job, arrives_in arr_seq j →
        valid_sporadic_job_with_jitter task_cost task_deadline task_jitter job_cost job_deadline job_task job_jitter j)
    (num_cpus : Nat)
    (sched : schedule Job num_cpus)
    (H_jobs_come_from_arrival_sequence : jobs_come_from_arrival_sequence sched arr_seq)
    (H_jobs_execute_after_jitter : jobs_execute_after_jitter job_arrival job_jitter sched)
    (ts : taskset_of sporadic_task)
    (H_constrained_deadlines :
      ∀ tsk : sporadic_task, tsk ∈ ts → task_deadline tsk ≤ task_period tsk)
    (tsk_i : sporadic_task)
    (j_i : Job)
    (H_j_i_arrives : arrives_in arr_seq j_i)
    (H_job_of_tsk_i : job_task j_i = tsk_i)
    (tsk_k : sporadic_task)
    (H_tsk_k_in_task_set : tsk_k ∈ ts)
    (R_k : time)
    (H_R_k_le_deadline : task_jitter tsk_k + R_k ≤ task_deadline tsk_k)
    (delta : time)
    (H_all_previous_jobs_completed_on_time :
      ∀ j_k : Job, arrives_in arr_seq j_k → job_task j_k = tsk_k →
        job_arrival j_k + task_jitter tsk_k + R_k < job_arrival j_i + task_jitter tsk_i + delta →
        completed job_cost sched j_k (job_arrival j_k + task_jitter tsk_k + R_k) = true)
    (H_many_jobs : div_floor (task_deadline tsk_i) (task_period tsk_k) < (((((jobs_scheduled_between sched (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost job_jitter sched j_i (j') (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y)))).length)
    (elem : Job)
    (num_mid_jobs : Nat)
    (H_at_least_two_jobs : (((((jobs_scheduled_between sched (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost job_jitter sched j_i (j') (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y)))).length = num_mid_jobs + 2)
:
    completed job_cost sched ((((((jobs_scheduled_between sched (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost job_jitter sched j_i (j') (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y)))).getD 0 elem) (job_arrival ((((((jobs_scheduled_between sched (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost job_jitter sched j_i (j') (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y)))).getD 0 elem) + task_jitter tsk_k + R_k) = true := by
  have H_jobs_must_arrive_to_execute :=
    arrival_before_jitter job_arrival job_jitter sched H_jobs_execute_after_jitter
  have JIT : job_jitter j_i ≤ task_jitter tsk_i := by
    have := (H_valid_job_parameters _ H_j_i_arrives).2
    unfold job_jitter_leq_task_jitter at this
    rw [H_job_of_tsk_i] at this
    exact of_decide_eq_true this
  have h0 : 0 < (((((jobs_scheduled_between sched (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost job_jitter sched j_i (j') (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y)))).length := by omega
  have h1 : 1 < (((((jobs_scheduled_between sched (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost job_jitter sched j_i (j') (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y)))).length := by omega
  obtain ⟨FSTarr, FSTtsk, _, _⟩ := interference_bound_edf_all_jobs_from_tsk_k job_arrival job_cost job_task job_jitter num_cpus sched H_jobs_come_from_arrival_sequence j_i tsk_k delta ((((((jobs_scheduled_between sched (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost job_jitter sched j_i (j') (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y)))).getD 0 elem) (by rw [getD_lt h0]; exact List.getElem_mem _)
  obtain ⟨SNDarr, SNDtsk, SNDnz, _⟩ := interference_bound_edf_all_jobs_from_tsk_k job_arrival job_cost job_task job_jitter num_cpus sched H_jobs_come_from_arrival_sequence j_i tsk_k delta ((((((jobs_scheduled_between sched (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost job_jitter sched j_i (j') (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y)))).getD 1 elem) (by rw [getD_lt h1]; exact List.getElem_mem _)
  have SNDbefore := interfering_job_arrives_before job_arrival job_cost job_jitter num_cpus sched H_jobs_must_arrive_to_execute j_i _ _ _ SNDnz
  have ORD := interference_bound_edf_jobs_ordered_by_arrival job_arrival job_cost job_task job_jitter
    num_cpus sched j_i tsk_k delta 0 elem (by omega)
  have DIFF : ((((((jobs_scheduled_between sched (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost job_jitter sched j_i (j') (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y)))).getD 0 elem) ≠ (((((jobs_scheduled_between sched (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost job_jitter sched j_i (j') (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y)))).getD 1 elem := by
    rw [getD_lt h0, getD_lt h1]
    intro EQ
    have := (List.Nodup.getElem_inj_iff (sorted_nodup job_arrival job_cost job_jitter job_task num_cpus sched j_i tsk_k delta)).mp EQ
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
    (task_jitter : sporadic_task → time)
    {Job : Type v} [DecidableEq Job]
    (job_arrival : Job → time)
    (job_cost : Job → time)
    (job_deadline : Job → time)
    (job_task : Job → sporadic_task)
    (job_jitter : Job → time)
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
    (H_R_k_le_deadline : task_jitter tsk_k + R_k ≤ task_deadline tsk_k)
    (delta : time)
    (H_delta_le_deadline : delta ≤ task_deadline tsk_i)
    (H_many_jobs : div_floor (task_deadline tsk_i) (task_period tsk_k) < (((((jobs_scheduled_between sched (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost job_jitter sched j_i (j') (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y)))).length)
    (elem : Job)
    (num_mid_jobs : Nat)
    (H_at_least_two_jobs : (((((jobs_scheduled_between sched (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost job_jitter sched j_i (j') (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y)))).length = num_mid_jobs + 2)
:
    (num_mid_jobs + 1) * task_period tsk_k ≤ job_arrival ((((((jobs_scheduled_between sched (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost job_jitter sched j_i (j') (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y)))).getD (num_mid_jobs + 1) elem) - job_arrival ((((((jobs_scheduled_between sched (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost job_jitter sched j_i (j') (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y)))).getD 0 elem) := by
  have hlen : (((((jobs_scheduled_between sched (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost job_jitter sched j_i (j') (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y)))).length - 1 = num_mid_jobs + 1 := by omega
  have TEL := Prosa.Classic.Util.Sum.telescoping_sum Job job_arrival (((((jobs_scheduled_between sched (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost job_jitter sched j_i (j') (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y)))) elem
    (fun i hi => interference_bound_edf_jobs_ordered_by_arrival job_arrival job_cost job_task job_jitter num_cpus sched j_i tsk_k delta i elem hi)
  rw [hlen] at TEL
  rw [TEL]
  have hnd := sorted_nodup job_arrival job_cost job_jitter job_task num_cpus sched j_i tsk_k delta
  calc (num_mid_jobs + 1) * task_period tsk_k
      = ∑ _i ∈ Finset.Ico 0 (num_mid_jobs + 1), task_period tsk_k := by simp
    _ ≤ _ := by
        apply Finset.sum_le_sum
        intro i hi
        rw [Finset.mem_Ico] at hi
        have h1 : i < (((((jobs_scheduled_between sched (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost job_jitter sched j_i (j') (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y)))).length := by omega
        have h2 : i + 1 < (((((jobs_scheduled_between sched (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost job_jitter sched j_i (j') (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y)))).length := by omega
        obtain ⟨CURarr, CURtsk, _, _⟩ := interference_bound_edf_all_jobs_from_tsk_k job_arrival job_cost job_task job_jitter num_cpus sched H_jobs_come_from_arrival_sequence j_i tsk_k delta ((((((jobs_scheduled_between sched (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost job_jitter sched j_i (j') (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y)))).getD i elem) (by rw [getD_lt h1]; exact List.getElem_mem _)
        obtain ⟨NEXTarr, NEXTtsk, _, _⟩ := interference_bound_edf_all_jobs_from_tsk_k job_arrival job_cost job_task job_jitter num_cpus sched H_jobs_come_from_arrival_sequence j_i tsk_k delta ((((((jobs_scheduled_between sched (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost job_jitter sched j_i (j') (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y)))).getD (i + 1) elem) (by rw [getD_lt h2]; exact List.getElem_mem _)
        have ARRle := interference_bound_edf_jobs_ordered_by_arrival job_arrival job_cost job_task job_jitter num_cpus sched j_i tsk_k delta i elem (by omega)
        have DIFF : (((((jobs_scheduled_between sched (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost job_jitter sched j_i (j') (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y)))).getD i elem ≠ (((((jobs_scheduled_between sched (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost job_jitter sched j_i (j') (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y)))).getD (i + 1) elem := by
          rw [getD_lt h1, getD_lt h2]
          intro EQ
          have := (List.Nodup.getElem_inj_iff hnd).mp EQ
          omega
        have SPO := H_sporadic_tasks _ _ DIFF CURarr NEXTarr (CURtsk.trans NEXTtsk.symm) ARRle
        rw [CURtsk] at SPO
        omega'

theorem interference_bound_edf_n_k_covers_middle_jobs_plus_one
    {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost : sporadic_task → time)
    (task_period : sporadic_task → time)
    (task_deadline : sporadic_task → time)
    (task_jitter : sporadic_task → time)
    {Job : Type v} [DecidableEq Job]
    (job_arrival : Job → time)
    (job_cost : Job → time)
    (job_deadline : Job → time)
    (job_task : Job → sporadic_task)
    (job_jitter : Job → time)
    {arr_seq : arrival_sequence Job}
    (H_sporadic_tasks : sporadic_task_model task_period job_arrival job_task arr_seq)
    (H_valid_job_parameters :
      ∀ j : Job, arrives_in arr_seq j →
        valid_sporadic_job_with_jitter task_cost task_deadline task_jitter job_cost job_deadline job_task job_jitter j)
    (num_cpus : Nat)
    (sched : schedule Job num_cpus)
    (H_jobs_come_from_arrival_sequence : jobs_come_from_arrival_sequence sched arr_seq)
    (H_jobs_execute_after_jitter : jobs_execute_after_jitter job_arrival job_jitter sched)
    (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched)
    (H_at_least_one_cpu : 0 < num_cpus)
    (ts : taskset_of sporadic_task)
    (H_valid_task_parameters :
      valid_sporadic_taskset task_cost task_period task_deadline ts.val)
    (H_constrained_deadlines :
      ∀ tsk : sporadic_task, tsk ∈ ts → task_deadline tsk ≤ task_period tsk)
    (H_edf_policy :
      respects_JLFP_policy job_arrival job_cost job_jitter arr_seq sched (EDF job_arrival job_deadline))
    (tsk_i : sporadic_task)
    (H_tsk_i_in_task_set : tsk_i ∈ ts)
    (j_i : Job)
    (H_j_i_arrives : arrives_in arr_seq j_i)
    (H_job_of_tsk_i : job_task j_i = tsk_i)
    (tsk_k : sporadic_task)
    (H_tsk_k_in_task_set : tsk_k ∈ ts)
    (R_k : time)
    (H_R_k_le_deadline : task_jitter tsk_k + R_k ≤ task_deadline tsk_k)
    (delta : time)
    (H_delta_le_deadline : delta ≤ task_deadline tsk_i)
    (H_all_previous_jobs_completed_on_time :
      ∀ j_k : Job, arrives_in arr_seq j_k → job_task j_k = tsk_k →
        job_arrival j_k + task_jitter tsk_k + R_k < job_arrival j_i + task_jitter tsk_i + delta →
        completed job_cost sched j_k (job_arrival j_k + task_jitter tsk_k + R_k) = true)
    (H_many_jobs : div_floor (task_deadline tsk_i) (task_period tsk_k) < (((((jobs_scheduled_between sched (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost job_jitter sched j_i (j') (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y)))).length)
    (elem : Job)
    (num_mid_jobs : Nat)
    (H_at_least_two_jobs : (((((jobs_scheduled_between sched (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost job_jitter sched j_i (j') (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y)))).length = num_mid_jobs + 2)
:
    num_mid_jobs + 1 ≤ div_floor (task_deadline tsk_i) (task_period tsk_k) := by
  have DIST := interference_bound_edf_many_periods_in_between task_cost task_period task_deadline task_jitter job_arrival job_cost job_deadline job_task job_jitter H_sporadic_tasks num_cpus sched H_jobs_come_from_arrival_sequence H_at_least_one_cpu ts tsk_i H_tsk_i_in_task_set j_i tsk_k H_tsk_k_in_task_set R_k H_R_k_le_deadline delta H_delta_le_deadline H_many_jobs elem num_mid_jobs H_at_least_two_jobs
  have COMP := interference_bound_edf_j_fst_completed_on_time task_cost task_period task_deadline task_jitter job_arrival job_cost job_deadline job_task job_jitter H_sporadic_tasks H_valid_job_parameters num_cpus sched H_jobs_come_from_arrival_sequence H_jobs_execute_after_jitter ts H_constrained_deadlines tsk_i j_i H_j_i_arrives H_job_of_tsk_i tsk_k H_tsk_k_in_task_set R_k H_R_k_le_deadline delta H_all_previous_jobs_completed_on_time H_many_jobs elem num_mid_jobs H_at_least_two_jobs
  have AFTERt1 := interference_bound_edf_j_fst_completion_implies_rt_bound_inside_interval task_period task_deadline task_jitter job_arrival job_cost job_task job_jitter num_cpus sched H_jobs_come_from_arrival_sequence H_completed_jobs_dont_execute tsk_i j_i tsk_k R_k delta H_many_jobs elem COMP
  have hdl := sorted_job_deadline_le task_cost task_deadline task_jitter job_arrival job_cost job_deadline job_task job_jitter arr_seq H_valid_job_parameters num_cpus sched H_jobs_come_from_arrival_sequence H_edf_policy tsk_i j_i H_j_i_arrives H_job_of_tsk_i tsk_k delta ((((((jobs_scheduled_between sched (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost job_jitter sched j_i (j') (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y)))).getD (num_mid_jobs + 1) elem) (by rw [getD_lt (by omega)]; exact List.getElem_mem _)
  have ORD := interference_bound_edf_j_fst_before_j_lst job_arrival job_cost job_task job_jitter num_cpus sched j_i tsk_k delta elem num_mid_jobs H_at_least_two_jobs
  have hp : 0 < task_period tsk_k := by
    have := (H_valid_task_parameters tsk_k H_tsk_k_in_task_set).2.1
    simpa [task_period_positive] using this
  by_contra LTnk
  have hdiv : task_deadline tsk_i < task_period tsk_k * (div_floor (task_deadline tsk_i) (task_period tsk_k) + 1) := by
    unfold div_floor
    exact Nat.lt_mul_div_succ _ hp
  have hmul : (div_floor (task_deadline tsk_i) (task_period tsk_k) + 1) * task_period tsk_k ≤ (num_mid_jobs + 1) * task_period tsk_k :=
    Nat.mul_le_mul_right _ (by omega)
  have e1 : (div_floor (task_deadline tsk_i) (task_period tsk_k) + 1) * task_period tsk_k = task_period tsk_k * (div_floor (task_deadline tsk_i) (task_period tsk_k) + 1) := Nat.mul_comm _ _
  omega'

theorem interference_bound_edf_holds_for_middle_and_last_jobs
    {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost : sporadic_task → time)
    (task_period : sporadic_task → time)
    (task_deadline : sporadic_task → time)
    (task_jitter : sporadic_task → time)
    {Job : Type v} [DecidableEq Job]
    (job_arrival : Job → time)
    (job_cost : Job → time)
    (job_deadline : Job → time)
    (job_task : Job → sporadic_task)
    (job_jitter : Job → time)
    {arr_seq : arrival_sequence Job}
    (H_sporadic_tasks : sporadic_task_model task_period job_arrival job_task arr_seq)
    (H_valid_job_parameters :
      ∀ j : Job, arrives_in arr_seq j →
        valid_sporadic_job_with_jitter task_cost task_deadline task_jitter job_cost job_deadline job_task job_jitter j)
    (num_cpus : Nat)
    (sched : schedule Job num_cpus)
    (H_jobs_come_from_arrival_sequence : jobs_come_from_arrival_sequence sched arr_seq)
    (H_jobs_execute_after_jitter : jobs_execute_after_jitter job_arrival job_jitter sched)
    (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched)
    (H_at_least_one_cpu : 0 < num_cpus)
    (ts : taskset_of sporadic_task)
    (H_valid_task_parameters :
      valid_sporadic_taskset task_cost task_period task_deadline ts.val)
    (H_constrained_deadlines :
      ∀ tsk : sporadic_task, tsk ∈ ts → task_deadline tsk ≤ task_period tsk)
    (H_edf_policy :
      respects_JLFP_policy job_arrival job_cost job_jitter arr_seq sched (EDF job_arrival job_deadline))
    (tsk_i : sporadic_task)
    (H_tsk_i_in_task_set : tsk_i ∈ ts)
    (j_i : Job)
    (H_j_i_arrives : arrives_in arr_seq j_i)
    (H_job_of_tsk_i : job_task j_i = tsk_i)
    (tsk_k : sporadic_task)
    (H_tsk_k_in_task_set : tsk_k ∈ ts)
    (R_k : time)
    (H_R_k_le_deadline : task_jitter tsk_k + R_k ≤ task_deadline tsk_k)
    (delta : time)
    (H_delta_le_deadline : delta ≤ task_deadline tsk_i)
    (H_all_previous_jobs_completed_on_time :
      ∀ j_k : Job, arrives_in arr_seq j_k → job_task j_k = tsk_k →
        job_arrival j_k + task_jitter tsk_k + R_k < job_arrival j_i + task_jitter tsk_i + delta →
        completed job_cost sched j_k (job_arrival j_k + task_jitter tsk_k + R_k) = true)
    (H_many_jobs : div_floor (task_deadline tsk_i) (task_period tsk_k) < (((((jobs_scheduled_between sched (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost job_jitter sched j_i (j') (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y)))).length)
    (elem : Job)
    (num_mid_jobs : Nat)
    (H_at_least_two_jobs : (((((jobs_scheduled_between sched (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost job_jitter sched j_i (j') (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y)))).length = num_mid_jobs + 2)
:
    job_interference job_arrival job_cost job_jitter sched j_i (((((((jobs_scheduled_between sched (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost job_jitter sched j_i (j') (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y)))).getD (num_mid_jobs + 1) elem)) (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta) +
        ∑ i ∈ Finset.Ico 0 num_mid_jobs, job_interference job_arrival job_cost job_jitter sched j_i ((((((jobs_scheduled_between sched (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost job_jitter sched j_i (j') (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y)))).getD (i + 1) elem) (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta) ≤
      div_floor (task_deadline tsk_i) (task_period tsk_k) * task_cost tsk_k := by
  have NK := interference_bound_edf_n_k_covers_middle_jobs_plus_one task_cost task_period task_deadline task_jitter job_arrival job_cost job_deadline job_task job_jitter H_sporadic_tasks H_valid_job_parameters num_cpus sched H_jobs_come_from_arrival_sequence H_jobs_execute_after_jitter H_completed_jobs_dont_execute H_at_least_one_cpu ts H_valid_task_parameters H_constrained_deadlines H_edf_policy tsk_i H_tsk_i_in_task_set j_i H_j_i_arrives H_job_of_tsk_i tsk_k H_tsk_k_in_task_set R_k H_R_k_le_deadline delta H_delta_le_deadline H_all_previous_jobs_completed_on_time H_many_jobs elem num_mid_jobs H_at_least_two_jobs
  have COST : ∀ i, i < (((((jobs_scheduled_between sched (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost job_jitter sched j_i (j') (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y)))).length → job_interference job_arrival job_cost job_jitter sched j_i ((((((jobs_scheduled_between sched (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost job_jitter sched j_i (j') (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y)))).getD i elem) (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta) ≤ task_cost tsk_k := by
    intro i hi
    exact interference_bound_edf_interference_le_task_cost task_cost task_deadline task_jitter job_arrival job_cost job_deadline job_task job_jitter H_valid_job_parameters num_cpus sched H_jobs_come_from_arrival_sequence H_completed_jobs_dont_execute j_i tsk_k delta _
      ((sorted_mem job_arrival job_cost job_jitter job_task num_cpus sched j_i tsk_k delta _).mp
        (by rw [getD_lt hi]; exact List.getElem_mem _))
  have hlst := COST (num_mid_jobs + 1) (by omega)
  have hmid : ∑ i ∈ Finset.Ico 0 num_mid_jobs, job_interference job_arrival job_cost job_jitter sched j_i ((((((jobs_scheduled_between sched (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost job_jitter sched j_i (j') (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y)))).getD (i + 1) elem) (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta) ≤
      num_mid_jobs * task_cost tsk_k := by
    calc ∑ i ∈ Finset.Ico 0 num_mid_jobs, job_interference job_arrival job_cost job_jitter sched j_i ((((((jobs_scheduled_between sched (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost job_jitter sched j_i (j') (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y)))).getD (i + 1) elem) (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta)
        ≤ ∑ _i ∈ Finset.Ico 0 num_mid_jobs, task_cost tsk_k := by
          apply Finset.sum_le_sum
          intro i hi
          rw [Finset.mem_Ico] at hi
          exact COST (i + 1) (by omega)
      _ = num_mid_jobs * task_cost tsk_k := by simp
  have hmul := Nat.mul_le_mul_right (task_cost tsk_k) NK
  have e1 : (num_mid_jobs + 1) * task_cost tsk_k = num_mid_jobs * task_cost tsk_k +
      task_cost tsk_k := by rw [Nat.add_mul, Nat.one_mul]
  omega'

theorem interference_bound_edf_n_k_equals_num_mid_jobs_plus_one
    {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost : sporadic_task → time)
    (task_period : sporadic_task → time)
    (task_deadline : sporadic_task → time)
    (task_jitter : sporadic_task → time)
    {Job : Type v} [DecidableEq Job]
    (job_arrival : Job → time)
    (job_cost : Job → time)
    (job_deadline : Job → time)
    (job_task : Job → sporadic_task)
    (job_jitter : Job → time)
    {arr_seq : arrival_sequence Job}
    (H_sporadic_tasks : sporadic_task_model task_period job_arrival job_task arr_seq)
    (H_valid_job_parameters :
      ∀ j : Job, arrives_in arr_seq j →
        valid_sporadic_job_with_jitter task_cost task_deadline task_jitter job_cost job_deadline job_task job_jitter j)
    (num_cpus : Nat)
    (sched : schedule Job num_cpus)
    (H_jobs_come_from_arrival_sequence : jobs_come_from_arrival_sequence sched arr_seq)
    (H_jobs_execute_after_jitter : jobs_execute_after_jitter job_arrival job_jitter sched)
    (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched)
    (H_at_least_one_cpu : 0 < num_cpus)
    (ts : taskset_of sporadic_task)
    (H_valid_task_parameters :
      valid_sporadic_taskset task_cost task_period task_deadline ts.val)
    (H_constrained_deadlines :
      ∀ tsk : sporadic_task, tsk ∈ ts → task_deadline tsk ≤ task_period tsk)
    (H_edf_policy :
      respects_JLFP_policy job_arrival job_cost job_jitter arr_seq sched (EDF job_arrival job_deadline))
    (tsk_i : sporadic_task)
    (H_tsk_i_in_task_set : tsk_i ∈ ts)
    (j_i : Job)
    (H_j_i_arrives : arrives_in arr_seq j_i)
    (H_job_of_tsk_i : job_task j_i = tsk_i)
    (tsk_k : sporadic_task)
    (H_tsk_k_in_task_set : tsk_k ∈ ts)
    (R_k : time)
    (H_R_k_le_deadline : task_jitter tsk_k + R_k ≤ task_deadline tsk_k)
    (delta : time)
    (H_delta_le_deadline : delta ≤ task_deadline tsk_i)
    (H_all_previous_jobs_completed_on_time :
      ∀ j_k : Job, arrives_in arr_seq j_k → job_task j_k = tsk_k →
        job_arrival j_k + task_jitter tsk_k + R_k < job_arrival j_i + task_jitter tsk_i + delta →
        completed job_cost sched j_k (job_arrival j_k + task_jitter tsk_k + R_k) = true)
    (H_many_jobs : div_floor (task_deadline tsk_i) (task_period tsk_k) < (((((jobs_scheduled_between sched (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost job_jitter sched j_i (j') (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y)))).length)
    (elem : Job)
    (num_mid_jobs : Nat)
    (H_at_least_two_jobs : (((((jobs_scheduled_between sched (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost job_jitter sched j_i (j') (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y)))).length = num_mid_jobs + 2)
:
    div_floor (task_deadline tsk_i) (task_period tsk_k) = num_mid_jobs + 1 := by
  have NK := interference_bound_edf_n_k_covers_middle_jobs_plus_one task_cost task_period task_deadline task_jitter job_arrival job_cost job_deadline job_task job_jitter H_sporadic_tasks H_valid_job_parameters num_cpus sched H_jobs_come_from_arrival_sequence H_jobs_execute_after_jitter H_completed_jobs_dont_execute H_at_least_one_cpu ts H_valid_task_parameters H_constrained_deadlines H_edf_policy tsk_i H_tsk_i_in_task_set j_i H_j_i_arrives H_job_of_tsk_i tsk_k H_tsk_k_in_task_set R_k H_R_k_le_deadline delta H_delta_le_deadline H_all_previous_jobs_completed_on_time H_many_jobs elem num_mid_jobs H_at_least_two_jobs
  omega

/-! ### Two or more jobs: the first job -/

theorem interference_bound_edf_remainder_ge_slack
    {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost : sporadic_task → time)
    (task_period : sporadic_task → time)
    (task_deadline : sporadic_task → time)
    (task_jitter : sporadic_task → time)
    {Job : Type v} [DecidableEq Job]
    (job_arrival : Job → time)
    (job_cost : Job → time)
    (job_deadline : Job → time)
    (job_task : Job → sporadic_task)
    (job_jitter : Job → time)
    {arr_seq : arrival_sequence Job}
    (H_sporadic_tasks : sporadic_task_model task_period job_arrival job_task arr_seq)
    (H_valid_job_parameters :
      ∀ j : Job, arrives_in arr_seq j →
        valid_sporadic_job_with_jitter task_cost task_deadline task_jitter job_cost job_deadline job_task job_jitter j)
    (num_cpus : Nat)
    (sched : schedule Job num_cpus)
    (H_jobs_come_from_arrival_sequence : jobs_come_from_arrival_sequence sched arr_seq)
    (H_jobs_execute_after_jitter : jobs_execute_after_jitter job_arrival job_jitter sched)
    (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched)
    (H_at_least_one_cpu : 0 < num_cpus)
    (ts : taskset_of sporadic_task)
    (H_valid_task_parameters :
      valid_sporadic_taskset task_cost task_period task_deadline ts.val)
    (H_constrained_deadlines :
      ∀ tsk : sporadic_task, tsk ∈ ts → task_deadline tsk ≤ task_period tsk)
    (H_edf_policy :
      respects_JLFP_policy job_arrival job_cost job_jitter arr_seq sched (EDF job_arrival job_deadline))
    (tsk_i : sporadic_task)
    (H_tsk_i_in_task_set : tsk_i ∈ ts)
    (j_i : Job)
    (H_j_i_arrives : arrives_in arr_seq j_i)
    (H_job_of_tsk_i : job_task j_i = tsk_i)
    (tsk_k : sporadic_task)
    (H_tsk_k_in_task_set : tsk_k ∈ ts)
    (R_k : time)
    (H_R_k_le_deadline : task_jitter tsk_k + R_k ≤ task_deadline tsk_k)
    (delta : time)
    (H_delta_le_deadline : delta ≤ task_deadline tsk_i)
    (H_all_previous_jobs_completed_on_time :
      ∀ j_k : Job, arrives_in arr_seq j_k → job_task j_k = tsk_k →
        job_arrival j_k + task_jitter tsk_k + R_k < job_arrival j_i + task_jitter tsk_i + delta →
        completed job_cost sched j_k (job_arrival j_k + task_jitter tsk_k + R_k) = true)
    (H_many_jobs : div_floor (task_deadline tsk_i) (task_period tsk_k) < (((((jobs_scheduled_between sched (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost job_jitter sched j_i (j') (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y)))).length)
    (elem : Job)
    (num_mid_jobs : Nat)
    (H_at_least_two_jobs : (((((jobs_scheduled_between sched (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost job_jitter sched j_i (j') (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y)))).length = num_mid_jobs + 2)
:
    task_deadline tsk_k - R_k - task_jitter tsk_k ≤ task_deadline tsk_i % task_period tsk_k := by
  have NK := interference_bound_edf_n_k_equals_num_mid_jobs_plus_one task_cost task_period task_deadline task_jitter job_arrival job_cost job_deadline job_task job_jitter H_sporadic_tasks H_valid_job_parameters num_cpus sched H_jobs_come_from_arrival_sequence H_jobs_execute_after_jitter H_completed_jobs_dont_execute H_at_least_one_cpu ts H_valid_task_parameters H_constrained_deadlines H_edf_policy tsk_i H_tsk_i_in_task_set j_i H_j_i_arrives H_job_of_tsk_i tsk_k H_tsk_k_in_task_set R_k H_R_k_le_deadline delta H_delta_le_deadline H_all_previous_jobs_completed_on_time H_many_jobs elem num_mid_jobs H_at_least_two_jobs
  have DIST := interference_bound_edf_many_periods_in_between task_cost task_period task_deadline task_jitter job_arrival job_cost job_deadline job_task job_jitter H_sporadic_tasks num_cpus sched H_jobs_come_from_arrival_sequence H_at_least_one_cpu ts tsk_i H_tsk_i_in_task_set j_i tsk_k H_tsk_k_in_task_set R_k H_R_k_le_deadline delta H_delta_le_deadline H_many_jobs elem num_mid_jobs H_at_least_two_jobs
  have COMP := interference_bound_edf_j_fst_completed_on_time task_cost task_period task_deadline task_jitter job_arrival job_cost job_deadline job_task job_jitter H_sporadic_tasks H_valid_job_parameters num_cpus sched H_jobs_come_from_arrival_sequence H_jobs_execute_after_jitter ts H_constrained_deadlines tsk_i j_i H_j_i_arrives H_job_of_tsk_i tsk_k H_tsk_k_in_task_set R_k H_R_k_le_deadline delta H_all_previous_jobs_completed_on_time H_many_jobs elem num_mid_jobs H_at_least_two_jobs
  have AFTERt1 := interference_bound_edf_j_fst_completion_implies_rt_bound_inside_interval task_period task_deadline task_jitter job_arrival job_cost job_task job_jitter num_cpus sched H_jobs_come_from_arrival_sequence H_completed_jobs_dont_execute tsk_i j_i tsk_k R_k delta H_many_jobs elem COMP
  have hdl := sorted_job_deadline_le task_cost task_deadline task_jitter job_arrival job_cost job_deadline job_task job_jitter arr_seq H_valid_job_parameters num_cpus sched H_jobs_come_from_arrival_sequence H_edf_policy tsk_i j_i H_j_i_arrives H_job_of_tsk_i tsk_k delta ((((((jobs_scheduled_between sched (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost job_jitter sched j_i (j') (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y)))).getD (num_mid_jobs + 1) elem) (by rw [getD_lt (by omega)]; exact List.getElem_mem _)
  have ORD := interference_bound_edf_j_fst_before_j_lst job_arrival job_cost job_task job_jitter num_cpus sched j_i tsk_k delta elem num_mid_jobs H_at_least_two_jobs
  have hmod := Nat.mod_add_div (task_deadline tsk_i) (task_period tsk_k)
  unfold div_floor at NK
  rw [NK] at hmod
  have e1 : task_period tsk_k * (num_mid_jobs + 1) = (num_mid_jobs + 1) * task_period tsk_k :=
    Nat.mul_comm _ _
  omega'

theorem interference_bound_edf_simpl_by_moving_to_left_side
    {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_period : sporadic_task → time)
    (task_deadline : sporadic_task → time)
    (task_jitter : sporadic_task → time)
    {Job : Type v} [DecidableEq Job]
    (job_arrival : Job → time)
    (job_cost : Job → time)
    (job_task : Job → sporadic_task)
    (job_jitter : Job → time)
    (num_cpus : Nat)
    (sched : schedule Job num_cpus)
    (tsk_i : sporadic_task)
    (j_i : Job)
    (tsk_k : sporadic_task)
    (R_k : time)
    (delta : time)
    (elem : Job)
:
    job_interference job_arrival job_cost job_jitter sched j_i (((((((jobs_scheduled_between sched (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost job_jitter sched j_i (j') (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y)))).getD 0 elem)) (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta) + (task_deadline tsk_k - R_k - task_jitter tsk_k) +
        task_deadline tsk_i / task_period tsk_k * task_period tsk_k ≤ task_deadline tsk_i →
    job_interference job_arrival job_cost job_jitter sched j_i (((((((jobs_scheduled_between sched (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost job_jitter sched j_i (j') (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y)))).getD 0 elem)) (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta) ≤ task_deadline tsk_i % task_period tsk_k - (task_deadline tsk_k - R_k - task_jitter tsk_k) := by
  intro LE
  have hmod := Nat.mod_add_div (task_deadline tsk_i) (task_period tsk_k)
  have e1 : task_period tsk_k * (task_deadline tsk_i / task_period tsk_k) =
      task_deadline tsk_i / task_period tsk_k * task_period tsk_k := Nat.mul_comm _ _
  omega'

theorem interference_bound_edf_interference_of_j_fst_bounded_by_response_time
    {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost : sporadic_task → time)
    (task_period : sporadic_task → time)
    (task_deadline : sporadic_task → time)
    (task_jitter : sporadic_task → time)
    {Job : Type v} [DecidableEq Job]
    (job_arrival : Job → time)
    (job_cost : Job → time)
    (job_deadline : Job → time)
    (job_task : Job → sporadic_task)
    (job_jitter : Job → time)
    {arr_seq : arrival_sequence Job}
    (H_sporadic_tasks : sporadic_task_model task_period job_arrival job_task arr_seq)
    (H_valid_job_parameters :
      ∀ j : Job, arrives_in arr_seq j →
        valid_sporadic_job_with_jitter task_cost task_deadline task_jitter job_cost job_deadline job_task job_jitter j)
    (num_cpus : Nat)
    (sched : schedule Job num_cpus)
    (H_jobs_come_from_arrival_sequence : jobs_come_from_arrival_sequence sched arr_seq)
    (H_jobs_execute_after_jitter : jobs_execute_after_jitter job_arrival job_jitter sched)
    (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched)
    (H_sequential_jobs : sequential_jobs sched)
    (ts : taskset_of sporadic_task)
    (H_constrained_deadlines :
      ∀ tsk : sporadic_task, tsk ∈ ts → task_deadline tsk ≤ task_period tsk)
    (tsk_i : sporadic_task)
    (j_i : Job)
    (H_j_i_arrives : arrives_in arr_seq j_i)
    (H_job_of_tsk_i : job_task j_i = tsk_i)
    (tsk_k : sporadic_task)
    (H_tsk_k_in_task_set : tsk_k ∈ ts)
    (R_k : time)
    (H_R_k_le_deadline : task_jitter tsk_k + R_k ≤ task_deadline tsk_k)
    (delta : time)
    (H_all_previous_jobs_completed_on_time :
      ∀ j_k : Job, arrives_in arr_seq j_k → job_task j_k = tsk_k →
        job_arrival j_k + task_jitter tsk_k + R_k < job_arrival j_i + task_jitter tsk_i + delta →
        completed job_cost sched j_k (job_arrival j_k + task_jitter tsk_k + R_k) = true)
    (H_many_jobs : div_floor (task_deadline tsk_i) (task_period tsk_k) < (((((jobs_scheduled_between sched (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost job_jitter sched j_i (j') (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y)))).length)
    (elem : Job)
    (num_mid_jobs : Nat)
    (H_at_least_two_jobs : (((((jobs_scheduled_between sched (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost job_jitter sched j_i (j') (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y)))).length = num_mid_jobs + 2)
:
    job_interference job_arrival job_cost job_jitter sched j_i (((((((jobs_scheduled_between sched (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost job_jitter sched j_i (j') (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y)))).getD 0 elem)) (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta) ≤ ∑ _t ∈ Finset.Ico (job_arrival j_i + job_jitter j_i) (job_arrival ((((((jobs_scheduled_between sched (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost job_jitter sched j_i (j') (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y)))).getD 0 elem) + task_jitter tsk_k + R_k), 1 := by
  have COMP := interference_bound_edf_j_fst_completed_on_time task_cost task_period task_deadline task_jitter job_arrival job_cost job_deadline job_task job_jitter H_sporadic_tasks H_valid_job_parameters num_cpus sched H_jobs_come_from_arrival_sequence H_jobs_execute_after_jitter ts H_constrained_deadlines tsk_i j_i H_j_i_arrives H_job_of_tsk_i tsk_k H_tsk_k_in_task_set R_k H_R_k_le_deadline delta H_all_previous_jobs_completed_on_time H_many_jobs elem num_mid_jobs H_at_least_two_jobs
  have := job_interference_le_until_completion job_arrival job_cost job_jitter num_cpus sched H_completed_jobs_dont_execute H_sequential_jobs j_i ((((((jobs_scheduled_between sched (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost job_jitter sched j_i (j') (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y)))).getD 0 elem) (task_jitter tsk_k + R_k) (by rw [← Nat.add_assoc]; exact COMP) (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta)
  simp only [Finset.sum_const, Nat.card_Ico, smul_eq_mul, mul_one]
  omega

theorem interference_bound_edf_bounding_interference_with_interval_lengths
    {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost : sporadic_task → time)
    (task_period : sporadic_task → time)
    (task_deadline : sporadic_task → time)
    (task_jitter : sporadic_task → time)
    {Job : Type v} [DecidableEq Job]
    (job_arrival : Job → time)
    (job_cost : Job → time)
    (job_deadline : Job → time)
    (job_task : Job → sporadic_task)
    (job_jitter : Job → time)
    {arr_seq : arrival_sequence Job}
    (H_sporadic_tasks : sporadic_task_model task_period job_arrival job_task arr_seq)
    (H_valid_job_parameters :
      ∀ j : Job, arrives_in arr_seq j →
        valid_sporadic_job_with_jitter task_cost task_deadline task_jitter job_cost job_deadline job_task job_jitter j)
    (num_cpus : Nat)
    (sched : schedule Job num_cpus)
    (H_jobs_come_from_arrival_sequence : jobs_come_from_arrival_sequence sched arr_seq)
    (H_jobs_execute_after_jitter : jobs_execute_after_jitter job_arrival job_jitter sched)
    (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched)
    (H_sequential_jobs : sequential_jobs sched)
    (H_at_least_one_cpu : 0 < num_cpus)
    (ts : taskset_of sporadic_task)
    (H_valid_task_parameters :
      valid_sporadic_taskset task_cost task_period task_deadline ts.val)
    (H_constrained_deadlines :
      ∀ tsk : sporadic_task, tsk ∈ ts → task_deadline tsk ≤ task_period tsk)
    (H_edf_policy :
      respects_JLFP_policy job_arrival job_cost job_jitter arr_seq sched (EDF job_arrival job_deadline))
    (tsk_i : sporadic_task)
    (H_tsk_i_in_task_set : tsk_i ∈ ts)
    (j_i : Job)
    (H_j_i_arrives : arrives_in arr_seq j_i)
    (H_job_of_tsk_i : job_task j_i = tsk_i)
    (tsk_k : sporadic_task)
    (H_tsk_k_in_task_set : tsk_k ∈ ts)
    (R_k : time)
    (H_R_k_le_deadline : task_jitter tsk_k + R_k ≤ task_deadline tsk_k)
    (delta : time)
    (H_delta_le_deadline : delta ≤ task_deadline tsk_i)
    (H_all_previous_jobs_completed_on_time :
      ∀ j_k : Job, arrives_in arr_seq j_k → job_task j_k = tsk_k →
        job_arrival j_k + task_jitter tsk_k + R_k < job_arrival j_i + task_jitter tsk_i + delta →
        completed job_cost sched j_k (job_arrival j_k + task_jitter tsk_k + R_k) = true)
    (H_many_jobs : div_floor (task_deadline tsk_i) (task_period tsk_k) < (((((jobs_scheduled_between sched (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost job_jitter sched j_i (j') (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y)))).length)
    (elem : Job)
    (num_mid_jobs : Nat)
    (H_at_least_two_jobs : (((((jobs_scheduled_between sched (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost job_jitter sched j_i (j') (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y)))).length = num_mid_jobs + 2)
:
    job_interference job_arrival job_cost job_jitter sched j_i (((((((jobs_scheduled_between sched (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost job_jitter sched j_i (j') (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y)))).getD 0 elem)) (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta) + (task_deadline tsk_k - R_k - task_jitter tsk_k) +
        task_deadline tsk_i / task_period tsk_k * task_period tsk_k ≤
      ∑ _t ∈ Finset.Ico (job_arrival j_i + job_jitter j_i) (job_arrival ((((((jobs_scheduled_between sched (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost job_jitter sched j_i (j') (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y)))).getD 0 elem) + task_jitter tsk_k + R_k), 1 +
        ∑ _t ∈ Finset.Ico (job_arrival ((((((jobs_scheduled_between sched (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost job_jitter sched j_i (j') (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y)))).getD 0 elem) + task_jitter tsk_k + R_k) (job_arrival ((((((jobs_scheduled_between sched (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost job_jitter sched j_i (j') (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y)))).getD 0 elem) + task_deadline tsk_k), 1 +
        ∑ _t ∈ Finset.Ico (job_arrival ((((((jobs_scheduled_between sched (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost job_jitter sched j_i (j') (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y)))).getD 0 elem) + task_deadline tsk_k)
          (job_arrival ((((((jobs_scheduled_between sched (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost job_jitter sched j_i (j') (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y)))).getD (num_mid_jobs + 1) elem) + task_deadline tsk_k), 1 := by
  have RESP := interference_bound_edf_interference_of_j_fst_bounded_by_response_time task_cost task_period task_deadline task_jitter job_arrival job_cost job_deadline job_task job_jitter H_sporadic_tasks H_valid_job_parameters num_cpus sched H_jobs_come_from_arrival_sequence H_jobs_execute_after_jitter H_completed_jobs_dont_execute H_sequential_jobs ts H_constrained_deadlines tsk_i j_i H_j_i_arrives H_job_of_tsk_i tsk_k H_tsk_k_in_task_set R_k H_R_k_le_deadline delta H_all_previous_jobs_completed_on_time H_many_jobs elem num_mid_jobs H_at_least_two_jobs
  have NK := interference_bound_edf_n_k_equals_num_mid_jobs_plus_one task_cost task_period task_deadline task_jitter job_arrival job_cost job_deadline job_task job_jitter H_sporadic_tasks H_valid_job_parameters num_cpus sched H_jobs_come_from_arrival_sequence H_jobs_execute_after_jitter H_completed_jobs_dont_execute H_at_least_one_cpu ts H_valid_task_parameters H_constrained_deadlines H_edf_policy tsk_i H_tsk_i_in_task_set j_i H_j_i_arrives H_job_of_tsk_i tsk_k H_tsk_k_in_task_set R_k H_R_k_le_deadline delta H_delta_le_deadline H_all_previous_jobs_completed_on_time H_many_jobs elem num_mid_jobs H_at_least_two_jobs
  have DIST := interference_bound_edf_many_periods_in_between task_cost task_period task_deadline task_jitter job_arrival job_cost job_deadline job_task job_jitter H_sporadic_tasks num_cpus sched H_jobs_come_from_arrival_sequence H_at_least_one_cpu ts tsk_i H_tsk_i_in_task_set j_i tsk_k H_tsk_k_in_task_set R_k H_R_k_le_deadline delta H_delta_le_deadline H_many_jobs elem num_mid_jobs H_at_least_two_jobs
  unfold div_floor at NK
  rw [NK]
  simp only [Finset.sum_const, Nat.card_Ico, smul_eq_mul, Nat.mul_one] at RESP ⊢
  omega'

theorem interference_bound_edf_simpl_by_concatenation_of_intervals
    {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost : sporadic_task → time)
    (task_period : sporadic_task → time)
    (task_deadline : sporadic_task → time)
    (task_jitter : sporadic_task → time)
    {Job : Type v} [DecidableEq Job]
    (job_arrival : Job → time)
    (job_cost : Job → time)
    (job_deadline : Job → time)
    (job_task : Job → sporadic_task)
    (job_jitter : Job → time)
    {arr_seq : arrival_sequence Job}
    (H_sporadic_tasks : sporadic_task_model task_period job_arrival job_task arr_seq)
    (H_valid_job_parameters :
      ∀ j : Job, arrives_in arr_seq j →
        valid_sporadic_job_with_jitter task_cost task_deadline task_jitter job_cost job_deadline job_task job_jitter j)
    (num_cpus : Nat)
    (sched : schedule Job num_cpus)
    (H_jobs_come_from_arrival_sequence : jobs_come_from_arrival_sequence sched arr_seq)
    (H_jobs_execute_after_jitter : jobs_execute_after_jitter job_arrival job_jitter sched)
    (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched)
    (ts : taskset_of sporadic_task)
    (H_constrained_deadlines :
      ∀ tsk : sporadic_task, tsk ∈ ts → task_deadline tsk ≤ task_period tsk)
    (tsk_i : sporadic_task)
    (j_i : Job)
    (H_j_i_arrives : arrives_in arr_seq j_i)
    (H_job_of_tsk_i : job_task j_i = tsk_i)
    (tsk_k : sporadic_task)
    (H_tsk_k_in_task_set : tsk_k ∈ ts)
    (R_k : time)
    (H_R_k_le_deadline : task_jitter tsk_k + R_k ≤ task_deadline tsk_k)
    (delta : time)
    (H_all_previous_jobs_completed_on_time :
      ∀ j_k : Job, arrives_in arr_seq j_k → job_task j_k = tsk_k →
        job_arrival j_k + task_jitter tsk_k + R_k < job_arrival j_i + task_jitter tsk_i + delta →
        completed job_cost sched j_k (job_arrival j_k + task_jitter tsk_k + R_k) = true)
    (H_many_jobs : div_floor (task_deadline tsk_i) (task_period tsk_k) < (((((jobs_scheduled_between sched (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost job_jitter sched j_i (j') (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y)))).length)
    (elem : Job)
    (num_mid_jobs : Nat)
    (H_at_least_two_jobs : (((((jobs_scheduled_between sched (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost job_jitter sched j_i (j') (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y)))).length = num_mid_jobs + 2)
:
    ∑ _t ∈ Finset.Ico (job_arrival j_i + job_jitter j_i) (job_arrival ((((((jobs_scheduled_between sched (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost job_jitter sched j_i (j') (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y)))).getD 0 elem) + task_jitter tsk_k + R_k), 1 +
        ∑ _t ∈ Finset.Ico (job_arrival ((((((jobs_scheduled_between sched (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost job_jitter sched j_i (j') (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y)))).getD 0 elem) + task_jitter tsk_k + R_k) (job_arrival ((((((jobs_scheduled_between sched (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost job_jitter sched j_i (j') (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y)))).getD 0 elem) + task_deadline tsk_k), 1 +
        ∑ _t ∈ Finset.Ico (job_arrival ((((((jobs_scheduled_between sched (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost job_jitter sched j_i (j') (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y)))).getD 0 elem) + task_deadline tsk_k)
          (job_arrival ((((((jobs_scheduled_between sched (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost job_jitter sched j_i (j') (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y)))).getD (num_mid_jobs + 1) elem) + task_deadline tsk_k), 1 =
      job_arrival ((((((jobs_scheduled_between sched (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost job_jitter sched j_i (j') (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y)))).getD (num_mid_jobs + 1) elem) + task_deadline tsk_k - (job_arrival j_i + job_jitter j_i) := by
  have COMP := interference_bound_edf_j_fst_completed_on_time task_cost task_period task_deadline task_jitter job_arrival job_cost job_deadline job_task job_jitter H_sporadic_tasks H_valid_job_parameters num_cpus sched H_jobs_come_from_arrival_sequence H_jobs_execute_after_jitter ts H_constrained_deadlines tsk_i j_i H_j_i_arrives H_job_of_tsk_i tsk_k H_tsk_k_in_task_set R_k H_R_k_le_deadline delta H_all_previous_jobs_completed_on_time H_many_jobs elem num_mid_jobs H_at_least_two_jobs
  have AFTERt1 := interference_bound_edf_j_fst_completion_implies_rt_bound_inside_interval task_period task_deadline task_jitter job_arrival job_cost job_task job_jitter num_cpus sched H_jobs_come_from_arrival_sequence H_completed_jobs_dont_execute tsk_i j_i tsk_k R_k delta H_many_jobs elem COMP
  have ORD := interference_bound_edf_j_fst_before_j_lst job_arrival job_cost job_task job_jitter num_cpus sched j_i tsk_k delta elem num_mid_jobs H_at_least_two_jobs
  simp only [Finset.sum_const, Nat.card_Ico, smul_eq_mul, Nat.mul_one]
  omega'

theorem interference_bound_edf_interference_of_j_fst_limited_by_remainder_and_slack
    {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost : sporadic_task → time)
    (task_period : sporadic_task → time)
    (task_deadline : sporadic_task → time)
    (task_jitter : sporadic_task → time)
    {Job : Type v} [DecidableEq Job]
    (job_arrival : Job → time)
    (job_cost : Job → time)
    (job_deadline : Job → time)
    (job_task : Job → sporadic_task)
    (job_jitter : Job → time)
    {arr_seq : arrival_sequence Job}
    (H_sporadic_tasks : sporadic_task_model task_period job_arrival job_task arr_seq)
    (H_valid_job_parameters :
      ∀ j : Job, arrives_in arr_seq j →
        valid_sporadic_job_with_jitter task_cost task_deadline task_jitter job_cost job_deadline job_task job_jitter j)
    (num_cpus : Nat)
    (sched : schedule Job num_cpus)
    (H_jobs_come_from_arrival_sequence : jobs_come_from_arrival_sequence sched arr_seq)
    (H_jobs_execute_after_jitter : jobs_execute_after_jitter job_arrival job_jitter sched)
    (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched)
    (H_sequential_jobs : sequential_jobs sched)
    (H_at_least_one_cpu : 0 < num_cpus)
    (ts : taskset_of sporadic_task)
    (H_valid_task_parameters :
      valid_sporadic_taskset task_cost task_period task_deadline ts.val)
    (H_constrained_deadlines :
      ∀ tsk : sporadic_task, tsk ∈ ts → task_deadline tsk ≤ task_period tsk)
    (H_edf_policy :
      respects_JLFP_policy job_arrival job_cost job_jitter arr_seq sched (EDF job_arrival job_deadline))
    (tsk_i : sporadic_task)
    (H_tsk_i_in_task_set : tsk_i ∈ ts)
    (j_i : Job)
    (H_j_i_arrives : arrives_in arr_seq j_i)
    (H_job_of_tsk_i : job_task j_i = tsk_i)
    (tsk_k : sporadic_task)
    (H_tsk_k_in_task_set : tsk_k ∈ ts)
    (R_k : time)
    (H_R_k_le_deadline : task_jitter tsk_k + R_k ≤ task_deadline tsk_k)
    (delta : time)
    (H_delta_le_deadline : delta ≤ task_deadline tsk_i)
    (H_all_previous_jobs_completed_on_time :
      ∀ j_k : Job, arrives_in arr_seq j_k → job_task j_k = tsk_k →
        job_arrival j_k + task_jitter tsk_k + R_k < job_arrival j_i + task_jitter tsk_i + delta →
        completed job_cost sched j_k (job_arrival j_k + task_jitter tsk_k + R_k) = true)
    (H_many_jobs : div_floor (task_deadline tsk_i) (task_period tsk_k) < (((((jobs_scheduled_between sched (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost job_jitter sched j_i (j') (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y)))).length)
    (elem : Job)
    (num_mid_jobs : Nat)
    (H_at_least_two_jobs : (((((jobs_scheduled_between sched (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost job_jitter sched j_i (j') (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y)))).length = num_mid_jobs + 2)
:
    job_interference job_arrival job_cost job_jitter sched j_i (((((((jobs_scheduled_between sched (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost job_jitter sched j_i (j') (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y)))).getD 0 elem)) (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta) ≤ task_deadline tsk_i % task_period tsk_k - (task_deadline tsk_k - R_k - task_jitter tsk_k) := by
  apply interference_bound_edf_simpl_by_moving_to_left_side task_period task_deadline task_jitter job_arrival job_cost job_task job_jitter num_cpus sched tsk_i j_i tsk_k R_k delta elem
  have BOUND := interference_bound_edf_bounding_interference_with_interval_lengths task_cost task_period task_deadline task_jitter job_arrival job_cost job_deadline job_task job_jitter H_sporadic_tasks H_valid_job_parameters num_cpus sched H_jobs_come_from_arrival_sequence H_jobs_execute_after_jitter H_completed_jobs_dont_execute H_sequential_jobs H_at_least_one_cpu ts H_valid_task_parameters H_constrained_deadlines H_edf_policy tsk_i H_tsk_i_in_task_set j_i H_j_i_arrives H_job_of_tsk_i tsk_k H_tsk_k_in_task_set R_k H_R_k_le_deadline delta H_delta_le_deadline H_all_previous_jobs_completed_on_time H_many_jobs elem num_mid_jobs H_at_least_two_jobs
  have CONCAT := interference_bound_edf_simpl_by_concatenation_of_intervals task_cost task_period task_deadline task_jitter job_arrival job_cost job_deadline job_task job_jitter H_sporadic_tasks H_valid_job_parameters num_cpus sched H_jobs_come_from_arrival_sequence H_jobs_execute_after_jitter H_completed_jobs_dont_execute ts H_constrained_deadlines tsk_i j_i H_j_i_arrives H_job_of_tsk_i tsk_k H_tsk_k_in_task_set R_k H_R_k_le_deadline delta H_all_previous_jobs_completed_on_time H_many_jobs elem num_mid_jobs H_at_least_two_jobs
  have hdl := sorted_job_deadline_le task_cost task_deadline task_jitter job_arrival job_cost job_deadline job_task job_jitter arr_seq H_valid_job_parameters num_cpus sched H_jobs_come_from_arrival_sequence H_edf_policy tsk_i j_i H_j_i_arrives H_job_of_tsk_i tsk_k delta ((((((jobs_scheduled_between sched (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost job_jitter sched j_i (j') (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y)))).getD (num_mid_jobs + 1) elem) (by rw [getD_lt (by omega)]; exact List.getElem_mem _)
  rw [CONCAT] at BOUND
  omega'

theorem interference_bound_edf_holds_for_multiple_jobs
    {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost : sporadic_task → time)
    (task_period : sporadic_task → time)
    (task_deadline : sporadic_task → time)
    (task_jitter : sporadic_task → time)
    {Job : Type v} [DecidableEq Job]
    (job_arrival : Job → time)
    (job_cost : Job → time)
    (job_deadline : Job → time)
    (job_task : Job → sporadic_task)
    (job_jitter : Job → time)
    {arr_seq : arrival_sequence Job}
    (H_sporadic_tasks : sporadic_task_model task_period job_arrival job_task arr_seq)
    (H_valid_job_parameters :
      ∀ j : Job, arrives_in arr_seq j →
        valid_sporadic_job_with_jitter task_cost task_deadline task_jitter job_cost job_deadline job_task job_jitter j)
    (num_cpus : Nat)
    (sched : schedule Job num_cpus)
    (H_jobs_come_from_arrival_sequence : jobs_come_from_arrival_sequence sched arr_seq)
    (H_jobs_execute_after_jitter : jobs_execute_after_jitter job_arrival job_jitter sched)
    (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched)
    (H_sequential_jobs : sequential_jobs sched)
    (H_at_least_one_cpu : 0 < num_cpus)
    (ts : taskset_of sporadic_task)
    (H_valid_task_parameters :
      valid_sporadic_taskset task_cost task_period task_deadline ts.val)
    (H_constrained_deadlines :
      ∀ tsk : sporadic_task, tsk ∈ ts → task_deadline tsk ≤ task_period tsk)
    (H_edf_policy :
      respects_JLFP_policy job_arrival job_cost job_jitter arr_seq sched (EDF job_arrival job_deadline))
    (tsk_i : sporadic_task)
    (H_tsk_i_in_task_set : tsk_i ∈ ts)
    (j_i : Job)
    (H_j_i_arrives : arrives_in arr_seq j_i)
    (H_job_of_tsk_i : job_task j_i = tsk_i)
    (tsk_k : sporadic_task)
    (H_tsk_k_in_task_set : tsk_k ∈ ts)
    (R_k : time)
    (H_R_k_le_deadline : task_jitter tsk_k + R_k ≤ task_deadline tsk_k)
    (delta : time)
    (H_delta_le_deadline : delta ≤ task_deadline tsk_i)
    (H_all_previous_jobs_completed_on_time :
      ∀ j_k : Job, arrives_in arr_seq j_k → job_task j_k = tsk_k →
        job_arrival j_k + task_jitter tsk_k + R_k < job_arrival j_i + task_jitter tsk_i + delta →
        completed job_cost sched j_k (job_arrival j_k + task_jitter tsk_k + R_k) = true)
    (H_many_jobs : div_floor (task_deadline tsk_i) (task_period tsk_k) < (((((jobs_scheduled_between sched (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost job_jitter sched j_i (j') (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y)))).length)
    (elem : Job)
    (num_mid_jobs : Nat)
    (H_at_least_two_jobs : (((((jobs_scheduled_between sched (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost job_jitter sched j_i (j') (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y)))).length = num_mid_jobs + 2)
:
    ∑ i ∈ Finset.Ico 0 (num_mid_jobs + 2), job_interference job_arrival job_cost job_jitter sched j_i ((((((jobs_scheduled_between sched (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost job_jitter sched j_i (j') (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y)))).getD i elem) (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta) ≤ edf_specific_interference_bound task_cost task_period task_deadline task_jitter tsk_i tsk_k R_k := by
  have SPLIT : ∑ i ∈ Finset.Ico 0 (num_mid_jobs + 2), job_interference job_arrival job_cost job_jitter sched j_i ((((((jobs_scheduled_between sched (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost job_jitter sched j_i (j') (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y)))).getD i elem) (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta) =
      job_interference job_arrival job_cost job_jitter sched j_i (((((((jobs_scheduled_between sched (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost job_jitter sched j_i (j') (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y)))).getD (num_mid_jobs + 1) elem)) (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta) + job_interference job_arrival job_cost job_jitter sched j_i (((((((jobs_scheduled_between sched (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost job_jitter sched j_i (j') (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y)))).getD 0 elem)) (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta) +
        ∑ i ∈ Finset.Ico 0 num_mid_jobs, job_interference job_arrival job_cost job_jitter sched j_i ((((((jobs_scheduled_between sched (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost job_jitter sched j_i (j') (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y)))).getD (i + 1) elem) (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta) := by
    rw [← Finset.range_eq_Ico, ← Finset.range_eq_Ico, show num_mid_jobs + 2 =
      num_mid_jobs + 1 + 1 from rfl, Finset.sum_range_succ, Finset.sum_range_succ']
    omega
  have MID := interference_bound_edf_holds_for_middle_and_last_jobs task_cost task_period task_deadline task_jitter job_arrival job_cost job_deadline job_task job_jitter H_sporadic_tasks H_valid_job_parameters num_cpus sched H_jobs_come_from_arrival_sequence H_jobs_execute_after_jitter H_completed_jobs_dont_execute H_at_least_one_cpu ts H_valid_task_parameters H_constrained_deadlines H_edf_policy tsk_i H_tsk_i_in_task_set j_i H_j_i_arrives H_job_of_tsk_i tsk_k H_tsk_k_in_task_set R_k H_R_k_le_deadline delta H_delta_le_deadline H_all_previous_jobs_completed_on_time H_many_jobs elem num_mid_jobs H_at_least_two_jobs
  have FSTrem := interference_bound_edf_interference_of_j_fst_limited_by_remainder_and_slack task_cost task_period task_deadline task_jitter job_arrival job_cost job_deadline job_task job_jitter H_sporadic_tasks H_valid_job_parameters num_cpus sched H_jobs_come_from_arrival_sequence H_jobs_execute_after_jitter H_completed_jobs_dont_execute H_sequential_jobs H_at_least_one_cpu ts H_valid_task_parameters H_constrained_deadlines H_edf_policy tsk_i H_tsk_i_in_task_set j_i H_j_i_arrives H_job_of_tsk_i tsk_k H_tsk_k_in_task_set R_k H_R_k_le_deadline delta H_delta_le_deadline H_all_previous_jobs_completed_on_time H_many_jobs elem num_mid_jobs H_at_least_two_jobs
  have FSTcost := interference_bound_edf_interference_le_task_cost task_cost task_deadline task_jitter job_arrival job_cost job_deadline job_task job_jitter H_valid_job_parameters num_cpus sched H_jobs_come_from_arrival_sequence H_completed_jobs_dont_execute j_i tsk_k delta ((((((jobs_scheduled_between sched (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost job_jitter sched j_i (j') (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y)))).getD 0 elem)
    ((sorted_mem job_arrival job_cost job_jitter job_task num_cpus sched j_i tsk_k delta _).mp
      (by rw [getD_lt (by omega)]; exact List.getElem_mem _))
  have hmin := le_min FSTcost FSTrem
  rw [SPLIT]
  unfold edf_specific_interference_bound
  omega'

/-! ### Main theorem -/

theorem interference_bound_edf_bounds_interference
    {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost : sporadic_task → time)
    (task_period : sporadic_task → time)
    (task_deadline : sporadic_task → time)
    (task_jitter : sporadic_task → time)
    {Job : Type v} [DecidableEq Job]
    (job_arrival : Job → time)
    (job_cost : Job → time)
    (job_deadline : Job → time)
    (job_task : Job → sporadic_task)
    (job_jitter : Job → time)
    {arr_seq : arrival_sequence Job}
    (H_sporadic_tasks : sporadic_task_model task_period job_arrival job_task arr_seq)
    (H_valid_job_parameters :
      ∀ j : Job, arrives_in arr_seq j →
        valid_sporadic_job_with_jitter task_cost task_deadline task_jitter job_cost job_deadline job_task job_jitter j)
    (num_cpus : Nat)
    (sched : schedule Job num_cpus)
    (H_jobs_come_from_arrival_sequence : jobs_come_from_arrival_sequence sched arr_seq)
    (H_jobs_execute_after_jitter : jobs_execute_after_jitter job_arrival job_jitter sched)
    (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched)
    (H_sequential_jobs : sequential_jobs sched)
    (H_at_least_one_cpu : 0 < num_cpus)
    (ts : taskset_of sporadic_task)
    (H_valid_task_parameters :
      valid_sporadic_taskset task_cost task_period task_deadline ts.val)
    (H_constrained_deadlines :
      ∀ tsk : sporadic_task, tsk ∈ ts → task_deadline tsk ≤ task_period tsk)
    (H_edf_policy :
      respects_JLFP_policy job_arrival job_cost job_jitter arr_seq sched (EDF job_arrival job_deadline))
    (tsk_i : sporadic_task)
    (H_tsk_i_in_task_set : tsk_i ∈ ts)
    (j_i : Job)
    (H_j_i_arrives : arrives_in arr_seq j_i)
    (H_job_of_tsk_i : job_task j_i = tsk_i)
    (tsk_k : sporadic_task)
    (H_tsk_k_in_task_set : tsk_k ∈ ts)
    (R_k : time)
    (H_R_k_le_deadline : task_jitter tsk_k + R_k ≤ task_deadline tsk_k)
    (delta : time)
    (H_delta_le_deadline : delta ≤ task_deadline tsk_i)
    (H_all_previous_jobs_completed_on_time :
      ∀ j_k : Job, arrives_in arr_seq j_k → job_task j_k = tsk_k →
        job_arrival j_k + task_jitter tsk_k + R_k < job_arrival j_i + task_jitter tsk_i + delta →
        completed job_cost sched j_k (job_arrival j_k + task_jitter tsk_k + R_k) = true)
:
    task_interference job_arrival job_cost job_task job_jitter sched j_i tsk_k (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta) ≤ edf_specific_interference_bound task_cost task_period task_deadline task_jitter tsk_i tsk_k R_k := by
  have h1 := interference_bound_edf_use_another_definition job_arrival job_cost job_task job_jitter num_cpus sched j_i tsk_k delta
  rw [interference_bound_edf_simpl_by_filtering_interfering_jobs job_arrival job_cost job_task job_jitter num_cpus sched j_i tsk_k delta,
    interference_bound_edf_simpl_by_sorting_interfering_jobs job_arrival job_cost job_task job_jitter num_cpus sched j_i tsk_k delta] at h1
  refine le_trans h1 ?_
  by_cases NUM : (((((jobs_scheduled_between sched (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost job_jitter sched j_i (j') (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y)))).length ≤ div_floor (task_deadline tsk_i) (task_period tsk_k)
  · exact interference_bound_edf_holds_for_at_most_n_k_jobs task_cost task_period task_deadline task_jitter job_arrival job_cost job_deadline job_task job_jitter H_valid_job_parameters num_cpus sched H_jobs_come_from_arrival_sequence H_completed_jobs_dont_execute tsk_i j_i tsk_k R_k delta NUM
  have NUM : div_floor (task_deadline tsk_i) (task_period tsk_k) < (((((jobs_scheduled_between sched (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost job_jitter sched j_i (j') (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y)))).length := by omega
  obtain ⟨elem, _⟩ := List.exists_mem_of_length_pos (by omega : 0 < (((((jobs_scheduled_between sched (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost job_jitter sched j_i (j') (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y)))).length)
  rw [sumSeq_getD _ _ elem]
  obtain hlen | ⟨num_mid_jobs, hlen⟩ :
      (((((jobs_scheduled_between sched (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost job_jitter sched j_i (j') (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y)))).length = 1 ∨ ∃ m, (((((jobs_scheduled_between sched (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost job_jitter sched j_i (j') (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y)))).length = m + 2 := by
    rcases h : (((((jobs_scheduled_between sched (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta)).filter (fun j' =>
        decide (job_task j' = tsk_k) && !decide (job_interference job_arrival job_cost job_jitter sched j_i (j') (job_arrival j_i + job_jitter j_i) (job_arrival j_i + job_jitter j_i + delta) = 0)))).mergeSort (fun x y => decide (job_arrival x ≤ job_arrival y)))).length with _ | _ | m
    · omega
    · exact Or.inl rfl
    · exact Or.inr ⟨m, rfl⟩
  · rw [hlen, ← Finset.range_eq_Ico, Finset.sum_range_one]
    exact interference_bound_edf_holds_for_a_single_job task_cost task_period task_deadline task_jitter job_arrival job_cost job_deadline job_task job_jitter H_valid_job_parameters num_cpus sched H_jobs_come_from_arrival_sequence H_completed_jobs_dont_execute H_sequential_jobs ts H_valid_task_parameters H_edf_policy tsk_i j_i H_j_i_arrives H_job_of_tsk_i tsk_k H_tsk_k_in_task_set R_k H_R_k_le_deadline delta H_all_previous_jobs_completed_on_time NUM elem hlen
  · rw [hlen]
    exact interference_bound_edf_holds_for_multiple_jobs task_cost task_period task_deadline task_jitter job_arrival job_cost job_deadline job_task job_jitter H_sporadic_tasks H_valid_job_parameters num_cpus sched H_jobs_come_from_arrival_sequence H_jobs_execute_after_jitter H_completed_jobs_dont_execute H_sequential_jobs H_at_least_one_cpu ts H_valid_task_parameters H_constrained_deadlines H_edf_policy tsk_i H_tsk_i_in_task_set j_i H_j_i_arrives H_job_of_tsk_i tsk_k H_tsk_k_in_task_set R_k H_R_k_le_deadline delta H_delta_le_deadline H_all_previous_jobs_completed_on_time NUM elem num_mid_jobs hlen

/-! ### Monotonicity of the EDF-specific bound -/

theorem interference_bound_edf_monotonic
    {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost : sporadic_task → time)
    (task_period : sporadic_task → time)
    (task_deadline : sporadic_task → time)
    (task_jitter : sporadic_task → time)
    (tsk : sporadic_task)
    (tsk_other : sporadic_task)
    (H_period_positive : 0 < task_period tsk_other)
    (delta : time)
    (delta' : time)
    (R : time)
    (R' : time)
    (H_delta_monotonic : delta ≤ delta')
    (H_response_time_monotonic : R ≤ R')
    (H_cost_le_rt_bound : task_cost tsk_other ≤ R)
:
    interference_bound_edf task_cost task_period task_deadline task_jitter tsk delta (tsk_other, R) ≤
      interference_bound_edf task_cost task_period task_deadline task_jitter tsk delta' (tsk_other, R') := by
  have hW := W_monotonic task_cost task_period task_jitter tsk_other H_period_positive R R'
    H_cost_le_rt_bound H_response_time_monotonic delta delta' H_delta_monotonic
  unfold interference_bound_edf interference_bound_generic edf_specific_interference_bound
  apply min_le_min
  · exact min_le_min hW (by omega')
  · exact Nat.add_le_add_left (min_le_min (Nat.le_refl _) (by omega')) _

end Prosa.Classic.Analysis.Global.Jitter.InterferenceBoundEdf.InterferenceBoundEDFJitter
