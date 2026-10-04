-- Authoritative source:
-- ProsaBuddy classic Prosa (prosabuddy commit f692cb7479780cf6009493f373a309e13165201c)
-- source: classic/analysis/global/basic/workload_bound.v
-- sha256: see Prosa-Shunqi/classic-prosa/casestudy-translation/file_order.csv (rank 36)

import Prosa.Util.Sum
import Prosa.Classic.Util.DivMod
import Prosa.Classic.Util.Sum
import Prosa.Classic.Util.Sorting
import Prosa.Classic.Model.Arrival.Basic.Task
import Prosa.Classic.Model.Arrival.Basic.Job
import Prosa.Classic.Model.Arrival.Basic.TaskArrival
import Prosa.Classic.Model.Schedule.Global.Workload
import Prosa.Classic.Model.Schedule.Global.ResponseTime
import Prosa.Classic.Model.Schedule.Global.Schedulability
import Prosa.Classic.Model.Schedule.Global.Basic.Schedule

/-!
Bertogna and Cirinei's workload bound (Rocq module `WorkloadBound`, classic/analysis/global/basic/workload_bound.v).

Representation notes:
* The section-local `Let`s are unfolded in the statements: `sorted_jobs` is
  `(jobs_of_task_scheduled_between job_task sched tsk t1 (t1 + delta)).mergeSort
  (fun x y => decide (job_arrival x ≤ job_arrival y))` (MathComp's stable `sort`),
  `t2` is `t1 + delta`, `n_k` is `max_jobs task_cost task_period tsk R_tsk delta`,
  `workload_bound` is `W task_cost task_period tsk R_tsk delta`, `workload_of` is
  `workload job_task sched`, `job_has_completed_by` is `completed job_cost sched`,
  and `j_fst` / `j_lst` are `sorted_jobs.getD 0 elem` /
  `sorted_jobs.getD (num_mid_jobs + 1) elem`.
* The `let e_k := … in let p_k := … in` of `W` is inlined; `minn` is `min`.
* `\sum_(i <- s) F i` is `Prosa.Util.Sum.sumSeq s F`; `\sum_(a <= i < b)` is
  `∑ i ∈ Finset.Ico a b`; `x != 0` in proposition position is
  `(!decide (x = 0)) = true`; `j \in s` as a Boolean equation is `decide (j ∈ s)`.
* Binder lists follow the Rocq contract (`About` on the Rocq 9.3 reference build).
-/

set_option linter.dupNamespace false
-- Binder lists follow the Rocq contract, which abstracts some section hypotheses
-- that a proof does not use (e.g. `H_period_positive` in `W_monotonic`).
set_option linter.unusedVariables false

namespace Prosa.Classic.Analysis.Global.Basic.WorkloadBound.WorkloadBound

open Prosa.Classic.Model.Time.Time
open Prosa.Classic.Model.Arrival.Basic.ArrivalSequence.ArrivalSequence
open Prosa.Classic.Model.Arrival.Basic.Task.SporadicTaskset
open Prosa.Classic.Model.Arrival.Basic.Job.Job
open Prosa.Classic.Model.Arrival.Basic.TaskArrival.TaskArrival
open Prosa.Classic.Model.Schedule.Global.Basic.Schedule.Schedule
open Prosa.Classic.Model.Schedule.Global.Basic.Schedule.ScheduleOfSporadicTask
open Prosa.Classic.Model.Schedule.Global.ResponseTime.ResponseTime
open Prosa.Classic.Model.Schedule.Global.Workload.Workload
open Prosa.Classic.Util.DivMod (div_floor divSn_cases subndiv_eq_mod)
open Prosa.Util.Sum (sumSeq)
open BigOperators

universe u v

local macro "omega'" : tactic =>
  `(tactic| ((try dsimp only [Prosa.Classic.Model.Time.Time.time,
    Prosa.Classic.Model.Time.Time.instant, Prosa.Classic.Model.Time.Time.duration] at *) <;>
    omega))

/-! ### Bertogna and Cirinei's workload bound -/

def max_jobs {sporadic_task : Type u} [DecidableEq sporadic_task] (task_cost task_period : sporadic_task → time) (tsk : sporadic_task)
    (R_tsk delta : time) : Nat :=
  div_floor (delta + R_tsk - task_cost tsk) (task_period tsk)

def W {sporadic_task : Type u} [DecidableEq sporadic_task] (task_cost task_period : sporadic_task → time) (tsk : sporadic_task)
    (R_tsk delta : time) : Nat :=
  min (task_cost tsk)
      (delta + R_tsk - task_cost tsk - max_jobs task_cost task_period tsk R_tsk delta *
        task_period tsk) +
    max_jobs task_cost task_period tsk R_tsk delta * task_cost tsk

/-- LEAN_HELPER: `W` as a function of the remaining length `delta + R - e`. -/
private theorem W_eq {sporadic_task : Type u} [DecidableEq sporadic_task] (task_cost task_period : sporadic_task → time) (tsk : sporadic_task)
    (R_tsk delta : time) :
    W task_cost task_period tsk R_tsk delta =
      min (task_cost tsk) ((delta + R_tsk - task_cost tsk) % task_period tsk) +
        (delta + R_tsk - task_cost tsk) / task_period tsk * task_cost tsk := by
  unfold W max_jobs div_floor
  rw [subndiv_eq_mod]

/-- LEAN_HELPER: `y ↦ min e (y % p) + (y / p) * e` is monotone. -/
private theorem W_core_monotone (e p : Nat) : Monotone (fun y => min e (y % p) + y / p * e) := by
  apply monotone_nat_of_le_succ
  intro y
  rcases Nat.lt_or_ge 1 p with hp | hp
  · rcases divSn_cases y p hp with ⟨h1, h2⟩ | h
    · simp only [← h1, ← h2]
      have := min_le_min_left e (Nat.le_succ (y % p))
      omega
    · simp only [← h, Nat.add_mul, Nat.one_mul]
      have := min_le_left e (y % p)
      omega
  · interval_cases p
    · simp only [Nat.mod_zero, Nat.div_zero, Nat.zero_mul, Nat.add_zero]
      exact min_le_min_left e (Nat.le_succ y)
    · simp only [Nat.mod_one, Nat.div_one, Nat.add_mul, Nat.one_mul]
      omega

theorem W_monotonic {sporadic_task : Type u} [DecidableEq sporadic_task] (task_cost task_period : sporadic_task → time) (tsk : sporadic_task)
    (H_period_positive : 0 < task_period tsk) (R1 R2 : time)
    (H_R_lower_bound : task_cost tsk ≤ R1) (H_R1_le_R2 : R1 ≤ R2) :
    ∀ t1 t2 : time,
      t1 ≤ t2 →
      W task_cost task_period tsk R1 t1 ≤ W task_cost task_period tsk R2 t2 := by
  intro t1 t2 LEt
  rw [W_eq, W_eq]
  exact W_core_monotone (task_cost tsk) (task_period tsk) (by omega')

/-! ### LEAN_HELPER lemmas about the sorted job list -/

/-- LEAN_HELPER: defaulted lookup inside the list. -/
private theorem getD_lt {α : Type _} {l : List α} {i : Nat} {d : α} (h : i < l.length) :
    l.getD i d = l[i] := by
  simp [List.getD_eq_getElem?_getD, h]

/-- LEAN_HELPER: the sorted list has the same elements. -/
private theorem sorted_mem {sporadic_task : Type u} {Job : Type v} [DecidableEq sporadic_task] [DecidableEq Job] (job_arrival : Job → time) (job_task : Job → sporadic_task)
    {num_cpus : Nat} (sched : schedule Job num_cpus) (tsk : sporadic_task) (t1 delta : time)
    (j : Job) :
    j ∈ ((jobs_of_task_scheduled_between job_task sched tsk t1 (t1 + delta)).mergeSort
        (fun x y => decide (job_arrival x ≤ job_arrival y))) ↔ j ∈ jobs_of_task_scheduled_between job_task sched tsk t1 (t1 + delta) :=
  List.mem_mergeSort

/-- LEAN_HELPER: the sorted list has no duplicates. -/
private theorem sorted_nodup {sporadic_task : Type u} {Job : Type v} [DecidableEq sporadic_task] [DecidableEq Job] (job_arrival : Job → time) (job_task : Job → sporadic_task)
    {num_cpus : Nat} (sched : schedule Job num_cpus) (tsk : sporadic_task) (t1 delta : time) :
    (((jobs_of_task_scheduled_between job_task sched tsk t1 (t1 + delta)).mergeSort
        (fun x y => decide (job_arrival x ≤ job_arrival y)))).Nodup := by
  apply (List.mergeSort_perm _ _).nodup_iff.mpr
  exact (List.nodup_dedup _).filter _

/-- LEAN_HELPER: the sorted list is ordered by arrival time. -/
private theorem sorted_pairwise {sporadic_task : Type u} {Job : Type v} [DecidableEq sporadic_task] [DecidableEq Job] (job_arrival : Job → time) (job_task : Job → sporadic_task)
    {num_cpus : Nat} (sched : schedule Job num_cpus) (tsk : sporadic_task) (t1 delta : time) :
    List.Pairwise (fun a b => decide (job_arrival a ≤ job_arrival b) = true) (((jobs_of_task_scheduled_between job_task sched tsk t1 (t1 + delta)).mergeSort
        (fun x y => decide (job_arrival x ≤ job_arrival y)))) := by
  apply List.pairwise_mergeSort
  · intro a b c h1 h2; simp only [decide_eq_true_eq] at *; exact Nat.le_trans h1 h2
  · intro a b; simp only [Bool.or_eq_true, decide_eq_true_eq]; exact Nat.le_total _ _

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

/-- LEAN_HELPER: with sequential jobs, the service in `[a, b)` is at most `b - a`. -/
private theorem service_le_length {Job : Type v} [DecidableEq Job] {num_cpus : Nat} (sched : schedule Job num_cpus)
    (j : Job) (H_sequential_jobs : sequential_jobs sched) (a b : time) :
    ∑ t ∈ Finset.Ico a b, service_at sched j t ≤ b - a := by
  calc ∑ t ∈ Finset.Ico a b, service_at sched j t
      ≤ ∑ _t ∈ Finset.Ico a b, 1 :=
        Finset.sum_le_sum fun t _ => service_at_most_one sched j H_sequential_jobs t
    _ = b - a := by simp

/-! ### Simplifying the job sequence -/

theorem workload_bound_simpl_by_sorting_scheduled_jobs {sporadic_task : Type u} {Job : Type v} [DecidableEq sporadic_task] [DecidableEq Job] (job_arrival : Job → time)
    (job_task : Job → sporadic_task) {num_cpus : Nat} (sched : schedule Job num_cpus)
    (tsk : sporadic_task) (t1 delta : time) :
    workload_joblist job_task sched tsk t1 (t1 + delta) =
      sumSeq ((jobs_of_task_scheduled_between job_task sched tsk t1 (t1 + delta)).mergeSort
        (fun x y => decide (job_arrival x ≤ job_arrival y))) (fun i => service_during sched i t1 (t1 + delta)) := by
  unfold workload_joblist sumSeq
  exact ((List.mergeSort_perm _ _).map _).sum_eq.symm

theorem workload_bound_job_in_same_sequence {sporadic_task : Type u} {Job : Type v} [DecidableEq sporadic_task] [DecidableEq Job] (job_arrival : Job → time)
    (job_task : Job → sporadic_task) {num_cpus : Nat} (sched : schedule Job num_cpus)
    (tsk : sporadic_task) (t1 delta : time) (j : Job) :
    decide (j ∈ jobs_of_task_scheduled_between job_task sched tsk t1 (t1 + delta)) =
      decide (j ∈ ((jobs_of_task_scheduled_between job_task sched tsk t1 (t1 + delta)).mergeSort
        (fun x y => decide (job_arrival x ≤ job_arrival y)))) :=
  decide_eq_decide.mpr (sorted_mem job_arrival job_task sched tsk t1 delta j).symm

theorem workload_bound_all_jobs_from_tsk {sporadic_task : Type u} {Job : Type v} [DecidableEq sporadic_task] [DecidableEq Job] (job_arrival : Job → time)
    (job_task : Job → sporadic_task) (arr_seq : arrival_sequence Job) {num_cpus : Nat}
    (sched : schedule Job num_cpus) (H_jobs_come_from_arrival_sequence : jobs_come_from_arrival_sequence sched arr_seq) (tsk : sporadic_task) (t1 delta : time) :
    ∀ j_i : Job,
      j_i ∈ ((jobs_of_task_scheduled_between job_task sched tsk t1 (t1 + delta)).mergeSort
        (fun x y => decide (job_arrival x ≤ job_arrival y))) →
      arrives_in arr_seq j_i ∧
      job_task j_i = tsk ∧
      (!decide (service_during sched j_i t1 (t1 + delta) = 0)) = true ∧
      j_i ∈ jobs_scheduled_between sched t1 (t1 + delta) := by
  intro j_i IN
  rw [sorted_mem] at IN
  unfold jobs_of_task_scheduled_between at IN
  simp only [List.mem_filter, decide_eq_true_eq] at IN
  obtain ⟨INs, TSK⟩ := IN
  have IN2 := INs
  unfold jobs_scheduled_between at IN2
  rw [List.mem_dedup] at IN2
  obtain ⟨t, hmem, ht1, ht2⟩ := Prosa.Util.Bigcat.mem_bigcat_nat_exists _ _ _ _ IN2
  have SCHED : scheduled sched j_i t = true := by
    have := mem_scheduled_jobs_eq_scheduled sched j_i t
    rw [decide_eq_true hmem] at this
    exact this.symm
  refine ⟨H_jobs_come_from_arrival_sequence j_i t SCHED, TSK, ?_, INs⟩
  apply service_implies_cumulative_service sched j_i t
  · simp [ht1, ht2]
  · rw [← not_scheduled_no_service, SCHED]; rfl

theorem workload_bound_jobs_ordered_by_arrival {sporadic_task : Type u} {Job : Type v} [DecidableEq sporadic_task] [DecidableEq Job] (job_arrival : Job → time)
    (job_task : Job → sporadic_task) {num_cpus : Nat} (sched : schedule Job num_cpus)
    (tsk : sporadic_task) (t1 delta : time) :
    ∀ (i : Nat) (elem : Job),
      i < (((jobs_of_task_scheduled_between job_task sched tsk t1 (t1 + delta)).mergeSort
        (fun x y => decide (job_arrival x ≤ job_arrival y)))).length - 1 →
      job_arrival ((((jobs_of_task_scheduled_between job_task sched tsk t1 (t1 + delta)).mergeSort
        (fun x y => decide (job_arrival x ≤ job_arrival y)))).getD i elem) ≤ job_arrival ((((jobs_of_task_scheduled_between job_task sched tsk t1 (t1 + delta)).mergeSort
        (fun x y => decide (job_arrival x ≤ job_arrival y)))).getD (i + 1) elem) := by
  intro i elem LT
  have hp := sorted_pairwise job_arrival job_task sched tsk t1 delta
  have h1 : i < (((jobs_of_task_scheduled_between job_task sched tsk t1 (t1 + delta)).mergeSort
        (fun x y => decide (job_arrival x ≤ job_arrival y)))).length := by omega
  have h2 : i + 1 < (((jobs_of_task_scheduled_between job_task sched tsk t1 (t1 + delta)).mergeSort
        (fun x y => decide (job_arrival x ≤ job_arrival y)))).length := by omega
  rw [getD_lt h1, getD_lt h2]
  have := List.pairwise_iff_getElem.mp hp i (i + 1) h1 h2 (Nat.lt_succ_self i)
  simpa using this

/-! ### At most `n_k` jobs -/

theorem workload_bound_holds_for_at_most_n_k_jobs {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost task_period task_deadline : sporadic_task → time) {Job : Type v} [DecidableEq Job]
    (job_arrival job_cost : Job → time) (job_task : Job → sporadic_task)
    (job_deadline : Job → time) (arr_seq : arrival_sequence Job) (H_jobs_have_valid_parameters :
      ∀ j : Job, arrives_in arr_seq j →
        valid_sporadic_job task_cost task_deadline job_cost job_deadline job_task j) {num_cpus : Nat}
    (sched : schedule Job num_cpus) (H_jobs_come_from_arrival_sequence : jobs_come_from_arrival_sequence sched arr_seq) (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched) (tsk : sporadic_task) (t1 delta R_tsk : time) :
    (((jobs_of_task_scheduled_between job_task sched tsk t1 (t1 + delta)).mergeSort
        (fun x y => decide (job_arrival x ≤ job_arrival y)))).length ≤ max_jobs task_cost task_period tsk R_tsk delta →
    sumSeq ((jobs_of_task_scheduled_between job_task sched tsk t1 (t1 + delta)).mergeSort
        (fun x y => decide (job_arrival x ≤ job_arrival y))) (fun i => service_during sched i t1 (t1 + delta)) ≤ W task_cost task_period tsk R_tsk delta := by
  intro LEnk
  have hle : sumSeq ((jobs_of_task_scheduled_between job_task sched tsk t1 (t1 + delta)).mergeSort
        (fun x y => decide (job_arrival x ≤ job_arrival y))) (fun i => service_during sched i t1 (t1 + delta)) ≤
      (((jobs_of_task_scheduled_between job_task sched tsk t1 (t1 + delta)).mergeSort
        (fun x y => decide (job_arrival x ≤ job_arrival y)))).length * task_cost tsk := by
    unfold sumSeq
    have := List.sum_le_card_nsmul ((((jobs_of_task_scheduled_between job_task sched tsk t1 (t1 + delta)).mergeSort
        (fun x y => decide (job_arrival x ≤ job_arrival y)))).map (fun i => service_during sched i t1 (t1 + delta)))
      (task_cost tsk) (by
        intro x hx
        obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hx
        obtain ⟨ARR, TSK, _, _⟩ := workload_bound_all_jobs_from_tsk job_arrival job_task arr_seq
          sched H_jobs_come_from_arrival_sequence tsk t1 delta j hj
        exact cumulative_service_le_task_cost task_cost task_deadline job_cost job_deadline job_task
          sched H_completed_jobs_dont_execute tsk j TSK (H_jobs_have_valid_parameters j ARR) _ _)
    simpa using this
  unfold W
  have := Nat.mul_le_mul_right (task_cost tsk) LEnk
  omega

/-! ### A single job -/

theorem workload_bound_j_fst_is_job_of_tsk {sporadic_task : Type u} {Job : Type v} [DecidableEq sporadic_task] [DecidableEq Job] (job_arrival : Job → time)
    (job_task : Job → sporadic_task) (arr_seq : arrival_sequence Job) {num_cpus : Nat}
    (sched : schedule Job num_cpus) (H_jobs_come_from_arrival_sequence : jobs_come_from_arrival_sequence sched arr_seq) (tsk : sporadic_task) (t1 delta : time)
    (H_at_least_one_job : 0 < (((jobs_of_task_scheduled_between job_task sched tsk t1 (t1 + delta)).mergeSort
        (fun x y => decide (job_arrival x ≤ job_arrival y)))).length) (elem : Job) :
    arrives_in arr_seq ((((jobs_of_task_scheduled_between job_task sched tsk t1 (t1 + delta)).mergeSort
        (fun x y => decide (job_arrival x ≤ job_arrival y)))).getD 0 elem) ∧
    job_task ((((jobs_of_task_scheduled_between job_task sched tsk t1 (t1 + delta)).mergeSort
        (fun x y => decide (job_arrival x ≤ job_arrival y)))).getD 0 elem) = tsk ∧
    (!decide (service_during sched ((((jobs_of_task_scheduled_between job_task sched tsk t1 (t1 + delta)).mergeSort
        (fun x y => decide (job_arrival x ≤ job_arrival y)))).getD 0 elem) t1 (t1 + delta) = 0)) = true ∧
    (((jobs_of_task_scheduled_between job_task sched tsk t1 (t1 + delta)).mergeSort
        (fun x y => decide (job_arrival x ≤ job_arrival y)))).getD 0 elem ∈ jobs_scheduled_between sched t1 (t1 + delta) := by
  apply workload_bound_all_jobs_from_tsk job_arrival job_task arr_seq sched
    H_jobs_come_from_arrival_sequence
  rw [getD_lt H_at_least_one_job]
  exact List.getElem_mem _

theorem workload_bound_holds_for_a_single_job {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost task_period task_deadline : sporadic_task → time) {Job : Type v} [DecidableEq Job]
    (job_arrival job_cost : Job → time) (job_task : Job → sporadic_task)
    (job_deadline : Job → time) (arr_seq : arrival_sequence Job) (H_jobs_have_valid_parameters :
      ∀ j : Job, arrives_in arr_seq j →
        valid_sporadic_job task_cost task_deadline job_cost job_deadline job_task j) {num_cpus : Nat}
    (sched : schedule Job num_cpus) (H_jobs_come_from_arrival_sequence : jobs_come_from_arrival_sequence sched arr_seq) (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched) (H_sequential_jobs : sequential_jobs sched) (tsk : sporadic_task)
    (t1 delta R_tsk : time) (H_response_time_ge_cost : task_cost tsk ≤ R_tsk) (H_at_least_one_job : 0 < (((jobs_of_task_scheduled_between job_task sched tsk t1 (t1 + delta)).mergeSort
        (fun x y => decide (job_arrival x ≤ job_arrival y)))).length) (elem : Job) :
    ∑ i ∈ Finset.Ico 0 1, service_during sched ((((jobs_of_task_scheduled_between job_task sched tsk t1 (t1 + delta)).mergeSort
        (fun x y => decide (job_arrival x ≤ job_arrival y)))).getD i elem) t1 (t1 + delta) ≤ W task_cost task_period tsk R_tsk delta := by
  obtain ⟨ARR, TSK, _, _⟩ := workload_bound_j_fst_is_job_of_tsk job_arrival job_task arr_seq
    sched H_jobs_come_from_arrival_sequence tsk t1 delta H_at_least_one_job elem
  rw [← Finset.range_eq_Ico, Finset.sum_range_one]
  have hc := cumulative_service_le_task_cost task_cost task_deadline job_cost job_deadline job_task
    sched H_completed_jobs_dont_execute tsk _ TSK (H_jobs_have_valid_parameters _ ARR) t1
    (t1 + delta)
  have hd := cumulative_service_le_delta sched ((((jobs_of_task_scheduled_between job_task sched tsk t1 (t1 + delta)).mergeSort
        (fun x y => decide (job_arrival x ≤ job_arrival y)))).getD 0 elem) H_sequential_jobs t1 delta
  unfold W
  generalize max_jobs task_cost task_period tsk R_tsk delta = n
  cases n with
  | zero =>
      simp only [Nat.zero_mul, Nat.sub_zero, Nat.add_zero]
      exact le_min hc (by omega')
  | succ n =>
      have : task_cost tsk ≤ (n + 1) * task_cost tsk := Nat.le_mul_of_pos_left _ (Nat.succ_pos n)
      exact Nat.le_trans hc (Nat.le_trans this (Nat.le_add_left _ _))

/-! ### Two or more jobs -/

theorem workload_bound_j_lst_is_job_of_tsk {sporadic_task : Type u} {Job : Type v} [DecidableEq sporadic_task] [DecidableEq Job] (job_arrival : Job → time)
    (job_task : Job → sporadic_task) (arr_seq : arrival_sequence Job) {num_cpus : Nat}
    (sched : schedule Job num_cpus) (H_jobs_come_from_arrival_sequence : jobs_come_from_arrival_sequence sched arr_seq) (tsk : sporadic_task) (t1 delta : time) (num_mid_jobs : Nat) (H_at_least_two_jobs : ((jobs_of_task_scheduled_between job_task sched tsk t1 (t1 + delta)).mergeSort
        (fun x y => decide (job_arrival x ≤ job_arrival y))).length = num_mid_jobs + 2) (elem : Job) :
    arrives_in arr_seq ((((jobs_of_task_scheduled_between job_task sched tsk t1 (t1 + delta)).mergeSort
        (fun x y => decide (job_arrival x ≤ job_arrival y)))).getD (num_mid_jobs + 1) elem) ∧
    job_task ((((jobs_of_task_scheduled_between job_task sched tsk t1 (t1 + delta)).mergeSort
        (fun x y => decide (job_arrival x ≤ job_arrival y)))).getD (num_mid_jobs + 1) elem) = tsk ∧
    (!decide (service_during sched ((((jobs_of_task_scheduled_between job_task sched tsk t1 (t1 + delta)).mergeSort
        (fun x y => decide (job_arrival x ≤ job_arrival y)))).getD (num_mid_jobs + 1) elem) t1 (t1 + delta) = 0)) = true ∧
    (((jobs_of_task_scheduled_between job_task sched tsk t1 (t1 + delta)).mergeSort
        (fun x y => decide (job_arrival x ≤ job_arrival y)))).getD (num_mid_jobs + 1) elem ∈ jobs_scheduled_between sched t1 (t1 + delta) := by
  apply workload_bound_all_jobs_from_tsk job_arrival job_task arr_seq sched
    H_jobs_come_from_arrival_sequence
  rw [getD_lt (by omega)]
  exact List.getElem_mem _

theorem workload_bound_response_time_of_first_job_inside_interval {sporadic_task : Type u} {Job : Type v} [DecidableEq sporadic_task] [DecidableEq Job]
    (job_arrival job_cost : Job → time) (job_task : Job → sporadic_task)
    (arr_seq : arrival_sequence Job) {num_cpus : Nat} (sched : schedule Job num_cpus) (H_jobs_come_from_arrival_sequence : jobs_come_from_arrival_sequence sched arr_seq)
    (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched) (tsk : sporadic_task) (t1 delta R_tsk : time) (H_response_time_bound :
      ∀ j : Job, arrives_in arr_seq j → job_task j = tsk →
        job_arrival j + R_tsk < t1 + delta →
        completed job_cost sched j (job_arrival j + R_tsk) = true) (num_mid_jobs : Nat) (H_at_least_two_jobs : ((jobs_of_task_scheduled_between job_task sched tsk t1 (t1 + delta)).mergeSort
        (fun x y => decide (job_arrival x ≤ job_arrival y))).length = num_mid_jobs + 2) (elem : Job) :
    t1 ≤ job_arrival ((((jobs_of_task_scheduled_between job_task sched tsk t1 (t1 + delta)).mergeSort
        (fun x y => decide (job_arrival x ≤ job_arrival y)))).getD 0 elem) + R_tsk := by
  by_contra LTt1
  have LTt1 : job_arrival ((((jobs_of_task_scheduled_between job_task sched tsk t1 (t1 + delta)).mergeSort
        (fun x y => decide (job_arrival x ≤ job_arrival y)))).getD 0 elem) + R_tsk < t1 := by omega'
  obtain ⟨ARR, TSK, NZ, _⟩ := workload_bound_j_fst_is_job_of_tsk job_arrival job_task arr_seq
    sched H_jobs_come_from_arrival_sequence tsk t1 delta (by omega) elem
  have COMP := H_response_time_bound _ ARR TSK (by omega')
  have ZERO := cumulative_service_after_job_rt_zero job_arrival job_cost sched
    H_completed_jobs_dont_execute _ R_tsk COMP t1 (t1 + delta) (by omega')
  unfold service_during at NZ
  rw [ZERO] at NZ
  exact Bool.noConfusion NZ

theorem workload_bound_last_job_arrives_before_end_of_interval {sporadic_task : Type u} {Job : Type v} [DecidableEq sporadic_task] [DecidableEq Job] (job_arrival : Job → time)
    (job_task : Job → sporadic_task) (arr_seq : arrival_sequence Job) {num_cpus : Nat}
    (sched : schedule Job num_cpus) (H_jobs_come_from_arrival_sequence : jobs_come_from_arrival_sequence sched arr_seq) (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute job_arrival sched) (tsk : sporadic_task) (t1 delta : time) (num_mid_jobs : Nat) (H_at_least_two_jobs : ((jobs_of_task_scheduled_between job_task sched tsk t1 (t1 + delta)).mergeSort
        (fun x y => decide (job_arrival x ≤ job_arrival y))).length = num_mid_jobs + 2) (elem : Job) :
    job_arrival ((((jobs_of_task_scheduled_between job_task sched tsk t1 (t1 + delta)).mergeSort
        (fun x y => decide (job_arrival x ≤ job_arrival y)))).getD (num_mid_jobs + 1) elem) < t1 + delta := by
  by_contra LT2
  have LT2 : t1 + delta ≤ job_arrival ((((jobs_of_task_scheduled_between job_task sched tsk t1 (t1 + delta)).mergeSort
        (fun x y => decide (job_arrival x ≤ job_arrival y)))).getD (num_mid_jobs + 1) elem) := by omega'
  obtain ⟨_, _, NZ, _⟩ := workload_bound_j_lst_is_job_of_tsk job_arrival job_task arr_seq sched
    H_jobs_come_from_arrival_sequence tsk t1 delta num_mid_jobs H_at_least_two_jobs elem
  have ZERO := cumulative_service_before_job_arrival_zero job_arrival sched _
    H_jobs_must_arrive_to_execute t1 (t1 + delta) LT2
  unfold service_during at NZ
  rw [ZERO] at NZ
  exact Bool.noConfusion NZ

theorem workload_bound_service_of_first_and_last_jobs {sporadic_task : Type u} {Job : Type v} [DecidableEq sporadic_task] [DecidableEq Job] (job_arrival job_cost : Job → time)
    (job_task : Job → sporadic_task) (arr_seq : arrival_sequence Job) {num_cpus : Nat}
    (sched : schedule Job num_cpus) (H_jobs_come_from_arrival_sequence : jobs_come_from_arrival_sequence sched arr_seq) (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute job_arrival sched) (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched) (H_sequential_jobs : sequential_jobs sched) (tsk : sporadic_task)
    (t1 delta R_tsk : time) (H_response_time_bound :
      ∀ j : Job, arrives_in arr_seq j → job_task j = tsk →
        job_arrival j + R_tsk < t1 + delta →
        completed job_cost sched j (job_arrival j + R_tsk) = true) (num_mid_jobs : Nat) (H_at_least_two_jobs : ((jobs_of_task_scheduled_between job_task sched tsk t1 (t1 + delta)).mergeSort
        (fun x y => decide (job_arrival x ≤ job_arrival y))).length = num_mid_jobs + 2) (elem : Job) :
    service_during sched ((((jobs_of_task_scheduled_between job_task sched tsk t1 (t1 + delta)).mergeSort
        (fun x y => decide (job_arrival x ≤ job_arrival y)))).getD 0 elem) t1 (t1 + delta) +
        service_during sched ((((jobs_of_task_scheduled_between job_task sched tsk t1 (t1 + delta)).mergeSort
        (fun x y => decide (job_arrival x ≤ job_arrival y)))).getD (num_mid_jobs + 1) elem) t1 (t1 + delta) ≤
      (job_arrival ((((jobs_of_task_scheduled_between job_task sched tsk t1 (t1 + delta)).mergeSort
        (fun x y => decide (job_arrival x ≤ job_arrival y)))).getD 0 elem) + R_tsk - t1) +
        (t1 + delta - job_arrival ((((jobs_of_task_scheduled_between job_task sched tsk t1 (t1 + delta)).mergeSort
        (fun x y => decide (job_arrival x ≤ job_arrival y)))).getD (num_mid_jobs + 1) elem)) := by
  apply Nat.add_le_add
  · have INSIDE := workload_bound_response_time_of_first_job_inside_interval job_arrival job_cost
      job_task arr_seq sched H_jobs_come_from_arrival_sequence H_completed_jobs_dont_execute tsk
      t1 delta R_tsk H_response_time_bound num_mid_jobs H_at_least_two_jobs elem
    unfold service_during
    by_cases LEt2 : job_arrival ((((jobs_of_task_scheduled_between job_task sched tsk t1 (t1 + delta)).mergeSort
        (fun x y => decide (job_arrival x ≤ job_arrival y)))).getD 0 elem) + R_tsk < t1 + delta
    · obtain ⟨ARR, TSK, _, _⟩ := workload_bound_j_fst_is_job_of_tsk job_arrival job_task arr_seq
        sched H_jobs_come_from_arrival_sequence tsk t1 delta (by omega) elem
      rw [← Finset.sum_Ico_consecutive _ INSIDE (Nat.le_of_lt LEt2),
        cumulative_service_after_job_rt_zero job_arrival job_cost sched
          H_completed_jobs_dont_execute _ R_tsk (H_response_time_bound _ ARR TSK LEt2) _ _
          (Nat.le_refl _), Nat.add_zero]
      exact service_le_length sched _ H_sequential_jobs _ _
    · exact Nat.le_trans (service_le_length sched _ H_sequential_jobs _ _) (by omega')
  · unfold service_during
    by_cases LT : job_arrival ((((jobs_of_task_scheduled_between job_task sched tsk t1 (t1 + delta)).mergeSort
        (fun x y => decide (job_arrival x ≤ job_arrival y)))).getD (num_mid_jobs + 1) elem) ≤ t1
    · exact Nat.le_trans (service_le_length sched _ H_sequential_jobs _ _) (by omega')
    · have BEFORE := workload_bound_last_job_arrives_before_end_of_interval job_arrival job_task
        arr_seq sched H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute tsk t1 delta
        num_mid_jobs H_at_least_two_jobs elem
      rw [← Finset.sum_Ico_consecutive _ (by omega' : t1 ≤ _) (Nat.le_of_lt BEFORE),
        cumulative_service_before_job_arrival_zero job_arrival sched _
          H_jobs_must_arrive_to_execute t1 _ (Nat.le_refl _), Nat.zero_add]
      exact service_le_length sched _ H_sequential_jobs _ _

/-- LEAN_HELPER: the first job arrives no later than the last one. -/
private theorem first_le_last {sporadic_task : Type u} {Job : Type v} [DecidableEq sporadic_task] [DecidableEq Job] (job_arrival : Job → time) (job_task : Job → sporadic_task)
    {num_cpus : Nat} (sched : schedule Job num_cpus) (tsk : sporadic_task) (t1 delta : time)
    (num_mid_jobs : Nat) (H_at_least_two_jobs : ((jobs_of_task_scheduled_between job_task sched tsk t1 (t1 + delta)).mergeSort
        (fun x y => decide (job_arrival x ≤ job_arrival y))).length = num_mid_jobs + 2) (elem : Job) :
    job_arrival ((((jobs_of_task_scheduled_between job_task sched tsk t1 (t1 + delta)).mergeSort
        (fun x y => decide (job_arrival x ≤ job_arrival y)))).getD 0 elem) ≤
      job_arrival ((((jobs_of_task_scheduled_between job_task sched tsk t1 (t1 + delta)).mergeSort
        (fun x y => decide (job_arrival x ≤ job_arrival y)))).getD (num_mid_jobs + 1) elem) := by
  have := Prosa.Classic.Util.Sorting.prev_le_next job_arrival (((jobs_of_task_scheduled_between job_task sched tsk t1 (t1 + delta)).mergeSort
        (fun x y => decide (job_arrival x ≤ job_arrival y)))) elem 0 (num_mid_jobs + 1)
    (fun i hi => workload_bound_jobs_ordered_by_arrival job_arrival job_task sched tsk t1 delta i
      elem hi) (by omega)
  simpa using this

theorem workload_bound_simpl_expression_with_first_and_last {sporadic_task : Type u} {Job : Type v} [DecidableEq sporadic_task] [DecidableEq Job]
    (job_arrival job_cost : Job → time) (job_task : Job → sporadic_task)
    (arr_seq : arrival_sequence Job) {num_cpus : Nat} (sched : schedule Job num_cpus) (H_jobs_come_from_arrival_sequence : jobs_come_from_arrival_sequence sched arr_seq)
    (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute job_arrival sched) (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched) (tsk : sporadic_task) (t1 delta R_tsk : time) (H_response_time_bound :
      ∀ j : Job, arrives_in arr_seq j → job_task j = tsk →
        job_arrival j + R_tsk < t1 + delta →
        completed job_cost sched j (job_arrival j + R_tsk) = true) (num_mid_jobs : Nat) (H_at_least_two_jobs : ((jobs_of_task_scheduled_between job_task sched tsk t1 (t1 + delta)).mergeSort
        (fun x y => decide (job_arrival x ≤ job_arrival y))).length = num_mid_jobs + 2) (elem : Job) :
    job_arrival ((((jobs_of_task_scheduled_between job_task sched tsk t1 (t1 + delta)).mergeSort
        (fun x y => decide (job_arrival x ≤ job_arrival y)))).getD 0 elem) + R_tsk - t1 +
        (t1 + delta - job_arrival ((((jobs_of_task_scheduled_between job_task sched tsk t1 (t1 + delta)).mergeSort
        (fun x y => decide (job_arrival x ≤ job_arrival y)))).getD (num_mid_jobs + 1) elem)) =
      delta + R_tsk - (job_arrival ((((jobs_of_task_scheduled_between job_task sched tsk t1 (t1 + delta)).mergeSort
        (fun x y => decide (job_arrival x ≤ job_arrival y)))).getD (num_mid_jobs + 1) elem) -
        job_arrival ((((jobs_of_task_scheduled_between job_task sched tsk t1 (t1 + delta)).mergeSort
        (fun x y => decide (job_arrival x ≤ job_arrival y)))).getD 0 elem)) := by
  have lemma1 := workload_bound_last_job_arrives_before_end_of_interval job_arrival job_task
    arr_seq sched H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute tsk t1 delta
    num_mid_jobs H_at_least_two_jobs elem
  have lemma2 := workload_bound_response_time_of_first_job_inside_interval job_arrival job_cost
    job_task arr_seq sched H_jobs_come_from_arrival_sequence H_completed_jobs_dont_execute tsk t1
    delta R_tsk H_response_time_bound num_mid_jobs H_at_least_two_jobs elem
  have ORD := first_le_last job_arrival job_task sched tsk t1 delta num_mid_jobs
    H_at_least_two_jobs elem
  omega'

theorem workload_bound_service_of_middle_jobs {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost task_deadline : sporadic_task → time) {Job : Type v} [DecidableEq Job] (job_arrival job_cost : Job → time)
    (job_task : Job → sporadic_task) (job_deadline : Job → time)
    (arr_seq : arrival_sequence Job) (H_jobs_have_valid_parameters :
      ∀ j : Job, arrives_in arr_seq j →
        valid_sporadic_job task_cost task_deadline job_cost job_deadline job_task j) {num_cpus : Nat} (sched : schedule Job num_cpus)
    (H_jobs_come_from_arrival_sequence : jobs_come_from_arrival_sequence sched arr_seq) (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched) (tsk : sporadic_task) (t1 delta : time) (num_mid_jobs : Nat) (H_at_least_two_jobs : ((jobs_of_task_scheduled_between job_task sched tsk t1 (t1 + delta)).mergeSort
        (fun x y => decide (job_arrival x ≤ job_arrival y))).length = num_mid_jobs + 2) (elem : Job) :
    ∑ i ∈ Finset.Ico 0 num_mid_jobs, service_during sched ((((jobs_of_task_scheduled_between job_task sched tsk t1 (t1 + delta)).mergeSort
        (fun x y => decide (job_arrival x ≤ job_arrival y)))).getD (i + 1) elem) t1 (t1 + delta) ≤
      num_mid_jobs * task_cost tsk := by
  calc ∑ i ∈ Finset.Ico 0 num_mid_jobs, service_during sched ((((jobs_of_task_scheduled_between job_task sched tsk t1 (t1 + delta)).mergeSort
        (fun x y => decide (job_arrival x ≤ job_arrival y)))).getD (i + 1) elem) t1 (t1 + delta)
      ≤ ∑ _i ∈ Finset.Ico 0 num_mid_jobs, task_cost tsk := by
        apply Finset.sum_le_sum
        intro i hi
        rw [Finset.mem_Ico] at hi
        have hlt : i + 1 < (((jobs_of_task_scheduled_between job_task sched tsk t1 (t1 + delta)).mergeSort
        (fun x y => decide (job_arrival x ≤ job_arrival y)))).length := by omega
        obtain ⟨ARR, TSK, _, _⟩ := workload_bound_all_jobs_from_tsk job_arrival job_task arr_seq
          sched H_jobs_come_from_arrival_sequence tsk t1 delta ((((jobs_of_task_scheduled_between job_task sched tsk t1 (t1 + delta)).mergeSort
        (fun x y => decide (job_arrival x ≤ job_arrival y)))).getD (i + 1) elem)
          (by rw [getD_lt hlt]; exact List.getElem_mem _)
        exact cumulative_service_le_task_cost task_cost task_deadline job_cost job_deadline
          job_task sched H_completed_jobs_dont_execute tsk _ TSK
          (H_jobs_have_valid_parameters _ ARR) _ _
    _ = num_mid_jobs * task_cost tsk := by simp

theorem workload_bound_many_periods_in_between {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost task_period task_deadline : sporadic_task → time) {Job : Type v} [DecidableEq Job]
    (job_arrival : Job → time) (job_task : Job → sporadic_task)
    (arr_seq : arrival_sequence Job) {num_cpus : Nat} (sched : schedule Job num_cpus) (H_jobs_come_from_arrival_sequence : jobs_come_from_arrival_sequence sched arr_seq)
    (H_sporadic_tasks : sporadic_task_model task_period job_arrival job_task arr_seq) (tsk : sporadic_task) (H_constrained_deadline : task_deadline tsk ≤ task_period tsk) (t1 delta R_tsk : time) (H_response_time_ge_cost : task_cost tsk ≤ R_tsk) (H_no_deadline_miss : R_tsk ≤ task_deadline tsk) (num_mid_jobs : Nat) (H_at_least_two_jobs : ((jobs_of_task_scheduled_between job_task sched tsk t1 (t1 + delta)).mergeSort
        (fun x y => decide (job_arrival x ≤ job_arrival y))).length = num_mid_jobs + 2) (elem : Job) :
    (num_mid_jobs + 1) * task_period tsk ≤
      job_arrival ((((jobs_of_task_scheduled_between job_task sched tsk t1 (t1 + delta)).mergeSort
        (fun x y => decide (job_arrival x ≤ job_arrival y)))).getD (num_mid_jobs + 1) elem) -
        job_arrival ((((jobs_of_task_scheduled_between job_task sched tsk t1 (t1 + delta)).mergeSort
        (fun x y => decide (job_arrival x ≤ job_arrival y)))).getD 0 elem) := by
  have hlen : (((jobs_of_task_scheduled_between job_task sched tsk t1 (t1 + delta)).mergeSort
        (fun x y => decide (job_arrival x ≤ job_arrival y)))).length - 1 = num_mid_jobs + 1 := by omega
  have TEL := Prosa.Classic.Util.Sum.telescoping_sum Job job_arrival (((jobs_of_task_scheduled_between job_task sched tsk t1 (t1 + delta)).mergeSort
        (fun x y => decide (job_arrival x ≤ job_arrival y)))) elem
    (fun i hi => workload_bound_jobs_ordered_by_arrival job_arrival job_task sched tsk t1 delta i
      elem hi)
  rw [hlen] at TEL
  rw [TEL]
  have hnd := sorted_nodup job_arrival job_task sched tsk t1 delta
  calc (num_mid_jobs + 1) * task_period tsk
      = ∑ _i ∈ Finset.Ico 0 (num_mid_jobs + 1), task_period tsk := by simp
    _ ≤ _ := by
        apply Finset.sum_le_sum
        intro i hi
        rw [Finset.mem_Ico] at hi
        have h1 : i < (((jobs_of_task_scheduled_between job_task sched tsk t1 (t1 + delta)).mergeSort
        (fun x y => decide (job_arrival x ≤ job_arrival y)))).length := by omega
        have h2 : i + 1 < (((jobs_of_task_scheduled_between job_task sched tsk t1 (t1 + delta)).mergeSort
        (fun x y => decide (job_arrival x ≤ job_arrival y)))).length := by omega
        obtain ⟨CURarr, CURtsk, _, _⟩ := workload_bound_all_jobs_from_tsk job_arrival job_task
          arr_seq sched H_jobs_come_from_arrival_sequence tsk t1 delta ((((jobs_of_task_scheduled_between job_task sched tsk t1 (t1 + delta)).mergeSort
        (fun x y => decide (job_arrival x ≤ job_arrival y)))).getD i elem)
          (by rw [getD_lt h1]; exact List.getElem_mem _)
        obtain ⟨NEXTarr, NEXTtsk, _, _⟩ := workload_bound_all_jobs_from_tsk job_arrival job_task
          arr_seq sched H_jobs_come_from_arrival_sequence tsk t1 delta
          ((((jobs_of_task_scheduled_between job_task sched tsk t1 (t1 + delta)).mergeSort
        (fun x y => decide (job_arrival x ≤ job_arrival y)))).getD (i + 1) elem) (by rw [getD_lt h2]; exact List.getElem_mem _)
        have ARRle := workload_bound_jobs_ordered_by_arrival job_arrival job_task sched tsk t1
          delta i elem (by omega)
        have DIFF : (((jobs_of_task_scheduled_between job_task sched tsk t1 (t1 + delta)).mergeSort
        (fun x y => decide (job_arrival x ≤ job_arrival y)))).getD i elem ≠ (((jobs_of_task_scheduled_between job_task sched tsk t1 (t1 + delta)).mergeSort
        (fun x y => decide (job_arrival x ≤ job_arrival y)))).getD (i + 1) elem := by
          rw [getD_lt h1, getD_lt h2]
          intro EQ
          have := (List.Nodup.getElem_inj_iff hnd).mp EQ
          omega
        have SPO := H_sporadic_tasks _ _ DIFF CURarr NEXTarr (CURtsk.trans NEXTtsk.symm) ARRle
        rw [CURtsk] at SPO
        omega'

theorem workload_bound_n_k_covers_middle_jobs {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost task_period task_deadline : sporadic_task → time) {Job : Type v} [DecidableEq Job]
    (job_arrival job_cost : Job → time) (job_task : Job → sporadic_task)
    (arr_seq : arrival_sequence Job) {num_cpus : Nat} (sched : schedule Job num_cpus) (H_jobs_come_from_arrival_sequence : jobs_come_from_arrival_sequence sched arr_seq)
    (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute job_arrival sched) (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched) (H_sporadic_tasks : sporadic_task_model task_period job_arrival job_task arr_seq) (tsk : sporadic_task) (H_valid_task_parameters : is_valid_sporadic_task task_cost task_period task_deadline tsk) (H_constrained_deadline : task_deadline tsk ≤ task_period tsk) (t1 delta R_tsk : time) (H_response_time_bound :
      ∀ j : Job, arrives_in arr_seq j → job_task j = tsk →
        job_arrival j + R_tsk < t1 + delta →
        completed job_cost sched j (job_arrival j + R_tsk) = true) (H_response_time_ge_cost : task_cost tsk ≤ R_tsk) (H_no_deadline_miss : R_tsk ≤ task_deadline tsk) (num_mid_jobs : Nat) (H_at_least_two_jobs : ((jobs_of_task_scheduled_between job_task sched tsk t1 (t1 + delta)).mergeSort
        (fun x y => decide (job_arrival x ≤ job_arrival y))).length = num_mid_jobs + 2) (elem : Job) :
    num_mid_jobs ≤ max_jobs task_cost task_period tsk R_tsk delta := by
  obtain ⟨_, PERIOD, _, _, _⟩ := H_valid_task_parameters
  have hp : 0 < task_period tsk := by simpa [task_period_positive] using PERIOD
  by_contra LTnk
  have LTnk : max_jobs task_cost task_period tsk R_tsk delta < num_mid_jobs := by omega
  have MANY := workload_bound_many_periods_in_between task_cost task_period task_deadline
    job_arrival job_task arr_seq sched H_jobs_come_from_arrival_sequence H_sporadic_tasks tsk
    H_constrained_deadline t1 delta R_tsk H_response_time_ge_cost H_no_deadline_miss num_mid_jobs
    H_at_least_two_jobs elem
  have BEFORE := workload_bound_last_job_arrives_before_end_of_interval job_arrival job_task
    arr_seq sched H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute tsk t1 delta
    num_mid_jobs H_at_least_two_jobs elem
  have FIRST := workload_bound_response_time_of_first_job_inside_interval job_arrival job_cost
    job_task arr_seq sched H_jobs_come_from_arrival_sequence H_completed_jobs_dont_execute tsk t1
    delta R_tsk H_response_time_bound num_mid_jobs H_at_least_two_jobs elem
  have ORD := first_le_last job_arrival job_task sched tsk t1 delta num_mid_jobs
    H_at_least_two_jobs elem
  have hdiv : delta + R_tsk - task_cost tsk < task_period tsk * (max_jobs task_cost task_period tsk R_tsk delta + 1) := by
    unfold max_jobs div_floor
    exact Nat.lt_mul_div_succ _ hp
  have hmul : (max_jobs task_cost task_period tsk R_tsk delta + 2) * task_period tsk ≤ (num_mid_jobs + 1) * task_period tsk :=
    Nat.mul_le_mul_right _ (by omega)
  have e1 : (max_jobs task_cost task_period tsk R_tsk delta + 2) * task_period tsk = task_period tsk * (max_jobs task_cost task_period tsk R_tsk delta + 1) + task_period tsk := by
    rw [Nat.mul_comm, Nat.mul_add, Nat.mul_add]; omega
  omega'

theorem workload_bound_n_k_equals_num_mid_jobs {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost task_period task_deadline : sporadic_task → time) {Job : Type v} [DecidableEq Job]
    (job_arrival job_cost : Job → time) (job_task : Job → sporadic_task)
    (job_deadline : Job → time) (arr_seq : arrival_sequence Job) (H_jobs_have_valid_parameters :
      ∀ j : Job, arrives_in arr_seq j →
        valid_sporadic_job task_cost task_deadline job_cost job_deadline job_task j) {num_cpus : Nat}
    (sched : schedule Job num_cpus) (H_jobs_come_from_arrival_sequence : jobs_come_from_arrival_sequence sched arr_seq) (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute job_arrival sched) (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched) (H_sequential_jobs : sequential_jobs sched) (H_sporadic_tasks : sporadic_task_model task_period job_arrival job_task arr_seq) (tsk : sporadic_task) (H_valid_task_parameters : is_valid_sporadic_task task_cost task_period task_deadline tsk) (H_constrained_deadline : task_deadline tsk ≤ task_period tsk)
    (t1 delta R_tsk : time) (H_response_time_bound :
      ∀ j : Job, arrives_in arr_seq j → job_task j = tsk →
        job_arrival j + R_tsk < t1 + delta →
        completed job_cost sched j (job_arrival j + R_tsk) = true) (H_response_time_ge_cost : task_cost tsk ≤ R_tsk) (H_no_deadline_miss : R_tsk ≤ task_deadline tsk) (num_mid_jobs : Nat) (H_at_least_two_jobs : ((jobs_of_task_scheduled_between job_task sched tsk t1 (t1 + delta)).mergeSort
        (fun x y => decide (job_arrival x ≤ job_arrival y))).length = num_mid_jobs + 2) (elem : Job) :
    num_mid_jobs = max_jobs task_cost task_period tsk R_tsk delta →
    service_during sched ((((jobs_of_task_scheduled_between job_task sched tsk t1 (t1 + delta)).mergeSort
        (fun x y => decide (job_arrival x ≤ job_arrival y)))).getD (num_mid_jobs + 1) elem) t1 (t1 + delta) +
        service_during sched ((((jobs_of_task_scheduled_between job_task sched tsk t1 (t1 + delta)).mergeSort
        (fun x y => decide (job_arrival x ≤ job_arrival y)))).getD 0 elem) t1 (t1 + delta) +
        ∑ i ∈ Finset.Ico 0 num_mid_jobs, service_during sched ((((jobs_of_task_scheduled_between job_task sched tsk t1 (t1 + delta)).mergeSort
        (fun x y => decide (job_arrival x ≤ job_arrival y)))).getD (i + 1) elem) t1 (t1 + delta) ≤
      W task_cost task_period tsk R_tsk delta := by
  intro NKeq
  obtain ⟨_, PERIOD, _, _, CLEP⟩ := H_valid_task_parameters
  have hp : 0 < task_period tsk := by simpa [task_period_positive] using PERIOD
  have hep : task_cost tsk ≤ task_period tsk := by simpa [task_cost_le_period] using CLEP
  have FL := workload_bound_service_of_first_and_last_jobs job_arrival job_cost job_task arr_seq
    sched H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute
    H_completed_jobs_dont_execute H_sequential_jobs tsk t1 delta R_tsk H_response_time_bound
    num_mid_jobs H_at_least_two_jobs elem
  have EXPR := workload_bound_simpl_expression_with_first_and_last job_arrival job_cost job_task
    arr_seq sched H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute
    H_completed_jobs_dont_execute tsk t1 delta R_tsk H_response_time_bound num_mid_jobs
    H_at_least_two_jobs elem
  have MID := workload_bound_service_of_middle_jobs task_cost task_deadline job_arrival job_cost
    job_task job_deadline arr_seq H_jobs_have_valid_parameters sched
    H_jobs_come_from_arrival_sequence H_completed_jobs_dont_execute tsk t1 delta num_mid_jobs
    H_at_least_two_jobs elem
  have MANY := workload_bound_many_periods_in_between task_cost task_period task_deadline
    job_arrival job_task arr_seq sched H_jobs_come_from_arrival_sequence H_sporadic_tasks tsk
    H_constrained_deadline t1 delta R_tsk H_response_time_ge_cost H_no_deadline_miss num_mid_jobs
    H_at_least_two_jobs elem
  have hdiv : delta + R_tsk - task_cost tsk < task_period tsk * (max_jobs task_cost task_period tsk R_tsk delta + 1) := by
    unfold max_jobs div_floor
    exact Nat.lt_mul_div_succ _ hp
  unfold W
  rw [← NKeq] at hdiv ⊢
  have e1 : (num_mid_jobs + 1) * task_period tsk = num_mid_jobs * task_period tsk + task_period tsk :=
    by rw [Nat.add_mul, Nat.one_mul]
  have e2 : task_period tsk * (num_mid_jobs + 1) =
      num_mid_jobs * task_period tsk + task_period tsk := by
    rw [Nat.mul_comm, Nat.add_mul, Nat.one_mul]
  rcases min_cases (task_cost tsk)
      (delta + R_tsk - task_cost tsk - num_mid_jobs * task_period tsk) with ⟨h, _⟩ | ⟨h, _⟩ <;>
    rw [h] <;> omega'

theorem workload_bound_n_k_equals_num_mid_jobs_plus_1 {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost task_period task_deadline : sporadic_task → time) {Job : Type v} [DecidableEq Job]
    (job_arrival job_cost : Job → time) (job_task : Job → sporadic_task)
    (job_deadline : Job → time) (arr_seq : arrival_sequence Job) (H_jobs_have_valid_parameters :
      ∀ j : Job, arrives_in arr_seq j →
        valid_sporadic_job task_cost task_deadline job_cost job_deadline job_task j) {num_cpus : Nat}
    (sched : schedule Job num_cpus) (H_jobs_come_from_arrival_sequence : jobs_come_from_arrival_sequence sched arr_seq) (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute job_arrival sched) (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched) (H_sequential_jobs : sequential_jobs sched) (H_sporadic_tasks : sporadic_task_model task_period job_arrival job_task arr_seq) (tsk : sporadic_task) (H_constrained_deadline : task_deadline tsk ≤ task_period tsk)
    (t1 delta R_tsk : time) (H_response_time_bound :
      ∀ j : Job, arrives_in arr_seq j → job_task j = tsk →
        job_arrival j + R_tsk < t1 + delta →
        completed job_cost sched j (job_arrival j + R_tsk) = true) (H_response_time_ge_cost : task_cost tsk ≤ R_tsk) (H_no_deadline_miss : R_tsk ≤ task_deadline tsk) (num_mid_jobs : Nat) (H_at_least_two_jobs : ((jobs_of_task_scheduled_between job_task sched tsk t1 (t1 + delta)).mergeSort
        (fun x y => decide (job_arrival x ≤ job_arrival y))).length = num_mid_jobs + 2) (elem : Job) :
    num_mid_jobs + 1 = max_jobs task_cost task_period tsk R_tsk delta →
    service_during sched ((((jobs_of_task_scheduled_between job_task sched tsk t1 (t1 + delta)).mergeSort
        (fun x y => decide (job_arrival x ≤ job_arrival y)))).getD (num_mid_jobs + 1) elem) t1 (t1 + delta) +
        service_during sched ((((jobs_of_task_scheduled_between job_task sched tsk t1 (t1 + delta)).mergeSort
        (fun x y => decide (job_arrival x ≤ job_arrival y)))).getD 0 elem) t1 (t1 + delta) +
        ∑ i ∈ Finset.Ico 0 num_mid_jobs, service_during sched ((((jobs_of_task_scheduled_between job_task sched tsk t1 (t1 + delta)).mergeSort
        (fun x y => decide (job_arrival x ≤ job_arrival y)))).getD (i + 1) elem) t1 (t1 + delta) ≤
      W task_cost task_period tsk R_tsk delta := by
  intro NKeq
  have FL := workload_bound_service_of_first_and_last_jobs job_arrival job_cost job_task arr_seq
    sched H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute
    H_completed_jobs_dont_execute H_sequential_jobs tsk t1 delta R_tsk H_response_time_bound
    num_mid_jobs H_at_least_two_jobs elem
  have EXPR := workload_bound_simpl_expression_with_first_and_last job_arrival job_cost job_task
    arr_seq sched H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute
    H_completed_jobs_dont_execute tsk t1 delta R_tsk H_response_time_bound num_mid_jobs
    H_at_least_two_jobs elem
  have MID := workload_bound_service_of_middle_jobs task_cost task_deadline job_arrival job_cost
    job_task job_deadline arr_seq H_jobs_have_valid_parameters sched
    H_jobs_come_from_arrival_sequence H_completed_jobs_dont_execute tsk t1 delta num_mid_jobs
    H_at_least_two_jobs elem
  have MANY := workload_bound_many_periods_in_between task_cost task_period task_deadline
    job_arrival job_task arr_seq sched H_jobs_come_from_arrival_sequence H_sporadic_tasks tsk
    H_constrained_deadline t1 delta R_tsk H_response_time_ge_cost H_no_deadline_miss num_mid_jobs
    H_at_least_two_jobs elem
  obtain ⟨FSTarr, FSTtsk, _, _⟩ := workload_bound_j_fst_is_job_of_tsk job_arrival job_task
    arr_seq sched H_jobs_come_from_arrival_sequence tsk t1 delta (by omega) elem
  obtain ⟨LSTarr, LSTtsk, _, _⟩ := workload_bound_j_lst_is_job_of_tsk job_arrival job_task
    arr_seq sched H_jobs_come_from_arrival_sequence tsk t1 delta num_mid_jobs
    H_at_least_two_jobs elem
  have CF := cumulative_service_le_task_cost task_cost task_deadline job_cost job_deadline
    job_task sched H_completed_jobs_dont_execute tsk _ FSTtsk
    (H_jobs_have_valid_parameters _ FSTarr) t1 (t1 + delta)
  have CL := cumulative_service_le_task_cost task_cost task_deadline job_cost job_deadline
    job_task sched H_completed_jobs_dont_execute tsk _ LSTtsk
    (H_jobs_have_valid_parameters _ LSTarr) t1 (t1 + delta)
  have hdivle : max_jobs task_cost task_period tsk R_tsk delta * task_period tsk ≤ delta + R_tsk - task_cost tsk := by
    unfold max_jobs div_floor
    exact Nat.div_mul_le_self _ _
  unfold W
  rw [← NKeq] at hdivle ⊢
  have e3 : (num_mid_jobs + 1) * task_cost tsk = num_mid_jobs * task_cost tsk + task_cost tsk :=
    by rw [Nat.add_mul, Nat.one_mul]
  rcases min_cases (task_cost tsk)
      (delta + R_tsk - task_cost tsk - (num_mid_jobs + 1) * task_period tsk) with
      ⟨h, _⟩ | ⟨h, _⟩ <;>
    rw [h] <;> omega'

/-! ### Main theorem -/

theorem workload_bounded_by_W {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost task_period task_deadline : sporadic_task → time) {Job : Type v} [DecidableEq Job]
    (job_arrival job_cost : Job → time) (job_task : Job → sporadic_task)
    (job_deadline : Job → time) (arr_seq : arrival_sequence Job) (H_jobs_have_valid_parameters :
      ∀ j : Job, arrives_in arr_seq j →
        valid_sporadic_job task_cost task_deadline job_cost job_deadline job_task j) {num_cpus : Nat}
    (sched : schedule Job num_cpus) (H_jobs_come_from_arrival_sequence : jobs_come_from_arrival_sequence sched arr_seq) (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute job_arrival sched) (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched) (H_sequential_jobs : sequential_jobs sched) (H_sporadic_tasks : sporadic_task_model task_period job_arrival job_task arr_seq) (tsk : sporadic_task) (H_valid_task_parameters : is_valid_sporadic_task task_cost task_period task_deadline tsk) (H_constrained_deadline : task_deadline tsk ≤ task_period tsk)
    (t1 delta R_tsk : time) (H_response_time_bound :
      ∀ j : Job, arrives_in arr_seq j → job_task j = tsk →
        job_arrival j + R_tsk < t1 + delta →
        completed job_cost sched j (job_arrival j + R_tsk) = true) (H_response_time_ge_cost : task_cost tsk ≤ R_tsk) (H_no_deadline_miss : R_tsk ≤ task_deadline tsk) :
    workload job_task sched tsk t1 (t1 + delta) ≤ W task_cost task_period tsk R_tsk delta := by
  rw [workload_eq_workload_joblist,
    workload_bound_simpl_by_sorting_scheduled_jobs job_arrival job_task sched tsk t1 delta]
  by_cases NUM : (((jobs_of_task_scheduled_between job_task sched tsk t1 (t1 + delta)).mergeSort
        (fun x y => decide (job_arrival x ≤ job_arrival y)))).length ≤ max_jobs task_cost task_period tsk R_tsk delta
  · exact workload_bound_holds_for_at_most_n_k_jobs task_cost task_period task_deadline
      job_arrival job_cost job_task job_deadline arr_seq H_jobs_have_valid_parameters sched
      H_jobs_come_from_arrival_sequence H_completed_jobs_dont_execute tsk t1 delta R_tsk NUM
  have NUM : max_jobs task_cost task_period tsk R_tsk delta < (((jobs_of_task_scheduled_between job_task sched tsk t1 (t1 + delta)).mergeSort
        (fun x y => decide (job_arrival x ≤ job_arrival y)))).length := by omega
  obtain ⟨elem, _⟩ := List.exists_mem_of_length_pos (by omega : 0 < (((jobs_of_task_scheduled_between job_task sched tsk t1 (t1 + delta)).mergeSort
        (fun x y => decide (job_arrival x ≤ job_arrival y)))).length)
  rw [sumSeq_getD _ _ elem]
  obtain hlen | ⟨num_mid_jobs, hlen⟩ :
      (((jobs_of_task_scheduled_between job_task sched tsk t1 (t1 + delta)).mergeSort
        (fun x y => decide (job_arrival x ≤ job_arrival y)))).length = 1 ∨ ∃ m, (((jobs_of_task_scheduled_between job_task sched tsk t1 (t1 + delta)).mergeSort
        (fun x y => decide (job_arrival x ≤ job_arrival y)))).length = m + 2 := by
    rcases h : (((jobs_of_task_scheduled_between job_task sched tsk t1 (t1 + delta)).mergeSort
        (fun x y => decide (job_arrival x ≤ job_arrival y)))).length with _ | _ | m
    · omega
    · exact Or.inl rfl
    · exact Or.inr ⟨m, rfl⟩
  · rw [hlen]
    exact workload_bound_holds_for_a_single_job task_cost task_period task_deadline job_arrival
      job_cost job_task job_deadline arr_seq H_jobs_have_valid_parameters sched
      H_jobs_come_from_arrival_sequence H_completed_jobs_dont_execute H_sequential_jobs tsk t1
      delta R_tsk H_response_time_ge_cost (by omega) elem
  · have SPLIT : ∀ f : Nat → Nat, ∑ i ∈ Finset.Ico 0 (num_mid_jobs + 2), f i =
        f (num_mid_jobs + 1) + f 0 + ∑ i ∈ Finset.Ico 0 num_mid_jobs, f (i + 1) := by
      intro f
      rw [← Finset.range_eq_Ico, ← Finset.range_eq_Ico, show num_mid_jobs + 2 =
        num_mid_jobs + 1 + 1 from rfl, Finset.sum_range_succ, Finset.sum_range_succ']
      omega
    rw [hlen, SPLIT]
    have COVER := workload_bound_n_k_covers_middle_jobs task_cost task_period task_deadline
      job_arrival job_cost job_task arr_seq sched H_jobs_come_from_arrival_sequence
      H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_sporadic_tasks tsk
      H_valid_task_parameters H_constrained_deadline t1 delta R_tsk H_response_time_bound
      H_response_time_ge_cost H_no_deadline_miss num_mid_jobs hlen elem
    rcases (show max_jobs task_cost task_period tsk R_tsk delta = num_mid_jobs + 1 ∨ num_mid_jobs = max_jobs task_cost task_period tsk R_tsk delta by omega) with NKeq | NKeq
    · exact workload_bound_n_k_equals_num_mid_jobs_plus_1 task_cost task_period task_deadline
        job_arrival job_cost job_task job_deadline arr_seq H_jobs_have_valid_parameters sched
        H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute
        H_completed_jobs_dont_execute H_sequential_jobs H_sporadic_tasks tsk
        H_constrained_deadline t1 delta R_tsk H_response_time_bound H_response_time_ge_cost
        H_no_deadline_miss num_mid_jobs hlen elem NKeq.symm
    · exact workload_bound_n_k_equals_num_mid_jobs task_cost task_period task_deadline
        job_arrival job_cost job_task job_deadline arr_seq H_jobs_have_valid_parameters sched
        H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute
        H_completed_jobs_dont_execute H_sequential_jobs H_sporadic_tasks tsk
        H_valid_task_parameters H_constrained_deadline t1 delta R_tsk H_response_time_bound
        H_response_time_ge_cost H_no_deadline_miss num_mid_jobs hlen elem NKeq

end Prosa.Classic.Analysis.Global.Basic.WorkloadBound.WorkloadBound
