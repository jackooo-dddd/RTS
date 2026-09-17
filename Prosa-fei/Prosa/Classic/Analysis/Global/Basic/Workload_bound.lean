-- Translated from: ../rt-proofs/classic/analysis/global/basic/workload_bound.v
import Prosa.Classic.Util.All
import Prosa.Classic.Model.Arrival.Basic.Task
import Prosa.Classic.Model.Schedule.Global.Workload
import Prosa.Classic.Model.Schedule.Global.Basic.Schedule
import Prosa.Classic.Model.Arrival.Basic.Task_arrival
import Prosa.Classic.Model.Schedule.Global.Response_time
import Prosa.Classic.Model.Schedule.Global.Schedulability
import Prosa.Classic.Util.Div_mod
import Prosa.Classic.Util.Sorting
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic

set_option autoImplicit false

namespace Prosa.Classic.Analysis.Global.Basic.Workload_bound

open Prosa.Classic.Model.Time
open Prosa.Classic.Model.Arrival.Basic.Arrival_sequence
open Prosa.Classic.Model.Arrival.Basic.Task
open Prosa.Classic.Model.Arrival.Basic.Task.SporadicTask
open Prosa.Classic.Model.Arrival.Basic.Task_arrival
open Prosa.Classic.Model.Arrival.Basic.Job
open Prosa.Classic.Model.Schedule.Global.Basic.Schedule
open Prosa.Classic.Model.Schedule.Global.Basic.Schedule.Schedule
open Prosa.Classic.Model.Schedule.Global.Basic.Schedule.ScheduleOfSporadicTask
open Prosa.Classic.Model.Schedule.Global.Response_time
open Prosa.Classic.Model.Schedule.Global.Response_time.ResponseTime
open Prosa.Classic.Model.Schedule.Global.Schedulability
open Prosa.Classic.Model.Schedule.Global.Workload
open Prosa.Classic.Util.Sorting
open Prosa.Util.Div_mod

namespace WorkloadBound

section WorkloadBoundDef

variable {sporadic_task : Type _} [DecidableEq sporadic_task]
variable (task_cost : sporadic_task → Time)
variable (task_period : sporadic_task → Time)

variable (tsk : sporadic_task)
variable (R_tsk : Time)
variable (delta : Time)

def max_jobs : ℕ :=
  div_floor (delta + R_tsk - task_cost tsk) (task_period tsk)

def W : ℕ :=
  let e_k := task_cost tsk
  let p_k := task_period tsk
  min e_k (delta + R_tsk - e_k - max_jobs task_cost task_period tsk R_tsk delta * p_k) +
    max_jobs task_cost task_period tsk R_tsk delta * e_k

end WorkloadBoundDef

section BasicLemmas

variable {sporadic_task : Type _} [DecidableEq sporadic_task]
variable (task_cost : sporadic_task → Time)
variable (task_period : sporadic_task → Time)

variable (tsk : sporadic_task)

variable (H_period_positive : task_period tsk > 0)

variable (R1 R2 : Time)
variable (H_R_lower_bound : R1 ≥ task_cost tsk)
variable (H_R1_le_R2 : R1 ≤ R2)
include H_period_positive H_R_lower_bound H_R1_le_R2

include H_period_positive H_R_lower_bound H_R1_le_R2 in
theorem W_monotonic :
    ∀ (t1 t2 : Time),
      t1 ≤ t2 →
      W task_cost task_period tsk R1 t1 ≤
        W task_cost task_period tsk R2 t2 := by
  intro t1 t2 h_le
  dsimp only [W, max_jobs, div_floor]
  rw [Prosa.Classic.Util.Div_mod.subndiv_eq_mod, Prosa.Classic.Util.Div_mod.subndiv_eq_mod]
  set e := task_cost tsk
  set p := task_period tsk
  set x1 := t1 + R1
  set x2 := t2 + R2
  have h_x1_le_x2 : x1 ≤ x2 := Nat.add_le_add h_le H_R1_le_R2
  have h_e_le_x1 : e ≤ x1 := le_trans H_R_lower_bound (Nat.le_add_left _ _)
  set d := x2 - x1
  have h_x2_eq : x2 = x1 + d := (Nat.add_sub_cancel' h_x1_le_x2).symm
  rw [h_x2_eq]
  induction d with
  | zero => simp
  | succ d' ih =>
    apply le_trans ih
    have h_e_le_d : e ≤ x1 + d' := le_trans h_e_le_x1 (Nat.le_add_right _ _)
    rw [show x1 + (d' + 1) = (x1 + d') + 1 from by ring, Nat.succ_sub h_e_le_d]
    set n := x1 + d' - e
    by_cases h_p_le_1 : p ≤ 1
    · have h_p_eq : p = 1 := Nat.le_antisymm h_p_le_1 H_period_positive
      rw [h_p_eq]; simp [Nat.mod_one, Nat.div_one]
      rw [Nat.add_mul]; exact Nat.le_add_right _ _
    · push_neg at h_p_le_1
      have h_p_gt1 : p > 1 := h_p_le_1
      have h_div_cases := Prosa.Classic.Util.Div_mod.divSn_cases n p h_p_gt1
      rcases h_div_cases with ⟨h_div_eq, h_mod_eq⟩ | h_div_succ
      · rw [← h_div_eq, ← h_mod_eq]
        exact Nat.add_le_add_right (min_le_min_left e (Nat.le_succ _)) _
      · rw [← h_div_succ, show (n / p + 1) * e = n / p * e + e from by ring]
        have : min e (n % p) ≤ min e ((n + 1) % p) + e :=
          le_trans (min_le_left _ _) (Nat.le_add_left _ _)
        clear_value e n p; omega

end BasicLemmas

private lemma list_map_sum_range_eq {α : Type _} (l : List α) (f : α → ℕ) (d : α) :
    (l.map f).sum = ∑ i ∈ Finset.range l.length, f (l.getD i d) := by
  induction l with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    rw [ih, Finset.sum_range_succ']
    simp only [List.getD_cons_zero, List.getD_cons_succ]
    omega

private lemma list_map_sum_decomp' {α : Type _} (l : List α) (f : α → ℕ) (d : α) (n : ℕ)
    (h : l.length = n + 2) :
    (l.map f).sum = f (l.getD (n + 1) d) + f (l.getD 0 d) +
      ∑ i ∈ Finset.Ico 0 n, f (l.getD (i + 1) d) := by
  rw [list_map_sum_range_eq, h, Finset.sum_range_succ, Finset.sum_range_succ']
  have : Finset.range n = Finset.Ico 0 n := congr_fun Finset.range_eq_Ico n
  rw [this]
  ac_rfl

private lemma nat_sub_cross_eq (a b t1' d R : ℕ)
    (h1 : t1' ≤ a + R) (h2 : b < t1' + d) (h3 : a ≤ b) :
    a + R - t1' + (t1' + d - b) = d + R - (b - a) := by omega

private lemma nat_le_sub_of_add_le (a b c : ℕ) (h : a + c ≤ b) : c ≤ b - a := by omega

private lemma nat_le_sub_of_le_add (a b c : ℕ) (h : a ≤ b) : c ≤ b + c - a := by omega

private lemma nat_sub_lt_of_lt_add (a b c : ℕ) (h1 : a ≤ b) (h2 : b < a + c) : b - a < c := by omega

private lemma nat_lt_div_succ_mul (a b : ℕ) (hb : 0 < b) : a < (a / b + 1) * b := by
  have h1 := Nat.div_add_mod a b
  have h2 := Nat.mod_lt a hb
  nlinarith [mul_comm b (a / b)]

private lemma nat_sub_le_swap (a b c : ℕ) (h : a - b ≤ c) : a - c ≤ b := by omega

private lemma nat_sub_sub_add_cancel (a b c : ℕ) (h : b + c ≤ a) : a - b - c + b = a - c := by omega

section ProofWorkloadBound

variable {sporadic_task : Type _} [DecidableEq sporadic_task]
variable (task_cost : sporadic_task → Time)
variable (task_period : sporadic_task → Time)
variable (task_deadline : sporadic_task → Time)

variable {Job : Type _} [DecidableEq Job]
variable (job_arrival : Job → Time)
variable (job_cost : Job → Time)
variable (job_task : Job → sporadic_task)
variable (job_deadline : Job → Time)

variable (arr_seq : Prosa.Classic.Model.Arrival.Basic.Arrival_sequence.arrival_sequence Job)

variable (H_jobs_have_valid_parameters :
  ∀ (j : Job),
    Prosa.Classic.Model.Arrival.Basic.Arrival_sequence.arrives_in arr_seq j →
    Prosa.Classic.Model.Arrival.Basic.Job.valid_sporadic_job task_cost task_deadline job_cost job_deadline job_task j)

variable {num_cpus : ℕ}
variable (sched : schedule Job num_cpus)
variable (H_jobs_come_from_arrival_sequence :
  jobs_come_from_arrival_sequence sched arr_seq)

variable (H_jobs_must_arrive_to_execute :
  jobs_must_arrive_to_execute job_arrival sched)

variable (H_completed_jobs_dont_execute :
  completed_jobs_dont_execute job_cost sched)

variable (H_sequential_jobs : sequential_jobs sched)

variable (H_sporadic_tasks :
  sporadic_task_model task_period job_arrival job_task arr_seq)

variable (tsk : sporadic_task)

variable (H_valid_task_parameters :
  is_valid_sporadic_task task_cost task_period task_deadline tsk)

variable (H_constrained_deadline : task_deadline tsk ≤ task_period tsk)

variable (t1 delta : Time)

variable (R_tsk : Time)

variable (H_response_time_bound :
  ∀ (j : Job),
    Prosa.Classic.Model.Arrival.Basic.Arrival_sequence.arrives_in arr_seq j →
    job_task j = tsk →
    job_arrival j + R_tsk < t1 + delta →
    completed job_cost sched j (job_arrival j + R_tsk))

variable (H_response_time_ge_cost : R_tsk ≥ task_cost tsk)
variable (H_no_deadline_miss : R_tsk ≤ task_deadline tsk)

include H_jobs_have_valid_parameters H_jobs_come_from_arrival_sequence
  H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute
  H_sequential_jobs H_sporadic_tasks H_valid_task_parameters
  H_constrained_deadline H_response_time_bound
  H_response_time_ge_cost H_no_deadline_miss

section MainProof

private noncomputable def mk_sorted_jobs
    (ja : Job → Time) (jt : Job → sporadic_task) (s : schedule Job num_cpus)
    (tk : sporadic_task) (t1' delta' : Time) : List Job :=
  (jobs_of_task_scheduled_between jt s tk t1' (t1' + delta')).mergeSort
    (fun x y => decide (ja x ≤ ja y))

theorem workload_bound_simpl_by_sorting_scheduled_jobs :
    workload_joblist job_task sched tsk t1 (t1 + delta) =
      ((mk_sorted_jobs job_arrival job_task sched tsk t1 delta).map
        (fun i => service_during sched i t1 (t1 + delta))).sum := by
  unfold workload_joblist mk_sorted_jobs
  have hperm := List.mergeSort_perm
    (jobs_of_task_scheduled_between job_task sched tsk t1 (t1 + delta))
    (fun x y => decide (job_arrival x ≤ job_arrival y))
  have hnodup : (jobs_of_task_scheduled_between job_task sched tsk t1 (t1 + delta)).Nodup := by
    unfold jobs_of_task_scheduled_between
    exact List.Nodup.filter _ (List.nodup_dedup _)
  rw [List.sum_toFinset _ hnodup]
  exact (hperm.symm.map _).sum_eq

theorem workload_bound_job_in_same_sequence :
    ∀ (j : Job),
      (j ∈ jobs_of_task_scheduled_between job_task sched tsk t1 (t1 + delta)) =
        (j ∈ mk_sorted_jobs job_arrival job_task sched tsk t1 delta) := by
  intro j
  unfold mk_sorted_jobs
  have hperm := List.mergeSort_perm
    (jobs_of_task_scheduled_between job_task sched tsk t1 (t1 + delta))
    (fun x y => decide (job_arrival x ≤ job_arrival y))
  exact propext ⟨fun h => hperm.mem_iff.mpr h, fun h => hperm.mem_iff.mp h⟩

theorem workload_bound_all_jobs_from_tsk :
    ∀ (j_i : Job),
      j_i ∈ mk_sorted_jobs job_arrival job_task sched tsk t1 delta →
      Prosa.Classic.Model.Arrival.Basic.Arrival_sequence.arrives_in arr_seq j_i ∧
      job_task j_i = tsk ∧
      service_during sched j_i t1 (t1 + delta) ≠ 0 ∧
      j_i ∈ jobs_scheduled_between sched t1 (t1 + delta) := by
  intro j_i hj_i
  unfold mk_sorted_jobs at hj_i
  have hperm := List.mergeSort_perm
    (jobs_of_task_scheduled_between job_task sched tsk t1 (t1 + delta))
    (fun x y => decide (job_arrival x ≤ job_arrival y))
  have hj_i' : j_i ∈ jobs_of_task_scheduled_between job_task sched tsk t1 (t1 + delta) :=
    hperm.mem_iff.mp hj_i
  unfold jobs_of_task_scheduled_between at hj_i'
  rw [List.mem_filter] at hj_i'
  obtain ⟨hj_sched, hj_task⟩ := hj_i'
  have hj_task_eq : job_task j_i = tsk := by rwa [decide_eq_true_eq] at hj_task
  have hj_sched_dedup : j_i ∈ Prosa.Util.Bigcat.bigcat_nat (fun t => jobs_scheduled_at sched t) t1 (t1 + delta) := by
    unfold jobs_scheduled_between at hj_sched; rwa [List.mem_dedup] at hj_sched
  obtain ⟨t, ht_mem, ht_ge, ht_lt⟩ := Prosa.Util.Bigcat.mem_bigcat_nat_exists j_i t1 (t1 + delta) _ hj_sched_dedup
  rw [mem_scheduled_jobs_eq_scheduled] at ht_mem
  refine ⟨H_jobs_come_from_arrival_sequence j_i t ht_mem, hj_task_eq, ?_, hj_sched⟩
  have h_serv_ne : service_at sched j_i t ≠ 0 := by
    intro h_zero; exact (not_scheduled_no_service sched j_i t).mpr h_zero ht_mem
  exact service_implies_cumulative_service sched j_i t t1 (t1 + delta) ht_ge ht_lt h_serv_ne

theorem workload_bound_jobs_ordered_by_arrival :
    ∀ (i : ℕ) (elem : Job),
      i < (mk_sorted_jobs job_arrival job_task sched tsk t1 delta).length - 1 →
      decide (job_arrival
        ((mk_sorted_jobs job_arrival job_task sched tsk t1 delta).getD i elem) ≤
       job_arrival
        ((mk_sorted_jobs job_arrival job_task sched tsk t1 delta).getD (i + 1) elem)) = true := by
  intro i elem hi
  unfold mk_sorted_jobs at hi ⊢
  have htotal : ∀ a b : Job,
      (decide (job_arrival a ≤ job_arrival b) || decide (job_arrival b ≤ job_arrival a)) = true := by
    intro a b; simp only [Bool.or_eq_true, decide_eq_true_eq]; exact Nat.le_or_le _ _
  have htrans : ∀ a b c : Job,
      (decide (job_arrival a ≤ job_arrival b) = true) →
      (decide (job_arrival b ≤ job_arrival c) = true) →
      (decide (job_arrival a ≤ job_arrival c) = true) := by
    intro a b c hab hbc; simp only [decide_eq_true_eq] at hab hbc ⊢; exact le_trans hab hbc
  set sorted := (jobs_of_task_scheduled_between job_task sched tsk t1 (t1 + delta)).mergeSort
      (fun x y => decide (job_arrival x ≤ job_arrival y))
  have hpw := List.pairwise_mergeSort htrans htotal
      (jobs_of_task_scheduled_between job_task sched tsk t1 (t1 + delta))
  have hlen : i + 1 < sorted.length := by omega
  rw [List.getD_eq_getElem _ _ (show i < sorted.length by omega), List.getD_eq_getElem _ _ hlen]
  exact (List.pairwise_iff_getElem.mp hpw) i (i + 1) (show i < sorted.length by omega) hlen (by omega)

section WorkloadNotManyJobs

include H_jobs_have_valid_parameters H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_sequential_jobs H_sporadic_tasks H_valid_task_parameters H_constrained_deadline H_response_time_bound H_response_time_ge_cost H_no_deadline_miss in
theorem workload_bound_holds_for_at_most_n_k_jobs :
    (mk_sorted_jobs job_arrival job_task sched tsk t1 delta).length ≤
      max_jobs task_cost task_period tsk R_tsk delta →
    ((mk_sorted_jobs job_arrival job_task sched tsk t1 delta).map
      (fun i => service_during sched i t1 (t1 + delta))).sum ≤
      W task_cost task_period tsk R_tsk delta := by
  intro h_le
  set sorted := mk_sorted_jobs job_arrival job_task sched tsk t1 delta
  set f := fun i => service_during sched i t1 (t1 + delta)
  -- Each job's service ≤ task_cost tsk
  have h_each : ∀ j, j ∈ sorted → f j ≤ task_cost tsk := by
    intro j hj
    have h_props := workload_bound_all_jobs_from_tsk task_cost task_period task_deadline job_arrival job_cost job_task
      job_deadline arr_seq H_jobs_have_valid_parameters sched H_jobs_come_from_arrival_sequence
      H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_sequential_jobs
      H_sporadic_tasks tsk H_valid_task_parameters H_constrained_deadline t1 delta R_tsk
      H_response_time_bound H_response_time_ge_cost H_no_deadline_miss j hj
    obtain ⟨h_arr, h_tsk, _, _⟩ := h_props
    exact cumulative_service_le_task_cost task_cost task_deadline job_cost job_deadline job_task sched
      H_completed_jobs_dont_execute tsk j h_tsk (H_jobs_have_valid_parameters _ h_arr) t1 (t1 + delta)
  -- sum of services ≤ sorted.length * task_cost tsk
  have h_sum_le : (sorted.map f).sum ≤ sorted.length * task_cost tsk := by
    have h_bound : ∀ x, x ∈ sorted.map f → x ≤ task_cost tsk := by
      intro x hx; rw [List.mem_map] at hx
      obtain ⟨j', hj', rfl⟩ := hx; exact h_each j' hj'
    calc (sorted.map f).sum
        ≤ (sorted.map f).length * task_cost tsk := List.sum_le_card_nsmul _ _ (fun x hx => h_bound x hx)
      _ = sorted.length * task_cost tsk := by rw [List.length_map]
  -- sorted.length * task_cost tsk ≤ n_k * task_cost tsk ≤ W
  calc (sorted.map f).sum ≤ sorted.length * task_cost tsk := h_sum_le
    _ ≤ max_jobs task_cost task_period tsk R_tsk delta * task_cost tsk := Nat.mul_le_mul_right _ h_le
    _ ≤ W task_cost task_period tsk R_tsk delta := Nat.le_add_left _ _

end WorkloadNotManyJobs

section WorkloadSingleJob

variable (H_at_least_one_job :
  (mk_sorted_jobs job_arrival job_task sched tsk t1 delta).length > 0)

variable (elem : Job)
include H_at_least_one_job

theorem workload_bound_j_fst_is_job_of_tsk :
    let j_fst := (mk_sorted_jobs job_arrival job_task sched tsk t1 delta).getD 0 elem
    Prosa.Classic.Model.Arrival.Basic.Arrival_sequence.arrives_in arr_seq j_fst ∧
    job_task j_fst = tsk ∧
    service_during sched j_fst t1 (t1 + delta) ≠ 0 ∧
    j_fst ∈ jobs_scheduled_between sched t1 (t1 + delta) := by
  intro j_fst
  have hmem : j_fst ∈ mk_sorted_jobs job_arrival job_task sched tsk t1 delta := by
    simp only [j_fst]; simp [H_at_least_one_job]
  exact workload_bound_all_jobs_from_tsk task_cost task_period task_deadline job_arrival job_cost job_task
    job_deadline arr_seq H_jobs_have_valid_parameters sched H_jobs_come_from_arrival_sequence
    H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_sequential_jobs
    H_sporadic_tasks tsk H_valid_task_parameters H_constrained_deadline t1 delta R_tsk
    H_response_time_bound H_response_time_ge_cost H_no_deadline_miss j_fst hmem

include H_jobs_have_valid_parameters H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_sequential_jobs H_sporadic_tasks H_valid_task_parameters H_constrained_deadline H_response_time_bound H_response_time_ge_cost H_no_deadline_miss H_at_least_one_job in
theorem workload_bound_holds_for_a_single_job :
    ∑ i ∈ Finset.Ico 0 1,
      service_during sched
        ((mk_sorted_jobs job_arrival job_task sched tsk t1 delta).getD i elem)
        t1 (t1 + delta) ≤
      W task_cost task_period tsk R_tsk delta := by
  have : Finset.Ico 0 1 = {0} := by decide
  rw [this, Finset.sum_singleton]
  set sorted := mk_sorted_jobs job_arrival job_task sched tsk t1 delta
  set j_fst := sorted.getD 0 elem
  have h_fst_mem : j_fst ∈ mk_sorted_jobs job_arrival job_task sched tsk t1 delta := by
    unfold j_fst
    rw [List.getD_eq_getElem (hn := H_at_least_one_job)]
    exact List.getElem_mem H_at_least_one_job
  have h_props := workload_bound_all_jobs_from_tsk task_cost task_period task_deadline job_arrival job_cost job_task
      job_deadline arr_seq H_jobs_have_valid_parameters sched H_jobs_come_from_arrival_sequence
      H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_sequential_jobs
      H_sporadic_tasks tsk H_valid_task_parameters H_constrained_deadline t1 delta R_tsk
      H_response_time_bound H_response_time_ge_cost H_no_deadline_miss j_fst h_fst_mem
  obtain ⟨h_arr, h_tsk, _, _⟩ := h_props
  have h_serv_le_cost : service_during sched j_fst t1 (t1 + delta) ≤ task_cost tsk :=
    cumulative_service_le_task_cost task_cost task_deadline job_cost job_deadline job_task sched
      H_completed_jobs_dont_execute tsk j_fst h_tsk (H_jobs_have_valid_parameters _ h_arr) t1 (t1 + delta)
  have h_serv_le_delta : service_during sched j_fst t1 (t1 + delta) ≤ delta :=
    cumulative_service_le_delta sched j_fst H_sequential_jobs t1 delta
  unfold W max_jobs
  set n_k := div_floor (delta + R_tsk - task_cost tsk) (task_period tsk)
  cases n_k with
  | zero =>
    simp only [Nat.zero_mul, Nat.add_zero, Nat.sub_zero]
    apply Nat.le_min.mpr
    constructor
    · exact h_serv_le_cost
    · have hge : task_cost tsk ≤ R_tsk := H_response_time_ge_cost
      calc service_during sched j_fst t1 (t1 + delta)
          ≤ delta := h_serv_le_delta
        _ ≤ delta + R_tsk - task_cost tsk := Nat.le_sub_of_add_le (Nat.add_le_add_left hge delta)
  | succ k =>
    calc service_during sched j_fst t1 (t1 + delta)
        ≤ task_cost tsk := h_serv_le_cost
      _ = 1 * task_cost tsk := (Nat.one_mul _).symm
      _ ≤ (k + 1) * task_cost tsk := Nat.mul_le_mul_right _ (Nat.succ_le_succ (Nat.zero_le _))
      _ ≤ min (task_cost tsk) (delta + R_tsk - task_cost tsk - (k + 1) * task_period tsk) +
          (k + 1) * task_cost tsk := Nat.le_add_left _ _

end WorkloadSingleJob

section WorkloadTwoOrMoreJobs

variable (num_mid_jobs : ℕ)
variable (H_at_least_two_jobs :
  (mk_sorted_jobs job_arrival job_task sched tsk t1 delta).length = num_mid_jobs + 2)

variable (elem : Job)
include H_at_least_two_jobs

theorem workload_bound_j_lst_is_job_of_tsk :
    let j_lst := (mk_sorted_jobs job_arrival job_task sched tsk t1 delta).getD (num_mid_jobs + 1) elem
    Prosa.Classic.Model.Arrival.Basic.Arrival_sequence.arrives_in arr_seq j_lst ∧
    job_task j_lst = tsk ∧
    service_during sched j_lst t1 (t1 + delta) ≠ 0 ∧
    j_lst ∈ jobs_scheduled_between sched t1 (t1 + delta) := by
  intro j_lst
  have hmem : j_lst ∈ mk_sorted_jobs job_arrival job_task sched tsk t1 delta := by
    simp only [j_lst]; simp [show num_mid_jobs + 1 < (mk_sorted_jobs job_arrival job_task sched tsk t1 delta).length by omega]
  exact workload_bound_all_jobs_from_tsk task_cost task_period task_deadline job_arrival job_cost job_task
    job_deadline arr_seq H_jobs_have_valid_parameters sched H_jobs_come_from_arrival_sequence
    H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_sequential_jobs
    H_sporadic_tasks tsk H_valid_task_parameters H_constrained_deadline t1 delta R_tsk
    H_response_time_bound H_response_time_ge_cost H_no_deadline_miss j_lst hmem

include H_jobs_have_valid_parameters H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_sequential_jobs H_sporadic_tasks H_valid_task_parameters H_constrained_deadline H_response_time_bound H_response_time_ge_cost H_no_deadline_miss H_at_least_two_jobs in
theorem workload_bound_response_time_of_first_job_inside_interval :
    let j_fst := (mk_sorted_jobs job_arrival job_task sched tsk t1 delta).getD 0 elem
    t1 ≤ job_arrival j_fst + R_tsk := by
  intro j_fst
  by_contra h_lt
  push_neg at h_lt
  have h_sz : 0 < (mk_sorted_jobs job_arrival job_task sched tsk t1 delta).length := by
    rw [H_at_least_two_jobs]; omega
  have h_fst_mem : j_fst ∈ mk_sorted_jobs job_arrival job_task sched tsk t1 delta := by
    unfold j_fst
    rw [List.getD_eq_getElem (hn := h_sz)]
    exact List.getElem_mem h_sz
  have h_props := workload_bound_all_jobs_from_tsk task_cost task_period task_deadline job_arrival job_cost job_task
      job_deadline arr_seq H_jobs_have_valid_parameters sched H_jobs_come_from_arrival_sequence
      H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_sequential_jobs
      H_sporadic_tasks tsk H_valid_task_parameters H_constrained_deadline t1 delta R_tsk
      H_response_time_bound H_response_time_ge_cost H_no_deadline_miss j_fst h_fst_mem
  obtain ⟨h_arr, h_tsk, h_serv_ne, _⟩ := h_props
  have h_rt : job_arrival j_fst + R_tsk < t1 + delta := by
    calc job_arrival j_fst + R_tsk < t1 := h_lt
      _ ≤ t1 + delta := Nat.le_add_right _ _
  have h_comp := H_response_time_bound j_fst h_arr h_tsk h_rt
  have h_ge : t1 ≥ job_arrival j_fst + R_tsk := Nat.le_of_lt_succ (Nat.lt_succ_of_lt h_lt)
  have h_zero := cumulative_service_after_job_rt_zero job_arrival job_cost sched
    H_completed_jobs_dont_execute j_fst R_tsk h_comp t1 (t1 + delta) h_ge
  apply h_serv_ne
  unfold service_during
  exact h_zero

include H_jobs_have_valid_parameters H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_sequential_jobs H_sporadic_tasks H_valid_task_parameters H_constrained_deadline H_response_time_bound H_response_time_ge_cost H_no_deadline_miss H_at_least_two_jobs in
theorem workload_bound_last_job_arrives_before_end_of_interval :
    let j_lst := (mk_sorted_jobs job_arrival job_task sched tsk t1 delta).getD (num_mid_jobs + 1) elem
    job_arrival j_lst < t1 + delta := by
  intro j_lst
  by_contra h_ge
  push_neg at h_ge
  have h_lt : num_mid_jobs + 1 < (mk_sorted_jobs job_arrival job_task sched tsk t1 delta).length := by
    rw [H_at_least_two_jobs]; omega
  have h_lst_mem : j_lst ∈ mk_sorted_jobs job_arrival job_task sched tsk t1 delta := by
    unfold j_lst
    rw [List.getD_eq_getElem (hn := h_lt)]
    exact List.getElem_mem h_lt
  have h_props := workload_bound_all_jobs_from_tsk task_cost task_period task_deadline job_arrival job_cost job_task
      job_deadline arr_seq H_jobs_have_valid_parameters sched H_jobs_come_from_arrival_sequence
      H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_sequential_jobs
      H_sporadic_tasks tsk H_valid_task_parameters H_constrained_deadline t1 delta R_tsk
      H_response_time_bound H_response_time_ge_cost H_no_deadline_miss j_lst h_lst_mem
  obtain ⟨_, _, h_serv_ne, _⟩ := h_props
  apply h_serv_ne
  unfold service_during
  exact cumulative_service_before_job_arrival_zero job_arrival sched j_lst
    H_jobs_must_arrive_to_execute t1 (t1 + delta) h_ge

include H_jobs_have_valid_parameters H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_sequential_jobs H_sporadic_tasks H_valid_task_parameters H_constrained_deadline H_response_time_bound H_response_time_ge_cost H_no_deadline_miss H_at_least_two_jobs in
theorem workload_bound_service_of_first_and_last_jobs :
    let j_fst := (mk_sorted_jobs job_arrival job_task sched tsk t1 delta).getD 0 elem
    let j_lst := (mk_sorted_jobs job_arrival job_task sched tsk t1 delta).getD (num_mid_jobs + 1) elem
    service_during sched j_fst t1 (t1 + delta) +
    service_during sched j_lst t1 (t1 + delta) ≤
      (job_arrival j_fst + R_tsk - t1) +
      (t1 + delta - job_arrival j_lst) := by
  intro j_fst j_lst
  -- Get properties of j_fst
  have h_sz_fst : 0 < (mk_sorted_jobs job_arrival job_task sched tsk t1 delta).length := by
    rw [H_at_least_two_jobs]; omega
  have h_fst_mem : j_fst ∈ mk_sorted_jobs job_arrival job_task sched tsk t1 delta := by
    unfold j_fst; rw [List.getD_eq_getElem (hn := h_sz_fst)]
    exact List.getElem_mem h_sz_fst
  have h_fst_props := workload_bound_all_jobs_from_tsk task_cost task_period task_deadline job_arrival job_cost job_task
    job_deadline arr_seq H_jobs_have_valid_parameters sched H_jobs_come_from_arrival_sequence
    H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_sequential_jobs
    H_sporadic_tasks tsk H_valid_task_parameters H_constrained_deadline t1 delta R_tsk
    H_response_time_bound H_response_time_ge_cost H_no_deadline_miss j_fst h_fst_mem
  obtain ⟨h_fst_arr, h_fst_tsk, _, _⟩ := h_fst_props
  -- Get properties of j_lst
  have h_sz_lst : num_mid_jobs + 1 < (mk_sorted_jobs job_arrival job_task sched tsk t1 delta).length := by
    rw [H_at_least_two_jobs]; omega
  have h_lst_mem : j_lst ∈ mk_sorted_jobs job_arrival job_task sched tsk t1 delta := by
    unfold j_lst; rw [List.getD_eq_getElem (hn := h_sz_lst)]
    exact List.getElem_mem h_sz_lst
  have h_lst_props := workload_bound_all_jobs_from_tsk task_cost task_period task_deadline job_arrival job_cost job_task
    job_deadline arr_seq H_jobs_have_valid_parameters sched H_jobs_come_from_arrival_sequence
    H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_sequential_jobs
    H_sporadic_tasks tsk H_valid_task_parameters H_constrained_deadline t1 delta R_tsk
    H_response_time_bound H_response_time_ge_cost H_no_deadline_miss j_lst h_lst_mem
  obtain ⟨_, _, _, _⟩ := h_lst_props
  -- Key bounds
  have h_t1_le : t1 ≤ job_arrival j_fst + R_tsk :=
    workload_bound_response_time_of_first_job_inside_interval
      task_cost task_period task_deadline
      job_arrival job_cost job_task job_deadline
      arr_seq H_jobs_have_valid_parameters
      sched H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute
      H_completed_jobs_dont_execute H_sequential_jobs H_sporadic_tasks
      tsk H_valid_task_parameters H_constrained_deadline
      t1 delta R_tsk
      H_response_time_bound H_response_time_ge_cost H_no_deadline_miss
      num_mid_jobs H_at_least_two_jobs elem
  have h_lst_lt : job_arrival j_lst < t1 + delta :=
    workload_bound_last_job_arrives_before_end_of_interval
      task_cost task_period task_deadline
      job_arrival job_cost job_task job_deadline
      arr_seq H_jobs_have_valid_parameters
      sched H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute
      H_completed_jobs_dont_execute H_sequential_jobs H_sporadic_tasks
      tsk H_valid_task_parameters H_constrained_deadline
      t1 delta R_tsk
      H_response_time_bound H_response_time_ge_cost H_no_deadline_miss
      num_mid_jobs H_at_least_two_jobs elem
  have h_lst_le := Nat.le_of_lt h_lst_lt
  -- Bound for j_fst: service ≤ arr_fst + R_tsk - t1
  have h_fst_bound : service_during sched j_fst t1 (t1 + delta) ≤ job_arrival j_fst + R_tsk - t1 := by
    by_cases h_case : job_arrival j_fst + R_tsk < t1 + delta
    · -- j_fst completed within the interval
      have h_comp := H_response_time_bound j_fst h_fst_arr h_fst_tsk h_case
      have h_mid_le := Nat.le_of_lt h_case
      -- Split service at arr_fst + R_tsk
      have h_split : service_during sched j_fst t1 (t1 + delta) =
          service_during sched j_fst t1 (job_arrival j_fst + R_tsk) +
          service_during sched j_fst (job_arrival j_fst + R_tsk) (t1 + delta) := by
        unfold service_during
        exact (Finset.sum_Ico_consecutive (f := fun t => service_at sched j_fst t) h_t1_le h_mid_le).symm
      -- Service after RT = 0
      have h_after_zero : service_during sched j_fst (job_arrival j_fst + R_tsk) (t1 + delta) = 0 := by
        unfold service_during
        exact cumulative_service_after_job_rt_zero job_arrival job_cost sched
          H_completed_jobs_dont_execute j_fst R_tsk h_comp
          (job_arrival j_fst + R_tsk) (t1 + delta) (le_refl _)
      rw [h_split, h_after_zero, Nat.add_zero]
      -- Service before RT ≤ interval length
      have h_le_delta := cumulative_service_le_delta sched j_fst H_sequential_jobs t1
        (job_arrival j_fst + R_tsk - t1)
      rwa [Nat.add_sub_cancel' h_t1_le] at h_le_delta
    · -- arr_fst + R_tsk ≥ t1 + delta: service ≤ delta ≤ arr_fst + R_tsk - t1
      push_neg at h_case
      calc service_during sched j_fst t1 (t1 + delta)
          ≤ delta := cumulative_service_le_delta sched j_fst H_sequential_jobs t1 delta
        _ ≤ job_arrival j_fst + R_tsk - t1 := nat_le_sub_of_add_le t1 _ delta h_case
  -- Bound for j_lst: service ≤ t1 + delta - arr_lst
  have h_lst_bound : service_during sched j_lst t1 (t1 + delta) ≤ t1 + delta - job_arrival j_lst := by
    by_cases h_case : job_arrival j_lst ≥ t1
    · -- Split service at arr_lst
      have h_split : service_during sched j_lst t1 (t1 + delta) =
          service_during sched j_lst t1 (job_arrival j_lst) +
          service_during sched j_lst (job_arrival j_lst) (t1 + delta) := by
        unfold service_during
        exact (Finset.sum_Ico_consecutive (f := fun t => service_at sched j_lst t) h_case h_lst_le).symm
      -- Service before arrival = 0
      have h_before_zero : service_during sched j_lst t1 (job_arrival j_lst) = 0 :=
        cumulative_service_before_job_arrival_zero job_arrival sched j_lst
          H_jobs_must_arrive_to_execute t1 (job_arrival j_lst) (le_refl _)
      rw [h_split, h_before_zero, Nat.zero_add]
      have h_le_delta := cumulative_service_le_delta sched j_lst H_sequential_jobs
        (job_arrival j_lst) (t1 + delta - job_arrival j_lst)
      rwa [Nat.add_sub_cancel' h_lst_le] at h_le_delta
    · -- arr_lst < t1: service ≤ delta ≤ t1 + delta - arr_lst
      push_neg at h_case
      calc service_during sched j_lst t1 (t1 + delta)
          ≤ delta := cumulative_service_le_delta sched j_lst H_sequential_jobs t1 delta
        _ ≤ t1 + delta - job_arrival j_lst :=
            nat_le_sub_of_le_add _ _ delta (le_of_lt h_case)
  exact Nat.add_le_add h_fst_bound h_lst_bound

include H_jobs_have_valid_parameters H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_sequential_jobs H_sporadic_tasks H_valid_task_parameters H_constrained_deadline H_response_time_bound H_response_time_ge_cost H_no_deadline_miss H_at_least_two_jobs in
theorem workload_bound_simpl_expression_with_first_and_last :
    let j_fst := (mk_sorted_jobs job_arrival job_task sched tsk t1 delta).getD 0 elem
    let j_lst := (mk_sorted_jobs job_arrival job_task sched tsk t1 delta).getD (num_mid_jobs + 1) elem
    job_arrival j_fst + R_tsk - t1 +
      (t1 + delta - job_arrival j_lst) =
    delta + R_tsk -
      (job_arrival j_lst - job_arrival j_fst) := by
  intro j_fst j_lst
  have h_t1_le : t1 ≤ job_arrival j_fst + R_tsk :=
    workload_bound_response_time_of_first_job_inside_interval
      task_cost task_period task_deadline
      job_arrival job_cost job_task job_deadline
      arr_seq H_jobs_have_valid_parameters
      sched H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute
      H_completed_jobs_dont_execute H_sequential_jobs H_sporadic_tasks
      tsk H_valid_task_parameters H_constrained_deadline
      t1 delta R_tsk
      H_response_time_bound H_response_time_ge_cost H_no_deadline_miss
      num_mid_jobs H_at_least_two_jobs elem
  have h_lst_lt : job_arrival j_lst < t1 + delta :=
    workload_bound_last_job_arrives_before_end_of_interval
      task_cost task_period task_deadline
      job_arrival job_cost job_task job_deadline
      arr_seq H_jobs_have_valid_parameters
      sched H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute
      H_completed_jobs_dont_execute H_sequential_jobs H_sporadic_tasks
      tsk H_valid_task_parameters H_constrained_deadline
      t1 delta R_tsk
      H_response_time_bound H_response_time_ge_cost H_no_deadline_miss
      num_mid_jobs H_at_least_two_jobs elem
  -- j_fst ≤ j_lst in sorted order
  have h_sz : 0 < (mk_sorted_jobs job_arrival job_task sched tsk t1 delta).length := by
    rw [H_at_least_two_jobs]; omega
  have h_fst_le_lst : job_arrival j_fst ≤ job_arrival j_lst := by
    by_cases h_nm : num_mid_jobs + 1 = 0
    · omega
    · have h0lt : 0 < num_mid_jobs + 1 := Nat.pos_of_ne_zero h_nm
      set sorted := mk_sorted_jobs job_arrival job_task sched tsk t1 delta
      have h_ordered : ∀ i, i < sorted.length - 1 →
        job_arrival (sorted.getD i elem) ≤ job_arrival (sorted.getD (i + 1) elem) := by
        intro i hi
        have := workload_bound_jobs_ordered_by_arrival task_cost task_period task_deadline job_arrival job_cost job_task
          job_deadline arr_seq H_jobs_have_valid_parameters sched H_jobs_come_from_arrival_sequence
          H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_sequential_jobs
          H_sporadic_tasks tsk H_valid_task_parameters H_constrained_deadline t1 delta R_tsk
          H_response_time_bound H_response_time_ge_cost H_no_deadline_miss i elem hi
        simp only [decide_eq_true_eq] at this
        exact this
      -- Use transitivity across sorted list: arr(sorted[0]) ≤ arr(sorted[num_mid_jobs+1])
      have : ∀ i j, i ≤ j → j < sorted.length →
        job_arrival (sorted.getD i elem) ≤ job_arrival (sorted.getD j elem) := by
        intro i j hij hj
        induction j with
        | zero => simp [Nat.le_zero.mp hij]
        | succ k ih =>
          rcases Nat.eq_or_lt_of_le hij with rfl | hlt
          · exact Nat.le_refl _
          · exact Nat.le_trans (ih (Nat.lt_succ_iff.mp hlt) (Nat.lt_of_succ_lt hj))
              (h_ordered k (by omega))
      exact this 0 (num_mid_jobs + 1) (Nat.zero_le _) (by rw [H_at_least_two_jobs]; omega)
  exact nat_sub_cross_eq _ _ _ _ _ h_t1_le h_lst_lt h_fst_le_lst

include H_jobs_have_valid_parameters H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_sequential_jobs H_sporadic_tasks H_valid_task_parameters H_constrained_deadline H_response_time_bound H_response_time_ge_cost H_no_deadline_miss H_at_least_two_jobs in
theorem workload_bound_service_of_middle_jobs :
    ∑ i ∈ Finset.Ico 0 num_mid_jobs,
      service_during sched
        ((mk_sorted_jobs job_arrival job_task sched tsk t1 delta).getD (i + 1) elem)
        t1 (t1 + delta) ≤
      num_mid_jobs * task_cost tsk := by
  calc ∑ i ∈ Finset.Ico 0 num_mid_jobs,
      service_during sched
        ((mk_sorted_jobs job_arrival job_task sched tsk t1 delta).getD (i + 1) elem)
        t1 (t1 + delta)
      ≤ ∑ _i ∈ Finset.Ico 0 num_mid_jobs, task_cost tsk := by
        apply Finset.sum_le_sum
        intro i hi
        rw [Finset.mem_Ico] at hi
        have h_idx : i + 1 < (mk_sorted_jobs job_arrival job_task sched tsk t1 delta).length := by
          rw [H_at_least_two_jobs]; omega
        have h_in : (mk_sorted_jobs job_arrival job_task sched tsk t1 delta).getD (i + 1) elem ∈
            mk_sorted_jobs job_arrival job_task sched tsk t1 delta := by
          rw [List.getD_eq_getElem (hn := h_idx)]
          exact List.getElem_mem h_idx
        have h_props := workload_bound_all_jobs_from_tsk task_cost task_period task_deadline job_arrival job_cost job_task
          job_deadline arr_seq H_jobs_have_valid_parameters sched H_jobs_come_from_arrival_sequence
          H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_sequential_jobs
          H_sporadic_tasks tsk H_valid_task_parameters H_constrained_deadline t1 delta R_tsk
          H_response_time_bound H_response_time_ge_cost H_no_deadline_miss _ h_in
        obtain ⟨h_arr, h_tsk, _, _⟩ := h_props
        exact cumulative_service_le_task_cost task_cost task_deadline job_cost job_deadline job_task sched
          H_completed_jobs_dont_execute tsk _ h_tsk (H_jobs_have_valid_parameters _ h_arr) t1 (t1 + delta)
    _ = num_mid_jobs * task_cost tsk := by
          rw [Finset.sum_const]
          simp [mul_comm]

include H_jobs_have_valid_parameters H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_sequential_jobs H_sporadic_tasks H_valid_task_parameters H_constrained_deadline H_response_time_bound H_response_time_ge_cost H_no_deadline_miss H_at_least_two_jobs in
theorem workload_bound_many_periods_in_between :
    let j_fst := (mk_sorted_jobs job_arrival job_task sched tsk t1 delta).getD 0 elem
    let j_lst := (mk_sorted_jobs job_arrival job_task sched tsk t1 delta).getD (num_mid_jobs + 1) elem
    job_arrival j_lst - job_arrival j_fst ≥ (num_mid_jobs + 1) * task_period tsk := by
  intro j_fst j_lst
  set sorted := mk_sorted_jobs job_arrival job_task sched tsk t1 delta with sorted_def
  -- All jobs in sorted are in arr_seq with task = tsk
  have h_all_props : ∀ j, j ∈ sorted →
      Prosa.Classic.Model.Arrival.Basic.Arrival_sequence.arrives_in arr_seq j ∧
      job_task j = tsk := by
    intro j hj
    have := workload_bound_all_jobs_from_tsk task_cost task_period task_deadline job_arrival job_cost job_task
      job_deadline arr_seq H_jobs_have_valid_parameters sched H_jobs_come_from_arrival_sequence
      H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_sequential_jobs
      H_sporadic_tasks tsk H_valid_task_parameters H_constrained_deadline t1 delta R_tsk
      H_response_time_bound H_response_time_ge_cost H_no_deadline_miss j hj
    exact ⟨this.1, this.2.1⟩
  -- Sorted list is Nodup
  have h_nodup : sorted.Nodup := by
    unfold sorted mk_sorted_jobs
    exact (List.mergeSort_perm _ _).nodup_iff.mpr
      (List.Nodup.filter _ (List.nodup_dedup _))
  -- Consecutive elements have arrival gap ≥ period
  have h_consec_gap : ∀ i, i + 1 < sorted.length →
      job_arrival (sorted.getD (i + 1) elem) ≥
      job_arrival (sorted.getD i elem) + task_period tsk := by
    intro i hi
    -- Both in sorted → arrives_in and job_task = tsk
    have h_i_lt : i < sorted.length := by omega
    have h_mem_i : sorted.getD i elem ∈ sorted := by
      rw [List.getD_eq_getElem (hn := h_i_lt)]; exact List.getElem_mem h_i_lt
    have h_mem_i1 : sorted.getD (i + 1) elem ∈ sorted := by
      rw [List.getD_eq_getElem (hn := hi)]; exact List.getElem_mem hi
    have ⟨h_arr_i, h_tsk_i⟩ := h_all_props _ h_mem_i
    have ⟨h_arr_i1, h_tsk_i1⟩ := h_all_props _ h_mem_i1
    -- They are distinct (Nodup + different indices)
    have h_ne : sorted.getD i elem ≠ sorted.getD (i + 1) elem := by
      rw [List.getD_eq_getElem (hn := h_i_lt), List.getD_eq_getElem (hn := hi)]
      exact (List.pairwise_iff_getElem.mp h_nodup) i (i + 1) h_i_lt hi (by omega)
    -- Sorted order
    have h_i_lt_pred : i < sorted.length - 1 := by rw [H_at_least_two_jobs]; omega
    have h_ord := workload_bound_jobs_ordered_by_arrival task_cost task_period task_deadline job_arrival job_cost job_task
      job_deadline arr_seq H_jobs_have_valid_parameters sched H_jobs_come_from_arrival_sequence
      H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_sequential_jobs
      H_sporadic_tasks tsk H_valid_task_parameters H_constrained_deadline t1 delta R_tsk
      H_response_time_bound H_response_time_ge_cost H_no_deadline_miss
      i elem h_i_lt_pred
    simp only [decide_eq_true_eq] at h_ord
    -- Apply sporadic task model
    have h_sporadic := H_sporadic_tasks _ _ h_ne h_arr_i h_arr_i1
      (by rw [h_tsk_i, h_tsk_i1]) h_ord
    rwa [h_tsk_i] at h_sporadic
  -- Telescope by induction: for all n, n+1 < sorted.length →
  --   arrival(sorted[n+1]) ≥ arrival(sorted[0]) + (n+1) * period
  have h_telescope : ∀ n, n + 1 ≤ sorted.length →
      job_arrival (sorted.getD n elem) ≥
      job_arrival (sorted.getD 0 elem) + n * task_period tsk := by
    intro n
    induction n with
    | zero => intro _; simp
    | succ k ih =>
      intro hk
      have hk' : k + 1 ≤ sorted.length := by omega
      have ih_val := ih hk'
      have h_gap := h_consec_gap k (by rw [H_at_least_two_jobs]; omega)
      show job_arrival (sorted.getD 0 elem) + (k + 1) * task_period tsk ≤
          job_arrival (sorted.getD (k + 1) elem)
      calc job_arrival (sorted.getD 0 elem) + (k + 1) * task_period tsk
          = (job_arrival (sorted.getD 0 elem) + k * task_period tsk) + task_period tsk := by ring
        _ ≤ job_arrival (sorted.getD k elem) + task_period tsk := Nat.add_le_add_right ih_val _
        _ ≤ job_arrival (sorted.getD (k + 1) elem) := h_gap
  -- Apply to n = num_mid_jobs + 1
  have h_final := h_telescope (num_mid_jobs + 1) (by rw [H_at_least_two_jobs])
  exact nat_le_sub_of_add_le _ _ _ h_final

include H_jobs_have_valid_parameters H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_sequential_jobs H_sporadic_tasks H_valid_task_parameters H_constrained_deadline H_response_time_bound H_response_time_ge_cost H_no_deadline_miss H_at_least_two_jobs elem in
theorem workload_bound_n_k_covers_middle_jobs :
    max_jobs task_cost task_period tsk R_tsk delta ≥ num_mid_jobs := by
  have h_period_pos := H_valid_task_parameters.2.1
  have h_cost_le_period := H_valid_task_parameters.2.2.2.2
  set sorted := mk_sorted_jobs job_arrival job_task sched tsk t1 delta
  set j_fst := sorted.getD 0 elem
  set j_lst := sorted.getD (num_mid_jobs + 1) elem
  -- Period gap bound
  have h_periods := workload_bound_many_periods_in_between
    task_cost task_period task_deadline
    job_arrival job_cost job_task job_deadline
    arr_seq H_jobs_have_valid_parameters
    sched H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute
    H_completed_jobs_dont_execute H_sequential_jobs H_sporadic_tasks
    tsk H_valid_task_parameters H_constrained_deadline
    t1 delta R_tsk
    H_response_time_bound H_response_time_ge_cost H_no_deadline_miss
    num_mid_jobs H_at_least_two_jobs elem
  -- Arrival bounds
  have h_t1_le := workload_bound_response_time_of_first_job_inside_interval
    task_cost task_period task_deadline
    job_arrival job_cost job_task job_deadline
    arr_seq H_jobs_have_valid_parameters
    sched H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute
    H_completed_jobs_dont_execute H_sequential_jobs H_sporadic_tasks
    tsk H_valid_task_parameters H_constrained_deadline
    t1 delta R_tsk
    H_response_time_bound H_response_time_ge_cost H_no_deadline_miss
    num_mid_jobs H_at_least_two_jobs elem
  have h_lst_lt := workload_bound_last_job_arrives_before_end_of_interval
    task_cost task_period task_deadline
    job_arrival job_cost job_task job_deadline
    arr_seq H_jobs_have_valid_parameters
    sched H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute
    H_completed_jobs_dont_execute H_sequential_jobs H_sporadic_tasks
    tsk H_valid_task_parameters H_constrained_deadline
    t1 delta R_tsk
    H_response_time_bound H_response_time_ge_cost H_no_deadline_miss
    num_mid_jobs H_at_least_two_jobs elem
  -- (n+1)*p ≤ arr_lst - arr_fst < delta + R_tsk
  have h_periods' : job_arrival j_lst - job_arrival j_fst ≥ (num_mid_jobs + 1) * task_period tsk := h_periods
  have h_fst_le_lst : job_arrival j_fst ≤ job_arrival j_lst := by
    by_contra h; push_neg at h
    have h0 := Nat.sub_eq_zero_of_le (le_of_lt h)
    rw [h0] at h_periods'
    exact absurd h_periods' (not_le.mpr (Nat.mul_pos (Nat.succ_pos _) h_period_pos))
  have h_gap_lt : job_arrival j_lst - job_arrival j_fst < delta + R_tsk :=
    nat_sub_lt_of_lt_add _ _ _ h_fst_le_lst
      (calc job_arrival j_lst < t1 + delta := h_lst_lt
        _ ≤ (job_arrival j_fst + R_tsk) + delta := Nat.add_le_add_right h_t1_le _
        _ = job_arrival j_fst + (delta + R_tsk) := by ring)
  have h_period_lt : (num_mid_jobs + 1) * task_period tsk < delta + R_tsk :=
    lt_of_le_of_lt h_periods' h_gap_lt
  -- num_mid_jobs ≤ max_jobs = (delta + R_tsk - cost) / period
  show num_mid_jobs ≤ max_jobs task_cost task_period tsk R_tsk delta
  unfold max_jobs div_floor
  rw [Nat.le_div_iff_mul_le h_period_pos]
  -- cost + num_mid_jobs * period ≤ period + num_mid_jobs * period = (n+1)*period ≤ delta + R_tsk
  exact nat_le_sub_of_add_le _ _ _
    (le_trans (Nat.add_le_add_right h_cost_le_period _)
      (show task_period tsk + num_mid_jobs * task_period tsk ≤ delta + R_tsk from by
        have : task_period tsk + num_mid_jobs * task_period tsk = (num_mid_jobs + 1) * task_period tsk := by ring
        rw [this]; exact le_of_lt h_period_lt))

include H_jobs_have_valid_parameters H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_sequential_jobs H_sporadic_tasks H_valid_task_parameters H_constrained_deadline H_response_time_bound H_response_time_ge_cost H_no_deadline_miss H_at_least_two_jobs in
theorem workload_bound_n_k_equals_num_mid_jobs :
    let j_fst := (mk_sorted_jobs job_arrival job_task sched tsk t1 delta).getD 0 elem
    let j_lst := (mk_sorted_jobs job_arrival job_task sched tsk t1 delta).getD (num_mid_jobs + 1) elem
    num_mid_jobs = max_jobs task_cost task_period tsk R_tsk delta →
    service_during sched j_lst t1 (t1 + delta) +
      service_during sched j_fst t1 (t1 + delta) +
      ∑ i ∈ Finset.Ico 0 num_mid_jobs,
        service_during sched
          ((mk_sorted_jobs job_arrival job_task sched tsk t1 delta).getD (i + 1) elem)
          t1 (t1 + delta) ≤
      W task_cost task_period tsk R_tsk delta := by
  intro j_fst j_lst h_nk
  unfold max_jobs div_floor at h_nk
  unfold W max_jobs div_floor
  rw [← h_nk]
  apply Nat.add_le_add
  · have h_service := workload_bound_service_of_first_and_last_jobs
      task_cost task_period task_deadline
      job_arrival job_cost job_task job_deadline
      arr_seq H_jobs_have_valid_parameters
      sched H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute
      H_completed_jobs_dont_execute H_sequential_jobs H_sporadic_tasks
      tsk H_valid_task_parameters H_constrained_deadline
      t1 delta R_tsk
      H_response_time_bound H_response_time_ge_cost H_no_deadline_miss
      num_mid_jobs H_at_least_two_jobs elem
    have h_simpl := workload_bound_simpl_expression_with_first_and_last
      task_cost task_period task_deadline
      job_arrival job_cost job_task job_deadline
      arr_seq H_jobs_have_valid_parameters
      sched H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute
      H_completed_jobs_dont_execute H_sequential_jobs H_sporadic_tasks
      tsk H_valid_task_parameters H_constrained_deadline
      t1 delta R_tsk
      H_response_time_bound H_response_time_ge_cost H_no_deadline_miss
      num_mid_jobs H_at_least_two_jobs elem
    have h_periods := workload_bound_many_periods_in_between
      task_cost task_period task_deadline
      job_arrival job_cost job_task job_deadline
      arr_seq H_jobs_have_valid_parameters
      sched H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute
      H_completed_jobs_dont_execute H_sequential_jobs H_sporadic_tasks
      tsk H_valid_task_parameters H_constrained_deadline
      t1 delta R_tsk
      H_response_time_bound H_response_time_ge_cost H_no_deadline_miss
      num_mid_jobs H_at_least_two_jobs elem
    have h_bound : service_during sched j_lst t1 (t1 + delta) +
        service_during sched j_fst t1 (t1 + delta) ≤
        delta + R_tsk - (job_arrival j_lst - job_arrival j_fst) := by
      calc service_during sched j_lst t1 (t1 + delta) +
              service_during sched j_fst t1 (t1 + delta)
          = service_during sched j_fst t1 (t1 + delta) +
              service_during sched j_lst t1 (t1 + delta) := Nat.add_comm _ _
        _ ≤ (job_arrival j_fst + R_tsk - t1) +
              (t1 + delta - job_arrival j_lst) := h_service
        _ = delta + R_tsk - (job_arrival j_lst - job_arrival j_fst) := h_simpl
    apply le_trans h_bound
    apply Nat.le_min.mpr
    constructor
    · have h_period_pos := H_valid_task_parameters.2.1
      exact nat_sub_le_swap _ _ _
        (le_trans (le_of_lt (by rw [h_nk]; exact nat_lt_div_succ_mul _ _ h_period_pos)) h_periods)
    · have h_cost_le_period := H_valid_task_parameters.2.2.2.2
      calc delta + R_tsk - (job_arrival j_lst - job_arrival j_fst)
          ≤ delta + R_tsk - (task_cost tsk + num_mid_jobs * task_period tsk) :=
            tsub_le_tsub_left (le_trans (show task_cost tsk + num_mid_jobs * task_period tsk
                ≤ (num_mid_jobs + 1) * task_period tsk from by
              calc task_cost tsk + num_mid_jobs * task_period tsk
                  ≤ task_period tsk + num_mid_jobs * task_period tsk :=
                    Nat.add_le_add_right h_cost_le_period _
                _ = (num_mid_jobs + 1) * task_period tsk := by ring) h_periods) _
        _ = delta + R_tsk - task_cost tsk - num_mid_jobs * task_period tsk :=
            (Nat.sub_sub _ _ _).symm
  · exact workload_bound_service_of_middle_jobs
      task_cost task_period task_deadline
      job_arrival job_cost job_task job_deadline
      arr_seq H_jobs_have_valid_parameters
      sched H_jobs_come_from_arrival_sequence
      H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_sequential_jobs H_sporadic_tasks
      tsk H_valid_task_parameters H_constrained_deadline
      t1 delta R_tsk H_response_time_bound H_response_time_ge_cost H_no_deadline_miss
      num_mid_jobs H_at_least_two_jobs elem

include H_jobs_have_valid_parameters H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_sequential_jobs H_sporadic_tasks H_valid_task_parameters H_constrained_deadline H_response_time_bound H_response_time_ge_cost H_no_deadline_miss H_at_least_two_jobs in
theorem workload_bound_n_k_equals_num_mid_jobs_plus_1 :
    let j_fst := (mk_sorted_jobs job_arrival job_task sched tsk t1 delta).getD 0 elem
    let j_lst := (mk_sorted_jobs job_arrival job_task sched tsk t1 delta).getD (num_mid_jobs + 1) elem
    num_mid_jobs + 1 = max_jobs task_cost task_period tsk R_tsk delta →
    service_during sched j_lst t1 (t1 + delta) +
      service_during sched j_fst t1 (t1 + delta) +
      ∑ i ∈ Finset.Ico 0 num_mid_jobs,
        service_during sched
          ((mk_sorted_jobs job_arrival job_task sched tsk t1 delta).getD (i + 1) elem)
          t1 (t1 + delta) ≤
      W task_cost task_period tsk R_tsk delta := by
  intro j_fst j_lst h_nk
  unfold max_jobs div_floor at h_nk
  dsimp only [W, max_jobs, div_floor]
  rw [← h_nk]
  rw [show (num_mid_jobs + 1) * task_cost tsk =
    task_cost tsk + num_mid_jobs * task_cost tsk from by ring,
    ← Nat.add_assoc, ← min_add_add_right (task_cost tsk)]
  -- Simplify X + e = d+R-(nm+1)*p  (since e + (nm+1)*p ≤ d+R)
  have h_nk_mul_le : (num_mid_jobs + 1) * task_period tsk ≤
      delta + R_tsk - task_cost tsk := by
    rw [h_nk]; exact Nat.div_mul_le_self _ _
  have h_e_le_dR : task_cost tsk ≤ delta + R_tsk :=
    le_trans H_response_time_ge_cost (Nat.le_add_left _ _)
  have h_ep_le : task_cost tsk + (num_mid_jobs + 1) * task_period tsk ≤ delta + R_tsk := by
    calc task_cost tsk + (num_mid_jobs + 1) * task_period tsk
        ≤ task_cost tsk + (delta + R_tsk - task_cost tsk) :=
          Nat.add_le_add_left h_nk_mul_le _
      _ = delta + R_tsk := Nat.add_sub_cancel' h_e_le_dR
  conv_rhs =>
    arg 1; arg 2
    rw [nat_sub_sub_add_cancel _ _ _ h_ep_le]
  -- Goal: LHS ≤ min(e + e, d+R-(nm+1)*p) + nm*e
  apply Nat.add_le_add
  · -- service_lst + service_fst ≤ min(2*e, d+R-(nm+1)*p)
    have h_sz_fst : 0 < (mk_sorted_jobs job_arrival job_task sched tsk t1 delta).length := by
      rw [H_at_least_two_jobs]; omega
    have h_fst_mem : j_fst ∈ mk_sorted_jobs job_arrival job_task sched tsk t1 delta := by
      unfold j_fst; rw [List.getD_eq_getElem (hn := h_sz_fst)]
      exact List.getElem_mem h_sz_fst
    have h_fst_props := workload_bound_all_jobs_from_tsk task_cost task_period task_deadline job_arrival job_cost job_task
      job_deadline arr_seq H_jobs_have_valid_parameters sched H_jobs_come_from_arrival_sequence
      H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_sequential_jobs
      H_sporadic_tasks tsk H_valid_task_parameters H_constrained_deadline t1 delta R_tsk
      H_response_time_bound H_response_time_ge_cost H_no_deadline_miss j_fst h_fst_mem
    have h_sz_lst : num_mid_jobs + 1 < (mk_sorted_jobs job_arrival job_task sched tsk t1 delta).length := by
      rw [H_at_least_two_jobs]; omega
    have h_lst_mem : j_lst ∈ mk_sorted_jobs job_arrival job_task sched tsk t1 delta := by
      unfold j_lst; rw [List.getD_eq_getElem (hn := h_sz_lst)]
      exact List.getElem_mem h_sz_lst
    have h_lst_props := workload_bound_all_jobs_from_tsk task_cost task_period task_deadline job_arrival job_cost job_task
      job_deadline arr_seq H_jobs_have_valid_parameters sched H_jobs_come_from_arrival_sequence
      H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_sequential_jobs
      H_sporadic_tasks tsk H_valid_task_parameters H_constrained_deadline t1 delta R_tsk
      H_response_time_bound H_response_time_ge_cost H_no_deadline_miss j_lst h_lst_mem
    have h_fst_le : service_during sched j_fst t1 (t1 + delta) ≤ task_cost tsk :=
      cumulative_service_le_task_cost task_cost task_deadline job_cost job_deadline job_task sched
        H_completed_jobs_dont_execute tsk j_fst h_fst_props.2.1
        (H_jobs_have_valid_parameters _ h_fst_props.1) t1 (t1 + delta)
    have h_lst_le : service_during sched j_lst t1 (t1 + delta) ≤ task_cost tsk :=
      cumulative_service_le_task_cost task_cost task_deadline job_cost job_deadline job_task sched
        H_completed_jobs_dont_execute tsk j_lst h_lst_props.2.1
        (H_jobs_have_valid_parameters _ h_lst_props.1) t1 (t1 + delta)
    have h_service := workload_bound_service_of_first_and_last_jobs
      task_cost task_period task_deadline
      job_arrival job_cost job_task job_deadline
      arr_seq H_jobs_have_valid_parameters
      sched H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute
      H_completed_jobs_dont_execute H_sequential_jobs H_sporadic_tasks
      tsk H_valid_task_parameters H_constrained_deadline
      t1 delta R_tsk
      H_response_time_bound H_response_time_ge_cost H_no_deadline_miss
      num_mid_jobs H_at_least_two_jobs elem
    have h_simpl := workload_bound_simpl_expression_with_first_and_last
      task_cost task_period task_deadline
      job_arrival job_cost job_task job_deadline
      arr_seq H_jobs_have_valid_parameters
      sched H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute
      H_completed_jobs_dont_execute H_sequential_jobs H_sporadic_tasks
      tsk H_valid_task_parameters H_constrained_deadline
      t1 delta R_tsk
      H_response_time_bound H_response_time_ge_cost H_no_deadline_miss
      num_mid_jobs H_at_least_two_jobs elem
    have h_periods := workload_bound_many_periods_in_between
      task_cost task_period task_deadline
      job_arrival job_cost job_task job_deadline
      arr_seq H_jobs_have_valid_parameters
      sched H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute
      H_completed_jobs_dont_execute H_sequential_jobs H_sporadic_tasks
      tsk H_valid_task_parameters H_constrained_deadline
      t1 delta R_tsk
      H_response_time_bound H_response_time_ge_cost H_no_deadline_miss
      num_mid_jobs H_at_least_two_jobs elem
    apply Nat.le_min.mpr
    constructor
    · exact Nat.add_le_add h_lst_le h_fst_le
    · calc service_during sched j_lst t1 (t1 + delta) +
              service_during sched j_fst t1 (t1 + delta)
          = service_during sched j_fst t1 (t1 + delta) +
              service_during sched j_lst t1 (t1 + delta) := Nat.add_comm _ _
        _ ≤ (job_arrival j_fst + R_tsk - t1) +
              (t1 + delta - job_arrival j_lst) := h_service
        _ = delta + R_tsk - (job_arrival j_lst - job_arrival j_fst) := h_simpl
        _ ≤ delta + R_tsk - (num_mid_jobs + 1) * task_period tsk :=
            tsub_le_tsub_left h_periods _
  · exact workload_bound_service_of_middle_jobs
      task_cost task_period task_deadline
      job_arrival job_cost job_task job_deadline
      arr_seq H_jobs_have_valid_parameters
      sched H_jobs_come_from_arrival_sequence
      H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_sequential_jobs H_sporadic_tasks
      tsk H_valid_task_parameters H_constrained_deadline
      t1 delta R_tsk H_response_time_bound H_response_time_ge_cost H_no_deadline_miss
      num_mid_jobs H_at_least_two_jobs elem

end WorkloadTwoOrMoreJobs

include H_jobs_have_valid_parameters H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_sequential_jobs H_sporadic_tasks H_valid_task_parameters H_constrained_deadline H_response_time_bound H_response_time_ge_cost H_no_deadline_miss in
theorem workload_bounded_by_W :
    workload job_task sched tsk t1 (t1 + delta) ≤
      W task_cost task_period tsk R_tsk delta := by
  rw [workload_eq_workload_joblist]
  rw [workload_bound_simpl_by_sorting_scheduled_jobs task_cost task_period task_deadline job_arrival job_cost job_task
    job_deadline arr_seq H_jobs_have_valid_parameters sched H_jobs_come_from_arrival_sequence
    H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_sequential_jobs H_sporadic_tasks
    tsk H_valid_task_parameters H_constrained_deadline t1 delta R_tsk
    H_response_time_bound H_response_time_ge_cost H_no_deadline_miss]
  set sorted := mk_sorted_jobs job_arrival job_task sched tsk t1 delta with sorted_def
  set f := fun i => service_during sched i t1 (t1 + delta)
  by_cases h_le : sorted.length ≤ max_jobs task_cost task_period tsk R_tsk delta
  · exact workload_bound_holds_for_at_most_n_k_jobs
      task_cost task_period task_deadline job_arrival job_cost job_task job_deadline
      arr_seq H_jobs_have_valid_parameters sched H_jobs_come_from_arrival_sequence
      H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_sequential_jobs H_sporadic_tasks
      tsk H_valid_task_parameters H_constrained_deadline
      t1 delta R_tsk H_response_time_bound H_response_time_ge_cost H_no_deadline_miss h_le
  · push_neg at h_le
    have h_pos : 0 < sorted.length := by omega
    have h_nonempty : sorted ≠ [] := by intro h; simp [h] at h_pos
    obtain ⟨elem, _⟩ := List.exists_mem_of_ne_nil sorted h_nonempty
    by_cases h_one : sorted.length = 1
    · -- Single job case
      have h_eq : (sorted.map f).sum = ∑ i ∈ Finset.Ico 0 1,
          f (sorted.getD i elem) := by
        have : (sorted.map f).sum = ∑ i ∈ Finset.range sorted.length, f (sorted.getD i elem) := by
          induction sorted with
          | nil => simp
          | cons hd tl ih =>
            simp only [List.map_cons, List.sum_cons, List.length_cons, Finset.sum_range_succ',
              List.getD_cons_zero, List.getD_cons_succ]
            omega
        rw [this, h_one, congr_fun Finset.range_eq_Ico]
      rw [h_eq]
      exact workload_bound_holds_for_a_single_job
        task_cost task_period task_deadline job_arrival job_cost job_task job_deadline
        arr_seq H_jobs_have_valid_parameters sched H_jobs_come_from_arrival_sequence
        H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_sequential_jobs H_sporadic_tasks
        tsk H_valid_task_parameters H_constrained_deadline
        t1 delta R_tsk H_response_time_bound H_response_time_ge_cost H_no_deadline_miss
        (by omega : sorted.length > 0) elem
    · -- At least two jobs
      have h_ge2 : sorted.length ≥ 2 := by omega
      set num_mid_jobs := sorted.length - 2
      have H_at_least_two : sorted.length = num_mid_jobs + 2 := by omega
      rw [list_map_sum_decomp' sorted f elem num_mid_jobs H_at_least_two]
      have h_nk_ge := workload_bound_n_k_covers_middle_jobs
        task_cost task_period task_deadline job_arrival job_cost job_task job_deadline
        arr_seq H_jobs_have_valid_parameters sched H_jobs_come_from_arrival_sequence
        H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_sequential_jobs H_sporadic_tasks
        tsk H_valid_task_parameters H_constrained_deadline
        t1 delta R_tsk H_response_time_bound H_response_time_ge_cost H_no_deadline_miss
        num_mid_jobs H_at_least_two elem
      have h_nk_lt : max_jobs task_cost task_period tsk R_tsk delta < num_mid_jobs + 2 := by
        rw [← H_at_least_two]; exact h_le
      rcases Nat.eq_or_lt_of_le h_nk_ge with h_eq | h_lt
      · exact workload_bound_n_k_equals_num_mid_jobs
          task_cost task_period task_deadline job_arrival job_cost job_task job_deadline
          arr_seq H_jobs_have_valid_parameters sched H_jobs_come_from_arrival_sequence
          H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_sequential_jobs H_sporadic_tasks
          tsk H_valid_task_parameters H_constrained_deadline
          t1 delta R_tsk H_response_time_bound H_response_time_ge_cost H_no_deadline_miss
          num_mid_jobs H_at_least_two elem h_eq
      · have h_nk_eq : num_mid_jobs + 1 = max_jobs task_cost task_period tsk R_tsk delta := by omega
        exact workload_bound_n_k_equals_num_mid_jobs_plus_1
          task_cost task_period task_deadline job_arrival job_cost job_task job_deadline
          arr_seq H_jobs_have_valid_parameters sched H_jobs_come_from_arrival_sequence
          H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_sequential_jobs H_sporadic_tasks
          tsk H_valid_task_parameters H_constrained_deadline
          t1 delta R_tsk H_response_time_bound H_response_time_ge_cost H_no_deadline_miss
          num_mid_jobs H_at_least_two elem h_nk_eq

end MainProof

end ProofWorkloadBound

end WorkloadBound

end Prosa.Classic.Analysis.Global.Basic.Workload_bound
