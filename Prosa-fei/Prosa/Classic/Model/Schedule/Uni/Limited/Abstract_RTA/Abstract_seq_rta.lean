-- Translated from: ../rt-proofs/classic/model/schedule/uni/limited/abstract_RTA/abstract_seq_rta.v
import Prosa.Classic.Util.All
import Prosa.Classic.Model.Arrival.Basic.Job
import Prosa.Classic.Model.Arrival.Basic.Task_arrival
import Prosa.Classic.Model.Schedule.Uni.Service
import Prosa.Classic.Model.Schedule.Uni.Workload
import Prosa.Classic.Model.Schedule.Uni.Schedule
import Prosa.Classic.Model.Schedule.Uni.Response_time
import Prosa.Classic.Model.Schedule.Uni.Schedule_of_task
import Prosa.Classic.Model.Schedule.Uni.Limited.Rbf
import Prosa.Classic.Model.Schedule.Uni.Limited.Schedule
import Prosa.Classic.Model.Arrival.Curves.Bounds
import Prosa.Classic.Analysis.Uni.Arrival_curves.Workload_bound
import Prosa.Classic.Model.Schedule.Uni.Limited.Abstract_RTA.Definitions
import Prosa.Classic.Model.Schedule.Uni.Limited.Abstract_RTA.Sufficient_condition_for_lock_in_service
import Prosa.Classic.Model.Schedule.Uni.Limited.Abstract_RTA.Reduction_of_search_space
import Prosa.Classic.Model.Schedule.Uni.Limited.Abstract_RTA.Abstract_rta
import Mathlib.Tactic

namespace Prosa.Classic.Model.Schedule.Uni.Limited.Abstract_RTA.Abstract_seq_rta

open Prosa.Classic.Model.Time
open Prosa.Classic.Model.Arrival.Basic.Job
open Prosa.Classic.Model.Arrival.Basic.Arrival_sequence
open Prosa.Classic.Model.Arrival.Basic.Task_arrival
open Prosa.Classic.Model.Arrival.Curves.Bounds.ArrivalCurves
open Prosa.Classic.Model.Schedule.Uni.Schedule
open Prosa.Classic.Model.Schedule.Uni.Service
open Prosa.Classic.Model.Schedule.Uni.Workload
open Prosa.Classic.Model.Schedule.Uni.Response_time.ResponseTime
open Prosa.Classic.Model.Schedule.Uni.Schedule_of_task
open Prosa.Classic.Model.Schedule.Uni.Limited.Schedule
open Prosa.Classic.Model.Schedule.Uni.Limited.Rbf.RBF
open Prosa.Classic.Analysis.Uni.Arrival_curves.Workload_bound.MaxArrivalsWorkloadBound
open Prosa.Classic.Model.Schedule.Uni.Limited.Abstract_RTA.Definitions
open Prosa.Classic.Model.Schedule.Uni.Limited.Abstract_RTA.Sufficient_condition_for_lock_in_service
open Prosa.Classic.Model.Schedule.Uni.Limited.Abstract_RTA.Reduction_of_search_space.AbstractRTAReduction
open Prosa.Classic.Model.Schedule.Uni.Limited.Abstract_RTA.Abstract_rta.AbstractRTA
open Prosa.Util.Epsilon

namespace AbstractSeqRTA

section Sequential_Abstract_RTA

variable {Task : Type _} [DecidableEq Task]
variable (task_cost : Task → Time)

variable {Job : Type _} [DecidableEq Job]
variable (job_arrival : Job → Time)
variable (job_cost : Job → Time)
variable (job_task : Job → Task)

variable (arr_seq : arrival_sequence Job)
variable (H_arrival_times_are_consistent : arrival_times_are_consistent job_arrival arr_seq)
variable (H_arr_seq_is_a_set : arrival_sequence_is_a_set arr_seq)

variable (sched : schedule Job)
variable (H_jobs_come_from_arrival_sequence : jobs_come_from_arrival_sequence sched arr_seq)

variable (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute job_arrival sched)
variable (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched)

variable (H_job_cost_le_task_cost :
  cost_of_jobs_from_arrival_sequence_le_task_cost task_cost job_cost job_task arr_seq)

variable (ts : List Task)

variable (H_all_jobs_from_taskset :
  ∀ j, arrives_in arr_seq j → job_task j ∈ ts)

variable (max_arrivals : Task → Time → Nat)
variable (H_family_of_proper_arrival_curves :
  family_of_proper_arrival_curves job_task arr_seq max_arrivals ts)

variable (tsk : Task)
variable (H_tsk_in_ts : tsk ∈ ts)

variable (job_lock_in_service : Job → Time)
variable (task_lock_in_service : Task → Time)

variable (H_proper_job_lock_in_service :
  proper_job_lock_in_service job_cost arr_seq sched job_lock_in_service)

variable (H_proper_task_lock_in_service :
  proper_task_lock_in_service task_cost job_task arr_seq job_lock_in_service task_lock_in_service tsk)

variable (interference : Job → Time → Bool)
variable (interfering_workload : Job → Time → Time)

def interference_and_workload_consistent_with_sequential_jobs : Prop :=
  ∀ j t1 t2,
    arrives_in arr_seq j →
    job_task j = tsk →
    job_cost j > 0 →
    busy_interval job_arrival job_cost sched interference interfering_workload j t1 t2 →
    task_workload_between job_cost job_task arr_seq tsk 0 t1 =
    task_service_between job_task arr_seq sched tsk 0 t1

def task_interference_received_before (tsk' : Task) (upper_bound : Time) (t : Time) : Bool :=
  (!(task_scheduled_at job_task sched tsk' t)) &&
    ((arrivals_of_task_before job_task arr_seq tsk' upper_bound).any
      (fun j => interference j t))

noncomputable def cumul_task_interference (job_task : Job → Task) (sched : schedule Job)
    (arr_seq : arrival_sequence Job) (interference : Job → Time → Bool)
    (tsk' : Task) (upper_bound : Time) (t1 t2 : Time) : Nat :=
  ∑ t ∈ Finset.Ico t1 t2,
    ((!(task_scheduled_at job_task sched tsk' t)) &&
      ((arrivals_of_task_before job_task arr_seq tsk' upper_bound).any
        (fun j => interference j t))).toNat

def task_interference_is_bounded_by
    (task_interference_bound_function : Task → Time → Time → Time) : Prop :=
  ∀ j R t1 t2,
    arrives_in arr_seq j →
    job_task j = tsk →
    t1 + R < t2 →
    ¬ completed_by job_cost sched j (t1 + R) →
    busy_interval job_arrival job_cost sched interference interfering_workload j t1 t2 →
    let offset := job_arrival j - t1
    cumul_task_interference job_task sched arr_seq interference tsk t2 t1 (t1 + R) ≤
      task_interference_bound_function tsk offset R

variable (H_work_conserving :
  work_conserving job_arrival job_cost job_task arr_seq sched tsk interference interfering_workload)

variable (H_sequential_jobs : sequential_jobs job_arrival job_cost sched job_task)
variable (H_interference_and_workload_consistent_with_sequential_jobs :
  ∀ j t1 t2,
    arrives_in arr_seq j →
    job_task j = tsk →
    job_cost j > 0 →
    busy_interval job_arrival job_cost sched interference interfering_workload j t1 t2 →
    task_workload_between job_cost job_task arr_seq tsk 0 t1 =
    task_service_between job_task arr_seq sched tsk 0 t1)

variable (L : Time)
variable (H_busy_interval_exists :
  busy_intervals_are_bounded_by job_arrival job_cost job_task arr_seq sched tsk
    interference interfering_workload L)

variable (task_interference_bound_function : Task → Time → Time → Time)
variable (H_task_interference_is_bounded :
  ∀ j R t1 t2,
    arrives_in arr_seq j →
    job_task j = tsk →
    t1 + R < t2 →
    ¬ completed_by job_cost sched j (t1 + R) →
    busy_interval job_arrival job_cost sched interference interfering_workload j t1 t2 →
    let offset := job_arrival j - t1
    cumul_task_interference job_task sched arr_seq interference tsk t2 t1 (t1 + R) ≤
      task_interference_bound_function tsk offset R)

variable (R : Nat)
variable (H_R_is_maximum_seq :
  ∀ A,
    is_in_search_space tsk L
      (fun tsk' A' Δ =>
        task_request_bound_function task_cost max_arrivals tsk' (A' + ε) -
          task_cost tsk' + task_interference_bound_function tsk' A' Δ) A →
    ∃ F,
      A + F = (task_request_bound_function task_cost max_arrivals tsk (A + ε) -
        (task_cost tsk - task_lock_in_service tsk)) +
        task_interference_bound_function tsk A (A + F) ∧
      F + (task_cost tsk - task_lock_in_service tsk) ≤ R)

include H_interference_and_workload_consistent_with_sequential_jobs
  H_arrival_times_are_consistent H_arr_seq_is_a_set
  H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute in
theorem completed_before_beginning_of_busy_interval
    (j1 j2 : Job)
    (H_j1_arrives : arrives_in arr_seq j1)
    (H_j2_arrives : arrives_in arr_seq j2)
    (H_j1_from_tsk : job_task j1 = tsk)
    (H_j2_from_tsk : job_task j2 = tsk)
    (H_j1_cost_positive : job_cost_positive job_cost j1)
    (t1 t2 : Time)
    (H_busy_interval :
      busy_interval job_arrival job_cost sched interference interfering_workload j1 t1 t2) :
    job_arrival j2 < t1 →
    completed_by job_cost sched j2 t1 := by
  intro hJA
  by_cases hZERO : job_cost j2 = 0
  · simp only [completed_by, Time] at *; omega
  · have SWEQ := H_interference_and_workload_consistent_with_sequential_jobs
      j1 t1 t2 H_j1_arrives H_j1_from_tsk H_j1_cost_positive H_busy_interval
    -- Use all_jobs_have_completed_equiv_workload_eq_service backward
    have h_all_compl := (Prosa.Classic.Model.Schedule.Uni.Service.all_jobs_have_completed_equiv_workload_eq_service
      job_arrival job_cost arr_seq H_arrival_times_are_consistent sched
      H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute
      (fun j => decide (job_task j = tsk)) 0 t1 t1).mpr SWEQ
    apply h_all_compl
    · exact arrived_between_implies_in_arrivals job_arrival arr_seq
        H_arrival_times_are_consistent j2 0 t1 H_j2_arrives
        ⟨Nat.zero_le _, hJA⟩
    · simp [H_j2_from_tsk]

include H_sequential_jobs H_interference_and_workload_consistent_with_sequential_jobs
  H_arrival_times_are_consistent H_arr_seq_is_a_set
  H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute in
theorem arrives_after_beginning_of_busy_interval
    (j1 j2 : Job)
    (H_j1_arrives : arrives_in arr_seq j1)
    (H_j2_arrives : arrives_in arr_seq j2)
    (H_j1_from_tsk : job_task j1 = tsk)
    (H_j2_from_tsk : job_task j2 = tsk)
    (H_j1_cost_positive : job_cost_positive job_cost j1)
    (t1 t2 : Time)
    (H_busy_interval :
      busy_interval job_arrival job_cost sched interference interfering_workload j1 t1 t2) :
    ∀ t,
      t1 ≤ t →
      pending job_arrival job_cost sched j2 t →
      arrived_between job_arrival j2 t1 (t + 1) := by
  intro t hGE hPEND
  constructor
  · -- t1 ≤ job_arrival j2: by contradiction
    by_contra hLT
    push_neg at hLT
    -- j2 arrived before t1, so completed before t1
    have hCOMPL := completed_before_beginning_of_busy_interval job_arrival job_cost job_task
      arr_seq H_arrival_times_are_consistent H_arr_seq_is_a_set sched H_jobs_must_arrive_to_execute
      H_completed_jobs_dont_execute tsk interference interfering_workload
      H_interference_and_workload_consistent_with_sequential_jobs
      j1 j2 H_j1_arrives H_j2_arrives H_j1_from_tsk H_j2_from_tsk H_j1_cost_positive
      t1 t2 H_busy_interval hLT
    -- completed at t1, so completed at t (since t1 ≤ t)
    have hCOMPL_t := completion_monotonic job_cost sched j2 t1 t hGE hCOMPL
    -- But pending at t means not completed
    obtain ⟨_, hNC⟩ := hPEND
    exact hNC hCOMPL_t
  · -- job_arrival j2 < t + 1: from pending → arrived
    obtain ⟨hARR, _⟩ := hPEND
    simp only [has_arrived, Time] at *
    omega

include H_work_conserving H_sequential_jobs
  H_interference_and_workload_consistent_with_sequential_jobs
  H_arrival_times_are_consistent H_arr_seq_is_a_set
  H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute in
theorem bound_for_cumulative_job_interference_actual
    (j : Job)
    (H_j_arrives : arrives_in arr_seq j)
    (H_job_of_tsk : job_task j = tsk)
    (H_job_cost_positive : job_cost_positive job_cost j)
    (t1 t2 : Time)
    (H_busy_interval_j :
      busy_interval job_arrival job_cost sched interference interfering_workload j t1 t2)
    (x : Time)
    (H_inside_busy_interval : t1 + x < t2)
    (H_job_j_is_not_completed : ¬ completed_by job_cost sched j (t1 + x)) :
    cumul_interference interference j t1 (t1 + x) ≤
    (task_workload_between job_cost job_task arr_seq tsk t1
      (t1 + (job_arrival j - t1) + ε) - job_cost j) +
    cumul_task_interference job_task sched arr_seq interference tsk t2 t1 (t1 + x) := by
  set y := t1 + x with hy_def
  set A := job_arrival j - t1 with hA_def
  have hBI := H_busy_interval_j
  have hT1_LE_ARR := hBI.1.1
  -- j ∈ arrivals_between t1 (t1 + A + ε)
  have hIN : j ∈ jobs_arrived_between arr_seq t1 (t1 + A + ε) :=
    arrived_between_implies_in_arrivals job_arrival arr_seq H_arrival_times_are_consistent
      j t1 (t1 + A + ε) H_j_arrives ⟨hT1_LE_ARR, by simp only [hA_def, ε, Time]; omega⟩
  -- Fact1: task_service_of_jobs - service_during j ≤ task_workload - job_cost j
  have hFact1 : task_service_of_jobs_received_in job_task arr_seq sched tsk t1 (t1 + A + ε) t1 y
      - service_during sched j t1 y ≤
      task_workload_between job_cost job_task arr_seq tsk t1 (t1 + A + ε) - job_cost j := by
    -- service of each job ≤ cost of that job, so total service ≤ total workload
    -- Removing j from both: (Σ service) - service_j ≤ (Σ cost) - cost_j
    unfold task_service_of_jobs_received_in task_workload_between task_workload workload_of_jobs
    unfold service_of_jobs
    -- j ∈ the filtered list, so we can split: big_rem j
    set filt := (jobs_arrived_between arr_seq t1 (t1 + A + ε)).filter
      (fun j' => decide (job_task j' = tsk)) with hfilt_def
    have hj_filt : j ∈ filt := by
      rw [hfilt_def, List.mem_filter]
      exact ⟨hIN, by simp [H_job_of_tsk]⟩
    have hperm := List.perm_cons_erase hj_filt
    have hS := (hperm.map (fun j' => service_during sched j' t1 y)).sum_eq
    simp only [List.map_cons, List.sum_cons] at hS
    have hW := (hperm.map job_cost).sum_eq
    simp only [List.map_cons, List.sum_cons] at hW
    rw [hS, hW]
    have hrest : ((filt.erase j).map (fun j' => service_during sched j' t1 y)).sum ≤
        ((filt.erase j).map job_cost).sum := by
      suffices h : ∀ l : List Job,
          (l.map (fun j' => service_during sched j' t1 y)).sum ≤ (l.map job_cost).sum by exact h _
      intro l; induction l with
      | nil => simp
      | cons hd tl ih =>
        simp only [List.map_cons, List.sum_cons]
        exact Nat.add_le_add
          (cumulative_service_le_job_cost job_cost sched hd H_completed_jobs_dont_execute t1 y) ih
    omega
  -- Main inequality via per-timestep analysis
  apply le_trans _ (Nat.add_le_add_right hFact1 _)
  -- cumul_interference ≤ task_service - service_j + cumul_task_interference
  -- This follows from exchanging sums and per-timestep case analysis on sched(t)
  -- Exchange helper: list of Finset sums = Finset sum of list sums
  have h_lfse : ∀ (l : List Job),
      (l.map (fun j' => ∑ t' ∈ Finset.Ico t1 y, service_at sched j' t')).sum =
      ∑ t' ∈ Finset.Ico t1 y, (l.map (fun j' => service_at sched j' t')).sum := by
    intro l; induction l with
    | nil => simp
    | cons a l ih =>
      simp only [List.map_cons, List.sum_cons, ih, ← Finset.sum_add_distrib]
  set filt2 := (jobs_arrived_between arr_seq t1 (t1 + A + ε)).filter
    (fun j' => decide (job_task j' = tsk)) with hfilt2_def
  have hj_filt2 : j ∈ filt2 := by
    rw [hfilt2_def, List.mem_filter]
    exact ⟨hIN, by simp [H_job_of_tsk]⟩
  -- TSJ = Σ_t (filt2.map service_at).sum
  have h_tsj_eq : task_service_of_jobs_received_in job_task arr_seq sched tsk t1 (t1 + A + ε) t1 y =
      ∑ t' ∈ Finset.Ico t1 y, (filt2.map (fun j' => service_at sched j' t')).sum := by
    unfold task_service_of_jobs_received_in service_of_jobs service_during
    exact h_lfse filt2
  -- j ∈ arrivals_of_task_before tsk t2
  have hARR_LT_T2 : job_arrival j < t2 := hBI.1.2.1
  have hj_task_before : j ∈ arrivals_of_task_before job_task arr_seq tsk t2 := by
    unfold arrivals_of_task_before arrivals_of_task_between
    rw [List.mem_filter]
    exact ⟨arrived_between_implies_in_arrivals job_arrival arr_seq H_arrival_times_are_consistent
      j 0 t2 H_j_arrives ⟨Nat.zero_le _, hARR_LT_T2⟩,
      by simp [is_job_of_task, H_job_of_tsk]⟩
  -- CI + SD ≤ TSJ + CTI (by per-timestep case analysis)
  have h_sum : cumul_interference interference j t1 y + service_during sched j t1 y ≤
      task_service_of_jobs_received_in job_task arr_seq sched tsk t1 (t1 + A + ε) t1 y +
      cumul_task_interference job_task sched arr_seq interference tsk t2 t1 y := by
    rw [h_tsj_eq]
    unfold cumul_interference service_during cumul_task_interference
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro t ht
    have ht_bounds : t1 ≤ t ∧ t < y := Finset.mem_Ico.mp ht
    have ht_in_bi : t1 ≤ t ∧ t < t2 :=
      ⟨ht_bounds.1, lt_trans ht_bounds.2 H_inside_busy_interval⟩
    have h_wc := H_work_conserving j t1 t2 t H_j_arrives H_job_of_tsk H_job_cost_positive
      H_busy_interval_j ht_in_bi
    match h_sched : sched t with
    | none =>
      -- service_at = 0 for everyone since no one scheduled
      have h_not_sched : scheduled_at sched j t = false := by simp [scheduled_at, h_sched]
      have h_int : interference j t = true := by
        by_contra h; exact absurd (h_wc.1 h) (by simp [h_not_sched])
      have h_sum0 : (filt2.map (fun j' => service_at sched j' t)).sum = 0 := by
        apply List.sum_eq_zero; intro n hn; rw [List.mem_map] at hn
        obtain ⟨j', _, rfl⟩ := hn; simp [service_at, scheduled_at, h_sched]
      simp only [service_at, scheduled_at, h_sched, h_int, Bool.toNat_true, Bool.toNat_false,
        Nat.add_zero, h_sum0, Nat.zero_add]
      simp only [task_scheduled_at, h_sched, Bool.not_false, Bool.true_and]
      have h_any := List.any_of_mem (p := fun j' => interference j' t) hj_task_before h_int
      simp [h_any]
    | some s =>
      by_cases h_tsk_s : job_task s = tsk
      · by_cases h_eq : j = s
        · -- sched t = some j (j is scheduled)
          subst h_eq
          have h_sched_j : scheduled_at sched j t = true := by simp [scheduled_at, h_sched]
          have h_int_false := h_wc.2 h_sched_j
          have h_int_eq : interference j t = false := by
            by_contra h; push_neg at h
            exact h_int_false (by cases interference j t <;> simp_all)
          simp only [service_at, scheduled_at, h_sched, h_int_eq, Bool.toNat_false,
            Nat.zero_add, Bool.toNat_true, beq_self_eq_true]
          exact le_trans (Nat.le_refl 1) (le_trans
            (List.le_sum_of_mem (List.mem_map.mpr ⟨j, hj_filt2,
              by simp [service_at, scheduled_at, h_sched]⟩))
            (Nat.le_add_right _ _))
        · -- sched t = some s, s ≠ j, task s = tsk
          have h_not_sched : scheduled_at sched j t = false := by
            simp [scheduled_at, h_sched, show s ≠ j from Ne.symm h_eq]
          have h_int : interference j t = true := by
            by_contra h; exact absurd (h_wc.1 h) (by simp [h_not_sched])
          have h_sa_j : service_at sched j t = 0 := by simp [service_at, h_not_sched]
          simp only [h_sa_j, h_int, Bool.toNat_true, Nat.add_zero]
          -- s arrives and is pending at t
          have h_s_sched : scheduled_at sched s t = true := by simp [scheduled_at, h_sched]
          have h_s_arrives : arrives_in arr_seq s :=
            H_jobs_come_from_arrival_sequence s t h_s_sched
          have h_s_pending : pending job_arrival job_cost sched s t :=
            scheduled_implies_pending job_arrival job_cost sched
              H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute s t h_s_sched
          -- s arrives in [t1, t+1)
          have h_s_arr_between := arrives_after_beginning_of_busy_interval job_arrival job_cost
            job_task arr_seq H_arrival_times_are_consistent H_arr_seq_is_a_set sched
            H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute
            tsk interference interfering_workload
            H_sequential_jobs H_interference_and_workload_consistent_with_sequential_jobs
            j s H_j_arrives h_s_arrives H_job_of_tsk h_tsk_s H_job_cost_positive
            t1 t2 H_busy_interval_j t ht_bounds.1 h_s_pending
          -- job_arrival s ≤ job_arrival j (by sequential_jobs + contradiction)
          have h_arr_le : job_arrival s ≤ job_arrival j := by
            by_contra h_gt; push_neg at h_gt
            exact H_job_j_is_not_completed
              (completion_monotonic job_cost sched j t y (Nat.le_of_lt ht_bounds.2)
                (H_sequential_jobs j s t (by rw [H_job_of_tsk, h_tsk_s]) h_gt h_s_sched))
          -- s ∈ filt2
          have h_s_in_filt2 : s ∈ filt2 := by
            rw [hfilt2_def, List.mem_filter]
            constructor
            · apply arrived_between_implies_in_arrivals job_arrival arr_seq
                H_arrival_times_are_consistent s t1 (t1 + A + ε) h_s_arrives
              exact ⟨h_s_arr_between.1, by
                have := h_arr_le; have := hT1_LE_ARR
                simp only [hA_def, ε, Time] at *; omega⟩
            · simp [h_tsk_s]
          -- sum ≥ 1 (from s's contribution)
          exact le_trans
            (le_trans (show 1 ≤ service_at sched s t from by simp [service_at, scheduled_at, h_sched])
              (List.le_sum_of_mem (List.mem_map.mpr ⟨s, h_s_in_filt2, rfl⟩)))
            (Nat.le_add_right _ _)
      · -- sched t = some s, task s ≠ tsk
        have h_j_neq_s : j ≠ s := fun h => by subst h; exact h_tsk_s H_job_of_tsk
        have h_not_sched : scheduled_at sched j t = false := by
          simp [scheduled_at, h_sched, show s ≠ j from Ne.symm h_j_neq_s]
        have h_int : interference j t = true := by
          by_contra h; exact absurd (h_wc.1 h) (by simp [h_not_sched])
        -- All j' ∈ filt2 have task j' = tsk ≠ task s, so service_at j' t = 0
        have h_sum0 : (filt2.map (fun j' => service_at sched j' t)).sum = 0 := by
          apply List.sum_eq_zero; intro n hn; rw [List.mem_map] at hn
          obtain ⟨j', hj', rfl⟩ := hn
          have hj'_tsk : job_task j' = tsk := by
            have := (List.mem_filter.mp (show j' ∈ filt2 from hj')).2
            simpa [decide_eq_true_eq] using this
          simp only [service_at, scheduled_at, h_sched, beq_iff_eq, Option.some.injEq]
          have hj'_ne_s : j' ≠ s := fun h => by subst h; exact h_tsk_s hj'_tsk
          simp [Ne.symm hj'_ne_s]
        have h_sa_j : service_at sched j t = 0 := by simp [service_at, h_not_sched]
        simp only [h_sa_j, h_int, Bool.toNat_true, Nat.add_zero, h_sum0, Nat.zero_add]
        have h_not_tsched : task_scheduled_at job_task sched tsk t = false := by
          simp only [task_scheduled_at, h_sched]; exact decide_eq_false h_tsk_s
        have h_any := List.any_of_mem (p := fun j' => interference j' t) hj_task_before h_int
        simp [h_not_tsched, h_any]
  -- SD ≤ TSJ (j is one of the task's jobs)
  have h_sd_le : service_during sched j t1 y ≤
      task_service_of_jobs_received_in job_task arr_seq sched tsk t1 (t1 + A + ε) t1 y := by
    rw [h_tsj_eq]; unfold service_during
    apply Finset.sum_le_sum; intro t _
    exact List.le_sum_of_mem (List.mem_map.mpr ⟨j, hj_filt2, rfl⟩)
  omega

include H_arrival_times_are_consistent H_arr_seq_is_a_set H_job_cost_le_task_cost
  H_family_of_proper_arrival_curves H_tsk_in_ts in
theorem task_rbf_excl_tsk_bounds_task_workload_excl_j
    (j : Job)
    (H_j_arrives : arrives_in arr_seq j)
    (H_job_of_tsk : job_task j = tsk)
    (H_job_cost_positive : job_cost_positive job_cost j)
    (t1 t2 : Time)
    (H_busy_interval_j :
      busy_interval job_arrival job_cost sched interference interfering_workload j t1 t2) :
    task_workload_between job_cost job_task arr_seq tsk t1
      (t1 + (job_arrival j - t1) + ε) - job_cost j ≤
    task_request_bound_function task_cost max_arrivals tsk
      ((job_arrival j - t1) + ε) - task_cost tsk := by
  set A := job_arrival j - t1 with hA_def
  have hT1_LE_ARR := H_busy_interval_j.1.1
  -- Step 1: bound by task_cost * num_arrivals - task_cost
  apply le_trans _ (Nat.sub_le_sub_right (show task_cost tsk *
    Prosa.Classic.Model.Arrival.Basic.Task_arrival.num_arrivals_of_task job_task arr_seq tsk t1 (t1 + A + ε) ≤
    task_request_bound_function task_cost max_arrivals tsk (A + ε) from by
      unfold task_request_bound_function
      apply Nat.mul_le_mul_left
      have hPAC := H_family_of_proper_arrival_curves tsk H_tsk_in_ts
      convert hPAC.1 t1 (t1 + A + ε) (by simp only [Time]; omega) using 2 <;>
        first | rfl | (simp only [Time]; omega)) _)
  -- Step 2: task_workload - job_cost ≤ task_cost * num_arrivals - task_cost
  -- Split interval at t1 + A
  have hSPLIT : task_workload_between job_cost job_task arr_seq tsk t1 (t1 + A + ε) =
      task_workload_between job_cost job_task arr_seq tsk t1 (t1 + A) +
      task_workload_between job_cost job_task arr_seq tsk (t1 + A) (t1 + A + ε) := by
    unfold task_workload_between task_workload
    exact workload_of_jobs_cat job_cost arr_seq (t1 + A) t1 (t1 + A + ε) _ ⟨by simp only [Time]; omega, by simp only [Time]; omega⟩
  -- j is in arrivals at t1+A
  have hJ_IN_A : j ∈ jobs_arrived_between arr_seq (t1 + A) (t1 + A + ε) :=
    arrived_between_implies_in_arrivals job_arrival arr_seq H_arrival_times_are_consistent
      j (t1 + A) (t1 + A + ε) H_j_arrives
      ⟨by simp only [hA_def, Time] at *; omega, by simp only [hA_def, ε, Time] at *; omega⟩
  -- job_cost j ≤ task_workload_between(t1+A, t1+A+ε) since j contributes
  have hJ_LE_WL : job_cost j ≤ task_workload_between job_cost job_task arr_seq tsk (t1 + A) (t1 + A + ε) := by
    unfold task_workload_between task_workload workload_of_jobs
    have : j ∈ List.filter (fun j => decide (job_task j = tsk)) (jobs_arrived_between arr_seq (t1 + A) (t1 + A + ε)) := by
      exact List.mem_filter_of_mem hJ_IN_A (by simp [H_job_of_tsk])
    exact List.single_le_sum (fun _ _ => Nat.zero_le _) _ (List.mem_map.mpr ⟨j, this, rfl⟩)
  -- num_arrivals splitting
  have hNUM_SPLIT :
      Prosa.Classic.Model.Arrival.Basic.Task_arrival.num_arrivals_of_task job_task arr_seq tsk t1 (t1 + A + ε) =
      Prosa.Classic.Model.Arrival.Basic.Task_arrival.num_arrivals_of_task job_task arr_seq tsk t1 (t1 + A) +
      Prosa.Classic.Model.Arrival.Basic.Task_arrival.num_arrivals_of_task job_task arr_seq tsk (t1 + A) (t1 + A + ε) := by
    exact Prosa.Classic.Model.Arrival.Basic.Task_arrival.num_arrivals_of_task_cat
      job_task arr_seq tsk (t1 + A) t1 (t1 + A + ε) ⟨by simp only [Time]; omega, by simp only [Time]; omega⟩
  -- At least 1 arrival of tsk in [t1+A, t1+A+ε) (j itself)
  have hONE_ARRIVAL :
      1 ≤ Prosa.Classic.Model.Arrival.Basic.Task_arrival.num_arrivals_of_task
        job_task arr_seq tsk (t1 + A) (t1 + A + ε) := by
    unfold Prosa.Classic.Model.Arrival.Basic.Task_arrival.num_arrivals_of_task
    unfold Prosa.Classic.Model.Arrival.Basic.Task_arrival.arrivals_of_task_between
    have hMEM : j ∈ List.filter (Prosa.Classic.Model.Arrival.Basic.Task_arrival.is_job_of_task job_task tsk)
        (jobs_arrived_between arr_seq (t1 + A) (t1 + A + ε)) :=
      List.mem_filter_of_mem hJ_IN_A (by simp [Prosa.Classic.Model.Arrival.Basic.Task_arrival.is_job_of_task, H_job_of_tsk])
    exact List.length_pos_of_mem hMEM
  -- workload ≤ task_cost * num_arrivals for each sub-interval
  have hWL_LE_NUM1 :
      task_workload_between job_cost job_task arr_seq tsk t1 (t1 + A) ≤
      task_cost tsk * Prosa.Classic.Model.Arrival.Basic.Task_arrival.num_arrivals_of_task
        job_task arr_seq tsk t1 (t1 + A) := by
    unfold task_workload_between task_workload workload_of_jobs
    unfold Prosa.Classic.Model.Arrival.Basic.Task_arrival.num_arrivals_of_task
    unfold Prosa.Classic.Model.Arrival.Basic.Task_arrival.arrivals_of_task_between
    apply Prosa.Util.Sum.sum_majorant_constant
    intro j' hj' hTSK'
    have hj'_arr := in_arrivals_implies_arrived job_arrival arr_seq H_arrival_times_are_consistent
      j' t1 (t1 + A) hj'
    have hCOST := H_job_cost_le_task_cost j' hj'_arr
    simp only [decide_eq_true_eq] at hTSK'
    rw [← hTSK']; exact hCOST
  have hWL_LE_NUM2 :
      task_workload_between job_cost job_task arr_seq tsk (t1 + A) (t1 + A + ε) ≤
      task_cost tsk * Prosa.Classic.Model.Arrival.Basic.Task_arrival.num_arrivals_of_task
        job_task arr_seq tsk (t1 + A) (t1 + A + ε) := by
    unfold task_workload_between task_workload workload_of_jobs
    unfold Prosa.Classic.Model.Arrival.Basic.Task_arrival.num_arrivals_of_task
    unfold Prosa.Classic.Model.Arrival.Basic.Task_arrival.arrivals_of_task_between
    apply Prosa.Util.Sum.sum_majorant_constant
    intro j' hj' hTSK'
    have hj'_arr := in_arrivals_implies_arrived job_arrival arr_seq H_arrival_times_are_consistent
      j' (t1 + A) (t1 + A + ε) hj'
    have hCOST := H_job_cost_le_task_cost j' hj'_arr
    simp only [decide_eq_true_eq] at hTSK'
    rw [← hTSK']; exact hCOST
  -- Combine: workload - job_cost ≤ task_cost * num - task_cost
  rw [hSPLIT, hNUM_SPLIT, Nat.mul_add]
  -- Distribute subtraction using Nat.add_sub_assoc
  have hCLE : task_cost tsk ≤ task_cost tsk *
      Prosa.Classic.Model.Arrival.Basic.Task_arrival.num_arrivals_of_task
        job_task arr_seq tsk (t1 + A) (t1 + A + ε) :=
    Nat.le_mul_of_pos_right _ (by simp only [Time] at *; omega)
  rw [Nat.add_sub_assoc hJ_LE_WL, Nat.add_sub_assoc hCLE]
  apply Nat.add_le_add hWL_LE_NUM1
  -- Remaining: task_workload_between ... (t1+A) (t1+A+ε) - job_cost j ≤
  --            task_cost tsk * num_arrivals ... (t1+A) (t1+A+ε) - task_cost tsk
  -- Decompose by extracting j from the sum (big_rem style)
  unfold task_workload_between task_workload workload_of_jobs
  unfold Prosa.Classic.Model.Arrival.Basic.Task_arrival.num_arrivals_of_task
    Prosa.Classic.Model.Arrival.Basic.Task_arrival.arrivals_of_task_between
    Prosa.Classic.Model.Arrival.Basic.Task_arrival.is_job_of_task
  set L := (jobs_arrived_between arr_seq (t1 + A) (t1 + A + ε)).filter
    (fun j' => decide (job_task j' = tsk))
  have hj_in_L : j ∈ L :=
    List.mem_filter_of_mem hJ_IN_A (by simp [H_job_of_tsk])
  have hperm := List.perm_cons_erase hj_in_L
  have hW := (hperm.map job_cost).sum_eq
  simp only [List.map_cons, List.sum_cons] at hW
  have hN := hperm.length_eq
  simp only [List.length_cons] at hN
  rw [hW, hN]
  -- Goal: (job_cost j + rest_sum) - job_cost j ≤ task_cost tsk * (rest_count + 1) - task_cost tsk
  -- Suffices: rest_sum ≤ task_cost tsk * rest_count
  suffices h : ((L.erase j).map job_cost).sum ≤ task_cost tsk * (L.erase j).length by
    rw [Nat.add_comm (job_cost j), Nat.add_sub_cancel,
        Nat.mul_add, Nat.mul_one, Nat.add_sub_cancel]; exact h
  -- Prove: sum of costs of remaining jobs ≤ task_cost * count
  have h_sum_bound : ∀ (l : List Job), (∀ x ∈ l, job_cost x ≤ task_cost tsk) →
      (l.map job_cost).sum ≤ task_cost tsk * l.length := by
    intro l hl; induction l with
    | nil => simp
    | cons hd tl ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      rw [Nat.mul_succ, Nat.add_comm (task_cost tsk * tl.length)]
      exact Nat.add_le_add (hl hd (by simp)) (ih (fun x hx => hl x (by simp [hx])))
  apply h_sum_bound
  intro j' hj'
  have hj'_mem : j' ∈ L := List.erase_subset hj'
  have hj'_in := (List.mem_filter.mp hj'_mem).1
  have hj'_arrives := in_arrivals_implies_arrived job_arrival arr_seq
    H_arrival_times_are_consistent j' (t1 + A) (t1 + A + ε) hj'_in
  have hCOST' := H_job_cost_le_task_cost j' hj'_arrives
  have hTSK' : job_task j' = tsk := by
    have := (List.mem_filter.mp hj'_mem).2; simpa [decide_eq_true_eq]
  rw [← hTSK']; exact hCOST'

include H_work_conserving H_sequential_jobs
  H_interference_and_workload_consistent_with_sequential_jobs
  H_arrival_times_are_consistent H_arr_seq_is_a_set
  H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute
  H_job_cost_le_task_cost H_family_of_proper_arrival_curves H_tsk_in_ts in
theorem bound_for_cumulative_job_interference
    (j : Job)
    (H_j_arrives : arrives_in arr_seq j)
    (H_job_of_tsk : job_task j = tsk)
    (H_job_cost_positive : job_cost_positive job_cost j)
    (t1 t2 : Time)
    (H_busy_interval_j :
      busy_interval job_arrival job_cost sched interference interfering_workload j t1 t2)
    (x : Time)
    (H_inside_busy_interval : t1 + x < t2)
    (H_job_j_is_not_completed : ¬ completed_by job_cost sched j (t1 + x)) :
    cumul_interference interference j t1 (t1 + x) ≤
    (task_request_bound_function task_cost max_arrivals tsk
      ((job_arrival j - t1) + ε) - task_cost tsk) +
    cumul_task_interference job_task sched arr_seq interference tsk t2 t1 (t1 + x) := by
  have h_actual := bound_for_cumulative_job_interference_actual job_arrival job_cost job_task
    arr_seq H_arrival_times_are_consistent H_arr_seq_is_a_set sched
    H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute
    tsk interference interfering_workload H_work_conserving H_sequential_jobs
    H_interference_and_workload_consistent_with_sequential_jobs
    j H_j_arrives H_job_of_tsk H_job_cost_positive t1 t2 H_busy_interval_j
    x H_inside_busy_interval H_job_j_is_not_completed
  have h_rbf := task_rbf_excl_tsk_bounds_task_workload_excl_j task_cost job_arrival job_cost job_task
    arr_seq H_arrival_times_are_consistent H_arr_seq_is_a_set sched
    H_job_cost_le_task_cost ts max_arrivals H_family_of_proper_arrival_curves
    tsk H_tsk_in_ts interference interfering_workload
    j H_j_arrives H_job_of_tsk H_job_cost_positive t1 t2 H_busy_interval_j
  simp only [Time] at *; omega

include H_proper_job_lock_in_service H_proper_task_lock_in_service
  H_arrival_times_are_consistent H_family_of_proper_arrival_curves H_tsk_in_ts
  H_R_is_maximum_seq in
theorem max_in_seq_hypothesis_implies_max_in_nonseq_hypothesis
    (j : Job)
    (H_j_arrives : arrives_in arr_seq j)
    (H_job_of_tsk : job_task j = tsk) :
    ∀ A,
      is_in_search_space tsk L
        (fun tsk' A' Δ =>
          task_request_bound_function task_cost max_arrivals tsk' (A' + ε) -
            task_cost tsk' + task_interference_bound_function tsk' A' Δ) A →
      ∃ F,
        A + F = task_lock_in_service tsk +
          (task_request_bound_function task_cost max_arrivals tsk (A + ε) -
            task_cost tsk + task_interference_bound_function tsk A (A + F)) ∧
        F + (task_cost tsk - task_lock_in_service tsk) ≤ R := by
  obtain ⟨hTLIS_le_tcost, hTLIS_bounds⟩ := H_proper_task_lock_in_service
  intro A INSP
  obtain ⟨F, hFIX, hLE⟩ := H_R_is_maximum_seq A INSP
  refine ⟨F, ?_, hLE⟩
  -- Need: A + F = task_lock_in_service tsk + (task_rbf(A+ε) - task_cost tsk + tIBF tsk A (A+F))
  -- From hFIX: A + F = (task_rbf(A+ε) - (task_cost tsk - task_lock_in_service tsk)) + tIBF tsk A (A+F)
  -- So: task_rbf(A+ε) - (task_cost tsk - task_lock_in_service tsk) = task_lock_in_service tsk + (task_rbf(A+ε) - task_cost tsk)
  -- This requires task_cost tsk ≤ task_rbf(A+ε) and task_lock_in_service tsk ≤ task_cost tsk
  have hRBF_ge_cost : task_cost tsk ≤ task_request_bound_function task_cost max_arrivals tsk (A + ε) := by
    have h1 := task_rbf_1_ge_task_cost task_cost job_arrival job_task arr_seq H_arrival_times_are_consistent
      tsk max_arrivals (H_family_of_proper_arrival_curves tsk H_tsk_in_ts) j H_j_arrives H_job_of_tsk
    have h2 := task_rbf_monotone task_cost job_task arr_seq tsk max_arrivals (H_family_of_proper_arrival_curves tsk H_tsk_in_ts)
    exact le_trans h1 (h2 (by simp [ε]))
  simp only [Time] at *; omega

include H_arrival_times_are_consistent H_arr_seq_is_a_set
  H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute
  H_job_cost_le_task_cost H_all_jobs_from_taskset
  H_family_of_proper_arrival_curves H_tsk_in_ts
  H_proper_job_lock_in_service H_proper_task_lock_in_service
  H_work_conserving H_sequential_jobs
  H_interference_and_workload_consistent_with_sequential_jobs
  H_busy_interval_exists H_task_interference_is_bounded H_R_is_maximum_seq in
theorem uniprocessor_response_time_bound_seq :
    is_response_time_bound_of_task job_arrival job_cost job_task arr_seq sched tsk R := by
  intro j hARR hTSK
  -- Construct job interference bound for the total IBF
  have h_job_bounded : job_interference_is_bounded_by job_arrival job_cost job_task arr_seq sched tsk
      interference interfering_workload
      (fun tsk' A' Δ => task_request_bound_function task_cost max_arrivals tsk' (A' + ε) -
        task_cost tsk' + task_interference_bound_function tsk' A' Δ) := by
    intro t1' t2' R' j' hBUSY' hRLT' hARR' hTSK' hCOMPL'
    have h_pos : job_cost_positive job_cost j' := by
      simp only [job_cost_positive, completed_by, Time] at *; omega
    -- Use bound_for_cumulative_job_interference + H_task_interference_is_bounded
    apply le_trans
    · exact bound_for_cumulative_job_interference task_cost job_arrival job_cost job_task
        arr_seq H_arrival_times_are_consistent H_arr_seq_is_a_set sched
        H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute
        H_job_cost_le_task_cost ts max_arrivals H_family_of_proper_arrival_curves
        tsk H_tsk_in_ts interference interfering_workload H_work_conserving H_sequential_jobs
        H_interference_and_workload_consistent_with_sequential_jobs
        j' hARR' hTSK' h_pos t1' t2' hBUSY' R' hRLT' hCOMPL'
    · apply Nat.add_le_add_left
      exact H_task_interference_is_bounded j' R' t1' t2' hARR' hTSK' hRLT' hCOMPL' hBUSY'
  -- Construct H_R_is_maximum from max_in_seq_hypothesis_implies_max_in_nonseq_hypothesis
  have h_R_max := max_in_seq_hypothesis_implies_max_in_nonseq_hypothesis task_cost job_arrival
    job_cost job_task arr_seq H_arrival_times_are_consistent
    sched ts max_arrivals H_family_of_proper_arrival_curves tsk H_tsk_in_ts
    job_lock_in_service task_lock_in_service
    H_proper_job_lock_in_service H_proper_task_lock_in_service
    L task_interference_bound_function R H_R_is_maximum_seq
    j hARR hTSK
  -- Apply the main abstract RTA theorem
  exact @uniprocessor_response_time_bound Task _ task_cost Job _ job_arrival job_cost job_task
    arr_seq sched
    H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute
    H_job_cost_le_task_cost tsk job_lock_in_service task_lock_in_service
    H_proper_job_lock_in_service H_proper_task_lock_in_service
    interference interfering_workload H_work_conserving
    L H_busy_interval_exists
    (fun tsk' A' Δ => task_request_bound_function task_cost max_arrivals tsk' (A' + ε) -
      task_cost tsk' + task_interference_bound_function tsk' A' Δ)
    h_job_bounded R h_R_max j hARR hTSK

end Sequential_Abstract_RTA

end AbstractSeqRTA

end Prosa.Classic.Model.Schedule.Uni.Limited.Abstract_RTA.Abstract_seq_rta
