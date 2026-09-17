-- Translated from: ../rt-proofs/classic/model/schedule/uni/limited/fixed_priority/response_time_bound.v
import Prosa.Classic.Util.All
import Prosa.Classic.Model.Arrival.Basic.Job
import Prosa.Classic.Model.Schedule.Uni.Service
import Prosa.Classic.Model.Schedule.Uni.Limited.Platform.Definitions
import Prosa.Classic.Model.Arrival.Curves.Bounds
import Prosa.Classic.Analysis.Uni.Arrival_curves.Workload_bound
import Prosa.Classic.Model.Schedule.Uni.Limited.Busy_interval
import Prosa.Classic.Model.Schedule.Uni.Schedule
import Prosa.Classic.Model.Schedule.Uni.Workload
import Prosa.Classic.Model.Schedule.Uni.Response_time
import Prosa.Classic.Model.Schedule.Uni.Schedule_of_task
import Prosa.Classic.Model.Schedule.Uni.Limited.Schedule
import Prosa.Classic.Model.Schedule.Uni.Limited.Abstract_RTA.Definitions
import Prosa.Classic.Model.Schedule.Uni.Limited.Abstract_RTA.Reduction_of_search_space
import Prosa.Classic.Model.Schedule.Uni.Limited.Abstract_RTA.Abstract_rta
import Prosa.Classic.Model.Schedule.Uni.Limited.Rbf
import Prosa.Classic.Model.Priority
import Prosa.Classic.Model.Schedule.Uni.Limited.Jlfp_instantiation
import Prosa.Classic.Model.Schedule.Uni.Limited.Abstract_RTA.Abstract_seq_rta
import Prosa.Util.Epsilon
import Mathlib.Tactic

namespace Prosa.Classic.Model.Schedule.Uni.Limited.Fixed_priority.Response_time_bound

open Prosa.Classic.Model.Time
open Prosa.Classic.Model.Arrival.Basic.Job
open Prosa.Classic.Model.Arrival.Basic.Arrival_sequence
open Prosa.Classic.Model.Schedule.Uni.Schedule
open Prosa.Classic.Model.Schedule.Uni.Service
open Prosa.Classic.Model.Schedule.Uni.Workload
open Prosa.Classic.Model.Schedule.Uni.Response_time.ResponseTime
open Prosa.Classic.Model.Schedule.Uni.Schedule_of_task
open Prosa.Classic.Model.Schedule.Uni.Limited.Platform.Definitions.LimitedPreemptionPlatform
open Prosa.Classic.Model.Schedule.Uni.Limited.Schedule
open Prosa.Classic.Model.Schedule.Uni.Limited.Abstract_RTA.Definitions
open Prosa.Classic.Model.Schedule.Uni.Limited.Abstract_RTA.Reduction_of_search_space.AbstractRTAReduction
open Prosa.Classic.Model.Schedule.Uni.Limited.Abstract_RTA.Abstract_rta.AbstractRTA
open Prosa.Classic.Model.Schedule.Uni.Limited.Busy_interval.BusyIntervalJLFP
open Prosa.Classic.Model.Arrival.Curves.Bounds.ArrivalCurves
open Prosa.Classic.Analysis.Uni.Arrival_curves.Workload_bound.MaxArrivalsWorkloadBound
open Prosa.Classic.Model.Priority
open Prosa.Classic.Model.Schedule.Uni.Basic.Platform
open Prosa.Classic.Model.Schedule.Uni.Limited.Abstract_RTA.Abstract_seq_rta
open Prosa.Util.Epsilon

namespace AbstractRTAforFPwithArrivalCurves

section AbstractResponseTimeAnalysisForFP

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

  variable (H_work_conserving : Platform.work_conserving job_arrival job_cost arr_seq sched)

  variable (H_sequential_jobs : sequential_jobs job_arrival job_cost sched job_task)

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

  variable (higher_eq_priority : FP_policy Task)
  variable (H_priority_is_reflexive : FP_is_reflexive higher_eq_priority)
  variable (H_priority_is_transitive : FP_is_transitive higher_eq_priority)

  private abbrev jlfp_higher_eq_priority' : JLFP_policy Job :=
    FP_to_JLFP job_task higher_eq_priority

  private abbrev response_time_bounded_by' :=
    is_response_time_bound_of_task job_arrival job_cost job_task arr_seq sched

  private abbrev task_rbf' :=
    task_request_bound_function task_cost max_arrivals tsk

  private abbrev total_hep_rbf' :=
    total_hep_request_bound_function_FP task_cost higher_eq_priority max_arrivals ts tsk

  private abbrev total_ohep_rbf' :=
    total_ohep_request_bound_function_FP task_cost higher_eq_priority max_arrivals ts tsk

  variable (priority_inversion_bound : Time)
  variable (H_priority_inversion_is_bounded :
    priority_inversion_is_bounded_by job_arrival job_cost job_task arr_seq sched
      (FP_to_JLFP job_task higher_eq_priority) tsk priority_inversion_bound)

  variable (L : Time)
  variable (H_L_positive : L > 0)
  variable (H_fixed_point : L = priority_inversion_bound +
    total_hep_request_bound_function_FP task_cost higher_eq_priority max_arrivals ts tsk L)

  private abbrev is_in_search_space_FP' (A : Time) : Prop :=
    A < L ∧ task_request_bound_function task_cost max_arrivals tsk A ≠
      task_request_bound_function task_cost max_arrivals tsk (A + ε)

  private abbrev IBF' (R₀ : Time) : Time :=
    priority_inversion_bound +
      total_ohep_request_bound_function_FP task_cost higher_eq_priority max_arrivals ts tsk R₀

  variable (R : Time)
  variable (H_R_is_maximum :
    ∀ A,
      is_in_search_space_FP' task_cost max_arrivals tsk L A →
      ∃ F,
        A + F = priority_inversion_bound
                + (task_request_bound_function task_cost max_arrivals tsk (A + ε)
                   - (task_cost tsk - task_lock_in_service tsk))
                + total_ohep_request_bound_function_FP task_cost higher_eq_priority max_arrivals ts tsk (A + F) ∧
        F + (task_cost tsk - task_lock_in_service tsk) ≤ R)

  section FillingOutHypothesesOfAbstractRTATheorem

    private abbrev interference' : Job → Time → Bool :=
      fun (j : Job) (t : Time) =>
        is_priority_inversion sched (FP_to_JLFP job_task higher_eq_priority) j t != 0 ||
        (match sched t with
         | some jhp => (FP_to_JLFP job_task higher_eq_priority) jhp j && decide (jhp ≠ j)
         | none => false)

    private abbrev interfering_workload' : Job → Time → Nat :=
      fun (j : Job) (t : Time) =>
        is_priority_inversion sched (FP_to_JLFP job_task higher_eq_priority) j t +
        (((jobs_arriving_at arr_seq t).filter
          (fun jhp => (FP_to_JLFP job_task higher_eq_priority) jhp j && decide (jhp ≠ j))).map job_cost).sum

    include H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute
      H_completed_jobs_dont_execute H_work_conserving H_sequential_jobs
      H_priority_is_reflexive H_arrival_times_are_consistent H_arr_seq_is_a_set in
    include H_arrival_times_are_consistent H_arr_seq_is_a_set H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_work_conserving H_sequential_jobs H_job_cost_le_task_cost H_all_jobs_from_taskset H_family_of_proper_arrival_curves H_tsk_in_ts H_proper_job_lock_in_service H_proper_task_lock_in_service H_priority_is_reflexive H_priority_is_transitive H_priority_inversion_is_bounded H_L_positive H_fixed_point H_R_is_maximum in
    theorem instantiated_i_and_w_are_consistent_with_schedule :
        Prosa.Classic.Model.Schedule.Uni.Limited.Abstract_RTA.Definitions.work_conserving
          job_arrival job_cost job_task arr_seq sched tsk
          (interference' job_task sched higher_eq_priority)
          (interfering_workload' job_cost job_task arr_seq sched higher_eq_priority) := by
      intro j t1 t2 t ARR TSK POS BUSY ⟨hLE, hLT⟩
      have hFP_refl : JLFP_is_reflexive (FP_to_JLFP job_task higher_eq_priority) :=
        fun x => H_priority_is_reflexive (job_task x)
      have hFP_trans : JLFP_is_transitive (FP_to_JLFP job_task higher_eq_priority) :=
        fun y x z hxy hyz => H_priority_is_transitive (job_task y) (job_task x) (job_task z) hxy hyz
      have hFP_seq : JLFP_respects_sequential_jobs job_task job_arrival (FP_to_JLFP job_task higher_eq_priority) :=
        any_reflexive_FP_respects_sequential_jobs job_arrival job_task higher_eq_priority H_priority_is_reflexive
      have hBI := (Prosa.Classic.Model.Schedule.Uni.Limited.Jlfp_instantiation.JLFPInstantiation.instantiated_busy_interval_equivalent_edf_busy_interval
        job_arrival job_cost job_task arr_seq H_arrival_times_are_consistent H_arr_seq_is_a_set
        sched H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute
        H_sequential_jobs (FP_to_JLFP job_task higher_eq_priority)
        hFP_refl hFP_trans hFP_seq tsk j ARR TSK POS t1 t2).mpr BUSY
      constructor
      · intro hNI
        simp only [Bool.not_eq_true, Bool.or_eq_false_iff] at hNI
        obtain ⟨hPI, hHP⟩ := hNI
        cases h : sched t with
        | none =>
          exfalso
          exact not_quiet_implies_not_idle job_arrival job_cost job_task arr_seq
            H_arrival_times_are_consistent sched H_jobs_come_from_arrival_sequence
            (FP_to_JLFP job_task higher_eq_priority)
            tsk j ARR TSK POS
            H_work_conserving H_completed_jobs_dont_execute
            H_jobs_must_arrive_to_execute hFP_refl hFP_trans
            t1 t2 hBI.1 t ⟨hLE, hLT⟩ (by simp [is_idle, h])
        | some s =>
          simp only [Prosa.Classic.Model.Schedule.Uni.Limited.Busy_interval.BusyIntervalJLFP.is_priority_inversion, h] at hPI
          have hFP_sj : (FP_to_JLFP job_task higher_eq_priority) s j = true := by
            by_contra hc; push_neg at hc; simp [hc] at hPI
          simp only [h] at hHP
          have h_eq : s = j := by by_contra hne; simp [hFP_sj, hne] at hHP
          subst h_eq; simp [scheduled_at, h]
      · intro hSCHED
        simp only [Bool.not_eq_true, Bool.or_eq_false_iff]
        cases h : sched t with
        | none => simp [scheduled_at, h] at hSCHED
        | some s =>
          have hsj : s = j := by simp [scheduled_at, h] at hSCHED; exact hSCHED
          constructor
          · simp [Prosa.Classic.Model.Schedule.Uni.Limited.Busy_interval.BusyIntervalJLFP.is_priority_inversion, h, hsj, hFP_refl j]
          · simp [h, hsj]

    include H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute
      H_completed_jobs_dont_execute H_work_conserving H_sequential_jobs
      H_priority_is_reflexive H_arrival_times_are_consistent H_arr_seq_is_a_set in
    include H_arrival_times_are_consistent H_arr_seq_is_a_set H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_work_conserving H_sequential_jobs H_job_cost_le_task_cost H_all_jobs_from_taskset H_family_of_proper_arrival_curves H_tsk_in_ts H_proper_job_lock_in_service H_proper_task_lock_in_service H_priority_is_reflexive H_priority_is_transitive H_priority_inversion_is_bounded H_L_positive H_fixed_point H_R_is_maximum in
    theorem instantiated_interference_and_workload_consistent_with_sequential_jobs :
        ∀ j t1 t2,
          arrives_in arr_seq j →
          job_task j = tsk →
          job_cost j > 0 →
          Prosa.Classic.Model.Schedule.Uni.Limited.Abstract_RTA.Definitions.busy_interval
            job_arrival job_cost sched
            (interference' job_task sched higher_eq_priority)
            (interfering_workload' job_cost job_task arr_seq sched higher_eq_priority)
            j t1 t2 →
          workload_of_jobs job_cost (jobs_arrived_between arr_seq 0 t1)
            (fun j_other => decide (job_task j_other = tsk)) =
          service_of_jobs sched (jobs_arrived_between arr_seq 0 t1)
            (fun j_other => decide (job_task j_other = tsk)) 0 t1 := by
      intro j t1 t2 ARR TSK POS BUSY
      have hFP_refl : JLFP_is_reflexive (FP_to_JLFP job_task higher_eq_priority) :=
        fun x => H_priority_is_reflexive (job_task x)
      have hFP_trans : JLFP_is_transitive (FP_to_JLFP job_task higher_eq_priority) :=
        fun y x z hxy hyz => H_priority_is_transitive (job_task y) (job_task x) (job_task z) hxy hyz
      have hFP_seq : JLFP_respects_sequential_jobs job_task job_arrival (FP_to_JLFP job_task higher_eq_priority) :=
        any_reflexive_FP_respects_sequential_jobs job_arrival job_task higher_eq_priority H_priority_is_reflexive
      have hBI := (Prosa.Classic.Model.Schedule.Uni.Limited.Jlfp_instantiation.JLFPInstantiation.instantiated_busy_interval_equivalent_edf_busy_interval
        job_arrival job_cost job_task arr_seq H_arrival_times_are_consistent H_arr_seq_is_a_set
        sched H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute
        H_sequential_jobs (FP_to_JLFP job_task higher_eq_priority)
        hFP_refl hFP_trans hFP_seq tsk j ARR TSK POS t1 t2).mpr BUSY
      rw [← all_jobs_have_completed_equiv_workload_eq_service job_arrival job_cost arr_seq
        H_arrival_times_are_consistent sched H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute
        (fun j_other => decide (job_task j_other = tsk)) 0 t1 t1]
      intro s hARR_s hTSK_s
      have hARR_s' := in_arrivals_implies_arrived job_arrival arr_seq H_arrival_times_are_consistent s 0 t1 hARR_s
      obtain ⟨⟨_, hqt1, _, hle_arr, _⟩, _⟩ := hBI
      have hS_before := (in_arrivals_implies_arrived_between job_arrival arr_seq H_arrival_times_are_consistent s 0 t1 hARR_s).2
      have hTSK_eq : job_task s = tsk := by
        simp only [decide_eq_true_eq] at hTSK_s; exact hTSK_s
      have hPRIO : (FP_to_JLFP job_task higher_eq_priority) s j = true := by
        show higher_eq_priority (job_task s) (job_task j) = true
        rw [hTSK_eq, TSK]; exact H_priority_is_reflexive tsk
      exact hqt1 s hARR_s' hPRIO hS_before

    include H_arrival_times_are_consistent H_arr_seq_is_a_set
      H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute
      H_completed_jobs_dont_execute H_work_conserving
      H_job_cost_le_task_cost H_all_jobs_from_taskset
      H_family_of_proper_arrival_curves H_L_positive H_fixed_point
      H_priority_is_reflexive H_priority_inversion_is_bounded in
    include H_arrival_times_are_consistent H_arr_seq_is_a_set H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_work_conserving H_sequential_jobs H_job_cost_le_task_cost H_all_jobs_from_taskset H_family_of_proper_arrival_curves H_tsk_in_ts H_proper_job_lock_in_service H_proper_task_lock_in_service H_priority_is_reflexive H_priority_is_transitive H_priority_inversion_is_bounded H_L_positive H_fixed_point H_R_is_maximum in
    theorem instantiated_busy_intervals_are_bounded :
        Prosa.Classic.Model.Schedule.Uni.Limited.Abstract_RTA.Definitions.busy_intervals_are_bounded_by
          job_arrival job_cost job_task arr_seq sched tsk
          (interference' job_task sched higher_eq_priority)
          (interfering_workload' job_cost job_task arr_seq sched higher_eq_priority)
          L := by
      intro j ARR TSK POS
      have hFP_refl : JLFP_is_reflexive (FP_to_JLFP job_task higher_eq_priority) :=
        fun x => H_priority_is_reflexive (job_task x)
      have hFP_trans : JLFP_is_transitive (FP_to_JLFP job_task higher_eq_priority) :=
        fun y x z hxy hyz => H_priority_is_transitive (job_task y) (job_task x) (job_task z) hxy hyz
      have hFP_seq : JLFP_respects_sequential_jobs job_task job_arrival (FP_to_JLFP job_task higher_eq_priority) :=
        any_reflexive_FP_respects_sequential_jobs job_arrival job_task higher_eq_priority H_priority_is_reflexive
      have hPOS : job_cost_positive job_cost j := by simp only [job_cost_positive]; exact POS
      -- Per-job priority inversion bound
      have h_pi_job := H_priority_inversion_is_bounded j ARR TSK POS
      -- HEP workload bound: pi + hp_workload ≤ L
      have h_is_arrival_bound : is_arrival_bound_for_taskset job_task arr_seq max_arrivals ts :=
        fun tsk0 IN0 => (H_family_of_proper_arrival_curves tsk0 IN0).1
      have h_wkld : ∀ t,
          priority_inversion_bound +
            workload_of_higher_or_equal_priority_jobs job_cost
              (jobs_arrived_between arr_seq t (t + L)) (FP_to_JLFP job_task higher_eq_priority) j ≤ L := by
        intro t
        have h_bound := total_workload_le_total_rbf' task_cost job_arrival job_cost job_task arr_seq
          H_arrival_times_are_consistent H_arr_seq_is_a_set
          higher_eq_priority ts tsk
          (fun j0 hj0 => H_job_cost_le_task_cost j0 hj0)
          H_all_jobs_from_taskset max_arrivals h_is_arrival_bound j ARR TSK t L
        calc priority_inversion_bound + workload_of_higher_or_equal_priority_jobs job_cost
                (jobs_arrived_between arr_seq t (t + L)) (FP_to_JLFP job_task higher_eq_priority) j
            ≤ priority_inversion_bound +
                total_hep_request_bound_function_FP task_cost higher_eq_priority max_arrivals ts tsk L := by
              apply Nat.add_le_add_left
              unfold workload_of_higher_or_equal_priority_jobs
              exact h_bound
          _ = L := H_fixed_point.symm
      -- Get concrete busy interval
      obtain ⟨t1, t2, hle, harr, hbd, hBI⟩ := exists_busy_interval job_arrival job_cost job_task arr_seq
        H_arrival_times_are_consistent sched H_jobs_come_from_arrival_sequence
        (FP_to_JLFP job_task higher_eq_priority) tsk j ARR TSK hPOS
        H_arr_seq_is_a_set H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute
        H_work_conserving hFP_refl hFP_trans
        priority_inversion_bound h_pi_job
        L H_L_positive h_wkld POS
      -- Convert to abstract
      exact ⟨t1, t2, hle, harr, hbd,
        (Prosa.Classic.Model.Schedule.Uni.Limited.Jlfp_instantiation.JLFPInstantiation.instantiated_busy_interval_equivalent_edf_busy_interval
          job_arrival job_cost job_task arr_seq H_arrival_times_are_consistent H_arr_seq_is_a_set
          sched H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute
          H_sequential_jobs (FP_to_JLFP job_task higher_eq_priority)
          hFP_refl hFP_trans hFP_seq tsk j ARR TSK POS t1 t2).mp hBI⟩

    include H_arrival_times_are_consistent H_arr_seq_is_a_set
      H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute
      H_completed_jobs_dont_execute H_work_conserving H_sequential_jobs
      H_job_cost_le_task_cost H_all_jobs_from_taskset
      H_family_of_proper_arrival_curves H_priority_is_reflexive
      H_priority_inversion_is_bounded in
    include H_arrival_times_are_consistent H_arr_seq_is_a_set H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_work_conserving H_sequential_jobs H_job_cost_le_task_cost H_all_jobs_from_taskset H_family_of_proper_arrival_curves H_tsk_in_ts H_proper_job_lock_in_service H_proper_task_lock_in_service H_priority_is_reflexive H_priority_is_transitive H_priority_inversion_is_bounded H_L_positive H_fixed_point H_R_is_maximum in
    theorem instantiated_task_interference_is_bounded :
        ∀ j R₀ t1 t2,
          arrives_in arr_seq j →
          job_task j = tsk →
          t1 + R₀ < t2 →
          ¬ completed_by job_cost sched j (t1 + R₀) →
          Prosa.Classic.Model.Schedule.Uni.Limited.Abstract_RTA.Definitions.busy_interval
            job_arrival job_cost sched
            (interference' job_task sched higher_eq_priority)
            (interfering_workload' job_cost job_task arr_seq sched higher_eq_priority)
            j t1 t2 →
          cumulative_priority_inversion sched
            (FP_to_JLFP job_task higher_eq_priority) j t1 (t1 + R₀) +
          service_of_jobs sched (jobs_arrived_between arr_seq t1 (t1 + R₀))
            (fun jhp => (FP_to_JLFP job_task higher_eq_priority) jhp j &&
              decide (job_task jhp ≠ job_task j)) t1 (t1 + R₀) ≤
          priority_inversion_bound +
            total_ohep_request_bound_function_FP task_cost higher_eq_priority max_arrivals ts tsk R₀ := by
      intro j R₀ t1 t2 ARR TSK hRLT NCOMPL BUSY
      have hFP_refl : JLFP_is_reflexive (FP_to_JLFP job_task higher_eq_priority) :=
        fun x => H_priority_is_reflexive (job_task x)
      have hFP_trans : JLFP_is_transitive (FP_to_JLFP job_task higher_eq_priority) :=
        fun y x z hxy hyz => H_priority_is_transitive (job_task y) (job_task x) (job_task z) hxy hyz
      have hFP_seq : JLFP_respects_sequential_jobs job_task job_arrival (FP_to_JLFP job_task higher_eq_priority) :=
        any_reflexive_FP_respects_sequential_jobs job_arrival job_task higher_eq_priority H_priority_is_reflexive
      have POS : job_cost j > 0 := by
        by_contra h; push_neg at h; exact NCOMPL (by simp only [completed_by, Time] at *; omega)
      have hBI := (Prosa.Classic.Model.Schedule.Uni.Limited.Jlfp_instantiation.JLFPInstantiation.instantiated_busy_interval_equivalent_edf_busy_interval
        job_arrival job_cost job_task arr_seq H_arrival_times_are_consistent H_arr_seq_is_a_set
        sched H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute
        H_sequential_jobs (FP_to_JLFP job_task higher_eq_priority)
        hFP_refl hFP_trans hFP_seq tsk j ARR TSK POS t1 t2).mpr BUSY
      apply Nat.add_le_add
      · -- Part 1: cumulative_priority_inversion ≤ priority_inversion_bound
        apply Nat.le_trans _ (H_priority_inversion_is_bounded j ARR TSK POS t1 t2 hBI.1)
        apply Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.Ico_subset_Ico_right (by simp only [Time] at *; omega))
          (fun _ _ _ => Nat.zero_le _)
      · -- Part 2: service_of_jobs ≤ total_ohep_rbf
        apply Nat.le_trans (service_of_jobs_le_workload job_cost sched
          (jobs_arrived_between arr_seq t1 (t1 + R₀)) _ H_completed_jobs_dont_execute
          t1 (t1 + R₀))
        have h_is_arrival_bound : is_arrival_bound_for_taskset job_task arr_seq max_arrivals ts :=
          fun tsk0 IN0 => (H_family_of_proper_arrival_curves tsk0 IN0).1
        exact total_workload_le_total_rbf task_cost job_arrival job_cost job_task arr_seq
          H_arrival_times_are_consistent H_arr_seq_is_a_set
          higher_eq_priority ts tsk
          (fun j0 hj0 => H_job_cost_le_task_cost j0 hj0)
          H_all_jobs_from_taskset max_arrivals h_is_arrival_bound j ARR TSK t1 R₀

    section SolutionOfResponseTimeReccurenceExists

      variable (j : Job)
      variable (H_j_arrives : arrives_in arr_seq j)
      variable (H_job_of_tsk : job_task j = tsk)
      variable (H_job_cost_positive : job_cost_positive job_cost j)

      variable (A : Time)
      variable (H_A_is_in_abstract_search_space :
        is_in_search_space tsk L
          (fun _tsk A Δ =>
            task_request_bound_function task_cost max_arrivals tsk (A + ε) - task_cost tsk +
            (priority_inversion_bound +
              total_ohep_request_bound_function_FP task_cost higher_eq_priority max_arrivals ts tsk Δ)) A)

      include H_arrival_times_are_consistent H_arr_seq_is_a_set
        H_jobs_come_from_arrival_sequence H_completed_jobs_dont_execute
        H_job_cost_le_task_cost H_tsk_in_ts
        H_family_of_proper_arrival_curves
        H_j_arrives H_job_of_tsk H_job_cost_positive in
      include H_arrival_times_are_consistent H_arr_seq_is_a_set H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_work_conserving H_sequential_jobs H_job_cost_le_task_cost H_all_jobs_from_taskset H_family_of_proper_arrival_curves H_tsk_in_ts H_proper_job_lock_in_service H_proper_task_lock_in_service H_priority_is_reflexive H_priority_is_transitive H_priority_inversion_is_bounded H_L_positive H_fixed_point H_R_is_maximum H_j_arrives H_job_of_tsk H_job_cost_positive H_A_is_in_abstract_search_space in
      theorem A_is_in_concrete_search_space :
          is_in_search_space_FP' task_cost max_arrivals tsk L A := by
        unfold is_in_search_space are_not_equivalent_at_values_less_than at H_A_is_in_abstract_search_space
        rcases H_A_is_in_abstract_search_space with rfl | ⟨hPOS, hLT, x, _, hNEQ⟩
        · -- Case A = 0
          constructor
          · exact H_L_positive
          · have h0 := Prosa.Classic.Model.Schedule.Uni.Limited.Rbf.RBF.task_rbf_0_zero
              task_cost job_task arr_seq tsk max_arrivals (H_family_of_proper_arrival_curves tsk H_tsk_in_ts)
            have h1 := Prosa.Classic.Model.Schedule.Uni.Limited.Rbf.RBF.task_rbf_1_ge_task_cost
              task_cost job_arrival job_task arr_seq H_arrival_times_are_consistent
              tsk max_arrivals (H_family_of_proper_arrival_curves tsk H_tsk_in_ts) j H_j_arrives H_job_of_tsk
            have h_jc_le : job_cost j ≤ task_cost tsk := by
              have := H_job_cost_le_task_cost j H_j_arrives
              simp only [job_cost_le_task_cost, H_job_of_tsk] at this; exact this
            intro h_eq; rw [h0] at h_eq
            have h_eps : (0 : Time) + ε = 1 := by simp [ε, Time]
            rw [h_eps] at h_eq
            -- h_eq : 0 = task_rbf 1, but task_rbf 1 ≥ task_cost tsk ≥ job_cost j > 0
            have h_trb1_0 := h_eq.symm
            have h_tc_le : task_cost tsk ≤ 0 := by
              have := h1; rw [h_trb1_0] at this; exact this
            have h_jc_0 := Nat.le_zero.mp (Nat.le_trans h_jc_le h_tc_le)
            simp only [job_cost_positive] at H_job_cost_positive
            rw [h_jc_0] at H_job_cost_positive
            exact absurd H_job_cost_positive (by decide)
        · -- Case A > 0: if task_rbf A = task_rbf (A+ε), then IBF(A-ε,x) = IBF(A,x), contradiction
          constructor
          · exact hLT
          · intro h_eq
            have hAε : (A - ε) + ε = A := by simp only [ε, Time] at *; omega
            exact absurd (by simp only; rw [hAε, h_eq]) hNEQ

      include H_arrival_times_are_consistent H_arr_seq_is_a_set
        H_jobs_come_from_arrival_sequence H_completed_jobs_dont_execute
        H_job_cost_le_task_cost H_tsk_in_ts
        H_family_of_proper_arrival_curves H_R_is_maximum
        H_j_arrives H_job_of_tsk H_job_cost_positive in
      include H_arrival_times_are_consistent H_arr_seq_is_a_set H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_work_conserving H_sequential_jobs H_job_cost_le_task_cost H_all_jobs_from_taskset H_family_of_proper_arrival_curves H_tsk_in_ts H_proper_job_lock_in_service H_proper_task_lock_in_service H_priority_is_reflexive H_priority_is_transitive H_priority_inversion_is_bounded H_L_positive H_fixed_point H_R_is_maximum H_j_arrives H_job_of_tsk H_job_cost_positive H_A_is_in_abstract_search_space in
      theorem correct_search_space :
          ∃ F,
            A + F = task_request_bound_function task_cost max_arrivals tsk (A + ε)
                    - (task_cost tsk - task_lock_in_service tsk)
                    + (priority_inversion_bound +
                       total_ohep_request_bound_function_FP task_cost higher_eq_priority max_arrivals ts tsk (A + F)) ∧
            F + (task_cost tsk - task_lock_in_service tsk) ≤ R := by
        have h_concrete : is_in_search_space_FP' task_cost max_arrivals tsk L A := by
          unfold is_in_search_space are_not_equivalent_at_values_less_than at H_A_is_in_abstract_search_space
          rcases H_A_is_in_abstract_search_space with rfl | ⟨hPOS, hLT, x, _, hNEQ⟩
          · constructor
            · exact H_L_positive
            · have h0 := Prosa.Classic.Model.Schedule.Uni.Limited.Rbf.RBF.task_rbf_0_zero
                task_cost job_task arr_seq tsk max_arrivals (H_family_of_proper_arrival_curves tsk H_tsk_in_ts)
              have h1 := Prosa.Classic.Model.Schedule.Uni.Limited.Rbf.RBF.task_rbf_1_ge_task_cost
                task_cost job_arrival job_task arr_seq H_arrival_times_are_consistent
                tsk max_arrivals (H_family_of_proper_arrival_curves tsk H_tsk_in_ts) j H_j_arrives H_job_of_tsk
              have h_jc_le : job_cost j ≤ task_cost tsk := by
                have := H_job_cost_le_task_cost j H_j_arrives
                simp only [job_cost_le_task_cost, H_job_of_tsk] at this; exact this
              intro h_eq; rw [h0] at h_eq
              have h_eps : (0 : Time) + ε = 1 := by simp [ε, Time]
              rw [h_eps] at h_eq
              have h_trb1_0 := h_eq.symm
              have h_tc_le : task_cost tsk ≤ 0 := by
                have := h1; rw [h_trb1_0] at this; exact this
              have h_jc_0 := Nat.le_zero.mp (Nat.le_trans h_jc_le h_tc_le)
              simp only [job_cost_positive] at H_job_cost_positive
              rw [h_jc_0] at H_job_cost_positive
              exact absurd H_job_cost_positive (by decide)
          · constructor
            · exact hLT
            · intro h_eq
              have hAε : (A - ε) + ε = A := by simp only [ε, Time] at *; omega
              exact absurd (by simp only; rw [hAε, h_eq]) hNEQ
        obtain ⟨F, hFIX, hLE⟩ := H_R_is_maximum A h_concrete
        refine ⟨F, ?_, hLE⟩
        conv_rhs at hFIX =>
          rw [show ∀ (a b c : Nat), a + b + c = b + (a + c) from fun a b c => by omega]
        exact hFIX

    end SolutionOfResponseTimeReccurenceExists

  end FillingOutHypothesesOfAbstractRTATheorem

  include H_arrival_times_are_consistent H_arr_seq_is_a_set
    H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute
    H_completed_jobs_dont_execute H_work_conserving H_sequential_jobs
    H_job_cost_le_task_cost H_all_jobs_from_taskset
    H_family_of_proper_arrival_curves H_tsk_in_ts
    H_proper_job_lock_in_service H_proper_task_lock_in_service
    H_priority_is_reflexive H_priority_inversion_is_bounded
    H_L_positive H_fixed_point H_R_is_maximum in
  include H_arrival_times_are_consistent H_arr_seq_is_a_set H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_work_conserving H_sequential_jobs H_job_cost_le_task_cost H_all_jobs_from_taskset H_family_of_proper_arrival_curves H_tsk_in_ts H_proper_job_lock_in_service H_proper_task_lock_in_service H_priority_is_reflexive H_priority_is_transitive H_priority_inversion_is_bounded H_L_positive H_fixed_point H_R_is_maximum in
  theorem uniprocessor_response_time_bound_fp :
      response_time_bounded_by' job_arrival job_cost job_task arr_seq sched tsk R := by
    intro j ARR TSK
    by_cases POS : job_cost j > 0
    · have hPOS : job_cost_positive job_cost j := by simp only [job_cost_positive]; exact POS
      have hFP_refl : JLFP_is_reflexive (FP_to_JLFP job_task higher_eq_priority) :=
        fun x => H_priority_is_reflexive (job_task x)
      have hFP_trans : JLFP_is_transitive (FP_to_JLFP job_task higher_eq_priority) :=
        fun y x z hxy hyz => H_priority_is_transitive (job_task y) (job_task x) (job_task z) hxy hyz
      have hFP_seq : JLFP_respects_sequential_jobs job_task job_arrival (FP_to_JLFP job_task higher_eq_priority) :=
        any_reflexive_FP_respects_sequential_jobs job_arrival job_task higher_eq_priority H_priority_is_reflexive
      -- Build abstract task interference bound
      have h_task_interf_bounded :
          ∀ j' R₀ t1 t2,
            arrives_in arr_seq j' → job_task j' = tsk →
            t1 + R₀ < t2 → ¬ completed_by job_cost sched j' (t1 + R₀) →
            Prosa.Classic.Model.Schedule.Uni.Limited.Abstract_RTA.Definitions.busy_interval
              job_arrival job_cost sched
              (interference' job_task sched higher_eq_priority)
              (interfering_workload' job_cost job_task arr_seq sched higher_eq_priority)
              j' t1 t2 →
            AbstractSeqRTA.cumul_task_interference job_task sched arr_seq
              (interference' job_task sched higher_eq_priority)
              tsk t2 t1 (t1 + R₀) ≤
            priority_inversion_bound +
              total_ohep_request_bound_function_FP task_cost higher_eq_priority max_arrivals ts tsk R₀ := by
        intro j' R₀ t1' t2' ARR' TSK' hRLT' NCOMPL' BUSY'
        have POS' : job_cost j' > 0 := by
          by_contra h; push_neg at h; exact NCOMPL' (by simp only [completed_by, Time] at *; omega)
        have hBI' := (Prosa.Classic.Model.Schedule.Uni.Limited.Jlfp_instantiation.JLFPInstantiation.instantiated_busy_interval_equivalent_edf_busy_interval
          job_arrival job_cost job_task arr_seq H_arrival_times_are_consistent H_arr_seq_is_a_set
          sched H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute
          H_sequential_jobs (FP_to_JLFP job_task higher_eq_priority)
          hFP_refl hFP_trans hFP_seq tsk j' ARR' TSK' POS' t1' t2').mpr BUSY'
        have h_j_in := arrived_between_implies_in_arrivals job_arrival arr_seq H_arrival_times_are_consistent
          j' 0 t2' ARR' ⟨Nat.zero_le _, hBI'.1.2.2.2.2⟩
        have h_interf_eq : ∀ j₀ t₀,
          interference' job_task sched higher_eq_priority j₀ t₀ =
          Prosa.Classic.Model.Schedule.Uni.Limited.Jlfp_instantiation.JLFPInstantiation.interference
            (FP_to_JLFP job_task higher_eq_priority) sched j₀ t₀ := fun _ _ => rfl
        unfold AbstractSeqRTA.cumul_task_interference
        simp_rw [h_interf_eq]
        rw [Prosa.Classic.Model.Schedule.Uni.Limited.Jlfp_instantiation.JLFPInstantiation.cumulative_task_interference_split
          job_arrival job_cost job_task arr_seq H_arrival_times_are_consistent H_arr_seq_is_a_set
          sched H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute
          H_sequential_jobs (FP_to_JLFP job_task higher_eq_priority)
          hFP_refl hFP_trans hFP_seq tsk j' t1' (t1' + R₀) t2' TSK' h_j_in NCOMPL']
        have hQT1 := hBI'.1.2.1
        rw [Prosa.Classic.Model.Schedule.Uni.Limited.Jlfp_instantiation.JLFPInstantiation.instantiated_cumulative_interference_of_hep_tasks_equal_total_interference_of_hep_tasks
          job_arrival job_cost job_task arr_seq H_arrival_times_are_consistent H_arr_seq_is_a_set
          sched H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute
          H_sequential_jobs (FP_to_JLFP job_task higher_eq_priority)
          hFP_refl hFP_trans hFP_seq tsk j' ARR' TSK' t1' (t1' + R₀) hQT1]
        exact instantiated_task_interference_is_bounded task_cost job_arrival job_cost job_task
          arr_seq H_arrival_times_are_consistent H_arr_seq_is_a_set sched
          H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute
          H_work_conserving H_sequential_jobs H_job_cost_le_task_cost ts H_all_jobs_from_taskset
          max_arrivals H_family_of_proper_arrival_curves tsk H_tsk_in_ts
          job_lock_in_service task_lock_in_service
          H_proper_job_lock_in_service H_proper_task_lock_in_service
          higher_eq_priority H_priority_is_reflexive H_priority_is_transitive
          priority_inversion_bound H_priority_inversion_is_bounded
          L H_L_positive H_fixed_point R H_R_is_maximum
          j' R₀ t1' t2' ARR' TSK' hRLT' NCOMPL' BUSY'
      -- Apply uniprocessor_response_time_bound_seq
      exact AbstractSeqRTA.uniprocessor_response_time_bound_seq
        task_cost job_arrival job_cost job_task
        arr_seq H_arrival_times_are_consistent H_arr_seq_is_a_set
        sched H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute
        H_job_cost_le_task_cost ts H_all_jobs_from_taskset
        max_arrivals H_family_of_proper_arrival_curves
        tsk H_tsk_in_ts job_lock_in_service task_lock_in_service
        H_proper_job_lock_in_service H_proper_task_lock_in_service
        (interference' job_task sched higher_eq_priority)
        (interfering_workload' job_cost job_task arr_seq sched higher_eq_priority)
        (instantiated_i_and_w_are_consistent_with_schedule task_cost job_arrival job_cost job_task
          arr_seq H_arrival_times_are_consistent H_arr_seq_is_a_set sched
          H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute
          H_work_conserving H_sequential_jobs H_job_cost_le_task_cost
          ts H_all_jobs_from_taskset max_arrivals H_family_of_proper_arrival_curves
          tsk H_tsk_in_ts job_lock_in_service task_lock_in_service
          H_proper_job_lock_in_service H_proper_task_lock_in_service
          higher_eq_priority H_priority_is_reflexive H_priority_is_transitive
          priority_inversion_bound H_priority_inversion_is_bounded
          L H_L_positive H_fixed_point R H_R_is_maximum)
        H_sequential_jobs
        (instantiated_interference_and_workload_consistent_with_sequential_jobs task_cost job_arrival job_cost job_task
          arr_seq H_arrival_times_are_consistent H_arr_seq_is_a_set sched
          H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute
          H_work_conserving H_sequential_jobs H_job_cost_le_task_cost ts H_all_jobs_from_taskset
          max_arrivals H_family_of_proper_arrival_curves
          tsk H_tsk_in_ts job_lock_in_service task_lock_in_service
          H_proper_job_lock_in_service H_proper_task_lock_in_service
          higher_eq_priority H_priority_is_reflexive H_priority_is_transitive
          priority_inversion_bound H_priority_inversion_is_bounded
          L H_L_positive H_fixed_point R H_R_is_maximum)
        L
        (instantiated_busy_intervals_are_bounded task_cost job_arrival job_cost job_task
          arr_seq H_arrival_times_are_consistent H_arr_seq_is_a_set sched
          H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute
          H_work_conserving H_sequential_jobs H_job_cost_le_task_cost ts H_all_jobs_from_taskset
          max_arrivals H_family_of_proper_arrival_curves tsk H_tsk_in_ts
          job_lock_in_service task_lock_in_service
          H_proper_job_lock_in_service H_proper_task_lock_in_service
          higher_eq_priority H_priority_is_reflexive H_priority_is_transitive
          priority_inversion_bound H_priority_inversion_is_bounded
          L H_L_positive H_fixed_point R H_R_is_maximum)
        (fun _ A R₀ => priority_inversion_bound +
          total_ohep_request_bound_function_FP task_cost higher_eq_priority max_arrivals ts tsk R₀)
        h_task_interf_bounded
        R
        (fun A hA => correct_search_space task_cost job_arrival job_cost job_task
          arr_seq H_arrival_times_are_consistent H_arr_seq_is_a_set sched
          H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute
          H_work_conserving H_sequential_jobs H_job_cost_le_task_cost ts H_all_jobs_from_taskset
          max_arrivals H_family_of_proper_arrival_curves tsk H_tsk_in_ts
          job_lock_in_service task_lock_in_service
          H_proper_job_lock_in_service H_proper_task_lock_in_service
          higher_eq_priority H_priority_is_reflexive H_priority_is_transitive
          priority_inversion_bound H_priority_inversion_is_bounded
          L H_L_positive H_fixed_point R H_R_is_maximum
          j ARR TSK hPOS A hA)
        j ARR TSK
    · push_neg at POS
      have hzero : job_cost j = 0 := Nat.eq_zero_of_le_zero POS
      unfold is_response_time_bound_of_job completed_by
      simp [hzero]

end AbstractResponseTimeAnalysisForFP

end AbstractRTAforFPwithArrivalCurves

end Prosa.Classic.Model.Schedule.Uni.Limited.Fixed_priority.Response_time_bound
