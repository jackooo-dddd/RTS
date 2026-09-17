-- Translated from: ../rt-proofs/classic/model/schedule/uni/limited/edf/response_time_bound.v
import Prosa.Classic.Util.All
import Prosa.Classic.Model.Arrival.Basic.Job
import Prosa.Classic.Model.Schedule.Uni.Service
import Prosa.Classic.Model.Schedule.Uni.Limited.Platform.Definitions
import Prosa.Classic.Model.Arrival.Curves.Bounds
import Prosa.Classic.Analysis.Uni.Arrival_curves.Workload_bound
import Prosa.Classic.Model.Arrival.Basic.Arrival_sequence
import Prosa.Classic.Model.Schedule.Uni.Schedule
import Prosa.Classic.Model.Schedule.Uni.Workload
import Prosa.Classic.Model.Schedule.Uni.Response_time
import Prosa.Classic.Model.Schedule.Uni.Limited.Schedule
import Prosa.Classic.Model.Schedule.Uni.Limited.Busy_interval
import Prosa.Classic.Model.Priority
import Prosa.Classic.Model.Schedule.Uni.Basic.Platform
import Prosa.Classic.Model.Schedule.Uni.Limited.Abstract_RTA.Definitions
import Prosa.Classic.Model.Schedule.Uni.Limited.Abstract_RTA.Abstract_seq_rta
import Prosa.Classic.Model.Schedule.Uni.Limited.Jlfp_instantiation
import Prosa.Classic.Model.Schedule.Uni.Limited.Rbf
import Prosa.Util.Epsilon
import Mathlib.Tactic

namespace Prosa.Classic.Model.Schedule.Uni.Limited.Edf.Response_time_bound

open Prosa.Classic.Model.Time
open Prosa.Classic.Model.Arrival.Basic.Job
open Prosa.Classic.Model.Arrival.Curves.Bounds.ArrivalCurves
open Prosa.Classic.Model.Schedule.Uni.Schedule
open Prosa.Classic.Model.Schedule.Uni.Workload
open Prosa.Classic.Model.Schedule.Uni.Service
open Prosa.Classic.Model.Schedule.Uni.Response_time.ResponseTime
open Prosa.Classic.Model.Schedule.Uni.Limited.Platform.Definitions.LimitedPreemptionPlatform
open Prosa.Classic.Model.Schedule.Uni.Limited.Schedule
open Prosa.Classic.Model.Schedule.Uni.Limited.Busy_interval.BusyIntervalJLFP
open Prosa.Classic.Model.Schedule.Uni.Basic.Platform.Platform
open Prosa.Classic.Model.Priority
open Prosa.Classic.Analysis.Uni.Arrival_curves.Workload_bound.MaxArrivalsWorkloadBound
open Prosa.Classic.Model.Arrival.Basic.Arrival_sequence
open Prosa.Classic.Model.Schedule.Uni.Limited.Abstract_RTA.Abstract_seq_rta
open Prosa.Util.Epsilon

namespace AbstractRTAforEDFwithArrivalCurves

section AbstractResponseTimeAnalysisForEDF

  variable {Task : Type _} [DecidableEq Task]
  variable (task_cost : Task → Time)
  variable (task_deadline : Task → Time)

  variable {Job : Type _} [DecidableEq Job]
  variable (job_arrival : Job → Time)
  variable (job_cost : Job → Time)
  variable (job_task : Job → Task)

  private abbrev D := task_deadline
  private abbrev job_relative_deadline := fun j => task_deadline (job_task j)

  variable (arr_seq : arrival_sequence Job)
  variable (H_arrival_times_are_consistent :
    arrival_times_are_consistent job_arrival arr_seq)
  variable (H_arr_seq_is_a_set : arrival_sequence_is_a_set arr_seq)

  variable (sched : schedule Job)
  variable (H_jobs_come_from_arrival_sequence :
    jobs_come_from_arrival_sequence sched arr_seq)

  variable (H_jobs_must_arrive_to_execute :
    jobs_must_arrive_to_execute job_arrival sched)
  variable (H_completed_jobs_dont_execute :
    completed_jobs_dont_execute job_cost sched)

  variable (H_work_conserving :
    Prosa.Classic.Model.Schedule.Uni.Limited.Platform.Definitions.LimitedPreemptionPlatform.work_conserving
      job_arrival job_cost arr_seq sched)

  variable (H_sequential_jobs :
    sequential_jobs job_arrival job_cost sched job_task)

  variable (H_job_cost_le_task_cost :
    cost_of_jobs_from_arrival_sequence_le_task_cost
      task_cost job_cost job_task arr_seq)

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
    proper_task_lock_in_service
      task_cost job_task arr_seq job_lock_in_service task_lock_in_service tsk)

  private abbrev EDF_priority : JLFP_policy Job :=
    EDF job_arrival (fun j => task_deadline (job_task j))

  private abbrev rbf := task_request_bound_function task_cost max_arrivals
  private abbrev task_rbf := task_request_bound_function task_cost max_arrivals tsk
  private abbrev total_rbf := total_request_bound_function task_cost max_arrivals ts

  variable (priority_inversion_bound : Time)
  variable (H_priority_inversion_is_bounded :
    priority_inversion_is_bounded_by
      job_arrival job_cost job_task arr_seq sched
      (EDF job_arrival (fun j => task_deadline (job_task j)))
      tsk priority_inversion_bound)

  variable (L : Time)
  variable (H_L_positive : L > 0)
  variable (H_fixed_point :
    L = total_request_bound_function task_cost max_arrivals ts L)

  private noncomputable def bound_on_total_hep_workload (A Δ : Time) : Nat :=
    ((ts.filter (fun tsk_o => decide (tsk_o ≠ tsk))).map
      (fun tsk_o => task_request_bound_function task_cost max_arrivals tsk_o
        (min ((A + ε) + task_deadline tsk - task_deadline tsk_o) Δ))).sum

  def task_rbf_changes_at (A : Time) : Bool :=
    decide (task_request_bound_function task_cost max_arrivals tsk A ≠
            task_request_bound_function task_cost max_arrivals tsk (A + ε))

  def bound_on_total_hep_workload_changes_at (A : Time) : Bool :=
    ts.any (fun tsko =>
      decide (tsk ≠ tsko) &&
      decide (task_request_bound_function task_cost max_arrivals tsko
                (A + task_deadline tsk - task_deadline tsko) ≠
              task_request_bound_function task_cost max_arrivals tsko
                ((A + ε) + task_deadline tsk - task_deadline tsko)))

  private abbrev is_in_search_space (A : Time) : Bool :=
    decide (A < L) &&
      (task_rbf_changes_at task_cost max_arrivals tsk A ||
       bound_on_total_hep_workload_changes_at task_cost task_deadline ts max_arrivals tsk A)

  variable (R : Nat)
  variable (H_R_is_maximum :
    ∀ A,
      is_in_search_space task_cost task_deadline ts max_arrivals tsk L A = true →
      ∃ F,
        A + F = priority_inversion_bound
                + (task_request_bound_function task_cost max_arrivals tsk (A + ε) -
                   (task_cost tsk - task_lock_in_service tsk))
                + bound_on_total_hep_workload task_cost task_deadline ts max_arrivals tsk A (A + F) ∧
        F + (task_cost tsk - task_lock_in_service tsk) ≤ R)

  section FillingOutHypothesesOfAbstractRTATheorem

    include H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute
      H_completed_jobs_dont_execute H_work_conserving H_sequential_jobs in
    include H_arrival_times_are_consistent H_arr_seq_is_a_set H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_work_conserving H_sequential_jobs H_job_cost_le_task_cost H_all_jobs_from_taskset H_family_of_proper_arrival_curves H_tsk_in_ts H_proper_job_lock_in_service H_proper_task_lock_in_service H_priority_inversion_is_bounded H_L_positive H_fixed_point H_R_is_maximum in
    theorem instantiated_i_and_w_are_coherent_with_schedule :
        Prosa.Classic.Model.Schedule.Uni.Limited.Abstract_RTA.Definitions.work_conserving
          job_arrival job_cost job_task arr_seq sched tsk
          (fun j t => Prosa.Classic.Model.Schedule.Uni.Limited.Jlfp_instantiation.JLFPInstantiation.interference
            (EDF job_arrival (fun j => task_deadline (job_task j))) sched j t)
          (fun j t => Prosa.Classic.Model.Schedule.Uni.Limited.Jlfp_instantiation.JLFPInstantiation.interfering_workload
            (EDF job_arrival (fun j => task_deadline (job_task j))) job_cost arr_seq sched j t) := by
      intro j t1 t2 t ARR TSK POS BUSY ⟨hLE, hLT⟩
      -- Derive JLFP properties for EDF
      have hEDF_refl : JLFP_is_reflexive (EDF job_arrival (fun j => task_deadline (job_task j))) :=
        EDF_is_reflexive job_arrival (fun j => task_deadline (job_task j))
      have hEDF_trans : JLFP_is_transitive (EDF job_arrival (fun j => task_deadline (job_task j))) :=
        EDF_is_transitive job_arrival (fun j => task_deadline (job_task j))
      have hEDF_seq : JLFP_respects_sequential_jobs job_task job_arrival (EDF job_arrival (fun j => task_deadline (job_task j))) :=
        EDF_respects_sequential_jobs task_deadline job_arrival job_task
      -- Convert abstract busy interval to concrete
      have hBI := (Prosa.Classic.Model.Schedule.Uni.Limited.Jlfp_instantiation.JLFPInstantiation.instantiated_busy_interval_equivalent_edf_busy_interval
        job_arrival job_cost job_task arr_seq H_arrival_times_are_consistent H_arr_seq_is_a_set
        sched H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute
        H_sequential_jobs (EDF job_arrival (fun j => task_deadline (job_task j)))
        hEDF_refl hEDF_trans hEDF_seq tsk j ARR TSK POS t1 t2).mpr BUSY
      constructor
      · -- Forward: ¬ interference → scheduled
        intro hNI
        simp only [Prosa.Classic.Model.Schedule.Uni.Limited.Jlfp_instantiation.JLFPInstantiation.interference,
          Bool.not_eq_true, Bool.or_eq_false_iff] at hNI
        obtain ⟨hPI, hHP⟩ := hNI
        cases h : sched t with
        | none =>
          exfalso
          exact not_quiet_implies_not_idle job_arrival job_cost job_task arr_seq
            H_arrival_times_are_consistent sched H_jobs_come_from_arrival_sequence
            (EDF job_arrival (fun j => task_deadline (job_task j)))
            tsk j ARR TSK POS
            H_work_conserving H_completed_jobs_dont_execute
            H_jobs_must_arrive_to_execute hEDF_refl hEDF_trans
            t1 t2 hBI.1 t ⟨hLE, hLT⟩ (by simp [is_idle, h])
        | some s =>
          simp only [Prosa.Classic.Model.Schedule.Uni.Limited.Busy_interval.BusyIntervalJLFP.is_priority_inversion, h] at hPI
          simp only [Prosa.Classic.Model.Schedule.Uni.Limited.Jlfp_instantiation.JLFPInstantiation.is_interference_from_another_job_with_higher_eq_priority, h] at hHP
          have hEDF_sj : EDF job_arrival (fun j => task_deadline (job_task j)) s j = true := by
            by_contra hc; push_neg at hc; simp [hc] at hPI
          simp [hEDF_sj] at hHP
          subst hHP; simp [scheduled_at, h]
      · -- Backward: scheduled → ¬ interference
        intro hSCHED
        simp only [Prosa.Classic.Model.Schedule.Uni.Limited.Jlfp_instantiation.JLFPInstantiation.interference,
          Bool.not_eq_true, Bool.or_eq_false_iff]
        cases h : sched t with
        | none => simp [scheduled_at, h] at hSCHED
        | some s =>
          have hsj : s = j := by simp [scheduled_at, h] at hSCHED; exact hSCHED
          subst hsj
          constructor
          · simp [Prosa.Classic.Model.Schedule.Uni.Limited.Busy_interval.BusyIntervalJLFP.is_priority_inversion,
              h]
            exact hEDF_refl s
          · simp [Prosa.Classic.Model.Schedule.Uni.Limited.Jlfp_instantiation.JLFPInstantiation.is_interference_from_another_job_with_higher_eq_priority,
              h]

    include H_arrival_times_are_consistent H_arr_seq_is_a_set
      H_jobs_come_from_arrival_sequence H_completed_jobs_dont_execute
      H_sequential_jobs in
    include H_arrival_times_are_consistent H_arr_seq_is_a_set H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_work_conserving H_sequential_jobs H_job_cost_le_task_cost H_all_jobs_from_taskset H_family_of_proper_arrival_curves H_tsk_in_ts H_proper_job_lock_in_service H_proper_task_lock_in_service H_priority_inversion_is_bounded H_L_positive H_fixed_point H_R_is_maximum in
    theorem instantiated_interference_and_workload_consistent_with_sequential_jobs :
        ∀ j t1 t2,
          arrives_in arr_seq j →
          job_task j = tsk →
          job_cost j > 0 →
          Prosa.Classic.Model.Schedule.Uni.Limited.Abstract_RTA.Definitions.busy_interval
            job_arrival job_cost sched
            (fun j t => Prosa.Classic.Model.Schedule.Uni.Limited.Jlfp_instantiation.JLFPInstantiation.interference
              (EDF job_arrival (fun j => task_deadline (job_task j))) sched j t)
            (fun j t => Prosa.Classic.Model.Schedule.Uni.Limited.Jlfp_instantiation.JLFPInstantiation.interfering_workload
              (EDF job_arrival (fun j => task_deadline (job_task j))) job_cost arr_seq sched j t)
            j t1 t2 →
          workload_of_jobs job_cost (jobs_arrived_between arr_seq 0 t1)
            (fun j_other => decide (job_task j_other = tsk)) =
          service_of_jobs sched (jobs_arrived_between arr_seq 0 t1)
            (fun j_other => decide (job_task j_other = tsk)) 0 t1 := by
      intro j t1 t2 ARR TSK POS BUSY
      -- Derive JLFP properties for EDF
      have hEDF_refl : JLFP_is_reflexive (EDF job_arrival (fun j => task_deadline (job_task j))) :=
        EDF_is_reflexive job_arrival (fun j => task_deadline (job_task j))
      have hEDF_trans : JLFP_is_transitive (EDF job_arrival (fun j => task_deadline (job_task j))) :=
        EDF_is_transitive job_arrival (fun j => task_deadline (job_task j))
      have hEDF_seq : JLFP_respects_sequential_jobs job_task job_arrival (EDF job_arrival (fun j => task_deadline (job_task j))) :=
        EDF_respects_sequential_jobs task_deadline job_arrival job_task
      -- Convert abstract busy interval to concrete
      have hBI := (Prosa.Classic.Model.Schedule.Uni.Limited.Jlfp_instantiation.JLFPInstantiation.instantiated_busy_interval_equivalent_edf_busy_interval
        job_arrival job_cost job_task arr_seq H_arrival_times_are_consistent H_arr_seq_is_a_set
        sched H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute
        H_sequential_jobs (EDF job_arrival (fun j => task_deadline (job_task j)))
        hEDF_refl hEDF_trans hEDF_seq tsk j ARR TSK POS t1 t2).mpr BUSY
      -- Use all_jobs_have_completed_equiv_workload_eq_service
      rw [← all_jobs_have_completed_equiv_workload_eq_service job_arrival job_cost arr_seq
        H_arrival_times_are_consistent sched H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute
        (fun j_other => decide (job_task j_other = tsk)) 0 t1 t1]
      -- Show all same-task jobs arrived before t1 are completed by t1
      intro s hARR_s hTSK_s
      have hARR_s' := in_arrivals_implies_arrived job_arrival arr_seq H_arrival_times_are_consistent s 0 t1 hARR_s
      obtain ⟨⟨_, hqt1, _, hle_arr, _⟩, _⟩ := hBI
      have hS_before := (in_arrivals_implies_arrived_between job_arrival arr_seq H_arrival_times_are_consistent s 0 t1 hARR_s).2
      -- s has EDF priority over j: same task, arrived before t1 ≤ job_arrival j
      have hTSK_eq : job_task s = tsk := by
        simp only [decide_eq_true_eq] at hTSK_s; exact hTSK_s
      have hPRIO : EDF job_arrival (fun j => task_deadline (job_task j)) s j = true := by
        simp only [EDF, hTSK_eq, TSK, decide_eq_true_eq]
        simp only [Time] at *; omega
      exact hqt1 s hARR_s' hPRIO hS_before

    include H_arrival_times_are_consistent H_arr_seq_is_a_set
      H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute
      H_completed_jobs_dont_execute H_work_conserving
      H_job_cost_le_task_cost H_all_jobs_from_taskset
      H_family_of_proper_arrival_curves H_L_positive H_fixed_point in
    theorem instantiated_busy_intervals_are_bounded :
        ∀ j,
          arrives_in arr_seq j →
          job_task j = tsk →
          job_cost j > 0 →
          ∃ t1 t2,
            t1 ≤ job_arrival j ∧ job_arrival j < t2 ∧
            t2 ≤ t1 + L ∧
            busy_interval job_arrival job_cost arr_seq sched
              (EDF job_arrival (fun j => task_deadline (job_task j))) j t1 t2 := by
      intro j ARR TSK POS
      -- EDF is reflexive
      have hREFL : JLFP_is_reflexive (EDF job_arrival (fun j => task_deadline (job_task j))) :=
        EDF_is_reflexive job_arrival (fun j => task_deadline (job_task j))
      -- Workload bound: total_workload t (t + L) ≤ L
      have hWB : ∀ t,
          workload_of_jobs job_cost (jobs_arrived_between arr_seq t (t + L)) (fun _ => true) ≤ L := by
        intro t
        have h_is_arrival_bound : is_arrival_bound_for_taskset job_task arr_seq max_arrivals ts :=
          fun tsk0 IN0 => (H_family_of_proper_arrival_curves tsk0 IN0).1
        calc workload_of_jobs job_cost (jobs_arrived_between arr_seq t (t + L)) (fun _ => true)
            ≤ total_request_bound_function task_cost max_arrivals ts L := by
              apply total_workload_le_total_rbf'' task_cost job_arrival job_cost job_task arr_seq
                H_arrival_times_are_consistent H_arr_seq_is_a_set
              · exact fun j hj => H_job_cost_le_task_cost j hj
              · exact H_all_jobs_from_taskset
              · exact h_is_arrival_bound
          _ = L := H_fixed_point.symm
      -- Use exists_busy_interval_from_total_workload_bound
      apply exists_busy_interval_from_total_workload_bound job_arrival job_cost
        arr_seq H_arrival_times_are_consistent sched H_jobs_come_from_arrival_sequence
        (EDF job_arrival (fun j => task_deadline (job_task j)))
        H_arr_seq_is_a_set
        H_work_conserving H_completed_jobs_dont_execute H_jobs_must_arrive_to_execute
        hREFL L H_L_positive hWB j ARR POS

    include H_arrival_times_are_consistent H_arr_seq_is_a_set
      H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute
      H_completed_jobs_dont_execute H_work_conserving H_sequential_jobs
      H_job_cost_le_task_cost H_all_jobs_from_taskset
      H_family_of_proper_arrival_curves H_priority_inversion_is_bounded in
    include H_arrival_times_are_consistent H_arr_seq_is_a_set H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_work_conserving H_sequential_jobs H_job_cost_le_task_cost H_all_jobs_from_taskset H_family_of_proper_arrival_curves H_tsk_in_ts H_proper_job_lock_in_service H_proper_task_lock_in_service H_priority_inversion_is_bounded H_L_positive H_fixed_point H_R_is_maximum in
    theorem instantiated_task_interference_is_bounded :
        ∀ j R' t1 t2,
          arrives_in arr_seq j →
          job_task j = tsk →
          job_cost j > 0 →
          ¬ completed_by job_cost sched j (t1 + R') →
          busy_interval job_arrival job_cost arr_seq sched
            (EDF job_arrival (fun j => task_deadline (job_task j))) j t1 t2 →
          t1 + R' < t2 →
          cumulative_priority_inversion sched
            (EDF job_arrival (fun j => task_deadline (job_task j))) j t1 (t1 + R') ≤
            priority_inversion_bound ∧
          service_of_jobs sched (jobs_arrived_between arr_seq t1 (t1 + R'))
            (fun jhp => (EDF job_arrival (fun j => task_deadline (job_task j))) jhp j &&
              decide (job_task jhp ≠ job_task j)) t1 (t1 + R') ≤
            bound_on_total_hep_workload task_cost task_deadline ts max_arrivals tsk
              (job_arrival j - t1) R' := by
      intro j R' t1 t2 ARR TSK POS NCOMPL BUSY hRLT
      have hLE_arr : t1 ≤ job_arrival j := BUSY.1.2.2.2.1
      set A := job_arrival j - t1 with hA_def
      have hA_eq : job_arrival j = t1 + A := by simp only [Time] at *; omega
      constructor
      · -- Part 1: cumulative_priority_inversion ≤ priority_inversion_bound
        apply Nat.le_trans _ (H_priority_inversion_is_bounded j ARR TSK POS t1 t2 BUSY.1)
        apply Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.Ico_subset_Ico_right (by simp only [Time] at *; omega))
          (fun _ _ _ => Nat.zero_le _)
      · -- Part 2: service_of_jobs ≤ bound_on_total_hep_workload
        apply Nat.le_trans (service_of_jobs_le_workload job_cost sched
          (jobs_arrived_between arr_seq t1 (t1 + R')) _ H_completed_jobs_dont_execute
          t1 (t1 + R'))
        set l := jobs_arrived_between arr_seq t1 (t1 + R') with hl_def
        -- Simplify predicate using TSK
        suffices h_wkld : workload_of_jobs job_cost l
            (fun jhp => (EDF job_arrival (fun j => task_deadline (job_task j))) jhp j &&
              decide (job_task jhp ≠ tsk)) ≤
            bound_on_total_hep_workload task_cost task_deadline ts max_arrivals tsk A R' by
          convert h_wkld using 2; ext x; simp [TSK]
        unfold bound_on_total_hep_workload workload_of_jobs
        set pred_fn := (fun jhp => (EDF job_arrival (fun j => task_deadline (job_task j))) jhp j && decide (job_task jhp ≠ tsk))
        set filtered := l.filter pred_fn
        set task_list := ts.filter (fun tsk_o => decide (tsk_o ≠ tsk))
        -- Exchange: group filtered jobs by task
        have h_in_task_list : ∀ j0, j0 ∈ filtered → job_task j0 ∈ task_list := by
          intro j0 hj0
          simp only [filtered, pred_fn, List.mem_filter, Bool.and_eq_true, decide_eq_true_eq] at hj0
          simp only [task_list, List.mem_filter, decide_eq_true_eq]
          exact ⟨H_all_jobs_from_taskset j0
            (in_arrivals_implies_arrived job_arrival arr_seq H_arrival_times_are_consistent j0 t1 (t1 + R') hj0.1),
            hj0.2.2⟩
        have exchange : ∀ (jobs : List Job) (groups : List Task),
            (∀ j0, j0 ∈ jobs → job_task j0 ∈ groups) →
            (jobs.map job_cost).sum ≤
            (groups.map (fun g =>
              ((jobs.filter (fun j0 => decide (job_task j0 = g))).map job_cost).sum)).sum := by
          intro jobs groups h_cover
          induction jobs with
          | nil => simp
          | cons hd tl ih =>
            simp only [List.map_cons, List.sum_cons]
            have h_cover_tl := fun j0 hj0 => h_cover j0 (List.mem_cons_of_mem hd hj0)
            have h_rhs :
                (groups.map (fun g =>
                  (((hd :: tl).filter (fun j0 => decide (job_task j0 = g))).map job_cost).sum)).sum =
                (groups.map (fun g =>
                  (if decide (job_task hd = g) then job_cost hd else 0) +
                  ((tl.filter (fun j0 => decide (job_task j0 = g))).map job_cost).sum)).sum := by
              apply congr_arg List.sum
              apply List.map_congr_left; intro g _
              simp only [List.filter_cons]
              cases h : decide (job_task hd = g) <;> simp
            rw [h_rhs, List.sum_map_add]
            have h_hd : job_cost hd ≤
                (groups.map (fun g => if decide (job_task hd = g) then job_cost hd else 0)).sum := by
              have h_mem := h_cover hd List.mem_cons_self
              have h_in : (fun g => if decide (job_task hd = g) then job_cost hd else (0 : ℕ)) (job_task hd) ∈
                  groups.map (fun g => if decide (job_task hd = g) then job_cost hd else 0) :=
                List.mem_map_of_mem h_mem
              simp only [decide_true] at h_in
              exact List.single_le_sum (fun _ _ => Nat.zero_le _) _ h_in
            exact Nat.add_le_add h_hd (ih h_cover_tl)
        have h_exch := exchange filtered task_list h_in_task_list
        apply le_trans h_exch
        apply List.sum_le_sum
        intro tsk_o htsk_o
        simp only [task_list, List.mem_filter, decide_eq_true_eq] at htsk_o
        -- Per-task bound for tsk_o:
        -- (filtered.filter(task=tsk_o)).map(cost).sum ≤ rbf(tsk_o, min(V, R'))
        set V := min ((A + ε) + task_deadline tsk - task_deadline tsk_o) R' with hV_def
        have hV_le : V ≤ R' := Nat.min_le_right _ _
        set l' := jobs_arrived_between arr_seq t1 (t1 + V) with hl'_def
        set l2 := jobs_arrived_between arr_seq (t1 + V) (t1 + R') with hl2_def
        -- Split l = l' ++ l2
        have h_split : l = l' ++ l2 :=
          job_arrived_between_cat arr_seq t1 (t1 + V) (t1 + R') (by simp only [Time] at *; omega) (by simp only [Time] at *; omega)
        -- Rewrite filtered.filter using filter_filter
        have h_ff : filtered.filter (fun j0 => decide (job_task j0 = tsk_o)) =
            l.filter (fun j0 => pred_fn j0 && decide (job_task j0 = tsk_o)) := by
          simp only [filtered]
          simp [List.filter_filter, Bool.and_comm]
        rw [h_ff]
        -- Split l into l' ++ l2 in the filter
        rw [h_split, List.filter_append, List.map_append, List.sum_append]
        -- Show l2 part is empty (EDF forces contradiction)
        have h_l2_empty : (l2.filter (fun j0 => pred_fn j0 && decide (job_task j0 = tsk_o))) = [] := by
          rw [List.filter_eq_nil_iff.mpr]
          intro j0 hj0
          simp only [pred_fn, Bool.and_eq_true, Bool.eq_false_iff, decide_eq_true_eq, not_and]
          intro ⟨hEDF, _⟩ hTask
          simp only [EDF, decide_eq_true_eq] at hEDF
          rw [hTask] at hEDF
          have hj0_arr := in_arrivals_implies_arrived_between job_arrival arr_seq
            H_arrival_times_are_consistent j0 (t1 + V) (t1 + R') hj0
          -- Contradiction: j0 ≥ t1+V and EDF says j0 + D_tsk_o ≤ t1 + A + D_tsk
          exfalso
          rcases Nat.lt_or_ge ((A + ε) + task_deadline tsk - task_deadline tsk_o) R' with hlt | hge
          · have hV_eq : V = (A + ε) + task_deadline tsk - task_deadline tsk_o := by
              rw [hV_def, Nat.min_eq_left (Nat.le_of_lt hlt)]
            -- Build the chain: t1 + V + Dtsko ≤ j_arr + Dtsk
            have h_le := Nat.le_trans (Nat.add_le_add_right hj0_arr.1 (task_deadline tsk_o)) hEDF
            rw [hV_eq, hA_eq, TSK] at h_le; simp only [ε] at h_le
            suffices hsuf : ∀ (a b c d : Nat),
                a + (b + 1 + c - d) + d ≤ a + b + c → False by
              exact hsuf t1 A (task_deadline tsk) (task_deadline tsk_o) h_le
            intro a b c d h; omega
          · have hV_eq : V = R' := by rw [hV_def, Nat.min_eq_right hge]
            have h1 := hj0_arr.1; have h2 := hj0_arr.2
            rw [hV_eq] at h1; simp only [Time] at *; omega
        rw [h_l2_empty, List.map_nil, List.sum_nil, Nat.add_zero]
        -- Now: (l'.filter(pred && task)).map(cost).sum ≤ rbf(tsk_o, V)
        -- Step: drop pred_fn filter (weaker predicate gives larger set)
        calc ((l'.filter (fun j0 => pred_fn j0 && decide (job_task j0 = tsk_o))).map job_cost).sum
            ≤ ((l'.filter (fun j0 => decide (job_task j0 = tsk_o))).map job_cost).sum := by
              have h_sub : (l'.filter (fun j0 => pred_fn j0 && decide (job_task j0 = tsk_o))).Sublist
                  (l'.filter (fun j0 => decide (job_task j0 = tsk_o))) := by
                have := (List.filter_sublist (p := pred_fn) (l := l')).filter
                  (p := fun j0 => decide (job_task j0 = tsk_o))
                rw [List.filter_filter] at this
                convert this using 2; ext x; exact Bool.and_comm _ _
              exact h_sub.map job_cost |>.sum_le_sum (fun _ _ => Nat.zero_le _)
          _ ≤ task_cost tsk_o * (l'.filter (fun j0 => decide (job_task j0 = tsk_o))).length := by
              have h_bound : ∀ x ∈ (l'.filter (fun j0 => decide (job_task j0 = tsk_o))).map job_cost,
                  x ≤ task_cost tsk_o := by
                intro x hx; rw [List.mem_map] at hx
                obtain ⟨j0, hj0_mem, rfl⟩ := hx
                simp only [List.mem_filter, decide_eq_true_eq] at hj0_mem
                have hj0_arrives := in_arrivals_implies_arrived job_arrival arr_seq
                  H_arrival_times_are_consistent j0 t1 (t1 + V) hj0_mem.1
                have : job_cost j0 ≤ task_cost (job_task j0) := H_job_cost_le_task_cost j0 hj0_arrives
                rw [hj0_mem.2] at this; exact this
              have h1 := List.sum_le_card_nsmul
                ((l'.filter (fun j0 => decide (job_task j0 = tsk_o))).map job_cost)
                (task_cost tsk_o) h_bound
              rw [smul_eq_mul, List.length_map] at h1
              rw [Nat.mul_comm]; exact h1
          _ ≤ task_cost tsk_o * max_arrivals tsk_o V := by
              apply Nat.mul_le_mul_left
              have h_bound := (H_family_of_proper_arrival_curves tsk_o htsk_o.1).1
                t1 (t1 + V) (by simp only [Time] at *; omega)
              simp at h_bound; exact h_bound


    section SolutionOfResponseTimeReccurenceExists

      variable (j : Job)
      variable (H_j_arrives : arrives_in arr_seq j)
      variable (H_job_of_tsk : job_task j = tsk)
      variable (H_job_cost_positive : job_cost_positive job_cost j)

      variable (A : Time)

      include H_arrival_times_are_consistent H_arr_seq_is_a_set
        H_jobs_come_from_arrival_sequence H_completed_jobs_dont_execute
        H_job_cost_le_task_cost H_tsk_in_ts
        H_family_of_proper_arrival_curves
        H_j_arrives H_job_of_tsk H_job_cost_positive in
      include H_arrival_times_are_consistent H_arr_seq_is_a_set H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_work_conserving H_sequential_jobs H_job_cost_le_task_cost H_all_jobs_from_taskset H_family_of_proper_arrival_curves H_tsk_in_ts H_proper_job_lock_in_service H_proper_task_lock_in_service H_priority_inversion_is_bounded H_L_positive H_fixed_point H_R_is_maximum H_j_arrives H_job_of_tsk H_job_cost_positive in
      theorem A_is_in_concrete_search_space
          (H_A_is_in_abstract_search_space :
            A = 0 ∨
            (0 < A ∧ A < L ∧
              ∃ x, x < L ∧
                (fun tsk' A' R' =>
                  task_request_bound_function task_cost max_arrivals tsk' (A' + ε) -
                    task_cost tsk' +
                    (priority_inversion_bound +
                      bound_on_total_hep_workload task_cost task_deadline ts max_arrivals tsk A' R'))
                  tsk (A - ε) x ≠
                (fun tsk' A' R' =>
                  task_request_bound_function task_cost max_arrivals tsk' (A' + ε) -
                    task_cost tsk' +
                    (priority_inversion_bound +
                      bound_on_total_hep_workload task_cost task_deadline ts max_arrivals tsk A' R'))
                  tsk A x)) :
          is_in_search_space task_cost task_deadline ts max_arrivals tsk L A = true := by
        rcases H_A_is_in_abstract_search_space with rfl | ⟨hPOS, hLT, x, _, hNEQ⟩
        · -- A = 0: task_rbf changes at 0
          simp only [is_in_search_space, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq]
          refine ⟨H_L_positive, Or.inl ?_⟩
          simp only [task_rbf_changes_at, decide_eq_true_eq]
          have h0 := Prosa.Classic.Model.Schedule.Uni.Limited.Rbf.RBF.task_rbf_0_zero
            task_cost job_task arr_seq tsk max_arrivals (H_family_of_proper_arrival_curves tsk H_tsk_in_ts)
          have h1 := Prosa.Classic.Model.Schedule.Uni.Limited.Rbf.RBF.task_rbf_1_ge_task_cost
            task_cost job_arrival job_task arr_seq H_arrival_times_are_consistent
            tsk max_arrivals (H_family_of_proper_arrival_curves tsk H_tsk_in_ts) j H_j_arrives H_job_of_tsk
          have h_jc_le : job_cost j ≤ task_cost tsk := by
            have : job_cost j ≤ task_cost (job_task j) := H_job_cost_le_task_cost j H_j_arrives
            rw [H_job_of_tsk] at this; exact this
          have h_pos : 0 < task_request_bound_function task_cost max_arrivals tsk (0 + ε) :=
            Nat.lt_of_lt_of_le (by simp only [job_cost_positive] at H_job_cost_positive; exact H_job_cost_positive)
              (Nat.le_trans h_jc_le h1)
          rw [h0]; exact h_pos.ne
        · -- A > 0: by contradiction, both changes_at are false → IBF(A-ε,x) = IBF(A,x)
          simp only [is_in_search_space, Bool.and_eq_true, decide_eq_true_eq]
          refine ⟨hLT, ?_⟩
          by_contra h_not
          apply hNEQ
          simp only [Bool.or_eq_true, not_or, Bool.not_eq_true'] at h_not
          obtain ⟨hRBF_false, hBHW_false⟩ := h_not
          -- Extract: task_rbf A = task_rbf (A + ε)
          have hRBF_eq : task_request_bound_function task_cost max_arrivals tsk A =
              task_request_bound_function task_cost max_arrivals tsk (A + ε) := by
            simp only [task_rbf_changes_at, decide_eq_true_eq, ne_eq, not_not] at hRBF_false
            exact hRBF_false
          -- Extract per-task rbf equalities
          have hBHW_per_task : ∀ tsk_o, tsk_o ∈ ts → tsk_o ≠ tsk →
              task_request_bound_function task_cost max_arrivals tsk_o
                (A + task_deadline tsk - task_deadline tsk_o) =
              task_request_bound_function task_cost max_arrivals tsk_o
                ((A + ε) + task_deadline tsk - task_deadline tsk_o) := by
            intro tsk_o h_in h_neq
            by_contra h_ne
            have h_any : bound_on_total_hep_workload_changes_at task_cost task_deadline ts max_arrivals tsk A = true := by
              simp only [bound_on_total_hep_workload_changes_at]
              exact List.any_of_mem h_in (by simp only [Bool.and_eq_true, decide_eq_true_eq]; exact ⟨h_neq.symm, h_ne⟩)
            rw [h_any] at hBHW_false; exact absurd rfl hBHW_false
          -- Show IBF(A-ε, x) = IBF(A, x)
          simp only
          have hAε : (A - ε) + ε = A := by simp only [ε, Time] at *; omega
          rw [hAε, hRBF_eq]
          -- Remains: pi + bhw(A-ε, x) = pi + bhw(A, x)
          suffices h_bhw : bound_on_total_hep_workload task_cost task_deadline ts max_arrivals tsk (A - ε) x =
              bound_on_total_hep_workload task_cost task_deadline ts max_arrivals tsk A x by rw [h_bhw]
          unfold bound_on_total_hep_workload
          apply congr_arg List.sum; apply List.map_congr_left
          intro tsk_o htsk_o
          simp only [List.mem_filter, decide_eq_true_eq] at htsk_o
          -- Per-task: rbf(tsk_o, min(A + D - D_o, x)) = rbf(tsk_o, min((A+ε) + D - D_o, x))
          rw [show ((A - ε) + ε) = A from hAε]
          have h_eq_rbf := hBHW_per_task tsk_o htsk_o.1 htsk_o.2
          by_cases hcase : (A + ε) + task_deadline tsk - task_deadline tsk_o ≤ x
          · -- Case 1: min(a,x) = a, min(b,x) = b, equal by h_eq_rbf
            rw [Nat.min_eq_left (by simp only [ε, Time] at *; omega : A + task_deadline tsk - task_deadline tsk_o ≤ x),
                Nat.min_eq_left hcase]
            exact h_eq_rbf
          · -- Case 2: both mins = x
            push_neg at hcase
            rw [Nat.min_eq_right (by simp only [ε, Time] at *; omega), Nat.min_eq_right (by simp only [ε, Time] at *; omega)]

      include H_arrival_times_are_consistent H_arr_seq_is_a_set
        H_jobs_come_from_arrival_sequence H_completed_jobs_dont_execute
        H_job_cost_le_task_cost H_tsk_in_ts
        H_family_of_proper_arrival_curves H_R_is_maximum
        H_j_arrives H_job_of_tsk H_job_cost_positive in
      theorem correct_search_space
          (H_A_is_in_abstract_search_space :
            is_in_search_space task_cost task_deadline ts max_arrivals tsk L A = true) :
          ∃ F,
            A + F = task_request_bound_function task_cost max_arrivals tsk (A + ε) -
                    (task_cost tsk - task_lock_in_service tsk) +
                    (priority_inversion_bound +
                     bound_on_total_hep_workload task_cost task_deadline ts max_arrivals tsk A (A + F)) ∧
            F + (task_cost tsk - task_lock_in_service tsk) ≤ R := by
        obtain ⟨F, hFIX, hNEQ⟩ := H_R_is_maximum A H_A_is_in_abstract_search_space
        exact ⟨F, by rw [show ∀ (a b c : Nat), a + (b + c) = b + a + c from fun a b c => by omega]; exact hFIX, hNEQ⟩

    end SolutionOfResponseTimeReccurenceExists

  end FillingOutHypothesesOfAbstractRTATheorem

  include H_arrival_times_are_consistent H_arr_seq_is_a_set
    H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute
    H_completed_jobs_dont_execute H_work_conserving H_sequential_jobs
    H_job_cost_le_task_cost H_all_jobs_from_taskset
    H_family_of_proper_arrival_curves H_tsk_in_ts
    H_proper_job_lock_in_service H_proper_task_lock_in_service
    H_priority_inversion_is_bounded H_L_positive H_fixed_point H_R_is_maximum in
  include H_arrival_times_are_consistent H_arr_seq_is_a_set H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_work_conserving H_sequential_jobs H_job_cost_le_task_cost H_all_jobs_from_taskset H_family_of_proper_arrival_curves H_tsk_in_ts H_proper_job_lock_in_service H_proper_task_lock_in_service H_priority_inversion_is_bounded H_L_positive H_fixed_point H_R_is_maximum in
  theorem uniprocessor_response_time_bound_edf :
      is_response_time_bound_of_task job_arrival job_cost job_task arr_seq sched tsk R := by
    intro j ARR TSK
    by_cases POS : job_cost j > 0
    · -- Apply abstract RTA framework with JLFP interference instantiation
      have hPOS : job_cost_positive job_cost j := by simp only [job_cost_positive]; exact POS
      have hEDF_refl : JLFP_is_reflexive (EDF job_arrival (fun j => task_deadline (job_task j))) :=
        EDF_is_reflexive job_arrival (fun j => task_deadline (job_task j))
      have hEDF_trans : JLFP_is_transitive (EDF job_arrival (fun j => task_deadline (job_task j))) :=
        EDF_is_transitive job_arrival (fun j => task_deadline (job_task j))
      have hEDF_seq : JLFP_respects_sequential_jobs job_task job_arrival (EDF job_arrival (fun j => task_deadline (job_task j))) :=
        EDF_respects_sequential_jobs task_deadline job_arrival job_task
      -- Build abstract task interference bound
      have h_task_interf_bounded :
          ∀ j' R₀ t1 t2,
            arrives_in arr_seq j' → job_task j' = tsk →
            t1 + R₀ < t2 → ¬ completed_by job_cost sched j' (t1 + R₀) →
            Prosa.Classic.Model.Schedule.Uni.Limited.Abstract_RTA.Definitions.busy_interval
              job_arrival job_cost sched
              (fun j t => Prosa.Classic.Model.Schedule.Uni.Limited.Jlfp_instantiation.JLFPInstantiation.interference
                (EDF job_arrival (fun j => task_deadline (job_task j))) sched j t)
              (fun j t => Prosa.Classic.Model.Schedule.Uni.Limited.Jlfp_instantiation.JLFPInstantiation.interfering_workload
                (EDF job_arrival (fun j => task_deadline (job_task j))) job_cost arr_seq sched j t)
              j' t1 t2 →
            AbstractSeqRTA.cumul_task_interference job_task sched arr_seq
              (fun j t => Prosa.Classic.Model.Schedule.Uni.Limited.Jlfp_instantiation.JLFPInstantiation.interference
                (EDF job_arrival (fun j => task_deadline (job_task j))) sched j t)
              tsk t2 t1 (t1 + R₀) ≤
            priority_inversion_bound +
              bound_on_total_hep_workload task_cost task_deadline ts max_arrivals tsk
                (job_arrival j' - t1) R₀ := by
        intro j' R₀ t1' t2' ARR' TSK' hRLT' NCOMPL' BUSY'
        have POS' : job_cost j' > 0 := by
          by_contra h; push_neg at h; exact NCOMPL' (by simp only [completed_by, Time] at *; omega)
        have hBI' := (Prosa.Classic.Model.Schedule.Uni.Limited.Jlfp_instantiation.JLFPInstantiation.instantiated_busy_interval_equivalent_edf_busy_interval
          job_arrival job_cost job_task arr_seq H_arrival_times_are_consistent H_arr_seq_is_a_set
          sched H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute
          H_sequential_jobs (EDF job_arrival (fun j => task_deadline (job_task j)))
          hEDF_refl hEDF_trans hEDF_seq tsk j' ARR' TSK' POS' t1' t2').mpr BUSY'
        have h_j_in := arrived_between_implies_in_arrivals job_arrival arr_seq H_arrival_times_are_consistent
          j' 0 t2' ARR' ⟨Nat.zero_le _, hBI'.1.2.2.2.2⟩
        unfold AbstractSeqRTA.cumul_task_interference
        rw [show (fun j t => Prosa.Classic.Model.Schedule.Uni.Limited.Jlfp_instantiation.JLFPInstantiation.interference
              (EDF job_arrival (fun j => task_deadline (job_task j))) sched j t) =
          Prosa.Classic.Model.Schedule.Uni.Limited.Jlfp_instantiation.JLFPInstantiation.interference
            (EDF job_arrival (fun j => task_deadline (job_task j))) sched from rfl]
        rw [Prosa.Classic.Model.Schedule.Uni.Limited.Jlfp_instantiation.JLFPInstantiation.cumulative_task_interference_split
          job_arrival job_cost job_task arr_seq H_arrival_times_are_consistent H_arr_seq_is_a_set
          sched H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute
          H_sequential_jobs (EDF job_arrival (fun j => task_deadline (job_task j)))
          hEDF_refl hEDF_trans hEDF_seq tsk j' t1' (t1' + R₀) t2' TSK' h_j_in NCOMPL']
        have hQT1 := hBI'.1.2.1
        rw [Prosa.Classic.Model.Schedule.Uni.Limited.Jlfp_instantiation.JLFPInstantiation.instantiated_cumulative_interference_of_hep_tasks_equal_total_interference_of_hep_tasks
          job_arrival job_cost job_task arr_seq H_arrival_times_are_consistent H_arr_seq_is_a_set
          sched H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute
          H_sequential_jobs (EDF job_arrival (fun j => task_deadline (job_task j)))
          hEDF_refl hEDF_trans hEDF_seq tsk j' ARR' TSK' t1' (t1' + R₀) hQT1]
        obtain ⟨h_pi, h_svc⟩ := instantiated_task_interference_is_bounded task_cost task_deadline job_arrival job_cost job_task
          arr_seq H_arrival_times_are_consistent H_arr_seq_is_a_set sched
          H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute
          H_work_conserving H_sequential_jobs H_job_cost_le_task_cost ts H_all_jobs_from_taskset
          max_arrivals H_family_of_proper_arrival_curves tsk H_tsk_in_ts
          job_lock_in_service task_lock_in_service
          H_proper_job_lock_in_service H_proper_task_lock_in_service
          priority_inversion_bound H_priority_inversion_is_bounded
          L H_L_positive H_fixed_point R H_R_is_maximum
          j' R₀ t1' t2' ARR' TSK' POS' NCOMPL' hBI' hRLT'
        exact Nat.add_le_add h_pi h_svc
      -- Apply uniprocessor_response_time_bound_seq
      exact AbstractSeqRTA.uniprocessor_response_time_bound_seq
        task_cost job_arrival job_cost job_task
        arr_seq H_arrival_times_are_consistent H_arr_seq_is_a_set
        sched H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute
        H_job_cost_le_task_cost ts H_all_jobs_from_taskset
        max_arrivals H_family_of_proper_arrival_curves
        tsk H_tsk_in_ts job_lock_in_service task_lock_in_service
        H_proper_job_lock_in_service H_proper_task_lock_in_service
        (fun j t => Prosa.Classic.Model.Schedule.Uni.Limited.Jlfp_instantiation.JLFPInstantiation.interference
          (EDF job_arrival (fun j => task_deadline (job_task j))) sched j t)
        (fun j t => Prosa.Classic.Model.Schedule.Uni.Limited.Jlfp_instantiation.JLFPInstantiation.interfering_workload
          (EDF job_arrival (fun j => task_deadline (job_task j))) job_cost arr_seq sched j t)
        (instantiated_i_and_w_are_coherent_with_schedule task_cost task_deadline job_arrival job_cost job_task
          arr_seq H_arrival_times_are_consistent H_arr_seq_is_a_set sched
          H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute
          H_work_conserving H_sequential_jobs H_job_cost_le_task_cost
          ts H_all_jobs_from_taskset max_arrivals H_family_of_proper_arrival_curves
          tsk H_tsk_in_ts job_lock_in_service task_lock_in_service
          H_proper_job_lock_in_service H_proper_task_lock_in_service
          priority_inversion_bound H_priority_inversion_is_bounded
          L H_L_positive H_fixed_point R H_R_is_maximum)
        H_sequential_jobs
        (instantiated_interference_and_workload_consistent_with_sequential_jobs task_cost task_deadline job_arrival job_cost job_task
          arr_seq H_arrival_times_are_consistent H_arr_seq_is_a_set sched
          H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute
          H_work_conserving H_sequential_jobs H_job_cost_le_task_cost ts H_all_jobs_from_taskset
          max_arrivals H_family_of_proper_arrival_curves
          tsk H_tsk_in_ts job_lock_in_service task_lock_in_service
          H_proper_job_lock_in_service H_proper_task_lock_in_service
          priority_inversion_bound H_priority_inversion_is_bounded
          L H_L_positive H_fixed_point R H_R_is_maximum)
        L
        (by
          intro j'' ARR'' TSK'' POS''
          obtain ⟨t1', t2', hle, harr, hbd, hBI⟩ :=
            instantiated_busy_intervals_are_bounded task_cost task_deadline job_arrival job_cost job_task
              arr_seq H_arrival_times_are_consistent H_arr_seq_is_a_set sched
              H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute
              H_work_conserving H_job_cost_le_task_cost ts H_all_jobs_from_taskset
              max_arrivals H_family_of_proper_arrival_curves
              tsk L H_L_positive H_fixed_point j'' ARR'' TSK'' POS''
          exact ⟨t1', t2', hle, harr, hbd,
            (Prosa.Classic.Model.Schedule.Uni.Limited.Jlfp_instantiation.JLFPInstantiation.instantiated_busy_interval_equivalent_edf_busy_interval
              job_arrival job_cost job_task arr_seq H_arrival_times_are_consistent H_arr_seq_is_a_set
              sched H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute
              H_sequential_jobs (EDF job_arrival (fun j => task_deadline (job_task j)))
              hEDF_refl hEDF_trans hEDF_seq tsk j'' ARR'' TSK'' POS'' t1' t2').mp hBI⟩)
        (fun _ A R₀ => priority_inversion_bound +
          bound_on_total_hep_workload task_cost task_deadline ts max_arrivals tsk A R₀)
        h_task_interf_bounded
        R
        (fun A hA => correct_search_space task_cost task_deadline job_arrival job_cost job_task
          arr_seq H_arrival_times_are_consistent H_arr_seq_is_a_set sched
          H_jobs_come_from_arrival_sequence H_completed_jobs_dont_execute
          H_job_cost_le_task_cost ts max_arrivals H_family_of_proper_arrival_curves
          tsk H_tsk_in_ts task_lock_in_service priority_inversion_bound
          L R H_R_is_maximum
          j ARR TSK hPOS A
          (A_is_in_concrete_search_space task_cost task_deadline job_arrival job_cost job_task
            arr_seq H_arrival_times_are_consistent H_arr_seq_is_a_set sched
            H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute
            H_work_conserving H_sequential_jobs H_job_cost_le_task_cost ts H_all_jobs_from_taskset
            max_arrivals H_family_of_proper_arrival_curves tsk H_tsk_in_ts
            job_lock_in_service task_lock_in_service
            H_proper_job_lock_in_service H_proper_task_lock_in_service
            priority_inversion_bound H_priority_inversion_is_bounded
            L H_L_positive H_fixed_point R H_R_is_maximum
            j ARR TSK hPOS A hA))
        j ARR TSK
    · -- Zero-cost case: job is trivially completed
      push_neg at POS
      have hzero : job_cost j = 0 := Nat.eq_zero_of_le_zero POS
      unfold is_response_time_bound_of_job completed_by
      simp [hzero]

end AbstractResponseTimeAnalysisForEDF

end AbstractRTAforEDFwithArrivalCurves

end Prosa.Classic.Model.Schedule.Uni.Limited.Edf.Response_time_bound
