-- Translated from: ../rt-proofs/classic/model/schedule/uni/limited/edf/nonpr_reg/concrete_models/response_time_bound.v
import Prosa.Classic.Util.All
import Prosa.Classic.Model.Arrival.Basic.Job
import Prosa.Classic.Model.Schedule.Uni.Service
import Prosa.Classic.Model.Schedule.Uni.Limited.Schedule
import Prosa.Classic.Model.Arrival.Curves.Bounds
import Prosa.Classic.Model.Schedule.Uni.Nonpreemptive.Schedule
import Prosa.Classic.Model.Arrival.Basic.Arrival_sequence
import Prosa.Classic.Model.Schedule.Uni.Schedule
import Prosa.Classic.Model.Schedule.Uni.Workload
import Prosa.Classic.Model.Schedule.Uni.Response_time
import Prosa.Classic.Model.Schedule.Uni.Limited.Platform.Definitions
import Prosa.Classic.Model.Schedule.Uni.Basic.Platform
import Prosa.Classic.Model.Priority
import Prosa.Classic.Analysis.Uni.Arrival_curves.Workload_bound
import Prosa.Util.Epsilon
import Prosa.Util.Nondecreasing
import Prosa.Classic.Model.Schedule.Uni.Limited.Platform.Limited
import Prosa.Classic.Model.Schedule.Uni.Limited.Edf.Nonpr_reg.Response_time_bound
import Prosa.Classic.Model.Schedule.Uni.Limited.Platform.Preemptive
import Prosa.Classic.Model.Schedule.Uni.Limited.Platform.Nonpreemptive
import Mathlib.Tactic

namespace Prosa.Classic.Model.Schedule.Uni.Limited.Edf.Nonpr_reg.Concrete_models.Response_time_bound

open Prosa.Classic.Model.Time
open Prosa.Classic.Model.Arrival.Curves.Bounds.ArrivalCurves
open Prosa.Classic.Model.Schedule.Uni.Schedule
open Prosa.Classic.Model.Schedule.Uni.Workload
open Prosa.Classic.Model.Schedule.Uni.Service
open Prosa.Classic.Model.Schedule.Uni.Response_time.ResponseTime
open Prosa.Classic.Model.Schedule.Uni.Limited.Platform.Definitions.LimitedPreemptionPlatform
open Prosa.Classic.Model.Schedule.Uni.Limited.Schedule
open Prosa.Classic.Model.Schedule.Uni.Nonpreemptive.Schedule
open Prosa.Classic.Model.Priority
open Prosa.Classic.Analysis.Uni.Arrival_curves.Workload_bound.MaxArrivalsWorkloadBound
open Prosa.Util.Epsilon
open Prosa.Classic.Model.Arrival.Basic.Arrival_sequence
open Prosa.Util.Nondecreasing
open Prosa.Util.List
open Prosa.Classic.Model.Schedule.Uni.Limited.Edf.Nonpr_reg.Response_time_bound.RTAforEDFwithBoundedNonpreemptiveSegmentsWithArrivalCurves
open Prosa.Classic.Model.Schedule.Uni.Limited.Platform.Preemptive.FullyPreemptivePlatform
open Prosa.Classic.Model.Schedule.Uni.Limited.Platform.Nonpreemptive.FullyNonPreemptivePlatform

namespace RTAforConcreteModels

section Analysis

  variable {Task : Type _} [DecidableEq Task]
  variable (task_cost : Task → Time)
  variable (task_deadline : Task → Time)

  variable {Job : Type _} [DecidableEq Job]
  variable (job_arrival : Job → Time)
  variable (job_cost : Job → Time)
  variable (job_task : Job → Task)

  variable (arr_seq : Prosa.Classic.Model.Arrival.Basic.Arrival_sequence.arrival_sequence Job)
  variable (H_arrival_times_are_consistent :
    Prosa.Classic.Model.Arrival.Basic.Arrival_sequence.arrival_times_are_consistent job_arrival arr_seq)
  variable (H_arr_seq_is_a_set :
    Prosa.Classic.Model.Arrival.Basic.Arrival_sequence.arrival_sequence_is_a_set arr_seq)

  variable (ts : List Task)

  variable (H_all_jobs_from_taskset :
    ∀ j, Prosa.Classic.Model.Arrival.Basic.Arrival_sequence.arrives_in arr_seq j → job_task j ∈ ts)

  variable (H_job_cost_le_task_cost :
    Prosa.Classic.Model.Arrival.Basic.Job.cost_of_jobs_from_arrival_sequence_le_task_cost
      task_cost job_cost job_task arr_seq)

  variable (max_arrivals : Task → Time → Nat)
  variable (H_family_of_proper_arrival_curves :
    family_of_proper_arrival_curves job_task arr_seq max_arrivals ts)

  variable (tsk : Task)
  variable (H_tsk_in_ts : tsk ∈ ts)

  variable (sched : schedule Job)
  variable (H_jobs_come_from_arrival_sequence : jobs_come_from_arrival_sequence sched arr_seq)

  variable (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute job_arrival sched)
  variable (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched)

  variable (H_sequential_jobs : sequential_jobs job_arrival job_cost sched job_task)

  variable (H_work_conserving :
    Prosa.Classic.Model.Schedule.Uni.Basic.Platform.Platform.work_conserving
      job_arrival job_cost arr_seq sched)

  private noncomputable def bound_on_total_hep_workload (A Δ : Time) : Nat :=
    ((ts.filter (fun tsk_o => decide (tsk_o ≠ tsk))).map
      (fun tsk_o => task_request_bound_function task_cost max_arrivals tsk_o
        (min ((A + ε) + task_deadline tsk - task_deadline tsk_o) Δ))).sum

  private noncomputable def task_rbf_changes_at_val (A : Time) : Bool :=
    decide (task_request_bound_function task_cost max_arrivals tsk A ≠
            task_request_bound_function task_cost max_arrivals tsk (A + ε))

  private noncomputable def bound_on_total_hep_workload_changes_at_val (A : Time) : Bool :=
    ts.any (fun tsk_o =>
      decide (tsk_o ≠ tsk) &&
      decide (task_request_bound_function task_cost max_arrivals tsk_o
                (A + task_deadline tsk - task_deadline tsk_o) ≠
              task_request_bound_function task_cost max_arrivals tsk_o
                ((A + ε) + task_deadline tsk - task_deadline tsk_o)))

  section RTAforFullyPreemptiveEDFModelwithArrivalCurves

    variable (H_respects_policy :
      respects_JLFP_policy_at_preemption_point
        job_arrival job_cost arr_seq sched
        (fun _j _prog => true)
        (EDF job_arrival (fun j => task_deadline (job_task j))))

    variable (L : Time)
    variable (H_L_positive : L > 0)
    variable (H_fixed_point : L = total_request_bound_function task_cost max_arrivals ts L)

    variable (R : Nat)
    variable (H_R_is_maximum :
      ∀ A,
        (decide (A < L) &&
          (task_rbf_changes_at_val task_cost max_arrivals tsk A ||
           bound_on_total_hep_workload_changes_at_val task_cost task_deadline ts max_arrivals tsk A)) = true →
        ∃ F,
          A + F = task_request_bound_function task_cost max_arrivals tsk (A + ε) +
                  bound_on_total_hep_workload task_cost task_deadline ts max_arrivals tsk A (A + F) ∧
          F ≤ R)

    include H_arrival_times_are_consistent H_arr_seq_is_a_set H_all_jobs_from_taskset
      H_job_cost_le_task_cost H_family_of_proper_arrival_curves H_tsk_in_ts
      H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute
      H_completed_jobs_dont_execute H_sequential_jobs H_work_conserving
      H_respects_policy H_L_positive H_fixed_point H_R_is_maximum in
    include H_arrival_times_are_consistent H_arr_seq_is_a_set H_all_jobs_from_taskset H_job_cost_le_task_cost H_family_of_proper_arrival_curves H_tsk_in_ts H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_sequential_jobs H_work_conserving H_respects_policy H_L_positive H_fixed_point H_R_is_maximum in
    theorem uniprocessor_response_time_bound_fully_preemptive_edf :
        is_response_time_bound_of_task job_arrival job_cost job_task arr_seq sched tsk R := by
      exact uniprocessor_response_time_bound_edf_with_bounded_nonpreemptive_segments
        (fun _ => ε) task_cost task_deadline
        job_arrival (fun _ => ε) job_cost job_task
        arr_seq H_arrival_times_are_consistent H_arr_seq_is_a_set
        sched H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute
        H_sequential_jobs (fun _ _ => true)
        (fun j hARR => ⟨fun t h => absurd h (by simp), fun prt _ _ => rfl⟩)
        (fun j hARR => ⟨rfl, rfl, fun _ => le_refl ε,
          fun progr ⟨_, hle⟩ => ⟨progr, le_refl _, by simp [ε], rfl⟩⟩)
        H_work_conserving H_respects_policy
        ts H_all_jobs_from_taskset H_job_cost_le_task_cost
        tsk H_tsk_in_ts max_arrivals H_family_of_proper_arrival_curves
        (fun j => job_cost j) (fun t => task_cost t)
        ⟨fun j hARR hPOS => hPOS,
         fun j hARR hPOS => Nat.le_refl _,
         fun j t t' hARR hLE hSERV hNCOMPL =>
           absurd (Prosa.Classic.Model.Schedule.Uni.Schedule.completion_monotonic job_cost sched j t t' hLE
             (by unfold completed_by; omega)) hNCOMPL⟩
        ⟨Nat.le_refl _,
         fun j hARR hTSK => by rw [← hTSK]; exact H_job_cost_le_task_cost j hARR⟩
        L H_L_positive H_fixed_point R
        (fun A hA => by
          have h_changes : bound_on_total_hep_workload_changes_at task_cost task_deadline max_arrivals ts tsk A =
              bound_on_total_hep_workload_changes_at_val task_cost task_deadline ts max_arrivals tsk A := by
            simp only [bound_on_total_hep_workload_changes_at, bound_on_total_hep_workload_changes_at_val]
            congr 1; ext tsk_o; congr 1; exact decide_eq_decide.mpr ne_comm
          rw [h_changes] at hA
          obtain ⟨F, hFIX, hLE⟩ := H_R_is_maximum A hA
          refine ⟨F, ?_, ?_⟩
          · have h_hwl :
                _root_.Prosa.Classic.Model.Schedule.Uni.Limited.Edf.Nonpr_reg.Response_time_bound.RTAforEDFwithBoundedNonpreemptiveSegmentsWithArrivalCurves.bound_on_total_hep_workload
                  task_cost task_deadline max_arrivals ts tsk A (A + F) =
                bound_on_total_hep_workload task_cost task_deadline ts max_arrivals tsk A (A + F) := rfl
            have h_bb : _root_.Prosa.Classic.Model.Schedule.Uni.Limited.Edf.Nonpr_reg.Response_time_bound.RTAforEDFwithBoundedNonpreemptiveSegmentsWithArrivalCurves.blocking_bound (fun (_ : Task) => ε) task_deadline ts tsk = 0 := by
              unfold _root_.Prosa.Classic.Model.Schedule.Uni.Limited.Edf.Nonpr_reg.Response_time_bound.RTAforEDFwithBoundedNonpreemptiveSegmentsWithArrivalCurves.blocking_bound
              generalize (ts.filter _) = l
              induction l with
              | nil => simp [List.foldl, List.map]
              | cons _ _ ih =>
                simp only [List.map_cons, List.foldl_cons, Nat.sub_self, max_self]
                exact ih
            simp only [h_bb, h_hwl, Nat.sub_self, Nat.sub_zero, Nat.add_zero, Time] at *; omega
          · simp only [Nat.sub_self, Nat.add_zero]; exact hLE)

  end RTAforFullyPreemptiveEDFModelwithArrivalCurves

  section RTAforFullyNonPreemptiveEDFModelwithArrivalCurves

    variable (H_nonpreemptive_sched : is_nonpreemptive_schedule job_cost sched)

    variable (H_respects_policy :
      respects_JLFP_policy_at_preemption_point
        job_arrival job_cost arr_seq sched
        (Prosa.Classic.Model.Schedule.Uni.Limited.Platform.Nonpreemptive.FullyNonPreemptivePlatform.can_be_preempted_for_fully_nonpreemptive_model job_cost)
        (EDF job_arrival (fun j => task_deadline (job_task j))))

    private noncomputable def blocking_bound_nonpreemptive : Nat :=
      ((ts.filter (fun tsk_other =>
        decide (tsk_other ≠ tsk) && decide (task_deadline tsk < task_deadline tsk_other))).map
        (fun tsk_other => task_cost tsk_other - ε)).foldl max 0

    variable (L : Time)
    variable (H_L_positive : L > 0)
    variable (H_fixed_point : L = total_request_bound_function task_cost max_arrivals ts L)

    variable (R : Nat)
    variable (H_R_is_maximum :
      ∀ A,
        (decide (A < L) &&
          (task_rbf_changes_at_val task_cost max_arrivals tsk A ||
           bound_on_total_hep_workload_changes_at_val task_cost task_deadline ts max_arrivals tsk A)) = true →
        ∃ F,
          A + F = blocking_bound_nonpreemptive task_cost task_deadline ts tsk +
                  (task_request_bound_function task_cost max_arrivals tsk (A + ε) -
                   (task_cost tsk - ε)) +
                  bound_on_total_hep_workload task_cost task_deadline ts max_arrivals tsk A (A + F) ∧
          F + (task_cost tsk - ε) ≤ R)

    include H_arrival_times_are_consistent H_arr_seq_is_a_set H_all_jobs_from_taskset
      H_job_cost_le_task_cost H_family_of_proper_arrival_curves H_tsk_in_ts
      H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute
      H_completed_jobs_dont_execute H_sequential_jobs H_work_conserving
      H_nonpreemptive_sched H_respects_policy H_L_positive H_fixed_point H_R_is_maximum in
    include H_arrival_times_are_consistent H_arr_seq_is_a_set H_all_jobs_from_taskset H_job_cost_le_task_cost H_family_of_proper_arrival_curves H_tsk_in_ts H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_sequential_jobs H_work_conserving H_nonpreemptive_sched H_respects_policy H_L_positive H_fixed_point H_R_is_maximum in
    theorem uniprocessor_response_time_bound_fully_nonpreemptive_edf :
        is_response_time_bound_of_task job_arrival job_cost job_task arr_seq sched tsk R := by
      by_cases H_task_cost_pos : task_cost tsk > 0
      · -- Positive cost case: use intermediate theorem
        exact uniprocessor_response_time_bound_edf_with_bounded_nonpreemptive_segments
          (fun t => task_cost t) task_cost task_deadline
          job_arrival (fun j => job_cost j) job_cost job_task
          arr_seq H_arrival_times_are_consistent H_arr_seq_is_a_set
          sched H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute
          H_sequential_jobs
          (Prosa.Classic.Model.Schedule.Uni.Limited.Platform.Nonpreemptive.FullyNonPreemptivePlatform.can_be_preempted_for_fully_nonpreemptive_model job_cost)
          -- correct_preemption_model
          (fun j hARR => by
            constructor
            · -- not_preemptive_implies_scheduled
              intro t hcant
              unfold Prosa.Classic.Model.Schedule.Uni.Limited.Platform.Nonpreemptive.FullyNonPreemptivePlatform.can_be_preempted_for_fully_nonpreemptive_model at hcant
              simp only [Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq] at hcant
              have hpos : service sched j t > 0 := Nat.pos_of_ne_zero hcant.1
              have hncomp : ¬ completed_by job_cost sched j t := by
                intro hcomp
                exact hcant.2 (Nat.le_antisymm (H_completed_jobs_dont_execute j t) hcomp)
              obtain ⟨ft, hft_lt, hft_sched⟩ := scheduled_at_earlier_time sched j t hpos
              exact H_nonpreemptive_sched j ft t (Nat.le_of_lt hft_lt) hft_sched hncomp
            · -- execution_starts_with_preemption_point
              intro prt hnsched hsched
              unfold Prosa.Classic.Model.Schedule.Uni.Limited.Platform.Nonpreemptive.FullyNonPreemptivePlatform.can_be_preempted_for_fully_nonpreemptive_model
              simp only [Bool.or_eq_true_iff, beq_iff_eq]
              left
              by_contra hne
              have hpos : service sched j (prt + 1) > 0 := Nat.pos_of_ne_zero hne
              obtain ⟨ft, hft_lt, hft_sched⟩ := scheduled_at_earlier_time sched j (prt + 1) hpos
              have hft_le_prt : ft ≤ prt := Nat.lt_succ_iff.mp hft_lt
              have hncomp : ¬ completed_by job_cost sched j prt := by
                intro hcomp
                have hcomp' := completion_monotonic job_cost sched j prt (prt + 1) (Nat.le_succ prt) hcomp
                exact scheduled_implies_not_completed job_cost sched j H_completed_jobs_dont_execute (prt + 1) hsched hcomp'
              exact hnsched (H_nonpreemptive_sched j ft prt hft_le_prt hft_sched hncomp))
          -- model_with_bounded_nonpreemptive_segments
          (fun j hARR => ⟨by
            show Prosa.Classic.Model.Schedule.Uni.Limited.Platform.Nonpreemptive.FullyNonPreemptivePlatform.can_be_preempted_for_fully_nonpreemptive_model job_cost j 0 = true
            unfold Prosa.Classic.Model.Schedule.Uni.Limited.Platform.Nonpreemptive.FullyNonPreemptivePlatform.can_be_preempted_for_fully_nonpreemptive_model
            rfl, by
            show Prosa.Classic.Model.Schedule.Uni.Limited.Platform.Nonpreemptive.FullyNonPreemptivePlatform.can_be_preempted_for_fully_nonpreemptive_model job_cost j (job_cost j) = true
            unfold Prosa.Classic.Model.Schedule.Uni.Limited.Platform.Nonpreemptive.FullyNonPreemptivePlatform.can_be_preempted_for_fully_nonpreemptive_model
            simp only [Bool.or_eq_true, beq_iff_eq]
            exact Or.inr trivial,
            fun _ => H_job_cost_le_task_cost j hARR,
            fun progr ⟨_, hle⟩ => by
              by_cases hprogr : progr = 0
              · exact ⟨progr, le_refl _, Nat.le_add_right _ _, by
                  show Prosa.Classic.Model.Schedule.Uni.Limited.Platform.Nonpreemptive.FullyNonPreemptivePlatform.can_be_preempted_for_fully_nonpreemptive_model job_cost j progr = true
                  unfold Prosa.Classic.Model.Schedule.Uni.Limited.Platform.Nonpreemptive.FullyNonPreemptivePlatform.can_be_preempted_for_fully_nonpreemptive_model
                  rw [hprogr]; rfl⟩
              · have hpos : 0 < progr := Nat.pos_of_ne_zero hprogr
                refine ⟨job_cost j, hle, ?_, ?_⟩
                · have h1 : 0 < progr := Nat.pos_of_ne_zero hprogr
                  have h2 : progr ≤ job_cost j := hle
                  have h_jc_pos : 0 < job_cost j := Nat.lt_of_lt_of_le h1 h2
                  show job_cost j ≤ progr + (job_cost j - 1)
                  calc job_cost j = job_cost j - 1 + 1 := (Nat.succ_pred_eq_of_pos h_jc_pos).symm
                    _ ≤ job_cost j - 1 + progr := Nat.add_le_add_left (Nat.succ_le_of_lt h1) _
                    _ = progr + (job_cost j - 1) := Nat.add_comm _ _
                · show Prosa.Classic.Model.Schedule.Uni.Limited.Platform.Nonpreemptive.FullyNonPreemptivePlatform.can_be_preempted_for_fully_nonpreemptive_model job_cost j (job_cost j) = true
                  unfold Prosa.Classic.Model.Schedule.Uni.Limited.Platform.Nonpreemptive.FullyNonPreemptivePlatform.can_be_preempted_for_fully_nonpreemptive_model
                  simp only [Bool.or_eq_true, beq_iff_eq]
                  exact Or.inr trivial⟩)
          H_work_conserving H_respects_policy
          ts H_all_jobs_from_taskset H_job_cost_le_task_cost
          tsk H_tsk_in_ts max_arrivals H_family_of_proper_arrival_curves
          (fun _j => ε) (fun _t => ε)
          ⟨fun j _hARR _hPOS => by simp [ε],
           fun j _hARR hPOS => hPOS,
           fun j t t' hARR hLE hSERV hNCOMPL => by
             have hSERV' : 0 < service sched j t := hSERV
             unfold service at hSERV'
             have := incremental_service_during sched j 0 t 0 hSERV'
             obtain ⟨t₀, ht₀_ge, ht₀_lt, hSCHED₀, _⟩ := this
             exact H_nonpreemptive_sched j t₀ t' (ht₀_lt.le.trans hLE) hSCHED₀ hNCOMPL⟩
          ⟨H_task_cost_pos, fun j _hARR _hTSK => le_refl _⟩
          L H_L_positive H_fixed_point R
          (fun A hA => by
            have h_changes : bound_on_total_hep_workload_changes_at task_cost task_deadline max_arrivals ts tsk A =
                bound_on_total_hep_workload_changes_at_val task_cost task_deadline ts max_arrivals tsk A := by
              simp only [bound_on_total_hep_workload_changes_at, bound_on_total_hep_workload_changes_at_val]
              congr 1; ext tsk_o; congr 1; exact decide_eq_decide.mpr ne_comm
            rw [h_changes] at hA
            obtain ⟨F, hFIX, hLE⟩ := H_R_is_maximum A hA
            have h_hwl :
                _root_.Prosa.Classic.Model.Schedule.Uni.Limited.Edf.Nonpr_reg.Response_time_bound.RTAforEDFwithBoundedNonpreemptiveSegmentsWithArrivalCurves.bound_on_total_hep_workload
                  task_cost task_deadline max_arrivals ts tsk A (A + F) =
                bound_on_total_hep_workload task_cost task_deadline ts max_arrivals tsk A (A + F) := rfl
            have h_bb :
                _root_.Prosa.Classic.Model.Schedule.Uni.Limited.Edf.Nonpr_reg.Response_time_bound.RTAforEDFwithBoundedNonpreemptiveSegmentsWithArrivalCurves.blocking_bound
                  (fun t => task_cost t) task_deadline ts tsk =
                blocking_bound_nonpreemptive task_cost task_deadline ts tsk := rfl
            exact ⟨F, by simp only [h_hwl, h_bb, ε, Time] at *; omega, hLE⟩)
      · -- Zero cost case
        push_neg at H_task_cost_pos
        have H_task_cost_zero : task_cost tsk = 0 := Nat.le_zero.mp H_task_cost_pos
        intro j ARR TSK
        have hJC : job_cost j ≤ task_cost (job_task j) := H_job_cost_le_task_cost j ARR
        rw [TSK, H_task_cost_zero] at hJC
        have hJC0 : job_cost j = 0 := Nat.le_zero.mp hJC
        unfold is_response_time_bound_of_job completed_by
        rw [hJC0]; exact Nat.zero_le _

  end RTAforFullyNonPreemptiveEDFModelwithArrivalCurves

  section RTAforFixedPreemptionPointsModelwithArrivalCurves

    variable (job_preemption_points : Job → List Time)
    variable (task_preemption_points : Task → List Time)
    variable (H_model_with_fixed_preemption_points :
      Prosa.Classic.Model.Schedule.Uni.Limited.Platform.Limited.ModelWithLimitedPreemptions.fixed_preemption_points_model
        task_cost job_cost job_task arr_seq
        job_preemption_points task_preemption_points ts)

    variable (H_schedule_with_limited_preemptions :
      Prosa.Classic.Model.Schedule.Uni.Limited.Platform.Limited.ModelWithLimitedPreemptions.is_schedule_with_limited_preemptions
        arr_seq job_preemption_points sched)

    variable (H_respects_policy :
      respects_JLFP_policy_at_preemption_point
        job_arrival job_cost arr_seq sched
        (Prosa.Classic.Model.Schedule.Uni.Limited.Platform.Limited.ModelWithLimitedPreemptions.can_be_preempted_for_model_with_limited_preemptions
          job_preemption_points)
        (EDF job_arrival (fun j => task_deadline (job_task j))))

    private noncomputable def blocking_bound_fixed : Nat :=
      ((ts.filter (fun tsk_other =>
        decide (tsk_other ≠ tsk) && decide (task_deadline tsk < task_deadline tsk_other))).map
        (fun tsk_other =>
          Prosa.Classic.Model.Schedule.Uni.Limited.Platform.Limited.ModelWithLimitedPreemptions.task_max_nps
            task_preemption_points tsk_other - ε)).foldl max 0

    variable (L : Time)
    variable (H_L_positive : L > 0)
    variable (H_fixed_point : L = total_request_bound_function task_cost max_arrivals ts L)

    variable (R : Nat)
    variable (H_R_is_maximum :
      ∀ A,
        (decide (A < L) &&
          (task_rbf_changes_at_val task_cost max_arrivals tsk A ||
           bound_on_total_hep_workload_changes_at_val task_cost task_deadline ts max_arrivals tsk A)) = true →
        ∃ F,
          A + F = blocking_bound_fixed task_deadline ts tsk task_preemption_points +
                  (task_request_bound_function task_cost max_arrivals tsk (A + ε) -
                   (Prosa.Classic.Model.Schedule.Uni.Limited.Platform.Limited.ModelWithLimitedPreemptions.task_last_nps
                      task_preemption_points tsk - ε)) +
                  bound_on_total_hep_workload task_cost task_deadline ts max_arrivals tsk A (A + F) ∧
          F + (Prosa.Classic.Model.Schedule.Uni.Limited.Platform.Limited.ModelWithLimitedPreemptions.task_last_nps
                 task_preemption_points tsk - ε) ≤ R)

    include H_arrival_times_are_consistent H_arr_seq_is_a_set H_all_jobs_from_taskset
      H_job_cost_le_task_cost H_family_of_proper_arrival_curves H_tsk_in_ts
      H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute
      H_completed_jobs_dont_execute H_sequential_jobs H_work_conserving
      H_model_with_fixed_preemption_points H_schedule_with_limited_preemptions
      H_respects_policy H_L_positive H_fixed_point H_R_is_maximum in
    include H_arrival_times_are_consistent H_arr_seq_is_a_set H_all_jobs_from_taskset H_job_cost_le_task_cost H_family_of_proper_arrival_curves H_tsk_in_ts H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_sequential_jobs H_work_conserving H_model_with_fixed_preemption_points H_schedule_with_limited_preemptions H_respects_policy H_L_positive H_fixed_point H_R_is_maximum in
    theorem uniprocessor_response_time_bound_edf_with_fixed_preemption_points :
        is_response_time_bound_of_task job_arrival job_cost job_task arr_seq sched tsk R := by
      exact uniprocessor_response_time_bound_edf_with_bounded_nonpreemptive_segments
        (Prosa.Classic.Model.Schedule.Uni.Limited.Platform.Limited.ModelWithLimitedPreemptions.task_max_nps
          task_preemption_points)
        task_cost task_deadline
        job_arrival
        (Prosa.Classic.Model.Schedule.Uni.Limited.Platform.Limited.ModelWithLimitedPreemptions.job_max_nps
          job_preemption_points)
        job_cost job_task
        arr_seq H_arrival_times_are_consistent H_arr_seq_is_a_set
        sched H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute
        H_sequential_jobs
        (Prosa.Classic.Model.Schedule.Uni.Limited.Platform.Limited.ModelWithLimitedPreemptions.can_be_preempted_for_model_with_limited_preemptions
          job_preemption_points)
        (Prosa.Classic.Model.Schedule.Uni.Limited.Platform.Limited.ModelWithLimitedPreemptions.model_with_fixed_preemption_points_is_correct
          arr_seq job_preemption_points sched H_schedule_with_limited_preemptions)
        (Prosa.Classic.Model.Schedule.Uni.Limited.Platform.Limited.ModelWithLimitedPreemptions.model_with_fixed_preemption_points_is_model_with_bounded_nonpreemptive_regions
          job_cost job_task arr_seq job_preemption_points
          (Prosa.Classic.Model.Schedule.Uni.Limited.Platform.Limited.ModelWithLimitedPreemptions.task_max_nps
            task_preemption_points)
          H_model_with_fixed_preemption_points.1
          (fun j hARR => by
            show Prosa.Classic.Model.Schedule.Uni.Limited.Platform.Limited.ModelWithLimitedPreemptions.job_max_nps
              job_preemption_points j ≤
              Prosa.Classic.Model.Schedule.Uni.Limited.Platform.Limited.ModelWithLimitedPreemptions.task_max_nps
              task_preemption_points (job_task j)
            unfold Prosa.Classic.Model.Schedule.Uni.Limited.Platform.Limited.ModelWithLimitedPreemptions.job_max_nps
              Prosa.Classic.Model.Schedule.Uni.Limited.Platform.Limited.ModelWithLimitedPreemptions.task_max_nps
            set xs := distances (job_preemption_points j)
            set ys := distances (task_preemption_points (job_task j))
            have hdom : ∀ n, nthD xs n ≤ nthD ys n :=
              fun n => H_model_with_fixed_preemption_points.2.2.2.2.2.1 j n hARR
            have hall : ∀ x, x ∈ xs → x ≤ max0 ys := by
              intro x hx
              obtain ⟨n, hn_lt, hn_eq⟩ := List.getElem_of_mem hx
              have hx_eq : x = nthD xs n := by
                simp only [nthD, List.getD, List.getElem?_eq_getElem hn_lt]; exact hn_eq.symm
              rw [hx_eq]
              calc nthD xs n ≤ nthD ys n := hdom n
                _ ≤ max0 ys := by
                    simp only [nthD, List.getD]
                    rcases Nat.lt_or_ge n ys.length with hlt | hge
                    · rw [List.getElem?_eq_getElem hlt]
                      exact in_max0_le ys _ (List.getElem_mem hlt)
                    · rw [List.getElem?_eq_none hge]
                      exact Nat.zero_le _
            have max0_le : ∀ (zs : List ℕ) (b : ℕ), (∀ x, x ∈ zs → x ≤ b) → max0 zs ≤ b := by
              intro zs b hle
              induction zs with
              | nil => simp [max0, List.foldl]
              | cons a tl ih =>
                rw [max0_cons]
                apply Nat.max_le.mpr
                exact ⟨hle a (List.mem_cons_self ..), ih (fun x hx => hle x (List.mem_cons_of_mem _ hx))⟩
            exact max0_le xs (max0 ys) hall))
        H_work_conserving H_respects_policy
        ts H_all_jobs_from_taskset H_job_cost_le_task_cost
        tsk H_tsk_in_ts max_arrivals H_family_of_proper_arrival_curves
        (fun j => job_cost j - (Prosa.Classic.Model.Schedule.Uni.Limited.Platform.Limited.ModelWithLimitedPreemptions.job_last_nps job_preemption_points j - ε))
        (fun t => task_cost t - (Prosa.Classic.Model.Schedule.Uni.Limited.Platform.Limited.ModelWithLimitedPreemptions.task_last_nps task_preemption_points t - ε))
        ⟨fun j hARR hPOS => by
           have hLAST := H_model_with_fixed_preemption_points.1.2.1 j hARR hPOS
           have h_nd_j := H_model_with_fixed_preemption_points.1.2.2.2.2 j hARR
           have h_end_j := H_model_with_fixed_preemption_points.1.2.2.2.1 j hARR
           have h_jlns_le : Prosa.Classic.Model.Schedule.Uni.Limited.Platform.Limited.ModelWithLimitedPreemptions.job_last_nps job_preemption_points j ≤ job_cost j :=
             le_trans (last_of_seq_le_max_of_seq _)
               (le_trans (max_distance_in_seq_le_last_element_of_seq _ h_nd_j) (le_of_eq h_end_j))
           simp only [Time, ε] at *; omega,
         fun j _hARR _hPOS => Nat.sub_le _ _,
         fun j t t' hARR hLE hSERV hNCOMPL => by
           have h_nd := H_model_with_fixed_preemption_points.1.2.2.2.2 j hARR
           have h_end := H_model_with_fixed_preemption_points.1.2.2.2.1 j hARR
           have h_beg := H_model_with_fixed_preemption_points.1.2.2.1 j hARR
           have hS_lt : service sched j t' < job_cost j := not_le.mp hNCOMPL
           have hS_ge : job_cost j -
               (Prosa.Classic.Model.Schedule.Uni.Limited.Platform.Limited.ModelWithLimitedPreemptions.job_last_nps job_preemption_points j - ε) ≤
               service sched j t' := le_trans hSERV (service_monotonic sched j t t' hLE)
           have hPOS : job_cost j > 0 := Nat.lt_of_le_of_lt (Nat.zero_le _) hS_lt
           have hLAST_pos := H_model_with_fixed_preemption_points.1.2.1 j hARR hPOS
           have h_jlns_le : Prosa.Classic.Model.Schedule.Uni.Limited.Platform.Limited.ModelWithLimitedPreemptions.job_last_nps job_preemption_points j ≤ job_cost j :=
             le_trans (last_of_seq_le_max_of_seq _)
               (le_trans (max_distance_in_seq_le_last_element_of_seq _ h_nd) (le_of_eq h_end))
           have h_len : 2 ≤ (job_preemption_points j).length := by
             by_contra hlt; push_neg at hlt
             have hle1 : (job_preemption_points j).length ≤ 1 := by omega
             have hfe : first0 (job_preemption_points j) = last0 (job_preemption_points j) := by
               cases hq : (job_preemption_points j) with
               | nil => simp [first0, last0, List.headD, List.getLastD]
               | cons a tl =>
                 cases tl with
                 | nil => simp [first0, last0, List.headD, List.getLastD]
                 | cons b rest => simp [hq] at hle1
             rw [h_beg, h_end] at hfe; omega
           have h_lsmd := last_seq_minus_last_distance_seq (job_preemption_points j) h_nd
           rw [h_end] at h_lsmd
           have h_last := last0_nth (job_preemption_points j)
           rw [h_end] at h_last
           have h_len_eq : (job_preemption_points j).length - 2 + 1 =
               (job_preemption_points j).length - 1 := by omega
           have h_jlns_eq : Prosa.Classic.Model.Schedule.Uni.Limited.Platform.Limited.ModelWithLimitedPreemptions.job_last_nps job_preemption_points j =
               last0 (distances (job_preemption_points j)) := rfl
           have h_gt : nthD (job_preemption_points j)
               ((job_preemption_points j).length - 2) < service sched j t' := by
             simp only [h_jlns_eq, Time, ε] at hS_ge hLAST_pos h_jlns_le h_lsmd ⊢; omega
           have h_lt : service sched j t' < nthD (job_preemption_points j)
               ((job_preemption_points j).length - 2 + 1) := by
             rw [h_len_eq, ← h_last]; exact hS_lt
           have h_not_mem := antidensity_of_nondecreasing_seq _ _ _ h_nd ⟨h_gt, h_lt⟩
           have h_cant : Prosa.Classic.Model.Schedule.Uni.Limited.Platform.Limited.ModelWithLimitedPreemptions.can_be_preempted_for_model_with_limited_preemptions
               job_preemption_points j (service sched j t') = false := by
             unfold Prosa.Classic.Model.Schedule.Uni.Limited.Platform.Limited.ModelWithLimitedPreemptions.can_be_preempted_for_model_with_limited_preemptions
             exact decide_eq_false h_not_mem
           exact H_schedule_with_limited_preemptions j t' hARR h_cant⟩
        ⟨Nat.sub_le _ _,
         fun j hARR hTSK => by
           have hCOST : job_cost j ≤ task_cost (job_task j) := H_job_cost_le_task_cost j hARR
           rw [hTSK] at hCOST
           by_cases hZERO : job_cost j = 0
           · simp only [Time, ε] at *; omega
           · have hPOS : job_cost j > 0 := Nat.pos_of_ne_zero hZERO
             have h_nd_j := H_model_with_fixed_preemption_points.1.2.2.2.2 j hARR
             have h_end_j := H_model_with_fixed_preemption_points.1.2.2.2.1 j hARR
             have h_beg_j := H_model_with_fixed_preemption_points.1.2.2.1 j hARR
             have h_nd_tsk := H_model_with_fixed_preemption_points.2.2.2.1 tsk H_tsk_in_ts
             have h_end_tsk := H_model_with_fixed_preemption_points.2.2.1 tsk H_tsk_in_ts
             have h_beg_tsk := H_model_with_fixed_preemption_points.2.1 tsk H_tsk_in_ts
             have h_same_len := H_model_with_fixed_preemption_points.2.2.2.2.1 j hARR
             have h_dist := H_model_with_fixed_preemption_points.2.2.2.2.2.1 j
             have h_len_j : 2 ≤ (job_preemption_points j).length := by
               by_contra hlt; push_neg at hlt
               have hle1 : (job_preemption_points j).length ≤ 1 := by omega
               have hfe : first0 (job_preemption_points j) = last0 (job_preemption_points j) := by
                 cases hq : (job_preemption_points j) with
                 | nil => simp [first0, last0, List.headD, List.getLastD]
                 | cons a tl =>
                   cases tl with
                   | nil => simp [first0, last0, List.headD, List.getLastD]
                   | cons b rest => simp [hq] at hle1
               rw [h_beg_j, h_end_j] at hfe; simp only [Time] at *; omega
             have h_len_tsk : 2 ≤ (task_preemption_points tsk).length := by
               have hsame := h_same_len; rw [hTSK] at hsame; omega
             have h_lsmd_j := last_seq_minus_last_distance_seq (job_preemption_points j) h_nd_j
             rw [h_end_j] at h_lsmd_j
             have h_lsmd_tsk := last_seq_minus_last_distance_seq (task_preemption_points tsk) h_nd_tsk
             rw [h_end_tsk] at h_lsmd_tsk
             have h_jlns_le : Prosa.Classic.Model.Schedule.Uni.Limited.Platform.Limited.ModelWithLimitedPreemptions.job_last_nps job_preemption_points j ≤ job_cost j :=
               le_trans (last_of_seq_le_max_of_seq _)
                 (le_trans (max_distance_in_seq_le_last_element_of_seq _ h_nd_j) (le_of_eq h_end_j))
             have h_tlns_le : Prosa.Classic.Model.Schedule.Uni.Limited.Platform.Limited.ModelWithLimitedPreemptions.task_last_nps task_preemption_points tsk ≤ task_cost tsk :=
               le_trans (last_of_seq_le_max_of_seq _)
                 (le_trans (max_distance_in_seq_le_last_element_of_seq _ h_nd_tsk) (le_of_eq h_end_tsk))
             have h_dom := domination_of_distances_implies_domination_of_seq
               (job_preemption_points j) (task_preemption_points tsk)
               (by rw [h_beg_j, h_beg_tsk])
               h_len_j h_len_tsk
               (by rw [h_same_len, hTSK])
               h_nd_j h_nd_tsk
               (fun n => by have := h_dist n hARR; rw [hTSK] at this; exact this)
             have h_len_eq : (job_preemption_points j).length = (task_preemption_points tsk).length := by
               rw [h_same_len, hTSK]
             have h_snd_last := h_dom ((task_preemption_points tsk).length - 2)
             rw [h_len_eq] at h_lsmd_j
             rw [← h_lsmd_j, ← h_lsmd_tsk] at h_snd_last
             have hLAST_pos := H_model_with_fixed_preemption_points.1.2.1 j hARR hPOS
             have h_nonempty := H_model_with_fixed_preemption_points.2.2.2.2.2.2
             have h_dist_len_pos : 0 < (distances (task_preemption_points tsk)).length := by
               have := size_of_seq_of_distances (task_preemption_points tsk) h_len_tsk; omega
             have h_tlns_pos : ε ≤ Prosa.Classic.Model.Schedule.Uni.Limited.Platform.Limited.ModelWithLimitedPreemptions.task_last_nps task_preemption_points tsk := by
               show ε ≤ last0 (distances (task_preemption_points tsk))
               rw [last0_nth]
               exact h_nonempty tsk ((distances (task_preemption_points tsk)).length - 1) H_tsk_in_ts (by omega)
             simp only [Prosa.Classic.Model.Schedule.Uni.Limited.Platform.Limited.ModelWithLimitedPreemptions.job_last_nps,
               Prosa.Classic.Model.Schedule.Uni.Limited.Platform.Limited.ModelWithLimitedPreemptions.task_last_nps,
               Prosa.Classic.Model.Schedule.Uni.Limited.Platform.Limited.ModelWithLimitedPreemptions.lengths_of_segments, Time, ε] at *
             omega⟩
        L H_L_positive H_fixed_point R
        (fun A hA => by
          have h_changes : bound_on_total_hep_workload_changes_at task_cost task_deadline max_arrivals ts tsk A =
              bound_on_total_hep_workload_changes_at_val task_cost task_deadline ts max_arrivals tsk A := by
            simp only [bound_on_total_hep_workload_changes_at, bound_on_total_hep_workload_changes_at_val]
            congr 1; ext tsk_o; congr 1; exact decide_eq_decide.mpr ne_comm
          rw [h_changes] at hA
          obtain ⟨F, hFIX, hLE⟩ := H_R_is_maximum A hA
          have h_hwl :
              _root_.Prosa.Classic.Model.Schedule.Uni.Limited.Edf.Nonpr_reg.Response_time_bound.RTAforEDFwithBoundedNonpreemptiveSegmentsWithArrivalCurves.bound_on_total_hep_workload
                task_cost task_deadline max_arrivals ts tsk A (A + F) =
              bound_on_total_hep_workload task_cost task_deadline ts max_arrivals tsk A (A + F) := rfl
          have h_bb :
              _root_.Prosa.Classic.Model.Schedule.Uni.Limited.Edf.Nonpr_reg.Response_time_bound.RTAforEDFwithBoundedNonpreemptiveSegmentsWithArrivalCurves.blocking_bound
                (Prosa.Classic.Model.Schedule.Uni.Limited.Platform.Limited.ModelWithLimitedPreemptions.task_max_nps
                  task_preemption_points) task_deadline ts tsk =
              blocking_bound_fixed task_deadline ts tsk task_preemption_points := rfl
          have h_nd_tsk := H_model_with_fixed_preemption_points.2.2.2.1 tsk H_tsk_in_ts
          have h_end_tsk := H_model_with_fixed_preemption_points.2.2.1 tsk H_tsk_in_ts
          have h_tlns_le : Prosa.Classic.Model.Schedule.Uni.Limited.Platform.Limited.ModelWithLimitedPreemptions.task_last_nps
              task_preemption_points tsk ≤ task_cost tsk :=
            le_trans (last_of_seq_le_max_of_seq _)
              (le_trans (max_distance_in_seq_le_last_element_of_seq _ h_nd_tsk) (le_of_eq h_end_tsk))
          exact ⟨F, by simp only [h_hwl, h_bb, Time, ε] at *; omega, by simp only [h_hwl, h_bb, Time, ε] at *; omega⟩)

  end RTAforFixedPreemptionPointsModelwithArrivalCurves

  section RTAforModelWithFloatingNonpreemptiveRegionsWithArrivalCurves

    variable (job_preemption_points : Job → List Time)
    variable (task_max_nps_val : Task → Time)
    variable (H_task_model_with_floating_nonpreemptive_regions :
      Prosa.Classic.Model.Schedule.Uni.Limited.Platform.Limited.ModelWithLimitedPreemptions.model_with_floating_nonpreemptive_regions
        job_cost job_task arr_seq job_preemption_points task_max_nps_val)

    variable (H_schedule_with_limited_preemptions :
      Prosa.Classic.Model.Schedule.Uni.Limited.Platform.Limited.ModelWithLimitedPreemptions.is_schedule_with_limited_preemptions
        arr_seq job_preemption_points sched)

    variable (H_respects_policy :
      respects_JLFP_policy_at_preemption_point
        job_arrival job_cost arr_seq sched
        (Prosa.Classic.Model.Schedule.Uni.Limited.Platform.Limited.ModelWithLimitedPreemptions.can_be_preempted_for_model_with_limited_preemptions
          job_preemption_points)
        (EDF job_arrival (fun j => task_deadline (job_task j))))

    def blocking_bound : Nat :=
      ((ts.filter (fun tsk_other =>
        decide (tsk_other ≠ tsk) && decide (task_deadline tsk < task_deadline tsk_other))).map
        (fun tsk_other => task_max_nps_val tsk_other - ε)).foldl max 0

    variable (L : Time)
    variable (H_L_positive : L > 0)
    variable (H_fixed_point : L = total_request_bound_function task_cost max_arrivals ts L)

    variable (R : Nat)
    variable (H_R_is_maximum :
      ∀ A,
        (decide (A < L) &&
          (task_rbf_changes_at_val task_cost max_arrivals tsk A ||
           bound_on_total_hep_workload_changes_at_val task_cost task_deadline ts max_arrivals tsk A)) = true →
        ∃ F,
          A + F = blocking_bound task_deadline ts tsk task_max_nps_val +
                  task_request_bound_function task_cost max_arrivals tsk (A + ε) +
                  bound_on_total_hep_workload task_cost task_deadline ts max_arrivals tsk A (A + F) ∧
          F ≤ R)

    include H_arrival_times_are_consistent H_arr_seq_is_a_set H_all_jobs_from_taskset
      H_job_cost_le_task_cost H_family_of_proper_arrival_curves H_tsk_in_ts
      H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute
      H_completed_jobs_dont_execute H_sequential_jobs H_work_conserving
      H_task_model_with_floating_nonpreemptive_regions H_schedule_with_limited_preemptions
      H_respects_policy H_L_positive H_fixed_point H_R_is_maximum in
    include H_arrival_times_are_consistent H_arr_seq_is_a_set H_all_jobs_from_taskset H_job_cost_le_task_cost H_family_of_proper_arrival_curves H_tsk_in_ts H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_sequential_jobs H_work_conserving H_task_model_with_floating_nonpreemptive_regions H_schedule_with_limited_preemptions H_respects_policy H_L_positive H_fixed_point H_R_is_maximum in
    theorem uniprocessor_response_time_bound_edf_with_floating_nonpreemptive_regions :
        is_response_time_bound_of_task job_arrival job_cost job_task arr_seq sched tsk R := by
      exact uniprocessor_response_time_bound_edf_with_bounded_nonpreemptive_segments
        task_max_nps_val task_cost task_deadline
        job_arrival
        (Prosa.Classic.Model.Schedule.Uni.Limited.Platform.Limited.ModelWithLimitedPreemptions.job_max_nps
          job_preemption_points)
        job_cost job_task
        arr_seq H_arrival_times_are_consistent H_arr_seq_is_a_set
        sched H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute
        H_sequential_jobs
        (Prosa.Classic.Model.Schedule.Uni.Limited.Platform.Limited.ModelWithLimitedPreemptions.can_be_preempted_for_model_with_limited_preemptions
          job_preemption_points)
        (Prosa.Classic.Model.Schedule.Uni.Limited.Platform.Limited.ModelWithLimitedPreemptions.model_with_fixed_preemption_points_is_correct
          arr_seq job_preemption_points sched H_schedule_with_limited_preemptions)
        (Prosa.Classic.Model.Schedule.Uni.Limited.Platform.Limited.ModelWithLimitedPreemptions.model_with_fixed_preemption_points_is_model_with_bounded_nonpreemptive_regions
          job_cost job_task arr_seq job_preemption_points task_max_nps_val
          H_task_model_with_floating_nonpreemptive_regions.1
          H_task_model_with_floating_nonpreemptive_regions.2)
        H_work_conserving H_respects_policy
        ts H_all_jobs_from_taskset H_job_cost_le_task_cost
        tsk H_tsk_in_ts max_arrivals H_family_of_proper_arrival_curves
        (fun j => job_cost j - (Prosa.Classic.Model.Schedule.Uni.Limited.Platform.Limited.ModelWithLimitedPreemptions.job_last_nps job_preemption_points j - ε))
        (fun _t => task_cost _t)
        ⟨fun j hARR hPOS => by
           have hLAST := H_task_model_with_floating_nonpreemptive_regions.1.2.1 j hARR hPOS
           have h_nd_j := H_task_model_with_floating_nonpreemptive_regions.1.2.2.2.2 j hARR
           have h_end_j := H_task_model_with_floating_nonpreemptive_regions.1.2.2.2.1 j hARR
           have h_jlns_le : Prosa.Classic.Model.Schedule.Uni.Limited.Platform.Limited.ModelWithLimitedPreemptions.job_last_nps job_preemption_points j ≤ job_cost j :=
             le_trans (last_of_seq_le_max_of_seq _)
               (le_trans (max_distance_in_seq_le_last_element_of_seq _ h_nd_j) (le_of_eq h_end_j))
           simp only [Time, ε] at *; omega,
         fun j _hARR _hPOS => Nat.sub_le _ _,
         fun j t t' hARR hLE hSERV hNCOMPL => by
           have h_nd := H_task_model_with_floating_nonpreemptive_regions.1.2.2.2.2 j hARR
           have h_end := H_task_model_with_floating_nonpreemptive_regions.1.2.2.2.1 j hARR
           have h_beg := H_task_model_with_floating_nonpreemptive_regions.1.2.2.1 j hARR
           have hS_lt : service sched j t' < job_cost j := not_le.mp hNCOMPL
           have hS_ge : job_cost j -
               (Prosa.Classic.Model.Schedule.Uni.Limited.Platform.Limited.ModelWithLimitedPreemptions.job_last_nps job_preemption_points j - ε) ≤
               service sched j t' := le_trans hSERV (service_monotonic sched j t t' hLE)
           have hPOS : job_cost j > 0 := Nat.lt_of_le_of_lt (Nat.zero_le _) hS_lt
           have hLAST_pos := H_task_model_with_floating_nonpreemptive_regions.1.2.1 j hARR hPOS
           have h_jlns_le : Prosa.Classic.Model.Schedule.Uni.Limited.Platform.Limited.ModelWithLimitedPreemptions.job_last_nps job_preemption_points j ≤ job_cost j :=
             le_trans (last_of_seq_le_max_of_seq _)
               (le_trans (max_distance_in_seq_le_last_element_of_seq _ h_nd) (le_of_eq h_end))
           have h_len : 2 ≤ (job_preemption_points j).length := by
             by_contra hlt; push_neg at hlt
             have hle1 : (job_preemption_points j).length ≤ 1 := by omega
             have hfe : first0 (job_preemption_points j) = last0 (job_preemption_points j) := by
               cases hq : (job_preemption_points j) with
               | nil => simp [first0, last0, List.headD, List.getLastD]
               | cons a tl =>
                 cases tl with
                 | nil => simp [first0, last0, List.headD, List.getLastD]
                 | cons b rest => simp [hq] at hle1
             rw [h_beg, h_end] at hfe; omega
           have h_lsmd := last_seq_minus_last_distance_seq (job_preemption_points j) h_nd
           rw [h_end] at h_lsmd
           have h_last := last0_nth (job_preemption_points j)
           rw [h_end] at h_last
           have h_len_eq : (job_preemption_points j).length - 2 + 1 =
               (job_preemption_points j).length - 1 := by omega
           have h_jlns_eq : Prosa.Classic.Model.Schedule.Uni.Limited.Platform.Limited.ModelWithLimitedPreemptions.job_last_nps job_preemption_points j =
               last0 (distances (job_preemption_points j)) := rfl
           have h_gt : nthD (job_preemption_points j)
               ((job_preemption_points j).length - 2) < service sched j t' := by
             simp only [h_jlns_eq, Time, ε] at hS_ge hLAST_pos h_jlns_le h_lsmd ⊢; omega
           have h_lt : service sched j t' < nthD (job_preemption_points j)
               ((job_preemption_points j).length - 2 + 1) := by
             rw [h_len_eq, ← h_last]; exact hS_lt
           have h_not_mem := antidensity_of_nondecreasing_seq _ _ _ h_nd ⟨h_gt, h_lt⟩
           have h_cant : Prosa.Classic.Model.Schedule.Uni.Limited.Platform.Limited.ModelWithLimitedPreemptions.can_be_preempted_for_model_with_limited_preemptions
               job_preemption_points j (service sched j t') = false := by
             unfold Prosa.Classic.Model.Schedule.Uni.Limited.Platform.Limited.ModelWithLimitedPreemptions.can_be_preempted_for_model_with_limited_preemptions
             exact decide_eq_false h_not_mem
           exact H_schedule_with_limited_preemptions j t' hARR h_cant⟩
        ⟨le_refl _,
         fun j hARR hTSK => by
           have hCOST : job_cost j ≤ task_cost (job_task j) := H_job_cost_le_task_cost j hARR
           rw [hTSK] at hCOST
           exact le_trans (Nat.sub_le _ _) hCOST⟩
        L H_L_positive H_fixed_point R
        (fun A hA => by
          have h_changes : bound_on_total_hep_workload_changes_at task_cost task_deadline max_arrivals ts tsk A =
              bound_on_total_hep_workload_changes_at_val task_cost task_deadline ts max_arrivals tsk A := by
            simp only [bound_on_total_hep_workload_changes_at, bound_on_total_hep_workload_changes_at_val]
            congr 1; ext tsk_o; congr 1; exact decide_eq_decide.mpr ne_comm
          rw [h_changes] at hA
          obtain ⟨F, hFIX, hLE⟩ := H_R_is_maximum A hA
          have h_hwl :
              _root_.Prosa.Classic.Model.Schedule.Uni.Limited.Edf.Nonpr_reg.Response_time_bound.RTAforEDFwithBoundedNonpreemptiveSegmentsWithArrivalCurves.bound_on_total_hep_workload
                task_cost task_deadline max_arrivals ts tsk A (A + F) =
              bound_on_total_hep_workload task_cost task_deadline ts max_arrivals tsk A (A + F) := rfl
          have h_bb :
              _root_.Prosa.Classic.Model.Schedule.Uni.Limited.Edf.Nonpr_reg.Response_time_bound.RTAforEDFwithBoundedNonpreemptiveSegmentsWithArrivalCurves.blocking_bound
                task_max_nps_val task_deadline ts tsk =
              blocking_bound task_deadline ts tsk task_max_nps_val := rfl
          exact ⟨F, by simp only [h_hwl, h_bb, Nat.sub_self, Nat.sub_zero, Nat.add_zero, Time] at *; omega,
            by simp only [Nat.sub_self, Nat.add_zero]; exact hLE⟩)

  end RTAforModelWithFloatingNonpreemptiveRegionsWithArrivalCurves

end Analysis

end RTAforConcreteModels

end Prosa.Classic.Model.Schedule.Uni.Limited.Edf.Nonpr_reg.Concrete_models.Response_time_bound
