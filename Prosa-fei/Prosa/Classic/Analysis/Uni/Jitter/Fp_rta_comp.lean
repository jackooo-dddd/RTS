-- Translated from: ../rt-proofs/classic/analysis/uni/jitter/fp_rta_comp.v
import Prosa.Classic.Util.All
import Prosa.Classic.Model.Priority
import Prosa.Classic.Model.Arrival.Basic.Task
import Prosa.Classic.Model.Arrival.Jitter.Job
import Prosa.Classic.Model.Schedule.Uni.Schedulability
import Prosa.Classic.Model.Schedule.Uni.Jitter.Schedule
import Prosa.Classic.Model.Schedule.Uni.Jitter.Platform
import Prosa.Classic.Analysis.Uni.Jitter.Workload_bound_fp
import Prosa.Classic.Analysis.Uni.Jitter.Fp_rta_theory

namespace Prosa.Classic.Analysis.Uni.Jitter.Fp_rta_comp

open Prosa.Classic.Model.Time
open Prosa.Classic.Model.Priority
open Prosa.Classic.Model.Arrival.Basic.Task.SporadicTaskset
open Prosa.Classic.Model.Arrival.Basic.Arrival_sequence
open Prosa.Classic.Model.Arrival.Basic.Task_arrival
open Prosa.Classic.Model.Arrival.Jitter.Arrival_sequence
open Prosa.Classic.Model.Schedule.Uni.Schedule
open Prosa.Classic.Model.Schedule.Uni.Schedulability
open Prosa.Classic.Model.Schedule.Uni.Jitter.Schedule
open Prosa.Classic.Model.Schedule.Uni.Jitter.Platform.Platform
open Prosa.Classic.Analysis.Uni.Jitter.Workload_bound_fp.WorkloadBoundFP
open Prosa.Classic.Util.Fixedpoint

namespace ResponseTimeIterationFP

section Analysis

  variable {SporadicTask : Type _} [DecidableEq SporadicTask]
  variable (task_cost : SporadicTask → Time)
  variable (task_period : SporadicTask → Time)
  variable (task_deadline : SporadicTask → Time)
  variable (task_jitter : SporadicTask → Time)

  variable (higher_eq_priority : FP_policy SporadicTask)

  def max_steps (tsk : SporadicTask) : Nat :=
    task_deadline tsk - task_cost tsk + 1

  def per_task_rta (ts : List SporadicTask) (tsk : SporadicTask) : Option Nat :=
    iter_fixpoint (total_workload_bound_fp task_cost task_period task_jitter higher_eq_priority ts tsk)
      (max_steps task_cost task_deadline tsk) (task_cost tsk)

  private def is_valid_bound (tsk_R : SporadicTask × Option Nat) : Option (SporadicTask × Nat) :=
    match tsk_R with
    | (tsk, some R) =>
      if task_jitter tsk + R ≤ task_deadline tsk then
        some (tsk, R)
      else none
    | (_, none) => none

  def fp_claimed_bounds (ts : List SporadicTask) : Option (List (SporadicTask × Nat)) :=
    let possible_bounds := ts.map (fun tsk => (tsk, per_task_rta task_cost task_period task_deadline task_jitter higher_eq_priority ts tsk))
    if possible_bounds.all (fun p => (is_valid_bound task_deadline task_jitter p).isSome) then
      some (possible_bounds.filterMap (is_valid_bound task_deadline task_jitter))
    else none

  def fp_schedulable (ts : List SporadicTask) : Bool :=
    (fp_claimed_bounds task_cost task_period task_deadline task_jitter higher_eq_priority ts).isSome

  section Lemmas

    variable (ts : List SporadicTask)

    variable (rt_bounds : List (SporadicTask × Nat))
    variable (H_analysis_succeeds :
      fp_claimed_bounds task_cost task_period task_deadline task_jitter higher_eq_priority ts = some rt_bounds)

    include H_analysis_succeeds

    -- Helper lemma to extract information from fp_claimed_bounds
    private theorem extract_from_bounds (tsk : SporadicTask) (R : Nat)
        (H_tsk_R_computed : (tsk, R) ∈ rt_bounds) :
        ∃ tsk' R',
          (tsk', some R') ∈ (ts.map (fun tsk => (tsk, per_task_rta task_cost task_period task_deadline task_jitter higher_eq_priority ts tsk))) ∧
          task_jitter tsk' + R' ≤ task_deadline tsk' ∧ tsk' = tsk ∧ R' = R := by
      have SOME := H_analysis_succeeds
      simp only [fp_claimed_bounds] at SOME
      set pb := ts.map (fun tsk => (tsk, per_task_rta task_cost task_period task_deadline task_jitter higher_eq_priority ts tsk))
      by_cases h_all : pb.all (fun p => (is_valid_bound task_deadline task_jitter p).isSome) = true
      · rw [if_pos h_all] at SOME
        have h_inj := Option.some.inj SOME
        rw [← h_inj] at H_tsk_R_computed
        rw [List.mem_filterMap] at H_tsk_R_computed
        obtain ⟨⟨tsk', optR⟩, h_mem, h_valid⟩ := H_tsk_R_computed
        cases optR with
        | none => simp [is_valid_bound] at h_valid
        | some R' =>
          dsimp only [is_valid_bound] at h_valid
          split_ifs at h_valid with h_le
          · have h_eq := Option.some.inj h_valid
            obtain ⟨h1, h2⟩ := Prod.mk.inj h_eq
            exact ⟨tsk', R', h_mem, h_le, h1, h2⟩
      · rw [if_neg h_all] at SOME; exact absurd SOME (by simp)

    section BoundExists

      variable (tsk : SporadicTask)
      variable (H_tsk_in_ts : tsk ∈ ts)

      include H_analysis_succeeds H_tsk_in_ts

      theorem fp_claimed_bounds_for_every_task :
          ∃ R, (tsk, R) ∈ rt_bounds := by
        have SOME := H_analysis_succeeds
        simp only [fp_claimed_bounds] at SOME
        set pb := ts.map (fun tsk => (tsk, per_task_rta task_cost task_period task_deadline task_jitter higher_eq_priority ts tsk))
        by_cases h_all : pb.all (fun p => (is_valid_bound task_deadline task_jitter p).isSome) = true
        · rw [if_pos h_all] at SOME
          have h_inj := Option.some.inj SOME
          have h_in_pb : (tsk, per_task_rta task_cost task_period task_deadline task_jitter higher_eq_priority ts tsk) ∈ pb := by
            apply List.mem_map.mpr; exact ⟨tsk, H_tsk_in_ts, rfl⟩
          have h_all_pred : (is_valid_bound task_deadline task_jitter (tsk, per_task_rta task_cost task_period task_deadline task_jitter higher_eq_priority ts tsk)).isSome = true :=
            List.all_eq_true.mp h_all _ h_in_pb
          cases h_rta : per_task_rta task_cost task_period task_deadline task_jitter higher_eq_priority ts tsk with
          | none =>
            rw [h_rta] at h_all_pred
            simp [is_valid_bound] at h_all_pred
          | some R =>
            rw [h_rta] at h_all_pred
            simp only [is_valid_bound] at h_all_pred
            by_cases h_le : task_jitter tsk + R ≤ task_deadline tsk
            · have h_in_pb' : (tsk, some R) ∈ pb := h_rta ▸ h_in_pb
              exact ⟨R, by rw [← h_inj]; exact List.mem_filterMap.mpr ⟨(tsk, some R), h_in_pb', by simp [is_valid_bound, h_le]⟩⟩
            · simp [h_le] at h_all_pred
        · rw [if_neg h_all] at SOME; exact absurd SOME (by simp)

    end BoundExists

    section PropertiesOfBound

      variable (tsk : SporadicTask)
      variable (R : Nat)
      variable (H_tsk_R_computed : (tsk, R) ∈ rt_bounds)

      include H_analysis_succeeds H_tsk_R_computed

      theorem fp_claimed_bounds_from_taskset :
          tsk ∈ ts := by
        obtain ⟨tsk', R', h_mem, _, h_tsk_eq, _⟩ := extract_from_bounds task_cost task_period task_deadline task_jitter higher_eq_priority ts rt_bounds H_analysis_succeeds tsk R H_tsk_R_computed
        subst h_tsk_eq
        obtain ⟨t, ht_in, ht_eq⟩ := List.mem_map.mp h_mem
        exact (Prod.mk.inj ht_eq).1 ▸ ht_in

      theorem fp_claimed_bounds_computes_iteration :
          per_task_rta task_cost task_period task_deadline task_jitter higher_eq_priority ts tsk = some R := by
        obtain ⟨tsk', R', h_mem, _, h_tsk_eq, h_R_eq⟩ := extract_from_bounds task_cost task_period task_deadline task_jitter higher_eq_priority ts rt_bounds H_analysis_succeeds tsk R H_tsk_R_computed
        subst h_tsk_eq; subst h_R_eq
        obtain ⟨t, ht_in, ht_eq⟩ := List.mem_map.mp h_mem
        have h1 := (Prod.mk.inj ht_eq).1
        subst h1
        exact (Prod.mk.inj ht_eq).2

      theorem fp_claimed_bounds_yields_fixed_point :
          R = total_workload_bound_fp task_cost task_period task_jitter higher_eq_priority ts tsk R := by
        have ITER := fp_claimed_bounds_computes_iteration task_cost task_period task_deadline task_jitter higher_eq_priority ts rt_bounds H_analysis_succeeds tsk R H_tsk_R_computed
        unfold per_task_rta at ITER
        have h_cases := iter_fixpoint_cases (total_workload_bound_fp task_cost task_period task_jitter higher_eq_priority ts tsk) (max_steps task_cost task_deadline tsk) (task_cost tsk)
        cases h_cases with
        | inl h_none => rw [h_none] at ITER; exact absurd ITER (by simp)
        | inr h_some =>
          obtain ⟨R', hR'_eq, hR'_fix⟩ := h_some
          rw [hR'_eq] at ITER
          have : R = R' := Option.some.inj ITER.symm
          subst this
          exact hR'_fix

      theorem fp_claimed_bounds_le_deadline :
          task_jitter tsk + R ≤ task_deadline tsk := by
        obtain ⟨tsk', R', _, h_le, h_tsk_eq, h_R_eq⟩ := extract_from_bounds task_cost task_period task_deadline task_jitter higher_eq_priority ts rt_bounds H_analysis_succeeds tsk R H_tsk_R_computed
        subst h_tsk_eq; subst h_R_eq
        exact h_le

      section FixedPoint

        variable (H_priority_is_reflexive : FP_is_reflexive higher_eq_priority)

        variable (H_cost_positive : task_cost tsk > 0)
        variable (H_period_positive :
          ∀ tsk, tsk ∈ ts → task_period tsk > 0)

        include H_priority_is_reflexive H_cost_positive H_period_positive

        theorem fp_claimed_bounds_ge_cost :
            R ≥ task_cost tsk := by
          have ITER := fp_claimed_bounds_computes_iteration task_cost task_period task_deadline task_jitter higher_eq_priority ts rt_bounds H_analysis_succeeds tsk R H_tsk_R_computed
          unfold per_task_rta at ITER
          have h_from_ts := fp_claimed_bounds_from_taskset task_cost task_period task_deadline task_jitter higher_eq_priority ts rt_bounds H_analysis_succeeds tsk R H_tsk_R_computed
          have h_mon : Prosa.Classic.Util.Fixedpoint.monotone (total_workload_bound_fp task_cost task_period task_jitter higher_eq_priority ts tsk) (· ≤ ·) := by
            intro x1 x2 hle
            exact total_workload_bound_fp_non_decreasing task_cost task_period task_jitter higher_eq_priority ts tsk H_period_positive x1 x2 hle
          have h_ge : task_cost tsk ≤ total_workload_bound_fp task_cost task_period task_jitter higher_eq_priority ts tsk (task_cost tsk) := by
            exact total_workload_bound_fp_ge_cost task_cost task_period task_jitter higher_eq_priority ts tsk h_from_ts H_priority_is_reflexive H_cost_positive (H_period_positive tsk h_from_ts)
          exact iter_fixpoint_ge_bottom (total_workload_bound_fp task_cost task_period task_jitter higher_eq_priority ts tsk) (· ≤ ·) (fun x => le_refl x) (fun x y z hxy hyz => le_trans hxy hyz) h_mon (max_steps task_cost task_deadline tsk) (task_cost tsk) R ITER h_ge

        theorem fp_claimed_bounds_gt_zero : R > 0 := by
          exact Nat.lt_of_lt_of_le H_cost_positive (fp_claimed_bounds_ge_cost task_cost task_period task_deadline task_jitter higher_eq_priority ts rt_bounds H_analysis_succeeds tsk R H_tsk_R_computed H_priority_is_reflexive H_cost_positive H_period_positive)

      end FixedPoint

    end PropertiesOfBound

  end Lemmas

end Analysis

section ProvingCorrectness

  variable {SporadicTask : Type _} [DecidableEq SporadicTask]
  variable (task_cost : SporadicTask → Time)
  variable (task_period : SporadicTask → Time)
  variable (task_deadline : SporadicTask → Time)
  variable (task_jitter : SporadicTask → Time)

  variable {Job : Type _} [DecidableEq Job]
  variable (job_arrival : Job → Time)
  variable (job_cost : Job → Time)
  variable (job_deadline : Job → Time)
  variable (job_jitter : Job → Time)
  variable (job_task : Job → SporadicTask)

  variable (ts : List SporadicTask)

  variable (H_positive_costs : ∀ tsk, tsk ∈ ts → task_cost tsk > 0)
  variable (H_positive_periods : ∀ tsk, tsk ∈ ts → task_period tsk > 0)

  variable (arr_seq : arrival_sequence Job)
  variable (H_arrival_times_are_consistent : arrival_times_are_consistent job_arrival arr_seq)
  variable (H_arr_seq_is_a_set : arrival_sequence_is_a_set arr_seq)

  variable (H_all_jobs_from_taskset :
    ∀ j, arrives_in arr_seq j → job_task j ∈ ts)

  variable (H_sporadic_tasks :
    sporadic_task_model task_period job_arrival job_task arr_seq)

  variable (H_job_cost_le_task_cost :
    ∀ j, arrives_in arr_seq j → job_cost j ≤ task_cost (job_task j))

  variable (H_job_jitter_le_task_jitter :
    ∀ j, arrives_in arr_seq j → job_jitter j ≤ task_jitter (job_task j))

  variable (H_job_deadline_eq_task_deadline :
    ∀ j, arrives_in arr_seq j → job_deadline j = task_deadline (job_task j))

  variable (higher_eq_priority : FP_policy SporadicTask)

  variable (H_priority_reflexive : FP_is_reflexive higher_eq_priority)
  variable (H_priority_transitive : FP_is_transitive higher_eq_priority)

  variable (sched : Prosa.Classic.Model.Schedule.Uni.Schedule.schedule Job)
  variable (H_jobs_come_from_arrival_sequence :
    Prosa.Classic.Model.Schedule.Uni.Schedule.jobs_come_from_arrival_sequence sched arr_seq)

  variable (H_jobs_execute_after_jitter :
    Prosa.Classic.Model.Schedule.Uni.Jitter.Schedule.jobs_execute_after_jitter job_arrival job_jitter sched)
  variable (H_completed_jobs_dont_execute :
    Prosa.Classic.Model.Schedule.Uni.Schedule.completed_jobs_dont_execute job_cost sched)

  variable (H_work_conserving :
    Prosa.Classic.Model.Schedule.Uni.Jitter.Platform.Platform.work_conserving
      job_arrival job_cost job_jitter arr_seq sched)
  variable (H_respects_FP_policy :
    Prosa.Classic.Model.Schedule.Uni.Jitter.Platform.Platform.respects_FP_policy
      job_arrival job_cost job_jitter job_task arr_seq sched higher_eq_priority)

  include H_positive_costs H_positive_periods H_arrival_times_are_consistent
          H_arr_seq_is_a_set H_all_jobs_from_taskset H_sporadic_tasks
          H_job_cost_le_task_cost H_job_jitter_le_task_jitter
          H_job_deadline_eq_task_deadline H_priority_reflexive
          H_priority_transitive H_jobs_come_from_arrival_sequence
          H_jobs_execute_after_jitter H_completed_jobs_dont_execute
          H_work_conserving H_respects_FP_policy

  theorem fp_analysis_yields_response_time_bounds :
      ∀ tsk R,
        (match fp_claimed_bounds task_cost task_period task_deadline task_jitter higher_eq_priority ts with
         | some rt_bounds => (tsk, R) ∈ rt_bounds
         | none => False) →
        Prosa.Classic.Model.Schedule.Uni.Schedulability.is_response_time_bound_of_task
          job_arrival job_cost job_task arr_seq sched tsk (task_jitter tsk + R) := by
    intro tsk R h_match
    -- Extract rt_bounds from the match
    set bounds_opt := fp_claimed_bounds task_cost task_period task_deadline task_jitter higher_eq_priority ts with h_bounds_def
    cases h_case : bounds_opt with
    | none => rw [h_case] at h_match; exact absurd h_match id
    | some rt_bounds =>
      rw [h_case] at h_match
      -- Now h_match : (tsk, R) ∈ rt_bounds
      -- Get key properties from the analysis lemmas
      have h_from_ts := fp_claimed_bounds_from_taskset task_cost task_period task_deadline task_jitter higher_eq_priority ts rt_bounds h_case tsk R h_match
      have h_fp := fp_claimed_bounds_yields_fixed_point task_cost task_period task_deadline task_jitter higher_eq_priority ts rt_bounds h_case tsk R h_match
      have h_R_gt := fp_claimed_bounds_gt_zero task_cost task_period task_deadline task_jitter higher_eq_priority ts rt_bounds h_case tsk R h_match H_priority_reflexive (H_positive_costs tsk h_from_ts) H_positive_periods
      -- Apply the main RTA theorem from Fp_rta_theory
      have h_rta := Prosa.Classic.Analysis.Uni.Jitter.Fp_rta_theory.ResponseTimeAnalysisFP.uniprocessor_response_time_bound_fp
        task_cost task_period task_jitter
        job_arrival job_cost job_jitter job_task
        ts H_positive_periods arr_seq H_arrival_times_are_consistent H_arr_seq_is_a_set
        H_sporadic_tasks H_job_cost_le_task_cost H_job_jitter_le_task_jitter
        H_all_jobs_from_taskset sched H_jobs_come_from_arrival_sequence
        H_jobs_execute_after_jitter H_completed_jobs_dont_execute
        higher_eq_priority H_priority_reflexive H_priority_transitive
        H_work_conserving H_respects_FP_policy
        tsk h_from_ts R h_R_gt h_fp
      -- h_rta gives us the bound in terms of ResponseTime.is_response_time_bound_of_task
      -- We need it in terms of Schedulability.is_response_time_bound_of_task
      -- These are propositionally equal: both say ∀ j, ... → completed_by ...
      -- The difference is only in how service_at is defined (Bool.toNat vs if-then-else)
      intro j h_arrives h_task
      have h_bound := h_rta j h_arrives h_task
      -- h_bound uses Schedule.completed_by, goal uses Schedulability.completed_by
      -- Both are job_cost j ≤ service sched j (job_arrival j + ...)
      -- where service = service_during 0 t = ∑ ... service_at
      -- Schedule.service_at uses Bool.toNat, Schedulability.service_at uses if-then-else
      show Prosa.Classic.Model.Schedule.Uni.Schedulability.completed_by job_cost sched j (job_arrival j + (task_jitter tsk + R))
      unfold Prosa.Classic.Model.Schedule.Uni.Schedulability.completed_by
        Prosa.Classic.Model.Schedule.Uni.Schedulability.service
        Prosa.Classic.Model.Schedule.Uni.Schedulability.service_during
        Prosa.Classic.Model.Schedule.Uni.Schedulability.service_at
        Prosa.Classic.Model.Schedule.Uni.Schedulability.scheduled_at
      show job_cost j ≤ ∑ t ∈ Finset.Ico 0 (job_arrival j + (task_jitter tsk + R)),
        if (sched t == some j) = true then 1 else 0
      -- h_bound : Schedule.completed_by = job_cost j ≤ ∑ ... Bool.toNat
      unfold Prosa.Classic.Model.Schedule.Uni.Response_time.ResponseTime.is_response_time_bound_of_job
        Prosa.Classic.Model.Schedule.Uni.Schedule.completed_by
        Prosa.Classic.Model.Schedule.Uni.Schedule.service
        Prosa.Classic.Model.Schedule.Uni.Schedule.service_during
        Prosa.Classic.Model.Schedule.Uni.Schedule.service_at
        Prosa.Classic.Model.Schedule.Uni.Schedule.scheduled_at at h_bound
      calc job_cost j
          ≤ ∑ t ∈ Finset.Ico 0 (job_arrival j + (task_jitter tsk + R)),
              (sched t == some j).toNat := h_bound
        _ = ∑ t ∈ Finset.Ico 0 (job_arrival j + (task_jitter tsk + R)),
              (if (sched t == some j) = true then 1 else 0) := by
            apply Finset.sum_congr rfl
            intro t _
            cases (sched t == some j) <;> simp

  section AnalysisIsSufficient

    variable (H_test_succeeds :
      fp_schedulable task_cost task_period task_deadline task_jitter higher_eq_priority ts = true)

    include H_test_succeeds

    theorem taskset_schedulable_by_fp_rta :
        ∀ tsk, tsk ∈ ts →
          Prosa.Classic.Model.Schedule.Uni.Schedulability.task_misses_no_deadline
            job_arrival job_cost job_deadline job_task arr_seq sched tsk := by
      intro tsk h_in
      have h_test := H_test_succeeds
      simp only [fp_schedulable, Option.isSome_iff_exists] at h_test
      obtain ⟨rt_bounds, h_bounds⟩ := h_test
      obtain ⟨R, h_R_in⟩ := fp_claimed_bounds_for_every_task task_cost task_period task_deadline task_jitter higher_eq_priority ts rt_bounds h_bounds tsk h_in
      have h_le := fp_claimed_bounds_le_deadline task_cost task_period task_deadline task_jitter higher_eq_priority ts rt_bounds h_bounds tsk R h_R_in
      have h_match : (match fp_claimed_bounds task_cost task_period task_deadline task_jitter higher_eq_priority ts with
         | some rt_bounds => (tsk, R) ∈ rt_bounds
         | none => False) := by rw [h_bounds]; exact h_R_in
      have h_bound := fp_analysis_yields_response_time_bounds task_cost task_period task_deadline task_jitter job_arrival job_cost job_deadline job_jitter job_task ts H_positive_costs H_positive_periods arr_seq H_arrival_times_are_consistent H_arr_seq_is_a_set H_all_jobs_from_taskset H_sporadic_tasks H_job_cost_le_task_cost H_job_jitter_le_task_jitter H_job_deadline_eq_task_deadline higher_eq_priority H_priority_reflexive H_priority_transitive sched H_jobs_come_from_arrival_sequence H_jobs_execute_after_jitter H_completed_jobs_dont_execute H_work_conserving H_respects_FP_policy tsk R h_match
      have h_cjde : Prosa.Classic.Model.Schedule.Uni.Schedulability.completed_jobs_dont_execute job_cost sched := by
        intro j t
        have h1 := H_completed_jobs_dont_execute j t
        show Prosa.Classic.Model.Schedule.Uni.Schedulability.service sched j t ≤ job_cost j
        have h_serv : Prosa.Classic.Model.Schedule.Uni.Schedule.service sched j t =
                      Prosa.Classic.Model.Schedule.Uni.Schedulability.service sched j t := by
          unfold Prosa.Classic.Model.Schedule.Uni.Schedule.service Prosa.Classic.Model.Schedule.Uni.Schedulability.service
          unfold Prosa.Classic.Model.Schedule.Uni.Schedule.service_during Prosa.Classic.Model.Schedule.Uni.Schedulability.service_during
          congr 1; ext t'
          unfold Prosa.Classic.Model.Schedule.Uni.Schedule.service_at Prosa.Classic.Model.Schedule.Uni.Schedule.scheduled_at
          unfold Prosa.Classic.Model.Schedule.Uni.Schedulability.service_at Prosa.Classic.Model.Schedule.Uni.Schedulability.scheduled_at
          simp [Bool.toNat, beq_iff_eq]
        rw [← h_serv]; exact h1
      exact Prosa.Classic.Model.Schedule.Uni.Schedulability.task_completes_before_deadline job_arrival job_cost job_deadline job_task arr_seq sched task_deadline H_job_deadline_eq_task_deadline h_cjde tsk (task_jitter tsk + R) h_le h_bound

    theorem jobs_schedulable_by_fp_rta :
        ∀ j, arrives_in arr_seq j →
          Prosa.Classic.Model.Schedule.Uni.Schedulability.job_misses_no_deadline
            job_arrival job_cost job_deadline sched j := by
      intro j h_arr
      have h_sched := taskset_schedulable_by_fp_rta task_cost task_period task_deadline task_jitter job_arrival job_cost job_deadline job_jitter job_task ts H_positive_costs H_positive_periods arr_seq H_arrival_times_are_consistent H_arr_seq_is_a_set H_all_jobs_from_taskset H_sporadic_tasks H_job_cost_le_task_cost H_job_jitter_le_task_jitter H_job_deadline_eq_task_deadline higher_eq_priority H_priority_reflexive H_priority_transitive sched H_jobs_come_from_arrival_sequence H_jobs_execute_after_jitter H_completed_jobs_dont_execute H_work_conserving H_respects_FP_policy H_test_succeeds
      exact h_sched (job_task j) (H_all_jobs_from_taskset j h_arr) j h_arr rfl

  end AnalysisIsSufficient

end ProvingCorrectness

end ResponseTimeIterationFP

end Prosa.Classic.Analysis.Uni.Jitter.Fp_rta_comp
