-- Authoritative source:
-- ProsaBuddy classic Prosa (prosabuddy commit f692cb7479780cf6009493f373a309e13165201c)
-- source: classic/model/schedule/uni/limited/edf/nonpr_reg/concrete_models/response_time_bound.v
-- sha256: see Prosa-Shunqi/classic-prosa/comprehensive-classic/file_order.csv (rank 188)

import Prosa.Classic.Util.All
import Prosa.Classic.Model.Arrival.Basic.Job
import Prosa.Classic.Model.Arrival.Basic.TaskArrival
import Prosa.Classic.Model.Priority
import Prosa.Classic.Model.Schedule.Uni.Service
import Prosa.Classic.Model.Schedule.Uni.Workload
import Prosa.Classic.Model.Schedule.Uni.Schedule
import Prosa.Classic.Model.Schedule.Uni.ResponseTime
import Prosa.Classic.Model.Schedule.Uni.Limited.Schedule
import Prosa.Classic.Model.Schedule.Uni.Limited.Edf.ResponseTimeBound
import Prosa.Classic.Model.Schedule.Uni.Limited.Edf.NonprReg.ResponseTimeBound
import Prosa.Classic.Model.Schedule.Uni.Limited.Rbf
import Prosa.Classic.Model.Arrival.Curves.Bounds
import Prosa.Classic.Analysis.Uni.ArrivalCurves.WorkloadBound
import Prosa.Classic.Model.Schedule.Uni.Nonpreemptive.Schedule
import Prosa.Classic.Model.Schedule.Uni.Limited.Platform.Limited
import Prosa.Classic.Model.Schedule.Uni.Limited.Platform.Preemptive
import Prosa.Classic.Model.Schedule.Uni.Limited.Platform.Nonpreemptive

/-!
Response-time analyses for four concrete EDF preemption models (Rocq module `RTAforConcreteModels` of
`classic/model/schedule/uni/limited/edf/nonpr_reg/concrete_models/response_time_bound.v`): fully preemptive, fully
nonpreemptive, fixed preemption points and floating nonpreemptive regions.

Representation notes:
* The section-local `Let`s are unfolded: `higher_eq_priority` is `EDF job_arrival (job_relative_dealine task_deadline
  job_task)` (the accepted name of `job_relative_deadline`); `task_rbf`, `total_rbf` are the request-bound functions of
  `MaxArrivalsWorkloadBound`; `bound_on_total_hep_workload A Δ` is the filtered sum over the other tasks of
  `rbf tsk_o (min (A + ε + D tsk - D tsk_o) Δ)`; the section-local `blocking_bound`s are the corresponding
  `Prosa.Util.Sum.maxFiltered` over the tasks with a larger relative deadline (definitionally the `blocking_bound` of
  the bounded-nonpreemptive-segments analysis); `is_in_search_space A` uses `task_rbf_changes_at` and
  `bound_on_total_hep_workload_changes_at` of the EDF analysis. The `Definition blocking_bound` of the last section
  is restated with its contract binders.
* Binder lists follow the Rocq contract. As in Rocq, every theorem instantiates the EDF analysis for bounded
  nonpreemptive segments (`classic/model/schedule/uni/limited/edf/nonpr_reg/response_time_bound.v`); the proofs of
  the side conditions are those of the FP variant (`…/fixed_priority/nonpr_reg/concrete_models/response_time_bound.v`),
  whose LEAN_HELPER lemmas are repeated here (they are private there).
-/

set_option linter.dupNamespace false
set_option linter.unusedVariables false

namespace Prosa.Classic.Model.Schedule.Uni.Limited.Edf.NonprReg.ConcreteModels.ResponseTimeBound.RTAforConcreteModels

open Prosa.Classic.Model.Time.Time
open Prosa.Classic.Model.Arrival.Basic.ArrivalSequence.ArrivalSequence
open Prosa.Classic.Model.Arrival.Basic.Job.Job
open Prosa.Classic.Model.Arrival.Basic.TaskArrival.TaskArrival
open Prosa.Classic.Model.Priority.Priority
open Prosa.Classic.Model.Schedule.Uni.Schedule.UniprocessorSchedule
open Prosa.Classic.Model.Schedule.Uni.Service.Service
open Prosa.Classic.Model.Schedule.Uni.ResponseTime.ResponseTime
open Prosa.Classic.Model.Schedule.Uni.Limited.Platform.Definitions.LimitedPreemptionPlatform
open Prosa.Classic.Model.Schedule.Uni.Limited.Platform.Limited.ModelWithLimitedPreemptions
open Prosa.Classic.Model.Schedule.Uni.Limited.Platform.Preemptive.FullyPreemptivePlatform
open Prosa.Classic.Model.Schedule.Uni.Limited.Platform.Nonpreemptive.FullyNonPreemptivePlatform
open Prosa.Classic.Model.Schedule.Uni.Nonpreemptive.Schedule.NonpreemptiveSchedule (is_nonpreemptive_schedule)
open Prosa.Classic.Model.Schedule.Uni.Limited.Schedule
open Prosa.Classic.Model.Schedule.Uni.Limited.Edf.ResponseTimeBound.AbstractRTAforEDFwithArrivalCurves
  (task_rbf_changes_at bound_on_total_hep_workload_changes_at)
open Prosa.Classic.Model.Schedule.Uni.Limited.Edf.NonprReg.ResponseTimeBound.RTAforEDFwithBoundedNonpreemptiveSegmentsWithArrivalCurves
  (uniprocessor_response_time_bound_edf_with_bounded_nonpreemptive_segments)
open Prosa.Classic.Model.Arrival.Curves.Bounds.ArrivalCurves
open Prosa.Classic.Analysis.Uni.ArrivalCurves.WorkloadBound.MaxArrivalsWorkloadBound
open Prosa.Util.Sum (maxFiltered sumFiltered)
open Prosa.Util.List (max0 first0 last0 last_of_seq_le_max_of_seq max_of_dominating_seq)
open Prosa.Util.Nondecreasing

universe u v

local macro "omega'" : tactic =>
  `(tactic| ((try dsimp only [Prosa.Classic.Model.Time.Time.time,
    Prosa.Classic.Model.Time.Time.instant, Prosa.Classic.Model.Time.Time.duration] at *) <;>
    omega))

/-! ### LEAN_HELPER lemmas -/

/-- LEAN_HELPER: the last element of a list is its element at the last index. -/
private theorem getD_last (xs : List Nat) : xs.getD (xs.length - 1) 0 = xs.getLastD 0 := by
  rw [List.getLastD_eq_getLast?, List.getLast?_eq_getElem?]
  simp [List.getD_eq_getElem?_getD]

/-- LEAN_HELPER: service is monotone. -/
private theorem service_mono {Job : Type v} [DecidableEq Job] (sched : schedule Job) (j : Job) (t t' : time)
    (LE : t ≤ t') : service sched j t ≤ service sched j t' := by
  unfold service service_during
  exact Finset.sum_le_sum_of_subset (Finset.Ico_subset_Ico (Nat.le_refl 0) LE)

/-- LEAN_HELPER: a filtered maximum of values bounded by `B` is bounded by `B`. -/
private theorem maxFiltered_le {α : Type _} (l : List α) (P : α → Bool) (F : α → Nat) (B : Nat)
    (H : ∀ x ∈ l, P x = true → F x ≤ B) : maxFiltered l P F ≤ B := by
  unfold maxFiltered
  induction l with
  | nil => exact Nat.zero_le _
  | cons a l ih =>
    have IH := ih (fun x hx Px => H x (List.mem_cons_of_mem _ hx) Px)
    rw [List.filter_cons]
    split
    · next Pa =>
      simp only [List.map_cons, List.foldr_cons]
      exact Nat.max_le.mpr ⟨H a List.mem_cons_self Pa, IH⟩
    · exact IH

/-- LEAN_HELPER: a blocking bound of zero-length segments vanishes. -/
private theorem blocking_bound_eps {Task : Type u} [DecidableEq Task] (task_deadline : Task → time)
    (ts : List Task) (tsk : Task) : Prosa.Classic.Model.Schedule.Uni.Limited.Edf.NonprReg.ResponseTimeBound.RTAforEDFwithBoundedNonpreemptiveSegmentsWithArrivalCurves.blocking_bound (fun _ => ε) task_deadline ts tsk = 0 :=
  Nat.le_zero.mp (maxFiltered_le _ _ _ 0 (fun x _ _ => Nat.le_of_eq (Nat.sub_self 1)))

/-- LEAN_HELPER: the last nonpreemptive segment of a job is no longer than its cost. -/
private theorem job_last_nps_le_cost {Job : Type v} [DecidableEq Job] (job_cost : Job → time)
    (arr_seq : arrival_sequence Job) (job_preemption_points : Job → List time)
    (MLP : limited_preemptions_job_model job_cost arr_seq job_preemption_points) (j : Job) (ARR : arrives_in arr_seq j) :
    job_last_nps job_preemption_points j ≤ job_cost j := by
  unfold job_last_nps lengths_of_segments
  rw [← MLP.2.2.2.1 j ARR]
  exact Nat.le_trans (last_of_seq_le_max_of_seq _)
    (max_distance_in_seq_le_last_element_of_seq _ (MLP.2.2.2.2 j ARR))

/-- LEAN_HELPER: in the model with preemption points, a job cannot be preempted once its service exceeds the
second-to-last preemption point, i.e. `job_cost j - (job_last_nps j - ε)` is a proper lock-in service. -/
private theorem limited_job_lock_in_service_is_proper {Job : Type v} [DecidableEq Job] (job_cost : Job → time)
    (arr_seq : arrival_sequence Job) (sched : schedule Job) (job_preemption_points : Job → List time)
    (MLP : limited_preemptions_job_model job_cost arr_seq job_preemption_points)
    (H_sched : is_schedule_with_limited_preemptions arr_seq job_preemption_points sched) :
    proper_job_lock_in_service job_cost arr_seq sched
      (fun j => job_cost j - (job_last_nps job_preemption_points j - ε)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro j ARR POS
    have P := of_decide_eq_true POS
    have LE := job_last_nps_le_cost job_cost arr_seq job_preemption_points MLP j ARR
    show 0 < job_cost j - (job_last_nps job_preemption_points j - ε)
    omega'
  · intro j ARR _
    exact Nat.sub_le _ _
  · intro j t t' ARR LE LOCK NCOMPL
    apply H_sched j t' ARR
    have NC : service sched j t' < job_cost j := by
      simpa [completed_by] using NCOMPL
    have MONO := service_mono sched j t t' LE
    have POS : 0 < job_cost j := by omega'
    have LSM := MLP.2.1 j ARR POS
    have LEc := job_last_nps_le_cost job_cost arr_seq job_preemption_points MLP j ARR
    have LEN := number_of_preemption_points_at_least_two job_cost arr_seq job_preemption_points MLP j ARR
    have ND := MLP.2.2.2.2 j ARR
    have ENDj := MLP.2.2.2.1 j ARR
    have E1 : (job_preemption_points j).getLastD 0 - (distances (job_preemption_points j)).getLastD 0 =
        (job_preemption_points j).getD ((job_preemption_points j).length - 2) 0 :=
      last_seq_minus_last_distance_seq (job_preemption_points j) ND
    have E2 : (job_preemption_points j).getD ((job_preemption_points j).length - 2 + 1) 0 =
        (job_preemption_points j).getLastD 0 := by
      rw [show (job_preemption_points j).length - 2 + 1 = (job_preemption_points j).length - 1 by omega']
      exact getD_last _
    have ENDj' : (job_preemption_points j).getLastD 0 = job_cost j := ENDj
    have LSM' : 0 < (distances (job_preemption_points j)).getLastD 0 := LSM
    have LEc' : (distances (job_preemption_points j)).getLastD 0 ≤ job_cost j := LEc
    have LOCK' : job_cost j - ((distances (job_preemption_points j)).getLastD 0 - ε) ≤ service sched j t := LOCK
    have h1 : (job_preemption_points j).getD ((job_preemption_points j).length - 2) 0 < service sched j t' := by
      omega'
    have h2 : service sched j t' < (job_preemption_points j).getD ((job_preemption_points j).length - 2 + 1) 0 := by
      omega'
    have NOTIN := antidensity_of_nondecreasing_seq (job_preemption_points j) (service sched j t')
      ((job_preemption_points j).length - 2) ND ⟨h1, h2⟩
    simp [can_be_preempted_for_model_with_limited_preemptions, NOTIN]

/-! ### Fully preemptive model -/

theorem uniprocessor_response_time_bound_fully_preemptive_edf {Task : Type u} [DecidableEq Task]
    (task_cost task_deadline : Task → time) {Job : Type v} [DecidableEq Job] (job_arrival job_cost : Job → time)
    (job_task : Job → Task) (arr_seq : arrival_sequence Job)
    (H_arrival_times_are_consistent : arrival_times_are_consistent job_arrival arr_seq)
    (H_arr_seq_is_a_set : arrival_sequence_is_a_set arr_seq) (ts : List Task)
    (H_all_jobs_from_taskset : ∀ j, arrives_in arr_seq j → job_task j ∈ ts)
    (H_job_cost_le_task_cost : cost_of_jobs_from_arrival_sequence_le_task_cost task_cost job_cost job_task arr_seq)
    (max_arrivals : Task → time → Nat)
    (H_family_of_proper_arrival_curves : family_of_proper_arrival_curves job_task arr_seq max_arrivals ts)
    (tsk : Task) (H_tsk_in_ts : tsk ∈ ts) (sched : schedule Job)
    (H_jobs_come_from_arrival_sequence : jobs_come_from_arrival_sequence sched arr_seq)
    (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute job_arrival sched)
    (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched)
    (H_sequential_jobs : sequential_jobs job_arrival job_cost sched job_task)
    (H_work_conserving : work_conserving job_arrival job_cost arr_seq sched)
    (H_respects_policy :
      respects_JLFP_policy_at_preemption_point job_arrival job_cost arr_seq sched
        (can_be_preempted_for_fully_preemptive_model (Job := Job)) (EDF job_arrival (job_relative_dealine task_deadline job_task)))
    (L : time) (H_L_positive : 0 < L)
    (H_fixed_point : L = total_request_bound_function task_cost max_arrivals ts L)
    (R : Nat)
    (H_R_is_maximum : ∀ A,
      (decide (A < L) && (task_rbf_changes_at task_cost max_arrivals tsk A ||
        bound_on_total_hep_workload_changes_at task_cost task_deadline ts max_arrivals tsk A)) = true →
      ∃ F, A + F = task_request_bound_function task_cost max_arrivals tsk (A + ε) +
          sumFiltered ts (fun tsk_o => !decide (tsk_o = tsk)) (fun tsk_o =>
            task_request_bound_function task_cost max_arrivals tsk_o (min (A + ε + task_deadline tsk - task_deadline tsk_o) (A + F))) ∧
        F ≤ R) :
    is_response_time_bound_of_task job_arrival job_cost job_task arr_seq sched tsk R := by
  have BLOCK := blocking_bound_eps task_deadline ts tsk
  refine uniprocessor_response_time_bound_edf_with_bounded_nonpreemptive_segments (fun _ => ε) task_cost task_deadline
    job_arrival (fun _ => ε) job_cost job_task arr_seq H_arrival_times_are_consistent H_arr_seq_is_a_set sched
    H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_sequential_jobs
    can_be_preempted_for_fully_preemptive_model
    (fully_preemptive_model_is_correct arr_seq sched)
    (fully_preemptive_model_is_model_with_bounded_nonpreemptive_regions job_cost job_task arr_seq)
    H_work_conserving H_respects_policy ts H_all_jobs_from_taskset H_job_cost_le_task_cost tsk H_tsk_in_ts max_arrivals
    H_family_of_proper_arrival_curves (fun j => job_cost j) (fun tsk => task_cost tsk) ?_ ?_ L H_L_positive H_fixed_point R ?_
  · refine ⟨?_, ?_, ?_⟩
    · intro j _ POS; exact of_decide_eq_true POS
    · intro j _ _; exact Nat.le_refl _
    · intro j t t' ARR LE SERV NCOMPL
      exfalso
      have := completion_monotonic job_cost sched j t t' LE (decide_eq_true SERV)
      rw [this] at NCOMPL
      exact Bool.noConfusion NCOMPL
  · refine ⟨Nat.le_refl _, ?_⟩
    intro j ARR TSK
    have := H_job_cost_le_task_cost j ARR
    simp only [job_cost_le_task_cost, decide_eq_true_eq] at this
    rw [TSK] at this
    exact this
  · intro A INSP
    obtain ⟨F, FIX, LE⟩ := H_R_is_maximum A INSP
    refine ⟨F, ?_, ?_⟩
    · rw [BLOCK]; omega'
    · omega'

/-! ### Fully nonpreemptive model -/

theorem uniprocessor_response_time_bound_fully_nonpreemptive_edf {Task : Type u} [DecidableEq Task]
    (task_cost task_deadline : Task → time) {Job : Type v} [DecidableEq Job] (job_arrival job_cost : Job → time)
    (job_task : Job → Task) (arr_seq : arrival_sequence Job)
    (H_arrival_times_are_consistent : arrival_times_are_consistent job_arrival arr_seq)
    (H_arr_seq_is_a_set : arrival_sequence_is_a_set arr_seq) (ts : List Task)
    (H_all_jobs_from_taskset : ∀ j, arrives_in arr_seq j → job_task j ∈ ts)
    (H_job_cost_le_task_cost : cost_of_jobs_from_arrival_sequence_le_task_cost task_cost job_cost job_task arr_seq)
    (max_arrivals : Task → time → Nat)
    (H_family_of_proper_arrival_curves : family_of_proper_arrival_curves job_task arr_seq max_arrivals ts)
    (tsk : Task) (H_tsk_in_ts : tsk ∈ ts) (sched : schedule Job)
    (H_jobs_come_from_arrival_sequence : jobs_come_from_arrival_sequence sched arr_seq)
    (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute job_arrival sched)
    (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched)
    (H_sequential_jobs : sequential_jobs job_arrival job_cost sched job_task)
    (H_work_conserving : work_conserving job_arrival job_cost arr_seq sched)
    (H_nonpreemptive_sched : is_nonpreemptive_schedule job_cost sched)
    (H_respects_policy :
      respects_JLFP_policy_at_preemption_point job_arrival job_cost arr_seq sched
        (can_be_preempted_for_fully_nonpreemptive_model job_cost) (EDF job_arrival (job_relative_dealine task_deadline job_task)))
    (L : time) (H_L_positive : 0 < L)
    (H_fixed_point : L = total_request_bound_function task_cost max_arrivals ts L)
    (R : Nat)
    (H_R_is_maximum : ∀ A,
      (decide (A < L) && (task_rbf_changes_at task_cost max_arrivals tsk A ||
        bound_on_total_hep_workload_changes_at task_cost task_deadline ts max_arrivals tsk A)) = true →
      ∃ F, A + F = maxFiltered ts (fun tsk_other => !decide (tsk_other = tsk) && decide (task_deadline tsk < task_deadline tsk_other))
        (fun tsk_other => task_cost tsk_other - ε) +
          (task_request_bound_function task_cost max_arrivals tsk (A + ε) - (task_cost tsk - ε)) +
          sumFiltered ts (fun tsk_o => !decide (tsk_o = tsk)) (fun tsk_o =>
            task_request_bound_function task_cost max_arrivals tsk_o (min (A + ε + task_deadline tsk - task_deadline tsk_o) (A + F))) ∧
        F + (task_cost tsk - ε) ≤ R) :
    is_response_time_bound_of_task job_arrival job_cost job_task arr_seq sched tsk R := by
  rcases Nat.eq_zero_or_pos (task_cost tsk) with ZERO | POS
  · intro j ARR TSK
    have NEQ := H_job_cost_le_task_cost j ARR
    simp only [job_cost_le_task_cost, decide_eq_true_eq, TSK, ZERO, Nat.le_zero] at NEQ
    simp [is_response_time_bound_of_job, completed_by, NEQ]
  refine uniprocessor_response_time_bound_edf_with_bounded_nonpreemptive_segments (fun tsk => task_cost tsk) task_cost task_deadline
    job_arrival (fun j => job_cost j) job_cost job_task arr_seq H_arrival_times_are_consistent H_arr_seq_is_a_set sched
    H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_sequential_jobs
    (can_be_preempted_for_fully_nonpreemptive_model job_cost)
    (fully_nonpreemptive_model_is_correct job_cost arr_seq sched H_nonpreemptive_sched H_completed_jobs_dont_execute)
    (fully_nonpreemptive_model_is_model_with_bounded_nonpreemptive_regions task_cost job_cost job_task arr_seq H_job_cost_le_task_cost)
    H_work_conserving H_respects_policy ts H_all_jobs_from_taskset H_job_cost_le_task_cost tsk H_tsk_in_ts max_arrivals
    H_family_of_proper_arrival_curves (fun _ => ε) (fun _ => ε) ?_ ⟨POS, fun _ _ _ => Nat.le_refl _⟩ L H_L_positive
    H_fixed_point R H_R_is_maximum
  refine ⟨fun _ _ _ => Nat.one_pos, fun j _ POSj => of_decide_eq_true POSj, ?_⟩
  intro j t t' ARR LE SERV NCOMPL
  have SERV' : 0 < service_during sched j 0 t := SERV
  obtain ⟨t_first, RANGE, SCHED, _⟩ := incremental_service_during sched j 0 t 0 SERV'
  simp only [Bool.and_eq_true, decide_eq_true_eq] at RANGE
  exact H_nonpreemptive_sched j t_first t' (by omega') SCHED NCOMPL

/-! ### Model with fixed preemption points -/

theorem uniprocessor_response_time_bound_edf_with_fixed_preemption_points {Task : Type u} [DecidableEq Task]
    (task_cost task_deadline : Task → time) {Job : Type v} [DecidableEq Job] (job_arrival job_cost : Job → time)
    (job_task : Job → Task) (arr_seq : arrival_sequence Job)
    (H_arrival_times_are_consistent : arrival_times_are_consistent job_arrival arr_seq)
    (H_arr_seq_is_a_set : arrival_sequence_is_a_set arr_seq) (ts : List Task)
    (H_all_jobs_from_taskset : ∀ j, arrives_in arr_seq j → job_task j ∈ ts)
    (H_job_cost_le_task_cost : cost_of_jobs_from_arrival_sequence_le_task_cost task_cost job_cost job_task arr_seq)
    (max_arrivals : Task → time → Nat)
    (H_family_of_proper_arrival_curves : family_of_proper_arrival_curves job_task arr_seq max_arrivals ts)
    (tsk : Task) (H_tsk_in_ts : tsk ∈ ts) (sched : schedule Job)
    (H_jobs_come_from_arrival_sequence : jobs_come_from_arrival_sequence sched arr_seq)
    (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute job_arrival sched)
    (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched)
    (H_sequential_jobs : sequential_jobs job_arrival job_cost sched job_task)
    (H_work_conserving : work_conserving job_arrival job_cost arr_seq sched)
    (job_preemption_points : Job → List time) (task_preemption_points : Task → List time)
    (H_model_with_fixed_preemption_points :
      fixed_preemption_points_model task_cost job_cost job_task arr_seq job_preemption_points task_preemption_points ts)
    (H_schedule_with_limited_preemptions :
      is_schedule_with_limited_preemptions arr_seq job_preemption_points sched)
    (H_respects_policy :
      respects_JLFP_policy_at_preemption_point job_arrival job_cost arr_seq sched
        (can_be_preempted_for_model_with_limited_preemptions job_preemption_points) (EDF job_arrival (job_relative_dealine task_deadline job_task)))
    (L : time) (H_L_positive : 0 < L)
    (H_fixed_point : L = total_request_bound_function task_cost max_arrivals ts L)
    (R : Nat)
    (H_R_is_maximum : ∀ A,
      (decide (A < L) && (task_rbf_changes_at task_cost max_arrivals tsk A ||
        bound_on_total_hep_workload_changes_at task_cost task_deadline ts max_arrivals tsk A)) = true →
      ∃ F, A + F = maxFiltered ts (fun tsk_other => !decide (tsk_other = tsk) && decide (task_deadline tsk < task_deadline tsk_other))
        (fun tsk_other => task_max_nps task_preemption_points tsk_other - ε) +
          (task_request_bound_function task_cost max_arrivals tsk (A + ε) - (task_last_nps task_preemption_points tsk - ε)) +
          sumFiltered ts (fun tsk_o => !decide (tsk_o = tsk)) (fun tsk_o =>
            task_request_bound_function task_cost max_arrivals tsk_o (min (A + ε + task_deadline tsk - task_deadline tsk_o) (A + F))) ∧
        F + (task_last_nps task_preemption_points tsk - ε) ≤ R) :
    is_response_time_bound_of_task job_arrival job_cost job_task arr_seq sched tsk R := by
  obtain ⟨MLP, BEG, END, INCR, HYP1, HYP2, HYP3⟩ := H_model_with_fixed_preemption_points
  have TLE : task_last_nps task_preemption_points tsk ≤ task_cost tsk := by
    unfold task_last_nps
    rw [← END tsk H_tsk_in_ts]
    exact Nat.le_trans (last_of_seq_le_max_of_seq _)
      (max_distance_in_seq_le_last_element_of_seq _ (INCR tsk H_tsk_in_ts))
  refine uniprocessor_response_time_bound_edf_with_bounded_nonpreemptive_segments (task_max_nps task_preemption_points) task_cost task_deadline
    job_arrival (job_max_nps job_preemption_points) job_cost job_task arr_seq H_arrival_times_are_consistent H_arr_seq_is_a_set sched
    H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_sequential_jobs
    (can_be_preempted_for_model_with_limited_preemptions job_preemption_points)
    (model_with_fixed_preemption_points_is_correct arr_seq job_preemption_points sched H_schedule_with_limited_preemptions)
    (model_with_fixed_preemption_points_is_model_with_bounded_nonpreemptive_regions job_cost job_task arr_seq
      job_preemption_points sched H_schedule_with_limited_preemptions (task_max_nps task_preemption_points) MLP
      (fun j ARR => max_of_dominating_seq _ _ (fun n => HYP2 j n ARR)))
    H_work_conserving H_respects_policy ts H_all_jobs_from_taskset H_job_cost_le_task_cost tsk H_tsk_in_ts max_arrivals
    H_family_of_proper_arrival_curves (fun j => job_cost j - (job_last_nps job_preemption_points j - ε))
    (fun tsk => task_cost tsk - (task_last_nps task_preemption_points tsk - ε))
    (limited_job_lock_in_service_is_proper job_cost arr_seq sched job_preemption_points MLP
      H_schedule_with_limited_preemptions) ⟨Nat.sub_le _ _, ?_⟩ L H_L_positive H_fixed_point R ?_
  · intro j ARR TSK
    rcases Nat.eq_zero_or_pos (job_cost j) with Z | POS
    · show job_cost j - (job_last_nps job_preemption_points j - ε) ≤ _
      rw [Z, Nat.zero_sub]
      exact Nat.zero_le _
    have LEN := number_of_preemption_points_at_least_two job_cost arr_seq job_preemption_points MLP j ARR
    have SZ : (job_preemption_points j).length = (task_preemption_points tsk).length := by
      rw [← TSK]; exact HYP1 j ARR
    have NDj := MLP.2.2.2.2 j ARR
    have NDt := INCR tsk H_tsk_in_ts
    have DOM := domination_of_distances_implies_domination_of_seq (job_preemption_points j) (task_preemption_points tsk)
      (by rw [MLP.2.2.1 j ARR, BEG tsk H_tsk_in_ts]) LEN (SZ ▸ LEN) SZ NDj NDt
      (fun n => by rw [← TSK]; exact HYP2 j n ARR) ((job_preemption_points j).length - 2)
    have DOM' : (job_preemption_points j).getD ((job_preemption_points j).length - 2) 0 ≤
        (task_preemption_points tsk).getD ((job_preemption_points j).length - 2) 0 := DOM
    have Ej : (job_preemption_points j).getLastD 0 - (distances (job_preemption_points j)).getLastD 0 =
        (job_preemption_points j).getD ((job_preemption_points j).length - 2) 0 :=
      last_seq_minus_last_distance_seq (job_preemption_points j) NDj
    have Et : (task_preemption_points tsk).getLastD 0 - (distances (task_preemption_points tsk)).getLastD 0 =
        (task_preemption_points tsk).getD ((job_preemption_points j).length - 2) 0 := by
      rw [SZ]; exact last_seq_minus_last_distance_seq (task_preemption_points tsk) NDt
    have ENDj : (job_preemption_points j).getLastD 0 = job_cost j := MLP.2.2.2.1 j ARR
    have ENDt : (task_preemption_points tsk).getLastD 0 = task_cost tsk := END tsk H_tsk_in_ts
    have JL : 0 < (distances (job_preemption_points j)).getLastD 0 := MLP.2.1 j ARR POS
    have JLE : (distances (job_preemption_points j)).getLastD 0 ≤ job_cost j :=
      job_last_nps_le_cost job_cost arr_seq job_preemption_points MLP j ARR
    have TLE' : (distances (task_preemption_points tsk)).getLastD 0 ≤ task_cost tsk := TLE
    have DLEN := size_of_seq_of_distances (task_preemption_points tsk) (SZ ▸ LEN)
    have TPOS : 1 ≤ (distances (task_preemption_points tsk)).getLastD 0 := by
      have := HYP3 tsk ((distances (task_preemption_points tsk)).length - 1) H_tsk_in_ts (by omega')
      rw [getD_last] at this
      exact this
    show job_cost j - ((distances (job_preemption_points j)).getLastD 0 - ε) ≤
      task_cost tsk - ((distances (task_preemption_points tsk)).getLastD 0 - ε)
    omega'
  · intro A INSP
    obtain ⟨F, FIX, LE⟩ := H_R_is_maximum A INSP
    unfold Prosa.Classic.Model.Schedule.Uni.Limited.Edf.NonprReg.ResponseTimeBound.RTAforEDFwithBoundedNonpreemptiveSegmentsWithArrivalCurves.blocking_bound
    refine ⟨F, ?_, ?_⟩ <;> omega'


/-! ### Model with floating nonpreemptive regions -/

def blocking_bound {Task : Type u} [DecidableEq Task] (task_deadline : Task → time) (ts : List Task) (tsk : Task)
    (task_max_nps : Task → time) : Nat :=
  maxFiltered ts (fun tsk_other => !decide (tsk_other = tsk) && decide (task_deadline tsk < task_deadline tsk_other))
        (fun tsk_other => task_max_nps tsk_other - ε)

theorem uniprocessor_response_time_bound_edf_with_floating_nonpreemptive_regions {Task : Type u} [DecidableEq Task]
    (task_cost task_deadline : Task → time) {Job : Type v} [DecidableEq Job] (job_arrival job_cost : Job → time)
    (job_task : Job → Task) (arr_seq : arrival_sequence Job)
    (H_arrival_times_are_consistent : arrival_times_are_consistent job_arrival arr_seq)
    (H_arr_seq_is_a_set : arrival_sequence_is_a_set arr_seq) (ts : List Task)
    (H_all_jobs_from_taskset : ∀ j, arrives_in arr_seq j → job_task j ∈ ts)
    (H_job_cost_le_task_cost : cost_of_jobs_from_arrival_sequence_le_task_cost task_cost job_cost job_task arr_seq)
    (max_arrivals : Task → time → Nat)
    (H_family_of_proper_arrival_curves : family_of_proper_arrival_curves job_task arr_seq max_arrivals ts)
    (tsk : Task) (H_tsk_in_ts : tsk ∈ ts) (sched : schedule Job)
    (H_jobs_come_from_arrival_sequence : jobs_come_from_arrival_sequence sched arr_seq)
    (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute job_arrival sched)
    (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched)
    (H_sequential_jobs : sequential_jobs job_arrival job_cost sched job_task)
    (H_work_conserving : work_conserving job_arrival job_cost arr_seq sched)
    (job_preemption_points : Job → List time) (task_max_nps : Task → time)
    (H_task_model_with_floating_nonpreemptive_regions :
      model_with_floating_nonpreemptive_regions job_cost job_task arr_seq job_preemption_points task_max_nps)
    (H_schedule_with_limited_preemptions :
      is_schedule_with_limited_preemptions arr_seq job_preemption_points sched)
    (H_respects_policy :
      respects_JLFP_policy_at_preemption_point job_arrival job_cost arr_seq sched
        (can_be_preempted_for_model_with_limited_preemptions job_preemption_points) (EDF job_arrival (job_relative_dealine task_deadline job_task)))
    (L : time) (H_L_positive : 0 < L)
    (H_fixed_point : L = total_request_bound_function task_cost max_arrivals ts L)
    (R : Nat)
    (H_R_is_maximum : ∀ A,
      (decide (A < L) && (task_rbf_changes_at task_cost max_arrivals tsk A ||
        bound_on_total_hep_workload_changes_at task_cost task_deadline ts max_arrivals tsk A)) = true →
      ∃ F, A + F = blocking_bound task_deadline ts tsk task_max_nps + task_request_bound_function task_cost max_arrivals tsk (A + ε) +
          sumFiltered ts (fun tsk_o => !decide (tsk_o = tsk)) (fun tsk_o =>
            task_request_bound_function task_cost max_arrivals tsk_o (min (A + ε + task_deadline tsk - task_deadline tsk_o) (A + F))) ∧
        F ≤ R) :
    is_response_time_bound_of_task job_arrival job_cost job_task arr_seq sched tsk R := by
  obtain ⟨MLP, JMLETM⟩ := H_task_model_with_floating_nonpreemptive_regions
  refine uniprocessor_response_time_bound_edf_with_bounded_nonpreemptive_segments task_max_nps task_cost task_deadline
    job_arrival (job_max_nps job_preemption_points) job_cost job_task arr_seq H_arrival_times_are_consistent H_arr_seq_is_a_set sched
    H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_sequential_jobs
    (can_be_preempted_for_model_with_limited_preemptions job_preemption_points)
    (model_with_fixed_preemption_points_is_correct arr_seq job_preemption_points sched H_schedule_with_limited_preemptions)
    (model_with_fixed_preemption_points_is_model_with_bounded_nonpreemptive_regions job_cost job_task arr_seq
      job_preemption_points sched H_schedule_with_limited_preemptions task_max_nps MLP JMLETM)
    H_work_conserving H_respects_policy ts H_all_jobs_from_taskset H_job_cost_le_task_cost tsk H_tsk_in_ts max_arrivals
    H_family_of_proper_arrival_curves (fun j => job_cost j - (job_last_nps job_preemption_points j - ε))
    (fun tsk => task_cost tsk)
    (limited_job_lock_in_service_is_proper job_cost arr_seq sched job_preemption_points MLP
      H_schedule_with_limited_preemptions) ⟨Nat.le_refl _, ?_⟩ L H_L_positive H_fixed_point R ?_
  · intro j ARR TSK
    have := H_job_cost_le_task_cost j ARR
    simp only [job_cost_le_task_cost, decide_eq_true_eq] at this
    rw [TSK] at this
    exact Nat.le_trans (Nat.sub_le _ _) this
  · intro A INSP
    obtain ⟨F, FIX, LE⟩ := H_R_is_maximum A INSP
    unfold blocking_bound at FIX
    unfold Prosa.Classic.Model.Schedule.Uni.Limited.Edf.NonprReg.ResponseTimeBound.RTAforEDFwithBoundedNonpreemptiveSegmentsWithArrivalCurves.blocking_bound
    refine ⟨F, ?_, ?_⟩ <;> omega'

end Prosa.Classic.Model.Schedule.Uni.Limited.Edf.NonprReg.ConcreteModels.ResponseTimeBound.RTAforConcreteModels
