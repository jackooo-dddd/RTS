-- Authoritative source:
-- ProsaBuddy classic Prosa (prosabuddy commit f692cb7479780cf6009493f373a309e13165201c)
-- source: classic/model/schedule/uni/limited/fixed_priority/response_time_bound.v
-- sha256: see Prosa-Shunqi/classic-prosa/comprehensive-classic/file_order.csv (rank 169)

import Prosa.Classic.Util.All
import Prosa.Classic.Model.Arrival.Basic.Job
import Prosa.Classic.Model.Arrival.Basic.TaskArrival
import Prosa.Classic.Model.Priority
import Prosa.Classic.Model.Schedule.Uni.Service
import Prosa.Classic.Model.Schedule.Uni.Workload
import Prosa.Classic.Model.Schedule.Uni.Schedule
import Prosa.Classic.Model.Schedule.Uni.ResponseTime
import Prosa.Classic.Model.Schedule.Uni.ScheduleOfTask
import Prosa.Classic.Model.Schedule.Uni.Limited.Platform.Definitions
import Prosa.Classic.Model.Schedule.Uni.Limited.Schedule
import Prosa.Classic.Model.Schedule.Uni.Limited.Rbf
import Prosa.Classic.Model.Schedule.Uni.Limited.AbstractRTA.Definitions
import Prosa.Classic.Model.Schedule.Uni.Limited.AbstractRTA.ReductionOfSearchSpace
import Prosa.Classic.Model.Schedule.Uni.Limited.AbstractRTA.AbstractSeqRta
import Prosa.Classic.Model.Schedule.Uni.Limited.JlfpInstantiation
import Prosa.Classic.Model.Arrival.Curves.Bounds
import Prosa.Classic.Analysis.Uni.ArrivalCurves.WorkloadBound
import Prosa.Classic.Model.Schedule.Uni.Limited.BusyInterval

/-!
Abstract response-time analysis for FP uniprocessor scheduling with arrival curves (Rocq module
`AbstractRTAforFPwithArrivalCurves` of `classic/model/schedule/uni/limited/fixed_priority/response_time_bound.v`).

Representation notes:
* The section-local `Let`s are unfolded: `jlfp_higher_eq_priority` is `FP_to_JLFP job_task higher_eq_priority`;
  `interference`/`interfering_workload` are the accepted `JLFPInstantiation.interference sched …` and
  `JLFPInstantiation.interfering_workload job_cost arr_seq sched …`; `task_rbf` is
  `task_request_bound_function task_cost max_arrivals tsk`; `total_hep_rbf`/`total_ohep_rbf` are
  `total_hep_request_bound_function_FP …`/`total_ohep_request_bound_function_FP …`; `IBF R` is
  `priority_inversion_bound + total_ohep_rbf R`; `is_in_search_space A` is
  `(decide (A < L) && !decide (task_rbf A = task_rbf (A + ε))) = true`; the section-local
  `total_interference_bound tsk A Δ` (whose `task_rbf` is that of the section task) is the corresponding `fun`.
* `ε` is the accepted `Prosa.Util.Epsilon` notation (`1`).
* Binder lists follow the Rocq contract. As in Rocq, the final theorem applies the accepted
  `AbstractSeqRTA.uniprocessor_response_time_bound_seq` with the instantiated interference, using the job under
  analysis (of positive cost) to discharge the search-space hypothesis.
-/

set_option linter.dupNamespace false
set_option linter.unusedVariables false

namespace Prosa.Classic.Model.Schedule.Uni.Limited.FixedPriority.ResponseTimeBound.AbstractRTAforFPwithArrivalCurves

open Prosa.Classic.Model.Time.Time
open Prosa.Classic.Model.Arrival.Basic.ArrivalSequence.ArrivalSequence
open Prosa.Classic.Model.Arrival.Basic.Job.Job
open Prosa.Classic.Model.Arrival.Basic.TaskArrival.TaskArrival
open Prosa.Classic.Model.Priority.Priority
open Prosa.Classic.Model.Schedule.Uni.Schedule.UniprocessorSchedule
open Prosa.Classic.Model.Schedule.Uni.Service.Service
open Prosa.Classic.Model.Schedule.Uni.Workload.Workload
open Prosa.Classic.Model.Schedule.Uni.ResponseTime.ResponseTime
open Prosa.Classic.Model.Schedule.Uni.ScheduleOfTask.ScheduleOfTask
open Prosa.Classic.Model.Schedule.Uni.Limited.Platform.Definitions.LimitedPreemptionPlatform
open Prosa.Classic.Model.Schedule.Uni.Limited.Schedule
open Prosa.Classic.Model.Schedule.Uni.Limited.Rbf.RBF
open Prosa.Classic.Model.Schedule.Uni.Limited.BusyInterval.BusyIntervalJLFP
open Prosa.Classic.Model.Schedule.Uni.Limited.JlfpInstantiation.JLFPInstantiation
open Prosa.Classic.Model.Schedule.Uni.Limited.AbstractRTA.ReductionOfSearchSpace.AbstractRTAReduction
  (is_in_search_space)
open Prosa.Classic.Model.Schedule.Uni.Limited.AbstractRTA.AbstractSeqRta.AbstractSeqRTA
  (uniprocessor_response_time_bound_seq)
open Prosa.Classic.Model.Arrival.Curves.Bounds.ArrivalCurves
open Prosa.Classic.Analysis.Uni.ArrivalCurves.WorkloadBound.MaxArrivalsWorkloadBound

universe u v

local macro "omega'" : tactic =>
  `(tactic| ((try dsimp only [Prosa.Classic.Model.Time.Time.time,
    Prosa.Classic.Model.Time.Time.instant, Prosa.Classic.Model.Time.Time.duration] at *) <;>
    omega))

/-! ### Filling out the hypotheses of the abstract RTA theorem -/

theorem instantiated_i_and_w_are_consistent_with_schedule
    {Task : Type u} [DecidableEq Task]
    {Job : Type v} [DecidableEq Job]
    (job_arrival : Job → time)
    (job_cost : Job → time)
    (job_task : Job → Task)
    (arr_seq : arrival_sequence Job)
    (H_arrival_times_are_consistent : arrival_times_are_consistent job_arrival arr_seq)
    (H_arr_seq_is_a_set : arrival_sequence_is_a_set arr_seq)
    (sched : schedule Job)
    (H_jobs_come_from_arrival_sequence : jobs_come_from_arrival_sequence sched arr_seq)
    (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute job_arrival sched)
    (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched)
    (H_work_conserving : work_conserving job_arrival job_cost arr_seq sched)
    (tsk : Task)
    (higher_eq_priority : FP_policy Task)
    (H_priority_is_reflexive : FP_is_reflexive higher_eq_priority)
    :
    Prosa.Classic.Model.Schedule.Uni.Limited.AbstractRTA.Definitions.AbstractRTADefinitions.work_conserving job_arrival job_cost job_task arr_seq sched tsk (interference sched (FP_to_JLFP job_task higher_eq_priority)) (interfering_workload job_cost arr_seq sched (FP_to_JLFP job_task higher_eq_priority)) := by
  intro j t1 t2 t ARR TSK POS BUSY NEQ
  have REFL : JLFP_is_reflexive (FP_to_JLFP job_task higher_eq_priority) :=
    fun x => H_priority_is_reflexive (job_task x)
  constructor
  · intro HYP
    simp only [interference, Bool.or_eq_true, not_or] at HYP
    obtain ⟨HYP1, HYP2⟩ := HYP
    cases SCHED : sched t with
    | some s =>
      simp only [BusyIntervalJLFP.is_priority_inversion, is_priority_inversion, SCHED, Bool.not_eq_true',
        Bool.not_eq_false] at HYP1
      simp only [is_interference_from_another_job_with_higher_eq_priority, SCHED, HYP1, Bool.true_and,
        Bool.not_eq_true', decide_eq_false_iff_not, not_not] at HYP2
      subst HYP2
      simp [scheduled_at, SCHED]
    | none =>
      exfalso
      have CBUSY := (instantiated_busy_interval_equivalent_edf_busy_interval job_arrival job_cost job_task arr_seq
        H_arrival_times_are_consistent H_arr_seq_is_a_set sched H_jobs_come_from_arrival_sequence
        H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute _ REFL j ARR (decide_eq_true POS) t1 t2).mpr BUSY
      have NI := not_quiet_implies_not_idle job_arrival job_cost arr_seq H_arrival_times_are_consistent sched
        (FP_to_JLFP job_task higher_eq_priority) j ARR (decide_eq_true POS) H_work_conserving
        H_jobs_must_arrive_to_execute REFL t1 t2 CBUSY.1 t NEQ
      exact NI (by simp [is_idle, SCHED])
  · intro HYP
    have SCHED : sched t = some j := of_decide_eq_true HYP
    simp only [interference, BusyIntervalJLFP.is_priority_inversion, is_priority_inversion,
      is_interference_from_another_job_with_higher_eq_priority, SCHED, FP_to_JLFP, H_priority_is_reflexive (job_task j),
      Bool.not_true, decide_true, Bool.and_false, Bool.or_false, Bool.false_eq_true, not_false_eq_true]

theorem instantiated_interference_and_workload_consistent_with_sequential_jobs
    {Task : Type u} [DecidableEq Task]
    {Job : Type v} [DecidableEq Job]
    (job_arrival : Job → time)
    (job_cost : Job → time)
    (job_task : Job → Task)
    (arr_seq : arrival_sequence Job)
    (H_arrival_times_are_consistent : arrival_times_are_consistent job_arrival arr_seq)
    (H_arr_seq_is_a_set : arrival_sequence_is_a_set arr_seq)
    (sched : schedule Job)
    (H_jobs_come_from_arrival_sequence : jobs_come_from_arrival_sequence sched arr_seq)
    (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute job_arrival sched)
    (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched)
    (tsk : Task)
    (higher_eq_priority : FP_policy Task)
    (H_priority_is_reflexive : FP_is_reflexive higher_eq_priority)
    :
    Prosa.Classic.Model.Schedule.Uni.Limited.AbstractRTA.AbstractSeqRta.AbstractSeqRTA.interference_and_workload_consistent_with_sequential_jobs job_arrival job_cost job_task arr_seq sched
      tsk (interference sched (FP_to_JLFP job_task higher_eq_priority)) (interfering_workload job_cost arr_seq sched (FP_to_JLFP job_task higher_eq_priority)) := by
  intro j t1 t2 ARR TSK POS BUSY
  have REFL : JLFP_is_reflexive (FP_to_JLFP job_task higher_eq_priority) :=
    fun x => H_priority_is_reflexive (job_task x)
  have CBUSY := (instantiated_busy_interval_equivalent_edf_busy_interval job_arrival job_cost job_task arr_seq
    H_arrival_times_are_consistent H_arr_seq_is_a_set sched H_jobs_come_from_arrival_sequence
    H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute _ REFL j ARR (decide_eq_true POS) t1 t2).mpr BUSY
  obtain ⟨⟨_, QT, _, _⟩, _⟩ := CBUSY
  apply (all_jobs_have_completed_equiv_workload_eq_service job_arrival job_cost arr_seq
    H_arrival_times_are_consistent sched H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute
    (fun j0 => decide (job_task j0 = tsk)) 0 t1 t1).mp
  intro s ARRs TSKs
  apply QT s (in_arrivals_implies_arrived arr_seq s 0 t1 ARRs)
  · have TSKs' : job_task s = tsk := of_decide_eq_true TSKs
    simp only [FP_to_JLFP, TSKs', TSK, H_priority_is_reflexive tsk]
  · exact in_arrivals_implies_arrived_before job_arrival arr_seq H_arrival_times_are_consistent s t1 ARRs

theorem instantiated_busy_intervals_are_bounded
    {Task : Type u} [DecidableEq Task]
    (task_cost : Task → time)
    {Job : Type v} [DecidableEq Job]
    (job_arrival : Job → time)
    (job_cost : Job → time)
    (job_task : Job → Task)
    (arr_seq : arrival_sequence Job)
    (H_arrival_times_are_consistent : arrival_times_are_consistent job_arrival arr_seq)
    (H_arr_seq_is_a_set : arrival_sequence_is_a_set arr_seq)
    (sched : schedule Job)
    (H_jobs_come_from_arrival_sequence : jobs_come_from_arrival_sequence sched arr_seq)
    (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute job_arrival sched)
    (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched)
    (H_work_conserving : work_conserving job_arrival job_cost arr_seq sched)
    (H_job_cost_le_task_cost :
      cost_of_jobs_from_arrival_sequence_le_task_cost task_cost job_cost job_task arr_seq)
    (ts : List Task)
    (H_all_jobs_from_taskset : ∀ j, arrives_in arr_seq j → job_task j ∈ ts)
    (max_arrivals : Task → time → Nat)
    (H_family_of_proper_arrival_curves :
      family_of_proper_arrival_curves job_task arr_seq max_arrivals ts)
    (tsk : Task)
    (higher_eq_priority : FP_policy Task)
    (H_priority_is_reflexive : FP_is_reflexive higher_eq_priority)
    (priority_inversion_bound : time)
    (H_priority_inversion_is_bounded :
      priority_inversion_is_bounded_by job_arrival job_cost job_task arr_seq sched (FP_to_JLFP job_task higher_eq_priority) tsk
        priority_inversion_bound)
    (L : time)
    (H_L_positive : 0 < L)
    (H_fixed_point :
      L = priority_inversion_bound + total_hep_request_bound_function_FP task_cost higher_eq_priority max_arrivals ts tsk L)
    :
    Prosa.Classic.Model.Schedule.Uni.Limited.AbstractRTA.Definitions.AbstractRTADefinitions.busy_intervals_are_bounded_by job_arrival job_cost job_task arr_seq sched tsk (interference sched (FP_to_JLFP job_task higher_eq_priority)) (interfering_workload job_cost arr_seq sched (FP_to_JLFP job_task higher_eq_priority)) L := by
  intro j ARR TSK POS
  have REFL : JLFP_is_reflexive (FP_to_JLFP job_task higher_eq_priority) :=
    fun x => H_priority_is_reflexive (job_task x)
  have ARRB : is_arrival_bound_for_taskset job_task arr_seq max_arrivals ts :=
    fun tsko INo => (H_family_of_proper_arrival_curves tsko INo).1
  obtain ⟨t1, t2, H1, H2, CBUSY⟩ := exists_busy_interval job_arrival job_cost arr_seq H_arrival_times_are_consistent
    sched H_jobs_come_from_arrival_sequence (FP_to_JLFP job_task higher_eq_priority) j ARR H_arr_seq_is_a_set
    H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_work_conserving REFL priority_inversion_bound
    (H_priority_inversion_is_bounded j ARR TSK POS) L H_L_positive
    (fun t => by
      calc priority_inversion_bound + workload_of_higher_or_equal_priority_jobs job_cost
            (jobs_arrived_between arr_seq t (t + L)) (FP_to_JLFP job_task higher_eq_priority) j
          ≤ priority_inversion_bound +
              total_hep_request_bound_function_FP task_cost higher_eq_priority max_arrivals ts tsk L :=
            Nat.add_le_add_left (total_workload_le_total_rbf' task_cost job_cost job_task arr_seq higher_eq_priority
              ts tsk H_job_cost_le_task_cost H_all_jobs_from_taskset max_arrivals ARRB j TSK t L) _
        _ = L := H_fixed_point.symm)
    POS
  exact ⟨t1, t2, H1, H2, (instantiated_busy_interval_equivalent_edf_busy_interval job_arrival job_cost job_task arr_seq
    H_arrival_times_are_consistent H_arr_seq_is_a_set sched H_jobs_come_from_arrival_sequence
    H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute _ REFL j ARR (decide_eq_true POS) t1 t2).mp CBUSY⟩

theorem instantiated_task_interference_is_bounded
    {Task : Type u} [DecidableEq Task]
    (task_cost : Task → time)
    {Job : Type v} [DecidableEq Job]
    (job_arrival : Job → time)
    (job_cost : Job → time)
    (job_task : Job → Task)
    (arr_seq : arrival_sequence Job)
    (H_arrival_times_are_consistent : arrival_times_are_consistent job_arrival arr_seq)
    (H_arr_seq_is_a_set : arrival_sequence_is_a_set arr_seq)
    (sched : schedule Job)
    (H_jobs_come_from_arrival_sequence : jobs_come_from_arrival_sequence sched arr_seq)
    (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute job_arrival sched)
    (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched)
    (H_sequential_jobs : sequential_jobs job_arrival job_cost sched job_task)
    (H_job_cost_le_task_cost :
      cost_of_jobs_from_arrival_sequence_le_task_cost task_cost job_cost job_task arr_seq)
    (ts : List Task)
    (H_all_jobs_from_taskset : ∀ j, arrives_in arr_seq j → job_task j ∈ ts)
    (max_arrivals : Task → time → Nat)
    (H_family_of_proper_arrival_curves :
      family_of_proper_arrival_curves job_task arr_seq max_arrivals ts)
    (tsk : Task)
    (higher_eq_priority : FP_policy Task)
    (H_priority_is_reflexive : FP_is_reflexive higher_eq_priority)
    (priority_inversion_bound : time)
    (H_priority_inversion_is_bounded :
      priority_inversion_is_bounded_by job_arrival job_cost job_task arr_seq sched (FP_to_JLFP job_task higher_eq_priority) tsk
        priority_inversion_bound)
    :
    Prosa.Classic.Model.Schedule.Uni.Limited.AbstractRTA.AbstractSeqRta.AbstractSeqRTA.task_interference_is_bounded_by job_arrival job_cost job_task arr_seq sched tsk (interference sched (FP_to_JLFP job_task higher_eq_priority)) (interfering_workload job_cost arr_seq sched (FP_to_JLFP job_task higher_eq_priority))
      (fun t A R => (priority_inversion_bound + total_ohep_request_bound_function_FP task_cost higher_eq_priority max_arrivals ts tsk (R))) := by
  intro j R t1 t2 ARR TSK LT NCOMPL BUSY
  intro offset
  have POS : 0 < job_cost j := by
    rcases Nat.eq_zero_or_pos (job_cost j) with ZERO | POS
    · exfalso
      simp [completed_by, ZERO] at NCOMPL
    · exact POS
  have REFL : JLFP_is_reflexive (FP_to_JLFP job_task higher_eq_priority) :=
    fun x => H_priority_is_reflexive (job_task x)
  have CBUSY := (instantiated_busy_interval_equivalent_edf_busy_interval job_arrival job_cost job_task arr_seq
    H_arrival_times_are_consistent H_arr_seq_is_a_set sched H_jobs_come_from_arrival_sequence
    H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute _ REFL j ARR (decide_eq_true POS) t1 t2).mpr BUSY
  obtain ⟨⟨LT12, QT, NQT, ARRj⟩, _⟩ := CBUSY
  have INarr : j ∈ jobs_arrived_before arr_seq t2 := by
    apply arrived_between_implies_in_arrivals job_arrival arr_seq H_arrival_times_are_consistent j 0 t2 ARR
    simp only [arrived_between, Bool.and_eq_true, decide_eq_true_eq] at ARRj ⊢
    exact ⟨Nat.zero_le _, ARRj.2⟩
  rw [cumulative_task_interference_split job_arrival job_cost job_task arr_seq sched H_sequential_jobs
    (FP_to_JLFP job_task higher_eq_priority)
    (any_reflexive_FP_respects_sequential_jobs job_arrival job_task higher_eq_priority H_priority_is_reflexive) tsk j
    t1 (t1 + R) t2 TSK INarr NCOMPL]
  apply Nat.add_le_add
  · calc ∑ t ∈ Finset.Ico t1 (t1 + R),
          (BusyIntervalJLFP.is_priority_inversion sched (FP_to_JLFP job_task higher_eq_priority) j t).toNat
        ≤ cumulative_priority_inversion sched (FP_to_JLFP job_task higher_eq_priority) j t1 t2 := by
          unfold cumulative_priority_inversion
          apply Finset.sum_le_sum_of_subset
          exact Finset.Ico_subset_Ico (Nat.le_refl _) (Nat.le_of_lt LT)
      _ ≤ priority_inversion_bound :=
          H_priority_inversion_is_bounded j ARR TSK POS t1 t2 ⟨LT12, QT, NQT, ARRj⟩
  · rw [instantiated_cumulative_interference_of_hep_tasks_equal_total_interference_of_hep_tasks job_arrival job_cost
      job_task arr_seq H_arrival_times_are_consistent H_arr_seq_is_a_set sched H_jobs_come_from_arrival_sequence
      H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute _ j t1 (t1 + R) QT]
    apply Nat.le_trans (service_of_jobs_le_workload job_cost sched _ _ H_completed_jobs_dont_execute t1 (t1 + R))
    rw [← TSK]
    exact total_workload_le_total_rbf task_cost job_cost job_task arr_seq higher_eq_priority ts (job_task j)
      H_job_cost_le_task_cost H_all_jobs_from_taskset max_arrivals
      (fun tsko INo => (H_family_of_proper_arrival_curves tsko INo).1) j rfl t1 R

theorem A_is_in_concrete_search_space
    {Task : Type u} [DecidableEq Task]
    (task_cost : Task → time)
    {Job : Type v} [DecidableEq Job]
    (job_arrival : Job → time)
    (job_cost : Job → time)
    (job_task : Job → Task)
    (arr_seq : arrival_sequence Job)
    (H_arrival_times_are_consistent : arrival_times_are_consistent job_arrival arr_seq)
    (H_job_cost_le_task_cost :
      cost_of_jobs_from_arrival_sequence_le_task_cost task_cost job_cost job_task arr_seq)
    (ts : List Task)
    (max_arrivals : Task → time → Nat)
    (H_family_of_proper_arrival_curves :
      family_of_proper_arrival_curves job_task arr_seq max_arrivals ts)
    (tsk : Task)
    (H_tsk_in_ts : tsk ∈ ts)
    (higher_eq_priority : FP_policy Task)
    (priority_inversion_bound : time)
    (L : time)
    (H_L_positive : 0 < L)
    (j : Job)
    (H_j_arrives : arrives_in arr_seq j)
    (H_job_of_tsk : job_task j = tsk)
    (H_job_cost_positive : job_cost_positive job_cost j = true)
    (A : time)
    (H_A_is_in_abstract_search_space :
      is_in_search_space tsk L (fun tsk0 A Δ => task_request_bound_function task_cost max_arrivals tsk (A + ε) - task_cost tsk0 + (priority_inversion_bound + total_ohep_request_bound_function_FP task_cost higher_eq_priority max_arrivals ts tsk (Δ))) A)
    :
    (decide (A < L) && !decide (task_request_bound_function task_cost max_arrivals tsk (A) = task_request_bound_function task_cost max_arrivals tsk (A + ε))) = true := by
  rcases H_A_is_in_abstract_search_space with ZERO | ⟨POSLT, x, LTx, NEQ⟩
  · subst ZERO
    have PROPER := H_family_of_proper_arrival_curves tsk H_tsk_in_ts
    have R0 := task_rbf_0_zero task_cost job_task arr_seq tsk max_arrivals PROPER
    have R1 := task_rbf_1_ge_task_cost task_cost job_arrival job_task arr_seq H_arrival_times_are_consistent tsk
      max_arrivals PROPER j H_j_arrives H_job_of_tsk
    have COST := H_job_cost_le_task_cost j H_j_arrives
    simp only [job_cost_le_task_cost, decide_eq_true_eq] at COST
    have POS := of_decide_eq_true H_job_cost_positive
    rw [H_job_of_tsk] at COST
    simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', decide_eq_false_iff_not]
    refine ⟨H_L_positive, ?_⟩
    rw [Nat.zero_add, R0]
    omega'
  · simp only [Bool.and_eq_true, decide_eq_true_eq] at POSLT
    simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', decide_eq_false_iff_not]
    refine ⟨POSLT.2, ?_⟩
    intro EQ
    apply NEQ
    have : A - ε + ε = A := by omega'
    simp only [this, EQ]

theorem correct_search_space
    {Task : Type u} [DecidableEq Task]
    (task_cost : Task → time)
    {Job : Type v} [DecidableEq Job]
    (job_arrival : Job → time)
    (job_cost : Job → time)
    (job_task : Job → Task)
    (arr_seq : arrival_sequence Job)
    (H_arrival_times_are_consistent : arrival_times_are_consistent job_arrival arr_seq)
    (H_job_cost_le_task_cost :
      cost_of_jobs_from_arrival_sequence_le_task_cost task_cost job_cost job_task arr_seq)
    (ts : List Task)
    (max_arrivals : Task → time → Nat)
    (H_family_of_proper_arrival_curves :
      family_of_proper_arrival_curves job_task arr_seq max_arrivals ts)
    (tsk : Task)
    (H_tsk_in_ts : tsk ∈ ts)
    (task_lock_in_service : Task → time)
    (higher_eq_priority : FP_policy Task)
    (priority_inversion_bound : time)
    (L : time)
    (H_L_positive : 0 < L)
    (R : time)
    (H_R_is_maximum : ∀ A,
      (decide (A < L) && !decide (task_request_bound_function task_cost max_arrivals tsk (A) = task_request_bound_function task_cost max_arrivals tsk (A + ε))) = true →
      ∃ F, A + F = priority_inversion_bound + (task_request_bound_function task_cost max_arrivals tsk (A + ε) - (task_cost tsk - task_lock_in_service tsk)) +
          total_ohep_request_bound_function_FP task_cost higher_eq_priority max_arrivals ts tsk (A + F) ∧
        F + (task_cost tsk - task_lock_in_service tsk) ≤ R)
    (j : Job)
    (H_j_arrives : arrives_in arr_seq j)
    (H_job_of_tsk : job_task j = tsk)
    (H_job_cost_positive : job_cost_positive job_cost j = true)
    (A : time)
    (H_A_is_in_abstract_search_space :
      is_in_search_space tsk L (fun tsk0 A Δ => task_request_bound_function task_cost max_arrivals tsk (A + ε) - task_cost tsk0 + (priority_inversion_bound + total_ohep_request_bound_function_FP task_cost higher_eq_priority max_arrivals ts tsk (Δ))) A)
    :
    ∃ F, A + F = task_request_bound_function task_cost max_arrivals tsk (A + ε) - (task_cost tsk - task_lock_in_service tsk) + (priority_inversion_bound + total_ohep_request_bound_function_FP task_cost higher_eq_priority max_arrivals ts tsk (A + F)) ∧
      F + (task_cost tsk - task_lock_in_service tsk) ≤ R := by
  obtain ⟨F, FIX, NEQ⟩ := H_R_is_maximum A (A_is_in_concrete_search_space task_cost job_arrival job_cost job_task arr_seq H_arrival_times_are_consistent H_job_cost_le_task_cost ts max_arrivals H_family_of_proper_arrival_curves tsk H_tsk_in_ts higher_eq_priority priority_inversion_bound L H_L_positive j H_j_arrives H_job_of_tsk H_job_cost_positive A H_A_is_in_abstract_search_space)
  exact ⟨F, by omega', NEQ⟩

/-! ### Final theorem -/

theorem uniprocessor_response_time_bound_fp
    {Task : Type u} [DecidableEq Task]
    (task_cost : Task → time)
    {Job : Type v} [DecidableEq Job]
    (job_arrival : Job → time)
    (job_cost : Job → time)
    (job_task : Job → Task)
    (arr_seq : arrival_sequence Job)
    (H_arrival_times_are_consistent : arrival_times_are_consistent job_arrival arr_seq)
    (H_arr_seq_is_a_set : arrival_sequence_is_a_set arr_seq)
    (sched : schedule Job)
    (H_jobs_come_from_arrival_sequence : jobs_come_from_arrival_sequence sched arr_seq)
    (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute job_arrival sched)
    (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched)
    (H_work_conserving : work_conserving job_arrival job_cost arr_seq sched)
    (H_sequential_jobs : sequential_jobs job_arrival job_cost sched job_task)
    (H_job_cost_le_task_cost :
      cost_of_jobs_from_arrival_sequence_le_task_cost task_cost job_cost job_task arr_seq)
    (ts : List Task)
    (H_all_jobs_from_taskset : ∀ j, arrives_in arr_seq j → job_task j ∈ ts)
    (max_arrivals : Task → time → Nat)
    (H_family_of_proper_arrival_curves :
      family_of_proper_arrival_curves job_task arr_seq max_arrivals ts)
    (tsk : Task)
    (H_tsk_in_ts : tsk ∈ ts)
    (job_lock_in_service : Job → time)
    (task_lock_in_service : Task → time)
    (H_proper_job_lock_in_service :
      proper_job_lock_in_service job_cost arr_seq sched job_lock_in_service)
    (H_proper_task_lock_in_service :
      proper_task_lock_in_service task_cost job_task arr_seq job_lock_in_service task_lock_in_service tsk)
    (higher_eq_priority : FP_policy Task)
    (H_priority_is_reflexive : FP_is_reflexive higher_eq_priority)
    (priority_inversion_bound : time)
    (H_priority_inversion_is_bounded :
      priority_inversion_is_bounded_by job_arrival job_cost job_task arr_seq sched (FP_to_JLFP job_task higher_eq_priority) tsk
        priority_inversion_bound)
    (L : time)
    (H_L_positive : 0 < L)
    (H_fixed_point :
      L = priority_inversion_bound + total_hep_request_bound_function_FP task_cost higher_eq_priority max_arrivals ts tsk L)
    (R : time)
    (H_R_is_maximum : ∀ A,
      (decide (A < L) && !decide (task_request_bound_function task_cost max_arrivals tsk (A) = task_request_bound_function task_cost max_arrivals tsk (A + ε))) = true →
      ∃ F, A + F = priority_inversion_bound + (task_request_bound_function task_cost max_arrivals tsk (A + ε) - (task_cost tsk - task_lock_in_service tsk)) +
          total_ohep_request_bound_function_FP task_cost higher_eq_priority max_arrivals ts tsk (A + F) ∧
        F + (task_cost tsk - task_lock_in_service tsk) ≤ R)
    :
    is_response_time_bound_of_task job_arrival job_cost job_task arr_seq sched tsk R := by
  intro js ARRs TSKs
  rcases Nat.eq_zero_or_pos (job_cost js) with ZERO | POS
  · simp [is_response_time_bound_of_job, completed_by, ZERO]
  exact uniprocessor_response_time_bound_seq task_cost job_arrival job_cost job_task arr_seq
    H_arrival_times_are_consistent sched H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute
    H_completed_jobs_dont_execute H_job_cost_le_task_cost ts max_arrivals H_family_of_proper_arrival_curves tsk
    H_tsk_in_ts job_lock_in_service task_lock_in_service H_proper_job_lock_in_service H_proper_task_lock_in_service
    (interference sched (FP_to_JLFP job_task higher_eq_priority)) (interfering_workload job_cost arr_seq sched (FP_to_JLFP job_task higher_eq_priority)) (instantiated_i_and_w_are_consistent_with_schedule job_arrival job_cost job_task arr_seq H_arrival_times_are_consistent H_arr_seq_is_a_set sched H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_work_conserving tsk higher_eq_priority H_priority_is_reflexive) H_sequential_jobs
    (instantiated_interference_and_workload_consistent_with_sequential_jobs job_arrival job_cost job_task arr_seq H_arrival_times_are_consistent H_arr_seq_is_a_set sched H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute tsk higher_eq_priority H_priority_is_reflexive) L
    (instantiated_busy_intervals_are_bounded task_cost job_arrival job_cost job_task arr_seq H_arrival_times_are_consistent H_arr_seq_is_a_set sched H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_work_conserving H_job_cost_le_task_cost ts H_all_jobs_from_taskset max_arrivals H_family_of_proper_arrival_curves tsk higher_eq_priority H_priority_is_reflexive priority_inversion_bound H_priority_inversion_is_bounded L H_L_positive H_fixed_point) (fun t A R => (priority_inversion_bound + total_ohep_request_bound_function_FP task_cost higher_eq_priority max_arrivals ts tsk (R)))
    (instantiated_task_interference_is_bounded task_cost job_arrival job_cost job_task arr_seq H_arrival_times_are_consistent H_arr_seq_is_a_set sched H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_sequential_jobs H_job_cost_le_task_cost ts H_all_jobs_from_taskset max_arrivals H_family_of_proper_arrival_curves tsk higher_eq_priority H_priority_is_reflexive priority_inversion_bound H_priority_inversion_is_bounded) R
    (fun A INSP => correct_search_space task_cost job_arrival job_cost job_task arr_seq H_arrival_times_are_consistent H_job_cost_le_task_cost ts max_arrivals H_family_of_proper_arrival_curves tsk H_tsk_in_ts task_lock_in_service higher_eq_priority priority_inversion_bound L H_L_positive R H_R_is_maximum js ARRs TSKs (decide_eq_true POS) A INSP)
    js ARRs TSKs

end Prosa.Classic.Model.Schedule.Uni.Limited.FixedPriority.ResponseTimeBound.AbstractRTAforFPwithArrivalCurves
