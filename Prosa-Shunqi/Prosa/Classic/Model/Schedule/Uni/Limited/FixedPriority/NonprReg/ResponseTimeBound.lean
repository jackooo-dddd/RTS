-- Authoritative source:
-- ProsaBuddy classic Prosa (prosabuddy commit f692cb7479780cf6009493f373a309e13165201c)
-- source: classic/model/schedule/uni/limited/fixed_priority/nonpr_reg/response_time_bound.v
-- sha256: see Prosa-Shunqi/classic-prosa/comprehensive-classic/file_order.csv (rank 181)

import Prosa.Classic.Util.All
import Prosa.Classic.Model.Arrival.Basic.Job
import Prosa.Classic.Model.Arrival.Basic.TaskArrival
import Prosa.Classic.Model.Priority
import Prosa.Classic.Model.Arrival.Curves.Bounds
import Prosa.Classic.Analysis.Uni.ArrivalCurves.WorkloadBound
import Prosa.Classic.Model.Schedule.Uni.Service
import Prosa.Classic.Model.Schedule.Uni.Workload
import Prosa.Classic.Model.Schedule.Uni.Schedule
import Prosa.Classic.Model.Schedule.Uni.ResponseTime
import Prosa.Classic.Model.Schedule.Uni.Limited.Platform.Definitions
import Prosa.Classic.Model.Schedule.Uni.Limited.Platform.PriorityInversionIsBounded
import Prosa.Classic.Model.Schedule.Uni.Limited.Schedule
import Prosa.Classic.Model.Schedule.Uni.Limited.BusyInterval
import Prosa.Classic.Model.Schedule.Uni.Limited.FixedPriority.ResponseTimeBound
import Prosa.Classic.Model.Schedule.Uni.Limited.Rbf

/-!
Response-time analysis for FP scheduling with bounded nonpreemptive segments and arrival curves (Rocq module
`RTAforFPwithBoundedNonpreemptiveSegmentsWithArrivalCurves` of
`classic/model/schedule/uni/limited/fixed_priority/nonpr_reg/response_time_bound.v`).

Representation notes:
* The section-local `Let`s are unfolded: `jlfp_higher_eq_priority` is `FP_to_JLFP job_task higher_eq_priority`,
  `max_length_of_priority_inversion` is the accepted `PriorityInversionIsBounded.max_length_of_priority_inversion
  job_max_nps arr_seq …`, `task_rbf`/`total_hep_rbf`/`total_ohep_rbf` are the request-bound functions of
  `MaxArrivalsWorkloadBound`, and `is_in_search_space A` is `(decide (A < L) && !decide (task_rbf A = task_rbf
  (A + ε))) = true`.
* `\max_(x <- s | P x) F x` is `Prosa.Util.Sum.maxFiltered s P F`; `~~ b` is `!b`; `ε` is `1`.
* Binder lists follow the Rocq contract. As in Rocq, the final theorem applies the FP analysis of
  `classic/model/schedule/uni/limited/fixed_priority/response_time_bound.v` with the blocking bound as the
  priority-inversion bound, which is proved here from the preemption model (`preemption_time_exists` and
  `not_quiet_implies_exists_scheduled_hp_job` of the accepted `PriorityInversionIsBounded` module).
-/

set_option linter.dupNamespace false
set_option linter.unusedVariables false

namespace Prosa.Classic.Model.Schedule.Uni.Limited.FixedPriority.NonprReg.ResponseTimeBound.RTAforFPwithBoundedNonpreemptiveSegmentsWithArrivalCurves

open Prosa.Classic.Model.Time.Time
open Prosa.Classic.Model.Arrival.Basic.ArrivalSequence.ArrivalSequence
open Prosa.Classic.Model.Arrival.Basic.Job.Job
open Prosa.Classic.Model.Arrival.Basic.TaskArrival.TaskArrival
open Prosa.Classic.Model.Priority.Priority
open Prosa.Classic.Model.Schedule.Uni.Schedule.UniprocessorSchedule
open Prosa.Classic.Model.Schedule.Uni.ResponseTime.ResponseTime
open Prosa.Classic.Model.Schedule.Uni.Limited.Platform.Definitions.LimitedPreemptionPlatform
open Prosa.Classic.Model.Schedule.Uni.Limited.Platform.PriorityInversionIsBounded.PriorityInversionIsBounded
open Prosa.Classic.Model.Schedule.Uni.Limited.Schedule
open Prosa.Classic.Model.Schedule.Uni.Limited.BusyInterval.BusyIntervalJLFP
open Prosa.Classic.Model.Schedule.Uni.Limited.FixedPriority.ResponseTimeBound.AbstractRTAforFPwithArrivalCurves
  (uniprocessor_response_time_bound_fp)
open Prosa.Classic.Model.Arrival.Curves.Bounds.ArrivalCurves
open Prosa.Classic.Analysis.Uni.ArrivalCurves.WorkloadBound.MaxArrivalsWorkloadBound
open Prosa.Util.Sum (maxFiltered)

universe u v

local macro "omega'" : tactic =>
  `(tactic| ((try dsimp only [Prosa.Classic.Model.Time.Time.time,
    Prosa.Classic.Model.Time.Time.instant, Prosa.Classic.Model.Time.Time.duration] at *) <;>
    omega))

def blocking_bound {Task : Type u} [DecidableEq Task] (task_max_nps : Task → time)
    (higher_eq_priority : FP_policy Task) (ts : List Task) (tsk : Task) : Nat :=
  maxFiltered ts (fun tsk_other => !higher_eq_priority tsk_other tsk) (fun tsk_other => task_max_nps tsk_other - ε)

/-! ### LEAN_HELPER lemmas -/

/-- LEAN_HELPER: a retained element is bounded by the filtered maximum. -/
private theorem le_maxFiltered {α : Type _} (l : List α) (P : α → Bool) (F : α → Nat) (x : α)
    (IN : x ∈ l) (Px : P x = true) : F x ≤ maxFiltered l P F := by
  unfold maxFiltered
  have hx : F x ∈ (l.filter P).map F := List.mem_map.mpr ⟨x, List.mem_filter.mpr ⟨IN, Px⟩, rfl⟩
  generalize (l.filter P).map F = m at hx
  induction m with
  | nil => simp at hx
  | cons a m ih =>
    simp only [List.foldr_cons]
    rcases List.mem_cons.mp hx with rfl | h
    · exact Nat.le_max_left _ _
    · exact Nat.le_trans (ih h) (Nat.le_max_right _ _)

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

/-- LEAN_HELPER: the cumulative priority inversion over an interval is at most its length. -/
private theorem cumulative_priority_inversion_le_length {Job : Type v} [DecidableEq Job] (sched : schedule Job)
    (higher_eq_priority : JLFP_policy Job) (j : Job) (t1 t2 : time) :
    cumulative_priority_inversion sched higher_eq_priority j t1 t2 ≤ t2 - t1 := by
  unfold cumulative_priority_inversion
  calc ∑ t ∈ Finset.Ico t1 t2, (is_priority_inversion sched higher_eq_priority j t).toNat
      ≤ ∑ _t ∈ Finset.Ico t1 t2, 1 := Finset.sum_le_sum (fun t _ => Bool.toNat_le _)
    _ = t2 - t1 := by simp

/-! ### Priority inversion is bounded -/

theorem priority_inversion_is_bounded_by_blocking {Task : Type u} [DecidableEq Task] (task_max_nps task_cost : Task → time)
    {Job : Type v} [DecidableEq Job] (job_max_nps job_cost : Job → time) (job_task : Job → Task)
    (arr_seq : arrival_sequence Job)
    (H_job_cost_le_task_cost : cost_of_jobs_from_arrival_sequence_le_task_cost task_cost job_cost job_task arr_seq)
    (higher_eq_priority : FP_policy Task) (can_be_preempted : Job → time → Bool)
    (H_model_with_bounded_nonpreemptive_segments :
      model_with_bounded_nonpreemptive_segments job_cost job_task arr_seq can_be_preempted job_max_nps task_max_nps)
    (ts : List Task) (H_all_jobs_from_taskset : ∀ j, arrives_in arr_seq j → job_task j ∈ ts) (tsk : Task) :
    ∀ (j : Job) (t : time),
      arrives_in arr_seq j →
      job_task j = tsk →
      max_length_of_priority_inversion job_max_nps arr_seq (FP_to_JLFP job_task higher_eq_priority) j t ≤
        blocking_bound task_max_nps higher_eq_priority ts tsk := by
  intro j t ARR TSK
  apply maxFiltered_le
  intro j' JINB NOTHEP
  have ARR' := in_arrivals_implies_arrived arr_seq j' 0 t JINB
  have NPS := (H_model_with_bounded_nonpreemptive_segments j' ARR').2.2.1 ARR'
  apply Nat.le_trans (Nat.sub_le_sub_right NPS _)
  apply le_maxFiltered ts _ (fun tsk_other => task_max_nps tsk_other - ε) (job_task j')
    (H_all_jobs_from_taskset j' ARR')
  simpa [FP_to_JLFP, TSK] using NOTHEP

theorem priority_inversion_is_bounded {Task : Type u} [DecidableEq Task] (task_max_nps task_cost : Task → time)
    {Job : Type v} [DecidableEq Job] (job_arrival job_max_nps job_cost : Job → time) (job_task : Job → Task)
    (arr_seq : arrival_sequence Job)
    (H_arrival_times_are_consistent : arrival_times_are_consistent job_arrival arr_seq) (sched : schedule Job)
    (H_jobs_come_from_arrival_sequence : jobs_come_from_arrival_sequence sched arr_seq)
    (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute job_arrival sched)
    (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched)
    (H_job_cost_le_task_cost : cost_of_jobs_from_arrival_sequence_le_task_cost task_cost job_cost job_task arr_seq)
    (higher_eq_priority : FP_policy Task) (H_priority_is_reflexive : FP_is_reflexive higher_eq_priority)
    (H_priority_is_transitive : FP_is_transitive higher_eq_priority) (can_be_preempted : Job → time → Bool)
    (H_correct_preemption_model : correct_preemption_model arr_seq sched can_be_preempted)
    (H_model_with_bounded_nonpreemptive_segments :
      model_with_bounded_nonpreemptive_segments job_cost job_task arr_seq can_be_preempted job_max_nps task_max_nps)
    (H_work_conserving : work_conserving job_arrival job_cost arr_seq sched)
    (H_respects_policy :
      respects_FP_policy_at_preemption_point job_arrival job_cost job_task arr_seq sched can_be_preempted
        higher_eq_priority)
    (ts : List Task) (H_all_jobs_from_taskset : ∀ j, arrives_in arr_seq j → job_task j ∈ ts) (tsk : Task) :
    priority_inversion_is_bounded_by job_arrival job_cost job_task arr_seq sched
      (FP_to_JLFP job_task higher_eq_priority) tsk (blocking_bound task_max_nps higher_eq_priority ts tsk) := by
  intro j ARR TSK POS t1 t2 PREF
  have BLOCK := priority_inversion_is_bounded_by_blocking task_max_nps task_cost job_max_nps job_cost job_task arr_seq
    H_job_cost_le_task_cost higher_eq_priority can_be_preempted H_model_with_bounded_nonpreemptive_segments ts
    H_all_jobs_from_taskset tsk j t1 ARR TSK
  rcases le_or_gt (t2 - t1) (blocking_bound task_max_nps higher_eq_priority ts tsk) with NEQ | NEQ
  · exact Nat.le_trans (cumulative_priority_inversion_le_length _ _ _ _ _) NEQ
  have REFL : JLFP_is_reflexive (FP_to_JLFP job_task higher_eq_priority) :=
    fun x => H_priority_is_reflexive (job_task x)
  have TRANS : JLFP_is_transitive (FP_to_JLFP job_task higher_eq_priority) :=
    fun y x z h1 h2 => H_priority_is_transitive _ _ _ h1 h2
  obtain ⟨ppt, PPT, GELE⟩ := preemption_time_exists task_max_nps job_arrival job_max_nps job_cost job_task arr_seq
    H_arrival_times_are_consistent sched H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute
    H_completed_jobs_dont_execute _ REFL TRANS can_be_preempted H_correct_preemption_model
    H_model_with_bounded_nonpreemptive_segments H_work_conserving H_respects_policy j ARR (decide_eq_true POS) t1 t2
    PREF
  simp only [Bool.and_eq_true, decide_eq_true_eq] at GELE
  obtain ⟨GE, LE⟩ := GELE
  have LT12 := PREF.1
  have PPTLE : ppt ≤ t2 := by omega'
  unfold cumulative_priority_inversion
  rw [← Finset.sum_Ico_consecutive _ GE PPTLE]
  have ZERO : ∑ t ∈ Finset.Ico ppt t2, (is_priority_inversion sched (FP_to_JLFP job_task higher_eq_priority) j t).toNat
      = 0 := by
    apply Finset.sum_eq_zero
    intro t ht
    rw [Finset.mem_Ico] at ht
    obtain ⟨j_hp, _, HP, SCHEDHP⟩ := not_quiet_implies_exists_scheduled_hp_job task_max_nps job_arrival job_max_nps
      job_cost job_task arr_seq H_arrival_times_are_consistent sched H_jobs_come_from_arrival_sequence
      H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute _ REFL TRANS can_be_preempted
      H_correct_preemption_model H_model_with_bounded_nonpreemptive_segments H_work_conserving H_respects_policy j ARR
      (decide_eq_true POS) t1 t2 PREF (ppt - t1)
      ⟨ppt, PPT, by simp only [Bool.and_eq_true, decide_eq_true_eq]; omega'⟩ t
      (by simp only [Bool.and_eq_true, decide_eq_true_eq]; omega')
    have SCHED : sched t = some j_hp := of_decide_eq_true SCHEDHP
    simp [is_priority_inversion, SCHED, HP]
  rw [ZERO, Nat.add_zero]
  calc _ ≤ ppt - t1 := cumulative_priority_inversion_le_length _ _ _ _ _
    _ ≤ blocking_bound task_max_nps higher_eq_priority ts tsk := by omega'

/-! ### Response-time bound -/

theorem uniprocessor_response_time_bound_fp_with_bounded_nonpreemptive_segments {Task : Type u} [DecidableEq Task]
    (task_max_nps task_cost : Task → time) {Job : Type v} [DecidableEq Job]
    (job_arrival job_max_nps job_cost : Job → time) (job_task : Job → Task) (arr_seq : arrival_sequence Job)
    (H_arrival_times_are_consistent : arrival_times_are_consistent job_arrival arr_seq)
    (H_arr_seq_is_a_set : arrival_sequence_is_a_set arr_seq) (sched : schedule Job)
    (H_jobs_come_from_arrival_sequence : jobs_come_from_arrival_sequence sched arr_seq)
    (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute job_arrival sched)
    (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched)
    (H_sequential_jobs : sequential_jobs job_arrival job_cost sched job_task)
    (H_job_cost_le_task_cost : cost_of_jobs_from_arrival_sequence_le_task_cost task_cost job_cost job_task arr_seq)
    (higher_eq_priority : FP_policy Task) (H_priority_is_reflexive : FP_is_reflexive higher_eq_priority)
    (H_priority_is_transitive : FP_is_transitive higher_eq_priority) (can_be_preempted : Job → time → Bool)
    (H_correct_preemption_model : correct_preemption_model arr_seq sched can_be_preempted)
    (H_model_with_bounded_nonpreemptive_segments :
      model_with_bounded_nonpreemptive_segments job_cost job_task arr_seq can_be_preempted job_max_nps task_max_nps)
    (H_work_conserving : work_conserving job_arrival job_cost arr_seq sched)
    (H_respects_policy :
      respects_FP_policy_at_preemption_point job_arrival job_cost job_task arr_seq sched can_be_preempted
        higher_eq_priority)
    (ts : List Task) (H_all_jobs_from_taskset : ∀ j, arrives_in arr_seq j → job_task j ∈ ts) (tsk : Task)
    (H_tsk_in_ts : tsk ∈ ts) (max_arrivals : Task → time → Nat)
    (H_family_of_proper_arrival_curves : family_of_proper_arrival_curves job_task arr_seq max_arrivals ts)
    (job_lock_in_service : Job → time) (task_lock_in_service : Task → time)
    (H_proper_job_lock_in_service : proper_job_lock_in_service job_cost arr_seq sched job_lock_in_service)
    (H_proper_task_lock_in_service :
      proper_task_lock_in_service task_cost job_task arr_seq job_lock_in_service task_lock_in_service tsk)
    (L : time) (H_L_positive : 0 < L)
    (H_fixed_point : L = blocking_bound task_max_nps higher_eq_priority ts tsk +
      total_hep_request_bound_function_FP task_cost higher_eq_priority max_arrivals ts tsk L)
    (R : Nat)
    (H_R_is_maximum : ∀ A,
      (decide (A < L) && !decide (task_request_bound_function task_cost max_arrivals tsk A =
        task_request_bound_function task_cost max_arrivals tsk (A + ε))) = true →
      ∃ F, A + F = blocking_bound task_max_nps higher_eq_priority ts tsk +
          (task_request_bound_function task_cost max_arrivals tsk (A + ε) -
            (task_cost tsk - task_lock_in_service tsk)) +
          total_ohep_request_bound_function_FP task_cost higher_eq_priority max_arrivals ts tsk (A + F) ∧
        F + (task_cost tsk - task_lock_in_service tsk) ≤ R) :
    is_response_time_bound_of_task job_arrival job_cost job_task arr_seq sched tsk R :=
  uniprocessor_response_time_bound_fp task_cost job_arrival job_cost job_task arr_seq H_arrival_times_are_consistent
    H_arr_seq_is_a_set sched H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute
    H_completed_jobs_dont_execute H_work_conserving H_sequential_jobs H_job_cost_le_task_cost ts
    H_all_jobs_from_taskset max_arrivals H_family_of_proper_arrival_curves tsk H_tsk_in_ts job_lock_in_service
    task_lock_in_service H_proper_job_lock_in_service H_proper_task_lock_in_service higher_eq_priority
    H_priority_is_reflexive (blocking_bound task_max_nps higher_eq_priority ts tsk)
    (priority_inversion_is_bounded task_max_nps task_cost job_arrival job_max_nps job_cost job_task arr_seq
      H_arrival_times_are_consistent sched H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute
      H_completed_jobs_dont_execute H_job_cost_le_task_cost higher_eq_priority H_priority_is_reflexive
      H_priority_is_transitive can_be_preempted H_correct_preemption_model H_model_with_bounded_nonpreemptive_segments
      H_work_conserving H_respects_policy ts H_all_jobs_from_taskset tsk)
    L H_L_positive H_fixed_point R H_R_is_maximum

end Prosa.Classic.Model.Schedule.Uni.Limited.FixedPriority.NonprReg.ResponseTimeBound.RTAforFPwithBoundedNonpreemptiveSegmentsWithArrivalCurves
