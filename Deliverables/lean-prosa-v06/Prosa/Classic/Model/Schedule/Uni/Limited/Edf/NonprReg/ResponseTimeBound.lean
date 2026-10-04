-- Authoritative source:
-- ProsaBuddy classic Prosa (prosabuddy commit f692cb7479780cf6009493f373a309e13165201c)
-- source: classic/model/schedule/uni/limited/edf/nonpr_reg/response_time_bound.v
-- sha256: see Prosa-Shunqi/classic-prosa/comprehensive-classic/file_order.csv (rank 180)

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
import Prosa.Classic.Model.Schedule.Uni.Limited.Edf.ResponseTimeBound
import Prosa.Classic.Model.Schedule.Uni.Limited.Rbf

/-!
Response-time analysis for EDF scheduling with bounded nonpreemptive segments and arrival curves (Rocq module
`RTAforEDFwithBoundedNonpreemptiveSegmentsWithArrivalCurves` of
`classic/model/schedule/uni/limited/edf/nonpr_reg/response_time_bound.v`).

Representation notes:
* The section-local `Let`s are unfolded: `higher_eq_priority` is `EDF job_arrival (job_relative_dealine task_deadline
  job_task)` (the accepted name of `job_relative_deadline`), `max_length_of_priority_inversion` is the accepted
  `PriorityInversionIsBounded.max_length_of_priority_inversion job_max_nps arr_seq …`, the request-bound functions are
  those of `MaxArrivalsWorkloadBound`, `bound_on_total_hep_workload A Δ` is the filtered sum over the other tasks of
  `rbf tsk_o (min (A + ε + D tsk - D tsk_o) Δ)`, and `task_rbf_changes_at`/`bound_on_total_hep_workload_changes_at`
  are the definitions of the EDF analysis (`classic/model/schedule/uni/limited/edf/response_time_bound.v`).
* `\max_(x <- s | P x) F x` is `Prosa.Util.Sum.maxFiltered s P F`; `x != y` is `!decide (x = y)`; `ε` is `1`.
* Binder lists follow the Rocq contract. As in Rocq, the final theorem applies the EDF analysis with the blocking
  bound as the priority-inversion bound, which is proved here from the preemption model.
-/

set_option linter.dupNamespace false
set_option linter.unusedVariables false

namespace Prosa.Classic.Model.Schedule.Uni.Limited.Edf.NonprReg.ResponseTimeBound.RTAforEDFwithBoundedNonpreemptiveSegmentsWithArrivalCurves

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
open Prosa.Classic.Model.Schedule.Uni.Limited.Edf.ResponseTimeBound.AbstractRTAforEDFwithArrivalCurves
  (uniprocessor_response_time_bound_edf task_rbf_changes_at bound_on_total_hep_workload_changes_at)
open Prosa.Classic.Model.Arrival.Curves.Bounds.ArrivalCurves
open Prosa.Classic.Analysis.Uni.ArrivalCurves.WorkloadBound.MaxArrivalsWorkloadBound
open Prosa.Util.Sum (maxFiltered sumFiltered)

universe u v

local macro "omega'" : tactic =>
  `(tactic| ((try dsimp only [Prosa.Classic.Model.Time.Time.time,
    Prosa.Classic.Model.Time.Time.instant, Prosa.Classic.Model.Time.Time.duration] at *) <;>
    omega))

def blocking_bound {Task : Type u} [DecidableEq Task] (task_max_nps task_deadline : Task → time)
    (ts : List Task) (tsk : Task) : Nat :=
  maxFiltered ts (fun tsk_other => !decide (tsk_other = tsk) && decide (task_deadline tsk < task_deadline tsk_other))
    (fun tsk_other => task_max_nps tsk_other - ε)

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

theorem priority_inversion_is_bounded_by_blocking {Task : Type u} [DecidableEq Task]
    (task_max_nps task_cost task_deadline : Task → time) {Job : Type v} [DecidableEq Job]
    (job_arrival job_max_nps job_cost : Job → time) (job_task : Job → Task) (arr_seq : arrival_sequence Job)
    (H_arrival_times_are_consistent : arrival_times_are_consistent job_arrival arr_seq)
    (can_be_preempted : Job → time → Bool)
    (H_model_with_bounded_nonpreemptive_segments :
      model_with_bounded_nonpreemptive_segments job_cost job_task arr_seq can_be_preempted job_max_nps task_max_nps)
    (ts : List Task) (H_all_jobs_from_taskset : ∀ j, arrives_in arr_seq j → job_task j ∈ ts)
    (H_job_cost_le_task_cost : cost_of_jobs_from_arrival_sequence_le_task_cost task_cost job_cost job_task arr_seq)
    (tsk : Task) :
    ∀ (j : Job) (t : time),
      arrives_in arr_seq j →
      job_task j = tsk →
      t ≤ job_arrival j →
      max_length_of_priority_inversion job_max_nps arr_seq (EDF job_arrival (job_relative_dealine task_deadline job_task)) j t ≤ blocking_bound task_max_nps task_deadline ts tsk := by
  intro j t ARR TSK LE
  apply maxFiltered_le
  intro j' JINB NOTHEP
  have ARR' := in_arrivals_implies_arrived arr_seq j' 0 t JINB
  have NPS := (H_model_with_bounded_nonpreemptive_segments j' ARR').2.2.1 ARR'
  have JA := in_arrivals_implies_arrived_between job_arrival arr_seq H_arrival_times_are_consistent j' 0 t JINB
  simp only [arrived_between, Bool.and_eq_true, decide_eq_true_eq] at JA
  have HEP : ¬ (job_arrival j' + task_deadline (job_task j') ≤ job_arrival j + task_deadline (job_task j)) := by
    intro h
    simp [EDF, job_relative_dealine, h] at NOTHEP
  rw [TSK] at HEP
  apply Nat.le_trans (Nat.sub_le_sub_right NPS _)
  apply le_maxFiltered ts _ (fun tsk_other => task_max_nps tsk_other - ε) (job_task j')
    (H_all_jobs_from_taskset j' ARR')
  have NEQ : job_task j' ≠ tsk := by
    intro h
    rw [h] at HEP
    omega'
  simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq]
  exact ⟨NEQ, by omega'⟩

theorem priority_inversion_is_bounded {Task : Type u} [DecidableEq Task]
    (task_max_nps task_cost task_deadline : Task → time) {Job : Type v} [DecidableEq Job]
    (job_arrival job_max_nps job_cost : Job → time) (job_task : Job → Task) (arr_seq : arrival_sequence Job)
    (H_arrival_times_are_consistent : arrival_times_are_consistent job_arrival arr_seq) (sched : schedule Job)
    (H_jobs_come_from_arrival_sequence : jobs_come_from_arrival_sequence sched arr_seq)
    (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute job_arrival sched)
    (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched)
    (can_be_preempted : Job → time → Bool)
    (H_correct_preemption_model : correct_preemption_model arr_seq sched can_be_preempted)
    (H_model_with_bounded_nonpreemptive_segments :
      model_with_bounded_nonpreemptive_segments job_cost job_task arr_seq can_be_preempted job_max_nps task_max_nps)
    (H_work_conserving : work_conserving job_arrival job_cost arr_seq sched)
    (H_respects_policy :
      respects_JLFP_policy_at_preemption_point job_arrival job_cost arr_seq sched can_be_preempted (EDF job_arrival (job_relative_dealine task_deadline job_task)))
    (ts : List Task) (H_all_jobs_from_taskset : ∀ j, arrives_in arr_seq j → job_task j ∈ ts)
    (H_job_cost_le_task_cost : cost_of_jobs_from_arrival_sequence_le_task_cost task_cost job_cost job_task arr_seq)
    (tsk : Task) :
    priority_inversion_is_bounded_by job_arrival job_cost job_task arr_seq sched (EDF job_arrival (job_relative_dealine task_deadline job_task)) tsk
      (blocking_bound task_max_nps task_deadline ts tsk) := by
  intro j ARR TSK POS t1 t2 PREF
  have T := PREF.2.2.2
  simp only [Bool.and_eq_true, decide_eq_true_eq] at T
  have BLOCK := priority_inversion_is_bounded_by_blocking task_max_nps task_cost task_deadline job_arrival job_max_nps
    job_cost job_task arr_seq H_arrival_times_are_consistent can_be_preempted H_model_with_bounded_nonpreemptive_segments
    ts H_all_jobs_from_taskset H_job_cost_le_task_cost tsk j t1 ARR TSK T.1
  rcases le_or_gt (t2 - t1) (blocking_bound task_max_nps task_deadline ts tsk) with NEQ | NEQ
  · exact Nat.le_trans (cumulative_priority_inversion_le_length _ _ _ _ _) NEQ
  have REFL : JLFP_is_reflexive (EDF job_arrival (job_relative_dealine task_deadline job_task)) := EDF_is_reflexive _ _
  have TRANS : JLFP_is_transitive (EDF job_arrival (job_relative_dealine task_deadline job_task)) := EDF_is_transitive _ _
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
  have ZERO : ∑ t ∈ Finset.Ico ppt t2, (is_priority_inversion sched (EDF job_arrival (job_relative_dealine task_deadline job_task)) j t).toNat = 0 := by
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
    _ ≤ blocking_bound task_max_nps task_deadline ts tsk := by omega'

/-! ### Response-time bound -/

theorem uniprocessor_response_time_bound_edf_with_bounded_nonpreemptive_segments {Task : Type u} [DecidableEq Task]
    (task_max_nps task_cost task_deadline : Task → time) {Job : Type v} [DecidableEq Job]
    (job_arrival job_max_nps job_cost : Job → time) (job_task : Job → Task) (arr_seq : arrival_sequence Job)
    (H_arrival_times_are_consistent : arrival_times_are_consistent job_arrival arr_seq)
    (H_arr_seq_is_a_set : arrival_sequence_is_a_set arr_seq) (sched : schedule Job)
    (H_jobs_come_from_arrival_sequence : jobs_come_from_arrival_sequence sched arr_seq)
    (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute job_arrival sched)
    (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched)
    (H_sequential_jobs : sequential_jobs job_arrival job_cost sched job_task)
    (can_be_preempted : Job → time → Bool)
    (H_correct_preemption_model : correct_preemption_model arr_seq sched can_be_preempted)
    (H_model_with_bounded_nonpreemptive_segments :
      model_with_bounded_nonpreemptive_segments job_cost job_task arr_seq can_be_preempted job_max_nps task_max_nps)
    (H_work_conserving : work_conserving job_arrival job_cost arr_seq sched)
    (H_respects_policy :
      respects_JLFP_policy_at_preemption_point job_arrival job_cost arr_seq sched can_be_preempted (EDF job_arrival (job_relative_dealine task_deadline job_task)))
    (ts : List Task) (H_all_jobs_from_taskset : ∀ j, arrives_in arr_seq j → job_task j ∈ ts)
    (H_job_cost_le_task_cost : cost_of_jobs_from_arrival_sequence_le_task_cost task_cost job_cost job_task arr_seq)
    (tsk : Task) (H_tsk_in_ts : tsk ∈ ts) (max_arrivals : Task → time → Nat)
    (H_family_of_proper_arrival_curves : family_of_proper_arrival_curves job_task arr_seq max_arrivals ts)
    (job_lock_in_service : Job → time) (task_lock_in_service : Task → time)
    (H_proper_job_lock_in_service : proper_job_lock_in_service job_cost arr_seq sched job_lock_in_service)
    (H_proper_task_lock_in_service :
      proper_task_lock_in_service task_cost job_task arr_seq job_lock_in_service task_lock_in_service tsk)
    (L : time) (H_L_positive : 0 < L)
    (H_fixed_point : L = total_request_bound_function task_cost max_arrivals ts L)
    (R : Nat)
    (H_R_is_maximum : ∀ A,
      (decide (A < L) && (task_rbf_changes_at task_cost max_arrivals tsk (A) || bound_on_total_hep_workload_changes_at task_cost task_deadline ts max_arrivals tsk (A))) = true →
      ∃ F, A + F = blocking_bound task_max_nps task_deadline ts tsk +
          (task_request_bound_function task_cost max_arrivals tsk (A + ε) -
            (task_cost tsk - task_lock_in_service tsk)) +
          sumFiltered ts (fun tsk_o => !decide (tsk_o = tsk)) (fun tsk_o => task_request_bound_function task_cost max_arrivals tsk_o (min (A + ε + task_deadline tsk - task_deadline tsk_o) (A + F))) ∧
        F + (task_cost tsk - task_lock_in_service tsk) ≤ R) :
    is_response_time_bound_of_task job_arrival job_cost job_task arr_seq sched tsk R :=
  uniprocessor_response_time_bound_edf task_cost task_deadline job_arrival job_cost job_task arr_seq
    H_arrival_times_are_consistent H_arr_seq_is_a_set sched H_jobs_come_from_arrival_sequence
    H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_work_conserving H_sequential_jobs
    H_job_cost_le_task_cost ts H_all_jobs_from_taskset max_arrivals H_family_of_proper_arrival_curves tsk H_tsk_in_ts
    job_lock_in_service task_lock_in_service H_proper_job_lock_in_service H_proper_task_lock_in_service
    (blocking_bound task_max_nps task_deadline ts tsk)
    (priority_inversion_is_bounded task_max_nps task_cost task_deadline job_arrival job_max_nps job_cost job_task arr_seq
      H_arrival_times_are_consistent sched H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute
      H_completed_jobs_dont_execute can_be_preempted H_correct_preemption_model
      H_model_with_bounded_nonpreemptive_segments H_work_conserving H_respects_policy ts H_all_jobs_from_taskset
      H_job_cost_le_task_cost tsk)
    L H_L_positive H_fixed_point R H_R_is_maximum

end Prosa.Classic.Model.Schedule.Uni.Limited.Edf.NonprReg.ResponseTimeBound.RTAforEDFwithBoundedNonpreemptiveSegmentsWithArrivalCurves
