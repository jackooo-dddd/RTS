-- Authoritative source:
-- ProsaBuddy classic Prosa (prosabuddy commit f692cb7479780cf6009493f373a309e13165201c)
-- source: classic/model/schedule/uni/limited/edf/response_time_bound.v
-- sha256: see Prosa-Shunqi/classic-prosa/comprehensive-classic/file_order.csv (rank 168)

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
`AbstractRTAforFPwithArrivalCurves` of `classic/model/schedule/uni/limited/edf/response_time_bound.v`).

Representation notes:
* The section-local `Let`s are unfolded: `EDF` is `EDF job_arrival (job_relative_dealine task_deadline job_task)` (the
  accepted name of `job_relative_deadline`); `bound_on_total_hep_workload A Δ` is the filtered sum over the other
  tasks of `rbf tsk_o (min (A + ε + D tsk - D tsk_o) Δ)` (`!=` as `!decide (_ = _)`, `minn` as `min`, `has` as
  `List.any`); `total_rbf` is `total_request_bound_function task_cost max_arrivals ts`;
  `interference`/`interfering_workload` are the accepted `JLFPInstantiation.interference sched …` and
  `JLFPInstantiation.interfering_workload job_cost arr_seq sched …`; `task_rbf` is
  `task_request_bound_function task_cost max_arrivals tsk`; `total_hep_rbf`/`total_ohep_rbf` are
  `IBF A R` is `priority_inversion_bound + bound_on_total_hep_workload A R`; `is_in_search_space A` is
  `(decide (A < L) && (task_rbf_changes_at A || bound_on_total_hep_workload_changes_at A)) = true`; the section-local
  `total_interference_bound tsk A Δ` (whose `task_rbf` is that of the section task) is the corresponding `fun`.
* `ε` is the accepted `Prosa.Util.Epsilon` notation (`1`).
* Binder lists follow the Rocq contract. The bound on the interference of other tasks follows the Rocq argument
  (exchange of sums, then for each other task the relevant jobs arrive within `min (A + ε + D tsk - D tsk_o) R` of
  the busy-interval start); the per-task workload is bounded with the accepted `task_workload_le_task_rbf`. As in
  Rocq, the final theorem applies the accepted
  `AbstractSeqRTA.uniprocessor_response_time_bound_seq` with the instantiated interference, using the job under
  analysis (of positive cost) to discharge the search-space hypothesis.
-/

set_option linter.dupNamespace false
set_option linter.unusedVariables false

namespace Prosa.Classic.Model.Schedule.Uni.Limited.Edf.ResponseTimeBound.AbstractRTAforEDFwithArrivalCurves

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
open Prosa.Util.Sum (sumFiltered)

universe u v

local macro "omega'" : tactic =>
  `(tactic| ((try dsimp only [Prosa.Classic.Model.Time.Time.time,
    Prosa.Classic.Model.Time.Time.instant, Prosa.Classic.Model.Time.Time.duration] at *) <;>
    omega))

def task_rbf_changes_at {Task : Type u} [DecidableEq Task] (task_cost : Task → time)
    (max_arrivals : Task → time → Nat) (tsk : Task) (A : time) : Bool :=
  !decide (task_request_bound_function task_cost max_arrivals tsk (A) = task_request_bound_function task_cost max_arrivals tsk (A + ε))

def bound_on_total_hep_workload_changes_at {Task : Type u} [DecidableEq Task] (task_cost task_deadline : Task → time)
    (ts : List Task) (max_arrivals : Task → time → Nat) (tsk : Task) (A : Nat) : Bool :=
  ts.any (fun tsko => !decide (tsk = tsko) &&
    !decide (task_request_bound_function task_cost max_arrivals tsko (A + task_deadline tsk - task_deadline tsko) =
      task_request_bound_function task_cost max_arrivals tsko (A + ε + task_deadline tsk - task_deadline tsko)))

/-! ### LEAN_HELPER lemmas -/

/-- LEAN_HELPER: a filtered sum over a concatenation. -/
private theorem sumFiltered_append' {α : Type _} (l1 l2 : List α) (P : α → Bool) (F : α → Nat) :
    sumFiltered (l1 ++ l2) P F = sumFiltered l1 P F + sumFiltered l2 P F := by
  simp [sumFiltered, List.filter_append, List.map_append, List.sum_append]

/-- LEAN_HELPER: a filtered sum with no retained element is zero. -/
private theorem sumFiltered_eq_zero {α : Type _} (l : List α) (P : α → Bool) (F : α → Nat)
    (H : ∀ x ∈ l, P x = false) : sumFiltered l P F = 0 := by
  unfold sumFiltered
  rw [List.filter_eq_nil_iff.mpr (fun x hx => by simp [H x hx])]
  rfl

/-- LEAN_HELPER: one retained term is bounded by the filtered sum. -/
private theorem single_le_sumFiltered {α : Type _} (l : List α) (P : α → Bool) (F : α → Nat) (x : α)
    (IN : x ∈ l) (Px : P x = true) : F x ≤ sumFiltered l P F := by
  unfold sumFiltered
  apply List.le_sum_of_mem
  exact List.mem_map.mpr ⟨x, List.mem_filter.mpr ⟨IN, Px⟩, rfl⟩

/-- LEAN_HELPER: a filtered sum of a sum of two functions. -/
private theorem sumFiltered_add {α : Type _} (l : List α) (P : α → Bool) (F G : α → Nat) :
    sumFiltered l P (fun x => F x + G x) = sumFiltered l P F + sumFiltered l P G := by
  unfold sumFiltered
  induction (l.filter P) with
  | nil => rfl
  | cons a l ih => simp only [List.map_cons, List.sum_cons, ih]; omega

/-- LEAN_HELPER: the workload of the jobs of other tasks is covered by the per-task workloads. -/
private theorem workload_le_sum_over_tasks {Task : Type u} [DecidableEq Task] {Job : Type v} [DecidableEq Job]
    (job_cost : Job → time) (job_task : Job → Task) (ts : List Task) (tsk : Task) (Q : Job → Bool) :
    ∀ l : List Job, (∀ x ∈ l, job_task x ∈ ts) →
      sumFiltered l (fun x => Q x && !decide (job_task x = tsk)) job_cost ≤
        sumFiltered ts (fun tsk_o => !decide (tsk_o = tsk))
          (fun tsk_o => sumFiltered l (fun x => Q x && decide (job_task x = tsk_o)) job_cost)
  | [], _ => by simp [sumFiltered]
  | a :: l, H => by
    have IH := workload_le_sum_over_tasks job_cost job_task ts tsk Q l (fun x hx => H x (List.mem_cons_of_mem _ hx))
    have SPLIT : sumFiltered ts (fun tsk_o => !decide (tsk_o = tsk))
          (fun tsk_o => sumFiltered (a :: l) (fun x => Q x && decide (job_task x = tsk_o)) job_cost) =
        sumFiltered ts (fun tsk_o => !decide (tsk_o = tsk))
          (fun tsk_o => if (Q a && decide (job_task a = tsk_o)) = true then job_cost a else 0) +
        sumFiltered ts (fun tsk_o => !decide (tsk_o = tsk))
          (fun tsk_o => sumFiltered l (fun x => Q x && decide (job_task x = tsk_o)) job_cost) := by
      rw [← sumFiltered_add]
      apply congrArg
      funext tsk_o
      unfold sumFiltered
      rw [List.filter_cons]
      split <;> simp_all
    rw [SPLIT]
    unfold sumFiltered at IH ⊢
    rw [List.filter_cons]
    split
    · next HQ =>
      simp only [List.map_cons, List.sum_cons]
      apply Nat.add_le_add _ IH
      simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at HQ
      have := single_le_sumFiltered ts (fun tsk_o => !decide (tsk_o = tsk))
        (fun tsk_o => if (Q a && decide (job_task a = tsk_o)) = true then job_cost a else 0) (job_task a)
        (H a List.mem_cons_self) (by simpa using HQ.2)
      rw [if_pos (show (Q a && decide (job_task a = job_task a)) = true by simp [HQ.1])] at this
      unfold sumFiltered at this
      exact this
    · exact Nat.le_trans IH (Nat.le_add_left _ _)

theorem instantiated_i_and_w_are_coherent_with_schedule
    {Task : Type u} [DecidableEq Task]
    (task_deadline : Task → time)
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
    :
    Prosa.Classic.Model.Schedule.Uni.Limited.AbstractRTA.Definitions.AbstractRTADefinitions.work_conserving job_arrival job_cost job_task arr_seq sched tsk (interference sched (EDF job_arrival (job_relative_dealine task_deadline job_task))) (interfering_workload job_cost arr_seq sched (EDF job_arrival (job_relative_dealine task_deadline job_task))) := by
  intro j t1 t2 t ARR TSK POS BUSY NEQ
  have REFL : JLFP_is_reflexive (EDF job_arrival (job_relative_dealine task_deadline job_task)) := fun x => by simp [EDF]
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
        (EDF job_arrival (job_relative_dealine task_deadline job_task)) j ARR (decide_eq_true POS) H_work_conserving H_jobs_must_arrive_to_execute REFL t1 t2 CBUSY.1 t NEQ
      exact NI (by simp [is_idle, SCHED])
  · intro HYP
    have SCHED : sched t = some j := of_decide_eq_true HYP
    simp only [interference, BusyIntervalJLFP.is_priority_inversion, is_priority_inversion,
      is_interference_from_another_job_with_higher_eq_priority, SCHED, EDF, Nat.le_refl, decide_true,
      Bool.not_true, Bool.and_false, Bool.or_false, Bool.false_eq_true, not_false_eq_true]

theorem instantiated_interference_and_workload_consistent_with_sequential_jobs
    {Task : Type u} [DecidableEq Task]
    (task_deadline : Task → time)
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
    :
    Prosa.Classic.Model.Schedule.Uni.Limited.AbstractRTA.AbstractSeqRta.AbstractSeqRTA.interference_and_workload_consistent_with_sequential_jobs job_arrival job_cost job_task arr_seq sched tsk (interference sched (EDF job_arrival (job_relative_dealine task_deadline job_task))) (interfering_workload job_cost arr_seq sched (EDF job_arrival (job_relative_dealine task_deadline job_task))) := by
  intro j t1 t2 ARR TSK POS BUSY
  have REFL : JLFP_is_reflexive (EDF job_arrival (job_relative_dealine task_deadline job_task)) := fun x => by simp [EDF]
  have CBUSY := (instantiated_busy_interval_equivalent_edf_busy_interval job_arrival job_cost job_task arr_seq
    H_arrival_times_are_consistent H_arr_seq_is_a_set sched H_jobs_come_from_arrival_sequence
    H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute _ REFL j ARR (decide_eq_true POS) t1 t2).mpr BUSY
  obtain ⟨⟨_, QT, _, JA⟩, _⟩ := CBUSY
  simp only [Bool.and_eq_true, decide_eq_true_eq] at JA
  apply (all_jobs_have_completed_equiv_workload_eq_service job_arrival job_cost arr_seq
    H_arrival_times_are_consistent sched H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute
    (fun j0 => decide (job_task j0 = tsk)) 0 t1 t1).mp
  intro s ARRs TSKs
  have TSKs' : job_task s = tsk := of_decide_eq_true TSKs
  have JAs := in_arrivals_implies_arrived_between job_arrival arr_seq H_arrival_times_are_consistent s 0 t1 ARRs
  simp only [arrived_between, Bool.and_eq_true, decide_eq_true_eq] at JAs
  apply QT s (in_arrivals_implies_arrived arr_seq s 0 t1 ARRs)
  · simp only [EDF, job_relative_dealine, TSKs', TSK, decide_eq_true_eq]
    omega'
  · exact in_arrivals_implies_arrived_before job_arrival arr_seq H_arrival_times_are_consistent s t1 ARRs

theorem instantiated_busy_intervals_are_bounded
    {Task : Type u} [DecidableEq Task]
    (task_cost : Task → time)
    (task_deadline : Task → time)
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
    (L : time)
    (H_L_positive : 0 < L)
    (H_fixed_point : L = total_request_bound_function task_cost max_arrivals ts L)
    :
    Prosa.Classic.Model.Schedule.Uni.Limited.AbstractRTA.Definitions.AbstractRTADefinitions.busy_intervals_are_bounded_by job_arrival job_cost job_task arr_seq sched tsk (interference sched (EDF job_arrival (job_relative_dealine task_deadline job_task))) (interfering_workload job_cost arr_seq sched (EDF job_arrival (job_relative_dealine task_deadline job_task))) L := by
  intro j ARR TSK POS
  have REFL : JLFP_is_reflexive (EDF job_arrival (job_relative_dealine task_deadline job_task)) := fun x => by simp [EDF]
  obtain ⟨t1, t2, H1, H2, CBUSY⟩ := exists_busy_interval_from_total_workload_bound job_arrival job_cost arr_seq
    H_arrival_times_are_consistent sched H_jobs_come_from_arrival_sequence (EDF job_arrival (job_relative_dealine task_deadline job_task)) H_arr_seq_is_a_set
    H_work_conserving H_completed_jobs_dont_execute H_jobs_must_arrive_to_execute REFL L H_L_positive
    (fun t => le_of_le_of_eq (total_workload_le_total_rbf'' task_cost job_cost job_task arr_seq ts
      H_job_cost_le_task_cost H_all_jobs_from_taskset max_arrivals
      (fun tsk0 IN0 => (H_family_of_proper_arrival_curves tsk0 IN0).1) t L) H_fixed_point.symm)
    j ARR (decide_eq_true POS)
  exact ⟨t1, t2, H1, H2, (instantiated_busy_interval_equivalent_edf_busy_interval job_arrival job_cost job_task arr_seq
    H_arrival_times_are_consistent H_arr_seq_is_a_set sched H_jobs_come_from_arrival_sequence
    H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute _ REFL j ARR (decide_eq_true POS) t1 t2).mp CBUSY⟩

theorem instantiated_task_interference_is_bounded
    {Task : Type u} [DecidableEq Task]
    (task_cost : Task → time)
    (task_deadline : Task → time)
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
    (priority_inversion_bound : time)
    (H_priority_inversion_is_bounded :
      priority_inversion_is_bounded_by job_arrival job_cost job_task arr_seq sched (EDF job_arrival (job_relative_dealine task_deadline job_task)) tsk
        priority_inversion_bound)
    :
    Prosa.Classic.Model.Schedule.Uni.Limited.AbstractRTA.AbstractSeqRta.AbstractSeqRTA.task_interference_is_bounded_by job_arrival job_cost job_task arr_seq sched tsk (interference sched (EDF job_arrival (job_relative_dealine task_deadline job_task))) (interfering_workload job_cost arr_seq sched (EDF job_arrival (job_relative_dealine task_deadline job_task))) (fun tsk0 A R => (priority_inversion_bound + sumFiltered ts (fun tsk_o => !decide (tsk_o = tsk)) (fun tsk_o => task_request_bound_function task_cost max_arrivals tsk_o (min (A + ε + task_deadline tsk - task_deadline tsk_o) (R))))) := by
  intro j R t1 t2 ARR TSK LT NCOMPL BUSY offset
  have POS : 0 < job_cost j := by
    rcases Nat.eq_zero_or_pos (job_cost j) with ZERO | POS
    · exfalso
      simp [completed_by, ZERO] at NCOMPL
    · exact POS
  have REFL : JLFP_is_reflexive (EDF job_arrival (job_relative_dealine task_deadline job_task)) := fun x => by simp [EDF]
  have CBUSY := (instantiated_busy_interval_equivalent_edf_busy_interval job_arrival job_cost job_task arr_seq
    H_arrival_times_are_consistent H_arr_seq_is_a_set sched H_jobs_come_from_arrival_sequence
    H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute _ REFL j ARR (decide_eq_true POS) t1 t2).mpr BUSY
  obtain ⟨⟨LT12, QT, NQT, ARRj⟩, _⟩ := CBUSY
  have ARRj' := ARRj
  simp only [Bool.and_eq_true, decide_eq_true_eq] at ARRj'
  have INarr : j ∈ jobs_arrived_before arr_seq t2 := by
    apply arrived_between_implies_in_arrivals job_arrival arr_seq H_arrival_times_are_consistent j 0 t2 ARR
    simp only [arrived_between, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨Nat.zero_le _, ARRj'.2⟩
  rw [cumulative_task_interference_split job_arrival job_cost job_task arr_seq sched H_sequential_jobs (EDF job_arrival (job_relative_dealine task_deadline job_task))
    (EDF_respects_sequential_jobs task_deadline job_arrival job_task) tsk j t1 (t1 + R) t2 TSK INarr NCOMPL]
  apply Nat.add_le_add
  · calc ∑ t ∈ Finset.Ico t1 (t1 + R), (BusyIntervalJLFP.is_priority_inversion sched (EDF job_arrival (job_relative_dealine task_deadline job_task)) j t).toNat
        ≤ cumulative_priority_inversion sched (EDF job_arrival (job_relative_dealine task_deadline job_task)) j t1 t2 := by
          unfold cumulative_priority_inversion
          apply Finset.sum_le_sum_of_subset
          exact Finset.Ico_subset_Ico (Nat.le_refl _) (Nat.le_of_lt LT)
      _ ≤ priority_inversion_bound :=
          H_priority_inversion_is_bounded j ARR TSK POS t1 t2 ⟨LT12, QT, NQT, ARRj⟩
  rw [instantiated_cumulative_interference_of_hep_tasks_equal_total_interference_of_hep_tasks job_arrival job_cost
    job_task arr_seq H_arrival_times_are_consistent H_arr_seq_is_a_set sched H_jobs_come_from_arrival_sequence
    H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute _ j t1 (t1 + R) QT]
  apply Nat.le_trans (service_of_jobs_le_workload job_cost sched _ _ H_completed_jobs_dont_execute t1 (t1 + R))
  unfold workload_of_jobs
  rw [TSK]
  have FROMTS : ∀ x ∈ jobs_arrived_between arr_seq t1 (t1 + R), job_task x ∈ ts :=
    fun x hx => H_all_jobs_from_taskset x (in_arrivals_implies_arrived arr_seq x _ _ hx)
  apply Nat.le_trans (workload_le_sum_over_tasks job_cost job_task ts tsk (fun jhp => (EDF job_arrival (job_relative_dealine task_deadline job_task)) jhp j) _ FROMTS)
  apply Prosa.Util.Sum.leq_sum_seq
  intro tsko INo _
  -- The relevant jobs of `tsko` arrive in `[t1, t1 + X)`.
  have ARRB : is_arrival_bound_for_taskset job_task arr_seq max_arrivals ts :=
    fun tsk0 IN0 => (H_family_of_proper_arrival_curves tsk0 IN0).1
  have hoff : offset = job_arrival j - t1 := rfl
  generalize hX : min (offset + ε + task_deadline tsk - task_deadline tsko) R = X
  have XLE : X ≤ R := by rw [← hX]; exact Nat.min_le_right _ _
  rw [job_arrived_between_cat arr_seq t1 (t1 + X) (t1 + R) (Nat.le_add_right _ _) (Nat.add_le_add_left XLE _),
    sumFiltered_append']
  have ZERO : sumFiltered (jobs_arrived_between arr_seq (t1 + X) (t1 + R))
      (fun x => (EDF job_arrival (job_relative_dealine task_deadline job_task)) x j && decide (job_task x = tsko)) job_cost = 0 := by
    apply sumFiltered_eq_zero
    intro x hx
    have JAx := in_arrivals_implies_arrived_between job_arrival arr_seq H_arrival_times_are_consistent x _ _ hx
    simp only [arrived_between, Bool.and_eq_true, decide_eq_true_eq] at JAx
    cases hP : ((EDF job_arrival (job_relative_dealine task_deadline job_task)) x j && decide (job_task x = tsko))
    · rfl
    · exfalso
      simp only [Bool.and_eq_true] at hP
      obtain ⟨HEP0, TSKx0⟩ := hP
      have TSKx : job_task x = tsko := of_decide_eq_true TSKx0
      have HEP : job_arrival x + task_deadline (job_task x) ≤ job_arrival j + task_deadline (job_task j) :=
        of_decide_eq_true HEP0
      rw [TSKx, TSK] at HEP
      rcases Nat.le_total (offset + ε + task_deadline tsk - task_deadline tsko) R with h | h
      · rw [Nat.min_eq_left h] at hX
        omega'
      · rw [Nat.min_eq_right h] at hX
        omega'
  rw [ZERO, Nat.add_zero]
  apply Nat.le_trans (Prosa.Util.Sum.leq_sum_seq_pred _ job_cost _ (fun x => decide (job_task x = tsko))
    (fun x _ h => by simp only [Bool.and_eq_true] at h; exact h.2))
  by_cases EX : ∃ x ∈ jobs_arrived_between arr_seq t1 (t1 + X), job_task x = tsko
  · obtain ⟨x, _, TSKx⟩ := EX
    have := task_workload_le_task_rbf task_cost job_cost job_task arr_seq ts tsko INo H_job_cost_le_task_cost
      max_arrivals ARRB x TSKx t1 X
    rw [TSKx] at this
    exact this
  · push_neg at EX
    rw [sumFiltered_eq_zero _ _ _ (fun x hx => by simpa using EX x hx)]
    exact Nat.zero_le _

theorem A_is_in_concrete_search_space
    {Task : Type u} [DecidableEq Task]
    (task_cost : Task → time)
    (task_deadline : Task → time)
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
    (priority_inversion_bound : time)
    (L : time)
    (H_L_positive : 0 < L)
    (j : Job)
    (H_j_arrives : arrives_in arr_seq j)
    (H_job_of_tsk : job_task j = tsk)
    (H_job_cost_positive : job_cost_positive job_cost j = true)
    (A : time)
    (H_A_is_in_abstract_search_space :
      is_in_search_space tsk L (fun tsk0 A Δ => task_request_bound_function task_cost max_arrivals tsk (A + ε) - task_cost tsk0 + (priority_inversion_bound + sumFiltered ts (fun tsk_o => !decide (tsk_o = tsk)) (fun tsk_o => task_request_bound_function task_cost max_arrivals tsk_o (min (A + ε + task_deadline tsk - task_deadline tsk_o) (Δ))))) A)
    :
    (decide (A < L) && (task_rbf_changes_at task_cost max_arrivals tsk (A) || bound_on_total_hep_workload_changes_at task_cost task_deadline ts max_arrivals tsk (A))) = true := by
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
    simp only [task_rbf_changes_at, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, Bool.not_eq_true',
      decide_eq_false_iff_not]
    refine ⟨H_L_positive, Or.inl ?_⟩
    rw [Nat.zero_add, R0]
    omega'
  · simp only [Bool.and_eq_true, decide_eq_true_eq] at POSLT
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨POSLT.2, ?_⟩
    by_contra NOT
    simp only [Bool.not_eq_true, Bool.or_eq_false_iff] at NOT
    obtain ⟨EQ1, EQ2⟩ := NOT
    simp only [task_rbf_changes_at, Bool.not_eq_false', decide_eq_true_eq] at EQ1
    simp only [bound_on_total_hep_workload_changes_at, List.any_eq_false, Bool.and_eq_true,
      Bool.not_eq_true', decide_eq_false_iff_not, not_and, not_not] at EQ2
    apply NEQ
    have AA : A - ε + ε = A := by omega'
    simp only [AA, EQ1]
    congr 2
    apply Prosa.Util.Sum.eq_sum_seq
    intro tsko INo NEQo
    simp only [Bool.not_eq_true', decide_eq_false_iff_not] at NEQo
    have E := EQ2 tsko INo (fun h => NEQo h.symm)
    apply decide_eq_true
    rcases Nat.lt_or_ge x (A + ε + task_deadline tsk - task_deadline tsko) with h | h
    · rw [Nat.min_eq_right (by omega' : x ≤ A + task_deadline tsk - task_deadline tsko), Nat.min_eq_right (Nat.le_of_lt h)]
    · rw [Nat.min_eq_left (by omega' : A + task_deadline tsk - task_deadline tsko ≤ x), Nat.min_eq_left h]
      exact E

theorem correct_search_space
    {Task : Type u} [DecidableEq Task]
    (task_cost : Task → time)
    (task_deadline : Task → time)
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
    (priority_inversion_bound : time)
    (L : time)
    (H_L_positive : 0 < L)
    (R : time)
    (H_R_is_maximum : ∀ A,
      (decide (A < L) && (task_rbf_changes_at task_cost max_arrivals tsk (A) || bound_on_total_hep_workload_changes_at task_cost task_deadline ts max_arrivals tsk (A))) = true →
      ∃ F, A + F = priority_inversion_bound + (task_request_bound_function task_cost max_arrivals tsk (A + ε) - (task_cost tsk - task_lock_in_service tsk)) +
          sumFiltered ts (fun tsk_o => !decide (tsk_o = tsk)) (fun tsk_o => task_request_bound_function task_cost max_arrivals tsk_o (min (A + ε + task_deadline tsk - task_deadline tsk_o) (A + F))) ∧
        F + (task_cost tsk - task_lock_in_service tsk) ≤ R)
    (j : Job)
    (H_j_arrives : arrives_in arr_seq j)
    (H_job_of_tsk : job_task j = tsk)
    (H_job_cost_positive : job_cost_positive job_cost j = true)
    (A : time)
    (H_A_is_in_abstract_search_space :
      is_in_search_space tsk L (fun tsk0 A Δ => task_request_bound_function task_cost max_arrivals tsk (A + ε) - task_cost tsk0 + (priority_inversion_bound + sumFiltered ts (fun tsk_o => !decide (tsk_o = tsk)) (fun tsk_o => task_request_bound_function task_cost max_arrivals tsk_o (min (A + ε + task_deadline tsk - task_deadline tsk_o) (Δ))))) A)
    :
    ∃ F, A + F = task_request_bound_function task_cost max_arrivals tsk (A + ε) - (task_cost tsk - task_lock_in_service tsk) + (priority_inversion_bound + sumFiltered ts (fun tsk_o => !decide (tsk_o = tsk)) (fun tsk_o => task_request_bound_function task_cost max_arrivals tsk_o (min (A + ε + task_deadline tsk - task_deadline tsk_o) (A + F)))) ∧
      F + (task_cost tsk - task_lock_in_service tsk) ≤ R := by
  obtain ⟨F, FIX, NEQ⟩ := H_R_is_maximum A (A_is_in_concrete_search_space task_cost task_deadline job_arrival job_cost job_task arr_seq H_arrival_times_are_consistent H_job_cost_le_task_cost ts max_arrivals H_family_of_proper_arrival_curves tsk H_tsk_in_ts priority_inversion_bound L H_L_positive j H_j_arrives H_job_of_tsk H_job_cost_positive A H_A_is_in_abstract_search_space)
  exact ⟨F, by omega', NEQ⟩

/-! ### Final theorem -/

theorem uniprocessor_response_time_bound_edf
    {Task : Type u} [DecidableEq Task]
    (task_cost : Task → time)
    (task_deadline : Task → time)
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
    (priority_inversion_bound : time)
    (H_priority_inversion_is_bounded :
      priority_inversion_is_bounded_by job_arrival job_cost job_task arr_seq sched (EDF job_arrival (job_relative_dealine task_deadline job_task)) tsk
        priority_inversion_bound)
    (L : time)
    (H_L_positive : 0 < L)
    (H_fixed_point : L = total_request_bound_function task_cost max_arrivals ts L)
    (R : time)
    (H_R_is_maximum : ∀ A,
      (decide (A < L) && (task_rbf_changes_at task_cost max_arrivals tsk (A) || bound_on_total_hep_workload_changes_at task_cost task_deadline ts max_arrivals tsk (A))) = true →
      ∃ F, A + F = priority_inversion_bound + (task_request_bound_function task_cost max_arrivals tsk (A + ε) - (task_cost tsk - task_lock_in_service tsk)) +
          sumFiltered ts (fun tsk_o => !decide (tsk_o = tsk)) (fun tsk_o => task_request_bound_function task_cost max_arrivals tsk_o (min (A + ε + task_deadline tsk - task_deadline tsk_o) (A + F))) ∧
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
    (interference sched (EDF job_arrival (job_relative_dealine task_deadline job_task))) (interfering_workload job_cost arr_seq sched (EDF job_arrival (job_relative_dealine task_deadline job_task))) (instantiated_i_and_w_are_coherent_with_schedule task_deadline job_arrival job_cost job_task arr_seq H_arrival_times_are_consistent H_arr_seq_is_a_set sched H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_work_conserving tsk) H_sequential_jobs
    (instantiated_interference_and_workload_consistent_with_sequential_jobs task_deadline job_arrival job_cost job_task arr_seq H_arrival_times_are_consistent H_arr_seq_is_a_set sched H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute tsk) L
    (instantiated_busy_intervals_are_bounded task_cost task_deadline job_arrival job_cost job_task arr_seq H_arrival_times_are_consistent H_arr_seq_is_a_set sched H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_work_conserving H_job_cost_le_task_cost ts H_all_jobs_from_taskset max_arrivals H_family_of_proper_arrival_curves tsk L H_L_positive H_fixed_point) (fun tsk0 A R => (priority_inversion_bound + sumFiltered ts (fun tsk_o => !decide (tsk_o = tsk)) (fun tsk_o => task_request_bound_function task_cost max_arrivals tsk_o (min (A + ε + task_deadline tsk - task_deadline tsk_o) (R)))))
    (instantiated_task_interference_is_bounded task_cost task_deadline job_arrival job_cost job_task arr_seq H_arrival_times_are_consistent H_arr_seq_is_a_set sched H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_sequential_jobs H_job_cost_le_task_cost ts H_all_jobs_from_taskset max_arrivals H_family_of_proper_arrival_curves tsk priority_inversion_bound H_priority_inversion_is_bounded) R
    (fun A INSP => correct_search_space task_cost task_deadline job_arrival job_cost job_task arr_seq H_arrival_times_are_consistent H_job_cost_le_task_cost ts max_arrivals H_family_of_proper_arrival_curves tsk H_tsk_in_ts task_lock_in_service priority_inversion_bound L H_L_positive R H_R_is_maximum js ARRs TSKs (decide_eq_true POS) A INSP)
    js ARRs TSKs

end Prosa.Classic.Model.Schedule.Uni.Limited.Edf.ResponseTimeBound.AbstractRTAforEDFwithArrivalCurves
