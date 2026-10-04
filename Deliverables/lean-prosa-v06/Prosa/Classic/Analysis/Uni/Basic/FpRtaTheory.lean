-- Authoritative source:
-- ProsaBuddy classic Prosa (prosabuddy commit f692cb7479780cf6009493f373a309e13165201c)
-- source: classic/analysis/uni/basic/fp_rta_theory.v
-- sha256: see Prosa-Shunqi/classic-prosa/comprehensive-classic/file_order.csv (rank 129)

import Prosa.Classic.Util.All
import Prosa.Classic.Model.Arrival.Basic.Job
import Prosa.Classic.Model.Arrival.Basic.Task
import Prosa.Classic.Model.Priority
import Prosa.Classic.Model.Arrival.Basic.TaskArrival
import Prosa.Classic.Model.Arrival.Basic.ArrivalBounds
import Prosa.Classic.Model.Schedule.Uni.ScheduleOfTask
import Prosa.Classic.Model.Schedule.Uni.Workload
import Prosa.Classic.Model.Schedule.Uni.Schedulability
import Prosa.Classic.Model.Schedule.Uni.ResponseTime
import Prosa.Classic.Model.Schedule.Uni.Service
import Prosa.Classic.Model.Schedule.Uni.Limited.BusyInterval
import Prosa.Classic.Model.Schedule.Uni.Basic.Platform
import Prosa.Classic.Analysis.Uni.Basic.WorkloadBoundFp

/-!
Response-time analysis for uniprocessor FP scheduling (Rocq module `ResponseTimeAnalysisFP` of
`classic/analysis/uni/basic/fp_rta_theory.v`).

Representation notes: the section-local `Let`s (`response_time_bounded_by`, `W`) are unfolded; `tsk \in ts` is
`tsk ∈ ts`; `work_conserving`/`respects_FP_policy` are the basic uniprocessor `Platform` ones. Binder lists follow
the Rocq contract (`H_tsk_in_ts` is not taken).
-/

set_option linter.unusedVariables false

namespace Prosa.Classic.Analysis.Uni.Basic.FpRtaTheory.ResponseTimeAnalysisFP

open Prosa.Classic.Model.Time.Time
open Prosa.Classic.Model.Arrival.Basic.ArrivalSequence.ArrivalSequence
open Prosa.Classic.Model.Arrival.Basic.Task.SporadicTaskset
open Prosa.Classic.Model.Arrival.Basic.Job.Job
open Prosa.Classic.Model.Priority.Priority
open Prosa.Classic.Model.Arrival.Basic.TaskArrival.TaskArrival (sporadic_task_model)
open Prosa.Classic.Model.Schedule.Uni.Schedule.UniprocessorSchedule
open Prosa.Classic.Model.Schedule.Uni.Basic.Platform.Platform
open Prosa.Classic.Model.Schedule.Uni.ResponseTime.ResponseTime
open Prosa.Classic.Analysis.Uni.Basic.WorkloadBoundFp.WorkloadBoundFP

universe u v

theorem uniprocessor_response_time_bound_fp {SporadicTask : Type u} [DecidableEq SporadicTask]
    (task_cost task_period task_deadline : SporadicTask → time) {Job : Type v} [DecidableEq Job]
    (job_arrival job_cost job_deadline : Job → time) (job_task : Job → SporadicTask) (arr_seq : arrival_sequence Job)
    (H_arrival_times_are_consistent : arrival_times_are_consistent job_arrival arr_seq)
    (H_no_duplicate_arrivals : arrival_sequence_is_a_set arr_seq)
    (H_sporadic_tasks : sporadic_task_model task_period job_arrival job_task arr_seq)
    (H_valid_job_parameters : ∀ j, arrives_in arr_seq j →
      valid_sporadic_job task_cost task_deadline job_cost job_deadline job_task j)
    (ts : List SporadicTask) (H_valid_task_parameters : valid_sporadic_taskset task_cost task_period task_deadline ts)
    (H_all_jobs_from_taskset : ∀ j, arrives_in arr_seq j → job_task j ∈ ts) (sched : schedule Job)
    (H_jobs_come_from_arrival_sequence : jobs_come_from_arrival_sequence sched arr_seq)
    (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute job_arrival sched)
    (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched)
    (higher_eq_priority : FP_policy SporadicTask) (H_priority_is_reflexive : FP_is_reflexive higher_eq_priority)
    (H_priority_is_transitive : FP_is_transitive higher_eq_priority)
    (H_work_conserving : work_conserving job_arrival job_cost arr_seq sched)
    (H_respects_fp_policy : respects_FP_policy job_arrival job_cost job_task arr_seq sched higher_eq_priority)
    (tsk : SporadicTask) (R : time) (H_R_positive : 0 < R)
    (H_response_time_is_fixed_point :
      R = total_workload_bound_fp task_cost task_period higher_eq_priority ts tsk R) :
    is_response_time_bound_of_task job_arrival job_cost job_task arr_seq sched tsk R := by
  intro j ARRj JOBtsk
  unfold is_response_time_bound_of_job
  rcases Nat.eq_zero_or_pos (job_cost j) with Z | POS
  · simp [completed_by, Z]
  have REFL : JLFP_is_reflexive (FP_to_JLFP job_task higher_eq_priority) :=
    fun x => H_priority_is_reflexive (job_task x)
  apply Prosa.Classic.Model.Schedule.Uni.Limited.BusyInterval.BusyIntervalJLFP.busy_interval_bounds_response_time
    job_arrival job_cost arr_seq H_arrival_times_are_consistent sched H_jobs_come_from_arrival_sequence
    (FP_to_JLFP job_task higher_eq_priority) j ARRj H_no_duplicate_arrivals H_jobs_must_arrive_to_execute
    H_completed_jobs_dont_execute H_work_conserving REFL 0 _ R H_R_positive
  · intro t
    have := fp_workload_bound_holds task_cost task_period task_deadline job_arrival job_cost job_deadline job_task ts
      H_valid_task_parameters arr_seq H_arrival_times_are_consistent H_no_duplicate_arrivals H_all_jobs_from_taskset
      H_valid_job_parameters H_sporadic_tasks tsk higher_eq_priority R H_response_time_is_fixed_point t
    unfold Prosa.Classic.Model.Schedule.Uni.Workload.Workload.workload_of_higher_or_equal_priority_tasks at this
    unfold Prosa.Classic.Model.Schedule.Uni.Workload.Workload.workload_of_higher_or_equal_priority_jobs FP_to_JLFP
    rw [JOBtsk, Nat.zero_add]
    exact this
  · -- there is no priority inversion: the scheduled job always has higher-or-equal priority
    intro t1 t2 BUSY
    unfold Prosa.Classic.Model.Schedule.Uni.Limited.BusyInterval.BusyIntervalJLFP.cumulative_priority_inversion
    rw [Nat.le_zero]
    apply Finset.sum_eq_zero
    intro t ht
    rw [Finset.mem_Ico] at ht
    unfold Prosa.Classic.Model.Schedule.Uni.Limited.BusyInterval.BusyIntervalJLFP.is_priority_inversion
    cases SCHED : sched t with
    | none => rfl
    | some s =>
      obtain ⟨jhp, ARRjhp, PEND, PRIO⟩ :=
        Prosa.Classic.Model.Schedule.Uni.Limited.BusyInterval.BusyIntervalJLFP.pending_hp_job_exists job_arrival
          job_cost arr_seq H_arrival_times_are_consistent sched (FP_to_JLFP job_task higher_eq_priority) j ARRj
          (decide_eq_true POS) H_jobs_must_arrive_to_execute REFL t1 t2 BUSY t
          (by simp only [Bool.and_eq_true, decide_eq_true_eq]; exact ht)
      have SPRIO : FP_to_JLFP job_task higher_eq_priority s j = true := by
        by_cases EQ : s = jhp
        · subst EQ; exact PRIO
        · have BACK : backlogged job_arrival job_cost sched jhp t = true := by
            have NS : scheduled_at sched jhp t = false := by
              simp only [scheduled_at, SCHED, decide_eq_false_iff_not]
              intro h; exact EQ (Option.some.inj h)
            simp [backlogged, PEND, NS]
          have HP := H_respects_fp_policy jhp s t ARRjhp BACK (by simp [scheduled_at, SCHED])
          exact H_priority_is_transitive (job_task jhp) (job_task s) (job_task j) HP PRIO
      simp only [SPRIO, Bool.not_true, Bool.toNat_false]

end Prosa.Classic.Analysis.Uni.Basic.FpRtaTheory.ResponseTimeAnalysisFP
