-- Translated from: ../rt-proofs/classic/analysis/uni/basic/fp_rta_theory.v
import Prosa.Classic.Util.All
import Prosa.Classic.Model.Arrival.Basic.Job
import Prosa.Classic.Model.Arrival.Basic.Task
import Prosa.Classic.Model.Arrival.Basic.Task_arrival
import Prosa.Classic.Model.Arrival.Basic.Arrival_bounds
import Prosa.Classic.Model.Priority
import Prosa.Classic.Model.Schedule.Uni.Schedule
import Prosa.Classic.Model.Schedule.Uni.Schedule_of_task
import Prosa.Classic.Model.Schedule.Uni.Workload
import Prosa.Classic.Model.Schedule.Uni.Schedulability
import Prosa.Classic.Model.Schedule.Uni.Response_time
import Prosa.Classic.Model.Schedule.Uni.Service
import Prosa.Classic.Model.Schedule.Uni.Limited.Busy_interval
import Prosa.Classic.Model.Schedule.Uni.Basic.Platform
import Prosa.Classic.Analysis.Uni.Basic.Workload_bound_fp
import Mathlib.Tactic

namespace Prosa.Classic.Analysis.Uni.Basic.Fp_rta_theory

open Prosa.Classic.Model.Time
open Prosa.Classic.Model.Arrival.Basic.Job
open Prosa.Classic.Model.Arrival.Basic.Arrival_sequence
open Prosa.Classic.Model.Arrival.Basic.Task.SporadicTask
open Prosa.Classic.Model.Arrival.Basic.Task.SporadicTaskset
open Prosa.Classic.Model.Arrival.Basic.Task_arrival
open Prosa.Classic.Model.Priority
open Prosa.Classic.Model.Schedule.Uni.Schedule
open Prosa.Classic.Model.Schedule.Uni.Schedule_of_task
open Prosa.Classic.Model.Schedule.Uni.Response_time.ResponseTime
open Prosa.Classic.Model.Schedule.Uni.Basic.Platform.Platform
open Prosa.Classic.Model.Schedule.Uni.Limited.Busy_interval.BusyIntervalJLFP
open Prosa.Classic.Analysis.Uni.Basic.Workload_bound_fp hiding sporadic_task_model
open Prosa.Classic.Analysis.Uni.Basic.Workload_bound_fp.WorkloadBoundFP

namespace ResponseTimeAnalysisFP

section ResponseTimeBound

  variable {SporadicTask : Type _} [DecidableEq SporadicTask]
  variable (task_cost : SporadicTask → Time)
  variable (task_period : SporadicTask → Time)
  variable (task_deadline : SporadicTask → Time)

  variable {Job : Type _} [DecidableEq Job]
  variable (job_arrival : Job → Time)
  variable (job_cost : Job → Time)
  variable (job_deadline : Job → Time)
  variable (job_task : Job → SporadicTask)

  variable (arr_seq : arrival_sequence Job)
  variable (H_arrival_times_are_consistent :
    arrival_times_are_consistent job_arrival arr_seq)
  variable (H_no_duplicate_arrivals : arrival_sequence_is_a_set arr_seq)

  variable (H_sporadic_tasks :
    sporadic_task_model task_period job_arrival job_task arr_seq)
  variable (H_valid_job_parameters :
    ∀ j,
      arrives_in arr_seq j →
      valid_sporadic_job task_cost task_deadline job_cost job_deadline job_task j)

  variable (ts : List SporadicTask)
  variable (H_valid_task_parameters :
    valid_sporadic_taskset task_cost task_period task_deadline ts)

  variable (H_all_jobs_from_taskset :
    ∀ j, arrives_in arr_seq j → job_task j ∈ ts)

  variable (sched : schedule Job)
  variable (H_jobs_come_from_arrival_sequence :
    jobs_come_from_arrival_sequence sched arr_seq)

  variable (H_jobs_must_arrive_to_execute :
    jobs_must_arrive_to_execute job_arrival sched)
  variable (H_completed_jobs_dont_execute :
    completed_jobs_dont_execute job_cost sched)

  variable (higher_eq_priority : FP_policy SporadicTask)
  variable (H_priority_is_reflexive : FP_is_reflexive higher_eq_priority)
  variable (H_priority_is_transitive : FP_is_transitive higher_eq_priority)

  variable (H_work_conserving :
    work_conserving job_arrival job_cost arr_seq sched)
  variable (H_respects_fp_policy :
    respects_FP_policy job_arrival job_cost job_task arr_seq sched higher_eq_priority)

  variable (tsk : SporadicTask)
  variable (H_tsk_in_ts : tsk ∈ ts)

  private abbrev response_time_bounded_by :=
    is_response_time_bound_of_task job_arrival job_cost job_task arr_seq sched

  variable (R : Time)
  variable (H_R_positive : R > 0)
  variable (H_response_time_is_fixed_point :
    R = total_workload_bound_fp task_cost task_period higher_eq_priority ts tsk R)

  include H_arrival_times_are_consistent H_no_duplicate_arrivals
          H_sporadic_tasks H_valid_job_parameters
          H_valid_task_parameters H_all_jobs_from_taskset
          H_jobs_come_from_arrival_sequence
          H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute
          H_priority_is_reflexive H_priority_is_transitive
          H_work_conserving H_respects_fp_policy
          H_tsk_in_ts H_R_positive H_response_time_is_fixed_point

  theorem uniprocessor_response_time_bound_fp :
      response_time_bounded_by job_arrival job_cost job_task arr_seq sched tsk R := by
    intro j ARRj JOBtsk
    -- Goal is: is_response_time_bound_of_job job_arrival job_cost sched j R
    -- i.e., completed_by job_cost sched j (job_arrival j + R)
    unfold is_response_time_bound_of_job
    -- Case split on whether job_cost j = 0
    by_cases hcost : job_cost j = 0
    · -- If cost is 0, then completed_by is trivial
      unfold completed_by
      simp [hcost]
    · -- If cost is positive
      push_neg at hcost
      have POS : job_cost j > 0 := Nat.pos_of_ne_zero hcost
      -- Use busy_interval_bounds_response_time with FP_to_JLFP priority and 0 inversion bound
      set prio := FP_to_JLFP job_task higher_eq_priority with prio_def
      apply Prosa.Classic.Model.Schedule.Uni.Limited.Busy_interval.BusyIntervalJLFP.busy_interval_bounds_response_time
        job_arrival job_cost job_task arr_seq
        H_arrival_times_are_consistent sched H_jobs_come_from_arrival_sequence
        prio tsk j ARRj JOBtsk POS
        H_no_duplicate_arrivals H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute
        H_work_conserving
        (fun x => H_priority_is_reflexive (job_task x))
        (fun y x z hxy hyz => H_priority_is_transitive _ _ _ hxy hyz)
        0
      · -- priority_inversion_of_job_is_bounded_by ... j 0
        intro t1 t2 BUSY
        show Prosa.Classic.Model.Schedule.Uni.Limited.Busy_interval.BusyIntervalJLFP.cumulative_priority_inversion sched prio j t1 t2 ≤ 0
        unfold Prosa.Classic.Model.Schedule.Uni.Limited.Busy_interval.BusyIntervalJLFP.cumulative_priority_inversion
        simp only [Nat.le_zero]
        apply Finset.sum_eq_zero
        intro t ht
        rw [Finset.mem_Ico] at ht
        unfold Prosa.Classic.Model.Schedule.Uni.Limited.Busy_interval.BusyIntervalJLFP.is_priority_inversion
        match hsched : sched t with
        | none => simp
        | some s =>
          simp only
          -- Need: if prio s j = true then 0 else 1 = 0
          -- Use pending_hp_job_exists to find a pending hp job jhp at time t
          have HP := Prosa.Classic.Model.Schedule.Uni.Limited.Busy_interval.BusyIntervalJLFP.pending_hp_job_exists
            job_arrival job_cost job_task arr_seq H_arrival_times_are_consistent sched
            H_jobs_come_from_arrival_sequence prio tsk j ARRj JOBtsk POS
            H_work_conserving H_completed_jobs_dont_execute H_jobs_must_arrive_to_execute
            (fun x => H_priority_is_reflexive (job_task x))
            (fun y x z hxy hyz => H_priority_is_transitive _ _ _ hxy hyz)
            t1 t2 BUSY t ⟨ht.1, ht.2⟩
          obtain ⟨jhp, hARRjhp, hPEND, hPRIO⟩ := HP
          -- Show prio s j = true
          suffices h : prio s j = true by rw [h]; simp
          -- Case split: s = jhp or s ≠ jhp
          by_cases heq : s = jhp
          · -- If s = jhp, then prio s j = prio jhp j = true
            rw [heq]; exact hPRIO
          · -- If s ≠ jhp, jhp is backlogged (pending but not scheduled at t since s ≠ jhp is scheduled)
            -- By H_respects_fp_policy, higher_eq_priority (job_task s) (job_task jhp)
            -- Then by transitivity, higher_eq_priority (job_task s) (job_task j)
            have hBL : backlogged job_arrival job_cost sched jhp t := by
              constructor
              · exact hPEND
              · -- jhp is not scheduled at t (s is, and s ≠ jhp)
                intro hsc
                simp only [scheduled_at] at hsc
                rw [hsched] at hsc
                simp at hsc
                exact heq hsc
            -- jhp arrives in arr_seq, so H_respects_fp_policy applies
            have hFP := H_respects_fp_policy jhp s t hARRjhp hBL (by simp [scheduled_at, hsched])
            -- hFP : higher_eq_priority (job_task s) (job_task jhp) = true
            -- hPRIO : prio jhp j = FP_to_JLFP job_task higher_eq_priority jhp j
            --       = higher_eq_priority (job_task jhp) (job_task j) = true
            show prio s j = true
            unfold prio FP_to_JLFP
            simp only [prio_def, FP_to_JLFP] at hPRIO
            exact H_priority_is_transitive _ _ _ hFP hPRIO
      · exact H_R_positive
      · -- Workload bound: ∀ t, 0 + hp_workload ... j t (t + R) ≤ R
        intro t
        simp only [Nat.zero_add]
        -- The goal is: hp_workload job_cost arr_seq prio j t (t + R) ≤ R
        -- hp_workload unfolds to workload_of_higher_or_equal_priority_jobs job_cost (jobs_arrived_between arr_seq t (t+R)) prio j
        -- With prio = FP_to_JLFP job_task higher_eq_priority and JOBtsk, this equals
        -- workload_of_higher_or_equal_priority_tasks job_cost job_task (jobs_arrived_between arr_seq t (t+R)) higher_eq_priority tsk
        -- which is exactly what fp_workload_bound_holds provides
        have hwb := fp_workload_bound_holds task_cost task_period task_deadline job_arrival job_cost
          job_deadline job_task ts H_valid_task_parameters arr_seq
          H_arrival_times_are_consistent H_no_duplicate_arrivals H_all_jobs_from_taskset
          H_valid_job_parameters H_sporadic_tasks tsk H_tsk_in_ts higher_eq_priority R
          H_response_time_is_fixed_point t
        -- These are definitionally equal by construction of prio and JOBtsk
        convert hwb using 2
        simp only [Prosa.Classic.Model.Schedule.Uni.Workload.workload_of_higher_or_equal_priority_tasks,
                    Prosa.Classic.Model.Schedule.Uni.Workload.workload_of_higher_or_equal_priority_jobs,
                    prio_def, FP_to_JLFP, JOBtsk]

end ResponseTimeBound

end ResponseTimeAnalysisFP

end Prosa.Classic.Analysis.Uni.Basic.Fp_rta_theory
