-- Case study: RTS_Papers/2007-RTSS-Theorem1/Theorem1.v
-- (Bertogna & Cirinei, RTSS 2007, "Response-Time Analysis for Globally Scheduled Symmetric
-- Multiprocessor Platforms", Theorem 1); sha256 and elaborated contract:
-- classic-prosa/casestudy-translation/contracts/
import CaseStudies.CommonFp
import Prosa.Util.Sum
import Prosa.Classic.Util.DivMod
import Prosa.Classic.Model.Arrival.Basic.Task
import Prosa.Classic.Model.Arrival.Basic.Job
import Prosa.Classic.Model.Arrival.Basic.TaskArrival
import Prosa.Classic.Model.Priority
import Prosa.Classic.Model.Schedule.Global.ResponseTime
import Prosa.Classic.Model.Schedule.Global.Basic.Schedule
import Prosa.Classic.Model.Schedule.Global.Basic.Platform
import Prosa.Classic.Model.Schedule.Global.Basic.Interference
import Prosa.Classic.Analysis.Global.Basic.WorkloadBound

/-!
Theorem 1 of RTSS 2007: under global fixed-priority scheduling, a solution `R ≤ d_tsk` of
`R = e_tsk + ⌊(Σ_(hp_tsk, R_hp) ∈ hp_bounds (⌈R / p_hp⌉ e_hp + e_hp)) / m⌋` is a response-time
bound of `tsk` (Rocq module `ResponseTimeAnalysisFP`, section `ResponseTimeBound`).  The interference
of a higher-priority task over an interval of length `delta` is bounded by `⌈delta / p⌉ e + e`
(`interference_bound_generic`), i.e. at most `⌈delta / p⌉` jobs released in the interval plus one
carry-in job.

Representation notes: `\sum_((tsk_other, R_other) <- R_prev) F (tsk_other, R_other)` is
`sumSeq R_prev (fun (tsk_other, R_other) => F (tsk_other, R_other))`; the section-local `Let`s are
unfolded (`response_time_bounded_by` is `is_response_time_bound_of_task … sched`, `is_hp_task` is
`higher_priority_task higher_eq_priority tsk`); Boolean tests in proposition position are `= true`.
Binder lists follow the Rocq contract (the two definitions abstract only the section variables they
use, the theorem every variable and hypothesis declared before it).

-/

set_option linter.unusedVariables false

namespace CaseStudies.RTSS2007.Theorem1.ResponseTimeAnalysisFP

open Prosa.Classic.Model.Time.Time
open Prosa.Classic.Model.Arrival.Basic.ArrivalSequence.ArrivalSequence
open Prosa.Classic.Model.Arrival.Basic.Task.SporadicTaskset
open Prosa.Classic.Model.Arrival.Basic.Task.SporadicTask
open Prosa.Classic.Model.Arrival.Basic.Job.Job
open Prosa.Classic.Model.Arrival.Basic.TaskArrival.TaskArrival
open Prosa.Classic.Model.Priority.Priority
open Prosa.Classic.Model.Schedule.Global.Basic.Schedule.Schedule
open Prosa.Classic.Model.Schedule.Global.Basic.Schedule.ScheduleOfSporadicTask
open Prosa.Classic.Model.Schedule.Global.ResponseTime.ResponseTime
open Prosa.Classic.Model.Schedule.Global.Basic.Platform.Platform
open Prosa.Classic.Model.Schedule.Global.Basic.Interference.Interference
open Prosa.Classic.Util.DivMod (div_floor div_ceil)
open Prosa.Util.Sum (sumSeq)

universe u v

def interference_bound_generic {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost task_period : sporadic_task → time) (delta : time)
    (tsk_R : sporadic_task × time) : Nat :=
  let tsk_other := tsk_R.1
  div_ceil delta (task_period tsk_other) * task_cost tsk_other + task_cost tsk_other

def total_interference_bound_fp {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost task_period : sporadic_task → time) (R_prev : List (sporadic_task × time))
    (delta : time) : Nat :=
  sumSeq R_prev (fun (tsk_other, R_other) =>
    interference_bound_generic task_cost task_period delta (tsk_other, R_other))

theorem Theorem1_07 {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost task_period task_deadline : sporadic_task → time)
    {Job : Type v} [DecidableEq Job] (job_arrival job_cost job_deadline : Job → time)
    (job_task : Job → sporadic_task) (arr_seq : arrival_sequence Job)
    (H_sporadic_tasks : sporadic_task_model task_period job_arrival job_task arr_seq)
    (H_valid_job_parameters : ∀ j : Job, arrives_in arr_seq j →
      valid_sporadic_job task_cost task_deadline job_cost job_deadline job_task j)
    (ts : taskset_of sporadic_task)
    (H_valid_task_parameters : valid_sporadic_taskset task_cost task_period task_deadline ts.val)
    (H_constrained_deadlines : ∀ tsk : sporadic_task, tsk ∈ ts → task_deadline tsk ≤ task_period tsk)
    (H_all_jobs_from_taskset : ∀ j : Job, arrives_in arr_seq j → job_task j ∈ ts)
    (num_cpus : Nat) (sched : schedule Job num_cpus)
    (H_jobs_come_from_arrival_sequence : jobs_come_from_arrival_sequence sched arr_seq)
    (H_sequential_jobs : sequential_jobs sched)
    (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute job_arrival sched)
    (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched)
    (H_at_least_one_cpu : 0 < num_cpus)
    (higher_eq_priority : FP_policy sporadic_task)
    (H_work_conserving : work_conserving job_arrival job_cost arr_seq sched)
    (H_respects_FP_policy : respects_FP_policy job_arrival job_cost job_task arr_seq sched higher_eq_priority)
    (tsk : sporadic_task) (task_in_ts : tsk ∈ ts)
    (hp_bounds : List (sporadic_task × time))
    (H_response_time_of_interfering_tasks_is_known : ∀ (hp_tsk : sporadic_task) (R : time),
      (hp_tsk, R) ∈ hp_bounds → is_response_time_bound_of_task job_arrival job_cost job_task arr_seq sched hp_tsk R)
    (H_hp_bounds_has_interfering_tasks : ∀ hp_tsk : sporadic_task, hp_tsk ∈ ts →
      higher_priority_task higher_eq_priority tsk hp_tsk = true → ∃ R : time, (hp_tsk, R) ∈ hp_bounds)
    (H_response_time_bounds_ge_cost : ∀ (hp_tsk : sporadic_task) (R : time),
      (hp_tsk, R) ∈ hp_bounds → task_cost hp_tsk ≤ R)
    (H_interfering_tasks_miss_no_deadlines : ∀ (hp_tsk : sporadic_task) (R : time),
      (hp_tsk, R) ∈ hp_bounds → R ≤ task_deadline hp_tsk)
    (R : time)
    (H_response_time_recurrence_holds : R = task_cost tsk +
      div_floor (total_interference_bound_fp task_cost task_period hp_bounds R) num_cpus)
    (H_response_time_no_larger_than_deadline : R ≤ task_deadline tsk) :
    is_response_time_bound_of_task job_arrival job_cost job_task arr_seq sched tsk R := by
  -- Proof as the classic `bertogna_cirinei_response_time_bound_fp`, by strong induction on the arrival time.
  -- If a job of `tsk` is not complete at `a_j + R`, the higher-priority interferences truncated at
  -- `R - e_tsk + 1` sum to at least `m (R - e_tsk + 1)` (`CommonFp.hp_interference_exceeds`).  Each task's
  -- interference is at most the classic workload bound `W`, which is at most `⌈R / p⌉ e + e` because
  -- `e ≤ R_hp ≤ d ≤ p`; summing contradicts the recurrence.
  -- The classic bound counts `⌊(delta + R_other - e) / p⌋ ≤ ⌈delta / p⌉` full jobs when `0 < e`, `R_other ≤ p`.
  have floor_le_ceil : ∀ (delta R_other e p : Nat), 0 < p → 0 < e → R_other ≤ p →
      (delta + R_other - e) / p ≤ div_ceil delta p := by
    intro delta R_other e p hp he hR
    unfold div_ceil
    split
    · rename_i hdvd
      obtain ⟨q, rfl⟩ := hdvd
      have hlt : p * q + R_other - e < (q + 1) * p := by
        rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm q p]; omega
      have := (Nat.div_lt_iff_lt_mul hp).mpr hlt
      rw [Nat.mul_div_cancel_left q hp]
      omega
    · have hq : delta < p * (delta / p) + p := by
        have := Nat.lt_mul_div_succ delta hp
        rwa [Nat.mul_add, Nat.mul_one] at this
      have hlt : delta + R_other - e < (delta / p + 2) * p := by
        rw [Nat.add_mul, Nat.mul_comm (delta / p) p]; omega
      have := (Nat.div_lt_iff_lt_mul hp).mpr hlt
      omega
  -- hence the classic workload bound `W` is at most `⌈delta / p⌉ e + e`
  have W_le : ∀ (k : sporadic_task) (R_k delta : time), 0 < task_period k → 0 < task_cost k →
      R_k ≤ task_period k →
      Prosa.Classic.Analysis.Global.Basic.WorkloadBound.WorkloadBound.W task_cost task_period k R_k delta ≤
        interference_bound_generic task_cost task_period delta (k, R_k) := by
    intro k R_k delta hp he hR
    have h1 := floor_le_ceil delta R_k (task_cost k) (task_period k) hp he hR
    have h2 := Nat.mul_le_mul_right (task_cost k) h1
    unfold Prosa.Classic.Analysis.Global.Basic.WorkloadBound.WorkloadBound.W
      Prosa.Classic.Analysis.Global.Basic.WorkloadBound.WorkloadBound.max_jobs div_floor interference_bound_generic
    simp only
    have h3 := min_le_left (task_cost k)
      (delta + R_k - task_cost k - (delta + R_k - task_cost k) / task_period k * task_period k)
    omega
  -- each higher-priority task's interference is within its bound
  have TASK : ∀ (j : Job) (k : sporadic_task) (R_k : time), (k, R_k) ∈ hp_bounds →
      task_interference job_arrival job_cost job_task sched j k (job_arrival j) (job_arrival j + R) ≤
        interference_bound_generic task_cost task_period R (k, R_k) := by
    intro j k R_k hk
    by_cases hx0 : task_interference job_arrival job_cost job_task sched j k (job_arrival j) (job_arrival j + R) = 0
    · rw [hx0]; exact Nat.zero_le _
    -- k runs some job, so k is a task of the task set and its parameters are valid
    have INts : k ∈ ts := by
      unfold task_interference at hx0
      obtain ⟨t, _, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hx0
      obtain ⟨cpu, _, hne'⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
      have hts : task_scheduled_on job_task sched k cpu t = true := by
        by_contra h
        simp only [Bool.not_eq_true] at h
        simp [h] at hne'
      unfold task_scheduled_on at hts
      cases hs : sched cpu t with
      | none => simp [hs] at hts
      | some j0 =>
          simp only [hs, decide_eq_true_eq] at hts
          have SCHED : scheduled sched j0 t = true := by
            simp only [scheduled, scheduled_on, List.any_eq_true, List.mem_finRange, true_and,
              decide_eq_true_eq]
            exact ⟨cpu, hs⟩
          rw [← hts]
          exact H_all_jobs_from_taskset j0 (H_jobs_come_from_arrival_sequence j0 t SCHED)
    have VALID := H_valid_task_parameters k INts
    simp only [is_valid_sporadic_task, task_cost_positive, task_period_positive, decide_eq_true_eq] at VALID
    have hRk : R_k ≤ task_period k :=
      le_trans (H_interfering_tasks_miss_no_deadlines k R_k hk) (H_constrained_deadlines k INts)
    exact le_trans
      (Prosa.Classic.Analysis.Global.Basic.BertognaFpTheory.ResponseTimeAnalysisFP.bertogna_fp_workload_bounds_interference
        task_cost task_period task_deadline job_arrival job_cost
        job_deadline job_task arr_seq H_sporadic_tasks H_valid_job_parameters ts H_valid_task_parameters
        H_constrained_deadlines H_all_jobs_from_taskset num_cpus sched H_jobs_come_from_arrival_sequence
        H_sequential_jobs H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute hp_bounds
        H_response_time_of_interfering_tasks_is_known H_response_time_bounds_ge_cost
        H_interfering_tasks_miss_no_deadlines R j k R_k hk)
      (W_le k R_k R VALID.2.1 VALID.1 hRk)
  have hRe : task_cost tsk ≤ R := by rw [H_response_time_recurrence_holds]; exact Nat.le_add_right _ _
  -- strong induction on the arrival time
  suffices MAIN : ∀ (n : Nat) (j : Job), job_arrival j = n → arrives_in arr_seq j →
      job_task j = tsk → completed job_cost sched j (job_arrival j + R) = true by
    intro j ARRj JOBtsk
    exact MAIN _ j rfl ARRj JOBtsk
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    intro j hn ARRj JOBtsk
    by_contra NOTCOMP
    have NOTCOMP' : (!completed job_cost sched j (job_arrival j + R)) = true := by
      simpa using NOTCOMP
    have BEFOREok : ∀ j0 : Job, arrives_in arr_seq j0 → job_task j0 = tsk →
        job_arrival j0 < job_arrival j → completed job_cost sched j0 (job_arrival j0 + R) = true :=
      fun j0 ARR0 JOB0 LT0 => IH (job_arrival j0) (hn ▸ LT0) j0 rfl ARR0 JOB0
    have EXC := CaseStudies.CommonFp.hp_interference_exceeds task_cost task_period task_deadline
      job_arrival job_cost job_deadline job_task arr_seq H_sporadic_tasks H_valid_job_parameters ts
      H_valid_task_parameters H_constrained_deadlines H_all_jobs_from_taskset num_cpus sched
      H_jobs_come_from_arrival_sequence H_sequential_jobs H_jobs_must_arrive_to_execute
      H_completed_jobs_dont_execute higher_eq_priority H_work_conserving H_respects_FP_policy tsk
      task_in_ts hp_bounds H_response_time_of_interfering_tasks_is_known
      H_hp_bounds_has_interfering_tasks H_interfering_tasks_miss_no_deadlines R hRe
      H_response_time_no_larger_than_deadline j ARRj JOBtsk NOTCOMP' BEFOREok
    have COVER := CaseStudies.CommonFp.sum_hp_le_sum_pairs ts
      (fun tsk_other => higher_priority_task higher_eq_priority tsk tsk_other) hp_bounds
      (fun tsk_k => min (task_interference job_arrival job_cost job_task sched j tsk_k
        (job_arrival j) (job_arrival j + R)) (R - task_cost tsk + 1))
      (fun k hk hhp => H_hp_bounds_has_interfering_tasks k hk hhp)
    have BOUND : sumSeq hp_bounds (fun p => min (task_interference job_arrival job_cost job_task sched j p.1
        (job_arrival j) (job_arrival j + R)) (R - task_cost tsk + 1)) ≤
        total_interference_bound_fp task_cost task_period hp_bounds R := by
      unfold total_interference_bound_fp
      apply CaseStudies.Common.sumSeq_le_sumSeq
      rintro ⟨k, R_k⟩ hk
      exact le_trans (min_le_left _ _) (TASK j k R_k hk)
    -- (⌊I / m⌋ + 1) m ≤ I is impossible
    have hsum := le_trans EXC (le_trans COVER BOUND)
    unfold div_floor at H_response_time_recurrence_holds
    generalize total_interference_bound_fp task_cost task_period hp_bounds R = I at hsum H_response_time_recurrence_holds
    have hR : R - task_cost tsk = I / num_cpus := by tomega
    rw [hR, Nat.add_mul, Nat.one_mul, Nat.mul_comm] at hsum
    have := Nat.div_add_mod I num_cpus
    have := Nat.mod_lt I H_at_least_one_cpu
    tomega

end CaseStudies.RTSS2007.Theorem1.ResponseTimeAnalysisFP
