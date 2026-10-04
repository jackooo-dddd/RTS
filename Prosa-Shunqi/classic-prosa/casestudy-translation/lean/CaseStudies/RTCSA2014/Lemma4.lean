-- Case study: RTS_Papers/2014-RTCSA-Lemma4/lemma4.v
-- sha256 dc145dedd61f07c46857a7903be09a2d2bd2db733efe69d64df3722b74c8c01c
-- (elaborated contract: classic-prosa/casestudy-translation/contracts/2014-RTCSA-Lemma4.txt)
import CaseStudies.Common
import Prosa.Util.Sum
import Prosa.Classic.Model.Arrival.Basic.ArrivalSequence
import Prosa.Classic.Util.DivMod
import Prosa.Classic.Model.Arrival.Basic.Task
import Prosa.Classic.Model.Arrival.Basic.Job
import Prosa.Classic.Model.Arrival.Basic.TaskArrival
import Prosa.Classic.Model.Priority
import Prosa.Classic.Model.Schedule.Global.Workload
import Prosa.Classic.Model.Schedule.Global.Schedulability
import Prosa.Classic.Model.Schedule.Global.ResponseTime
import Prosa.Classic.Model.Schedule.Global.Basic.Schedule
import Prosa.Classic.Model.Schedule.Global.Basic.Platform
import Prosa.Classic.Model.Schedule.Global.Basic.Interference
import Prosa.Classic.Model.Schedule.Global.Basic.ConstrainedDeadlines
import CaseStudies.WorkloadJobs
import Prosa.Classic.Util.Sum

/-!
Lemma 4 of the RTCSA 2014 paper ("Improving the Response Time Analysis of Global Fixed-Priority
Multiprocessor Scheduling") as stated by the case study `2014-RTCSA-Lemma4` (Rocq module `ResponseTimeAnalysisFP`):
the workload of a higher-priority task with a carry-in job in `[critical_instant, critical_instant + t)` is at most
the improved carry-in bound `W_CI R_k t`.  The carry-in workload bound (`Lemma1_09`), the no-carry-in workload bound
(`Lemma2`) and the existence of a tight release chain (`Lemma1_14`) are hypotheses; the section-local chain
predicates are unfolded as in the Rocq contract.  The conclusion quantifies its own `tsk_other` and `R_other`
(shadowing the section variables of the same names, which only the chain hypotheses mention).

Representation notes (classic-prosa representation addendum): `minn` is `min`; `x %% p` is `x % p`;
`\sum_(x <- s) F x` is `sumSeq s F` and `\sum_(x <- s | P x) F x` is `sumFiltered s P F` (pair patterns are
`fun (a, b) => …`); a Boolean summed as a number is `Bool.toNat`; `sort r s` is `s.mergeSort r` with the
relation decided; `take n s` is `s.take n`; `n.-1` is `n - 1`; `[seq x <- s | P x]` is `s.filter P`;
`x \notin s` is `!decide (x ∈ s)`; `count P ts` is `ts.val.countP P`; Boolean tests in proposition position
are `= true` (`~~ b` is `(!b) = true`), and chains `a <= t < b` are `(decide (a ≤ t) && decide (t < b)) = true`;
section-local `Let`s are unfolded.  Binder lists follow the Rocq contracts in
`classic-prosa/casestudy-translation/contracts/` (Rocq abstracts exactly the section variables a declaration
uses; a theorem abstracts every variable and hypothesis declared before it, so some binders are unused).
-/

set_option linter.unusedVariables false

namespace CaseStudies.RTCSA2014.Lemma4.ResponseTimeAnalysisFP

open Prosa.Classic.Model.Time.Time
open Prosa.Classic.Model.Arrival.Basic.ArrivalSequence.ArrivalSequence
open Prosa.Classic.Model.Arrival.Basic.Task.SporadicTaskset
open Prosa.Classic.Model.Arrival.Basic.Job.Job
open Prosa.Classic.Model.Arrival.Basic.TaskArrival.TaskArrival
open Prosa.Classic.Model.Priority.Priority
open Prosa.Classic.Model.Schedule.Global.Basic.Schedule.Schedule
open Prosa.Classic.Model.Schedule.Global.Basic.Schedule.ScheduleOfSporadicTask
open Prosa.Classic.Model.Schedule.Global.Workload.Workload
open Prosa.Classic.Model.Schedule.Global.Schedulability.Schedulability
open Prosa.Classic.Model.Schedule.Global.ResponseTime.ResponseTime
open Prosa.Classic.Model.Schedule.Global.Basic.Platform.Platform
open Prosa.Classic.Model.Schedule.Global.Basic.Interference.Interference
open Prosa.Classic.Util.DivMod (div_floor div_ceil)
open Prosa.Util.Sum (sumSeq sumFiltered)

universe u v

def x_p {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost task_period : sporadic_task → time) (tsk : sporadic_task) (R_tsk : time) : Nat :=
  let e_i := task_cost tsk
  let p_i := task_period tsk
  e_i - 1 + div_ceil (R_tsk - e_i) (p_i - e_i) * p_i - R_tsk

def x_delta {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost task_period : sporadic_task → time) (tsk : sporadic_task) (R_tsk delta : time) : Nat :=
  let e_i := task_cost tsk
  let p_i := task_period tsk
  min delta (div_ceil (R_tsk - e_i) (p_i - e_i) * e_i - 1)

def W_NC {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost task_period : sporadic_task → time) (tsk : sporadic_task) (delta : time) : Nat :=
  let e_i := task_cost tsk
  let p_i := task_period tsk
  div_floor delta p_i * e_i + min e_i (delta % p_i)

def W_CI {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost task_period : sporadic_task → time) (tsk : sporadic_task) (R_tsk delta : time) : Nat :=
  let e_i := task_cost tsk
  let p_i := task_period tsk
  div_floor (delta - x_p task_cost task_period tsk R_tsk) p_i * e_i +
    min e_i ((delta - x_p task_cost task_period tsk R_tsk) % p_i) +
    x_delta task_cost task_period tsk R_tsk delta

def interference_bound_generic {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost task_period : sporadic_task → time) (tsk : sporadic_task) (delta : time)
    (tsk_R : sporadic_task × time) : Nat :=
  let tsk_other := tsk_R.1
  let R_other := tsk_R.2
  min (W_CI task_cost task_period tsk_other R_other delta) (delta - task_cost tsk + 1)

def interference_bound_nc {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost task_period : sporadic_task → time) (tsk : sporadic_task) (delta : time)
    (tsk_R : sporadic_task × time) : Nat :=
  let tsk_other := tsk_R.1
  min (W_NC task_cost task_period tsk_other delta) (delta - task_cost tsk + 1)

def interference_bound_delta {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost task_period : sporadic_task → time) (tsk : sporadic_task) (delta : time)
    (tsk_R : sporadic_task × time) : Nat :=
  interference_bound_generic task_cost task_period tsk delta tsk_R -
    interference_bound_nc task_cost task_period tsk delta tsk_R

def sum_largest (n : Nat) (xs : List Nat) : Nat :=
  sumSeq ((xs.mergeSort (fun x y => decide (y ≤ x))).take n) (fun x => x)

def total_interference_bound_fp {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost task_period : sporadic_task → time) (tsk : sporadic_task)
    (R_prev : List (sporadic_task × time)) (delta : time) : Nat :=
  sumSeq R_prev (fun (tsk_other, R_other) =>
    interference_bound_generic task_cost task_period tsk delta (tsk_other, R_other))

def CI_taskset {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost task_period : sporadic_task → time) (tsk : sporadic_task)
    (R_prev : List (sporadic_task × time)) (delta : time) (num_cpus : Nat) :
    List (sporadic_task × time) :=
  (R_prev.mergeSort (fun p q =>
    decide (interference_bound_delta task_cost task_period tsk delta q ≤
      interference_bound_delta task_cost task_period tsk delta p))).take (num_cpus - 1)

def NC_taskset {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost task_period : sporadic_task → time) (tsk : sporadic_task)
    (R_prev : List (sporadic_task × time)) (delta : time) (num_cpus : Nat) :
    List (sporadic_task × time) :=
  R_prev.filter (fun p => !decide (p ∈ CI_taskset task_cost task_period tsk R_prev delta num_cpus))

def total_interference_bound_ci {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost task_period : sporadic_task → time) (tsk : sporadic_task)
    (R_prev : List (sporadic_task × time)) (delta : time) (num_cpus : Nat) : Nat :=
  sumSeq (CI_taskset task_cost task_period tsk R_prev delta num_cpus)
    (fun p => interference_bound_generic task_cost task_period tsk delta p)

def total_interference_bound_nc {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost task_period : sporadic_task → time) (tsk : sporadic_task)
    (R_prev : List (sporadic_task × time)) (delta : time) (num_cpus : Nat) : Nat :=
  sumSeq (NC_taskset task_cost task_period tsk R_prev delta num_cpus)
    (fun p => interference_bound_nc task_cost task_period tsk delta p)

def total_interference_bound_gn {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost task_period : sporadic_task → time) (tsk : sporadic_task)
    (R_prev : List (sporadic_task × time)) (delta : time) (num_cpus : Nat) : Nat :=
  sumSeq (NC_taskset task_cost task_period tsk R_prev delta num_cpus)
      (fun p => interference_bound_nc task_cost task_period tsk delta p) +
    sumSeq (CI_taskset task_cost task_period tsk R_prev delta num_cpus)
      (fun p => interference_bound_generic task_cost task_period tsk delta p)

def hp_busy {sporadic_task : Type u} {Job : Type v} [DecidableEq sporadic_task] [DecidableEq Job]
    (job_task : Job → sporadic_task) (ts : taskset_of sporadic_task) (num_cpus : Nat)
    (sched : schedule Job num_cpus) (higher_eq_priority : FP_policy sporadic_task)
    (tsk : sporadic_task) (t : time) : Prop :=
  ts.val.countP (fun tsk_other =>
    task_is_scheduled job_task sched tsk_other t &&
      higher_priority_task higher_eq_priority tsk tsk_other) = num_cpus

def is_carry_in_job {sporadic_task : Type u} {Job : Type v} [DecidableEq sporadic_task] [DecidableEq Job]
    (job_arrival : Job → time) (job_cost : Job → time) (job_task : Job → sporadic_task) (arr_seq : arrival_sequence Job) (num_cpus : Nat)
    (sched : schedule Job num_cpus) (higher_eq_priority : FP_policy sporadic_task) (tsk : sporadic_task) (j0 : Job) (t : time) : Prop :=
  arrives_in arr_seq j0 ∧
    higher_priority_task higher_eq_priority tsk (job_task j0) = true ∧
    job_arrival j0 < t ∧
    (!completed job_cost sched j0 t) = true

def carry_in_jobs_of {sporadic_task : Type u} {Job : Type v} [DecidableEq sporadic_task] [DecidableEq Job]
    (job_cost : Job → time) (job_task : Job → sporadic_task) (arr_seq : arrival_sequence Job) (num_cpus : Nat)
    (sched : schedule Job num_cpus) (higher_eq_priority : FP_policy sporadic_task) (tsk : sporadic_task) (tsk_other : sporadic_task) (t : time) : List Job :=
  (jobs_arrived_before arr_seq t).filter (fun j0 =>
    (decide (job_task j0 = tsk_other) && higher_priority_task higher_eq_priority tsk (job_task j0)) &&
      !completed job_cost sched j0 t)

def number_of_carry_in_jobs {sporadic_task : Type u} {Job : Type v} [DecidableEq sporadic_task] [DecidableEq Job]
    (job_cost : Job → time) (job_task : Job → sporadic_task) (arr_seq : arrival_sequence Job) (num_cpus : Nat)
    (sched : schedule Job num_cpus) (higher_eq_priority : FP_policy sporadic_task) (tsk : sporadic_task) (tsk_other : sporadic_task) (t : time) : Nat :=
  (carry_in_jobs_of job_cost job_task arr_seq num_cpus sched higher_eq_priority tsk tsk_other t).length

def task_has_carry_in_job {sporadic_task : Type u} {Job : Type v} [DecidableEq sporadic_task] [DecidableEq Job]
    (job_arrival : Job → time) (job_cost : Job → time) (job_task : Job → sporadic_task) (arr_seq : arrival_sequence Job) (num_cpus : Nat)
    (sched : schedule Job num_cpus) (higher_eq_priority : FP_policy sporadic_task) (tsk : sporadic_task) (tsk_other : sporadic_task) (t : time) : Prop :=
  ∃ j0 : Job, job_task j0 = tsk_other ∧
    is_carry_in_job job_arrival job_cost job_task arr_seq num_cpus sched higher_eq_priority tsk j0 t

def no_carry_in_workload_of_task {sporadic_task : Type u} {Job : Type v} [DecidableEq sporadic_task] [DecidableEq Job]
    (job_arrival job_cost : Job → time) (job_task : Job → sporadic_task) (arr_seq : arrival_sequence Job)
    (num_cpus : Nat) (sched : schedule Job num_cpus) (hp_tsk : sporadic_task) (t : time) : Prop :=
  ∀ j0 : Job, arrives_in arr_seq j0 → job_task j0 = hp_tsk → job_arrival j0 < t →
    completed job_cost sched j0 t = true

def carry_in_job_workload {Job : Type v} [DecidableEq Job] (job_cost : Job → time) (num_cpus : Nat)
    (sched : schedule Job num_cpus) (j0 : Job) (t : time) : Nat :=
  job_cost j0 - service sched j0 t

def carry_in_workload {sporadic_task : Type u} {Job : Type v} [DecidableEq sporadic_task] [DecidableEq Job]
    (job_cost : Job → time) (job_task : Job → sporadic_task) (arr_seq : arrival_sequence Job) (num_cpus : Nat)
    (sched : schedule Job num_cpus) (higher_eq_priority : FP_policy sporadic_task) (tsk : sporadic_task) (tsk_other : sporadic_task) (t : time) : Nat :=
  sumSeq (carry_in_jobs_of job_cost job_task arr_seq num_cpus sched higher_eq_priority tsk tsk_other t)
    (fun j0 => carry_in_job_workload job_cost num_cpus sched j0 t)

theorem Lemma4_14 {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost task_period task_deadline : sporadic_task → time)
    {Job : Type v} [DecidableEq Job] (job_arrival job_cost job_deadline : Job → time)
    (job_task : Job → sporadic_task) (arr_seq : arrival_sequence Job)
    (H_sporadic_tasks : sporadic_task_model task_period job_arrival job_task arr_seq)
    (H_valid_job_parameters : ∀ j : Job, arrives_in arr_seq j →
      valid_sporadic_job task_cost task_deadline job_cost job_deadline job_task j)
    (ts : taskset_of sporadic_task)
    (H_valid_task_parameters : ∀ tsk : sporadic_task, tsk ∈ ts →
      0 < task_cost tsk ∧ 0 < task_period tsk ∧ 0 < task_deadline tsk ∧
        task_cost tsk ≤ task_deadline tsk ∧ task_cost tsk < task_period tsk)
    (H_all_jobs_from_taskset : ∀ j : Job, arrives_in arr_seq j → job_task j ∈ ts)
    (num_cpus : Nat) (sched : schedule Job num_cpus)
    (H_jobs_come_from_arrival_sequence : jobs_come_from_arrival_sequence sched arr_seq)
    (H_arrival_times_are_consistent : arrival_times_are_consistent job_arrival arr_seq)
    (H_no_duplicate_arrivals : arrival_sequence_is_a_set arr_seq)
    (H_sequential_jobs : sequential_jobs sched)
    (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute job_arrival sched)
    (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched)
    (H_at_least_one_cpu : 0 < num_cpus)
    (previous_job_must_finished : ∀ (j1 j2 : Job) (t : time), scheduled sched j1 t = true →
      job_task j1 = job_task j2 → job_arrival j2 < job_arrival j1 → completed job_cost sched j2 t = true)
    (higher_eq_priority : FP_policy sporadic_task)
    (H_work_conserving : work_conserving job_arrival job_cost arr_seq sched)
    (H_respects_FP_policy : respects_FP_policy job_arrival job_cost job_task arr_seq sched higher_eq_priority)
    (H_priority_transitive : FP_is_transitive higher_eq_priority)
    (H_priority_antisymmetric : FP_is_antisymmetric_over_task_set higher_eq_priority ts.val)
    (H_sequential_tasks : ∀ (j1 j2 : Job) (t : time) (cpu : processor num_cpus),
      arrives_in arr_seq j1 → arrives_in arr_seq j2 → job_task j1 = job_task j2 →
      job_arrival j1 < job_arrival j2 → scheduled_on sched j2 cpu t = true →
      completed job_cost sched j1 t = true)
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
    (H_hp_bounds_uniq : hp_bounds.Nodup)
    (critical_instant : time)
    (critical_instant_left_boundary : critical_instant = 0 ∨ ¬ hp_busy job_task ts num_cpus sched higher_eq_priority tsk (critical_instant - 1))
    (critical_instant_is_busy : ts.val.countP (fun tsk_other =>
      task_is_scheduled job_task sched tsk_other critical_instant &&
        higher_priority_task higher_eq_priority tsk tsk_other) = num_cpus)
    (Lemma1_09 : ∀ (tsk_other : sporadic_task) (t : time), task_has_carry_in_job job_arrival job_cost job_task arr_seq num_cpus sched higher_eq_priority tsk tsk_other t →
      carry_in_workload job_cost job_task arr_seq num_cpus sched higher_eq_priority tsk tsk_other t ≤
        number_of_carry_in_jobs job_cost job_task arr_seq num_cpus sched higher_eq_priority tsk tsk_other t * task_cost tsk_other - 1)
    (Lemma2 : ∀ (tsk_other : sporadic_task) (R_other t : time) (delta : Nat),
      no_carry_in_workload_of_task job_arrival job_cost job_task arr_seq num_cpus sched tsk_other t →
      (tsk_other, R_other) ∈ hp_bounds →
      workload job_task sched tsk_other t (t + delta) ≤ W_NC task_cost task_period tsk_other delta)
    (Lemma1_14 : ∀ (tsk_other : sporadic_task) (R_other : time), task_has_carry_in_job job_arrival job_cost job_task arr_seq num_cpus sched higher_eq_priority tsk tsk_other critical_instant →
      (tsk_other, R_other) ∈ hp_bounds → task_cost tsk_other < R_other →
      ∃ (xi : time) (j_xi : Job),
        ((arrives_in arr_seq j_xi ∧ job_task j_xi = tsk_other ∧ critical_instant ≤ job_arrival j_xi) ∧
          (0 < xi ∧
            ((jobs_arrived_before arr_seq (job_arrival j_xi)).filter (fun j0 =>
              decide (job_task j0 = tsk_other) && decide (critical_instant ≤ job_arrival j0))).length = xi - 1) ∧
          job_arrival j_xi = critical_instant +
            (task_cost tsk_other - 1 + (number_of_carry_in_jobs job_cost job_task arr_seq num_cpus sched higher_eq_priority tsk tsk_other critical_instant + (xi - 1)) * task_period tsk_other - R_other) ∧
          arrives_in arr_seq j_xi ∧ job_task j_xi = tsk_other ∧
          (∀ j1 : Job, arrives_in arr_seq j1 → job_task j1 = tsk_other → job_arrival j1 < job_arrival j_xi →
            completed job_cost sched j1 (job_arrival j_xi) = true)) ∧
        (let k := number_of_carry_in_jobs job_cost job_task arr_seq num_cpus sched higher_eq_priority tsk tsk_other critical_instant + (xi - 1);
          0 < k ∧ R_other + (k * task_cost tsk_other - 1) ≤ task_cost tsk_other - 1 + k * task_period tsk_other ∧
            ∀ k0 : Nat, 0 < k0 → R_other + (k0 * task_cost tsk_other - 1) ≤ task_cost tsk_other - 1 + k0 * task_period tsk_other →
              k ≤ k0))
    (tsk_other : sporadic_task) (R_other delta xi : time) (j_xi : Job)
    (H_tight_chain_boundary_job : ((arrives_in arr_seq j_xi ∧ job_task j_xi = tsk_other ∧ critical_instant ≤ job_arrival j_xi) ∧
          (0 < xi ∧
            ((jobs_arrived_before arr_seq (job_arrival j_xi)).filter (fun j0 =>
              decide (job_task j0 = tsk_other) && decide (critical_instant ≤ job_arrival j0))).length = xi - 1) ∧
          job_arrival j_xi = critical_instant +
            (task_cost tsk_other - 1 + (number_of_carry_in_jobs job_cost job_task arr_seq num_cpus sched higher_eq_priority tsk tsk_other critical_instant + (xi - 1)) * task_period tsk_other - R_other) ∧
          arrives_in arr_seq j_xi ∧ job_task j_xi = tsk_other ∧
          (∀ j1 : Job, arrives_in arr_seq j1 → job_task j1 = tsk_other → job_arrival j1 < job_arrival j_xi →
            completed job_cost sched j1 (job_arrival j_xi) = true)))
    (H_tight_chain_prefix_job_count_is_minimal : (let k := number_of_carry_in_jobs job_cost job_task arr_seq num_cpus sched higher_eq_priority tsk tsk_other critical_instant + (xi - 1);
          0 < k ∧ R_other + (k * task_cost tsk_other - 1) ≤ task_cost tsk_other - 1 + k * task_period tsk_other ∧
            ∀ k0 : Nat, 0 < k0 → R_other + (k0 * task_cost tsk_other - 1) ≤ task_cost tsk_other - 1 + k0 * task_period tsk_other →
              k ≤ k0)) :
    ∀ (tsk_other0 : sporadic_task) (R_other0 : time) (t : Nat), task_has_carry_in_job job_arrival job_cost job_task arr_seq num_cpus sched higher_eq_priority tsk tsk_other0 critical_instant →
      (tsk_other0, R_other0) ∈ hp_bounds →
      workload job_task sched tsk_other0 critical_instant (critical_instant + t) ≤
        W_CI task_cost task_period tsk_other0 R_other0 t := by
  intro k R t hci hmem
  have hci' := hci
  obtain ⟨j0, htask0, harr0, hhp0, hlt0, hnc0⟩ := hci
  have hin : k ∈ ts := htask0 ▸ H_all_jobs_from_taskset j0 harr0
  obtain ⟨he0, hp0, hd0, hed, hep⟩ := H_valid_task_parameters k hin
  have heR := H_response_time_bounds_ge_cost k R hmem
  have hvalid : valid_sporadic_taskset task_cost task_period task_deadline ts.val := by
    intro k' hk'
    obtain ⟨h1, h2, h3, h4, h5⟩ := H_valid_task_parameters k' hk'
    simp only [is_valid_sporadic_task, task_cost_positive, task_period_positive,
      task_deadline_positive, task_cost_le_deadline, task_cost_le_period, decide_eq_true_eq]
    exact ⟨h1, h2, h3, h4, Nat.le_of_lt h5⟩
  -- at most one processor runs a job of `k` at a time
  have hsched : ∀ cpu s j', sched cpu s = some j' → scheduled sched j' s = true := by
    intro cpu s j' h
    simp only [scheduled, scheduled_on, List.any_eq_true, List.mem_finRange, true_and,
      decide_eq_true_eq]
    exact ⟨cpu, h⟩
  have honce : ∀ s c1 c2 j1 j2, sched c1 s = some j1 → sched c2 s = some j2 →
      job_task j1 = k → job_task j2 = k → c1 = c2 := by
    intro s c1 c2 j1 j2 h1 h2 t1 t2
    have := CaseStudies.Common.same_task_scheduled_eq task_cost task_period task_deadline job_arrival
      job_cost job_task arr_seq ts sched H_sporadic_tasks hvalid H_all_jobs_from_taskset
      H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute
      H_sequential_tasks s j1 j2 (hsched c1 s j1 h1) (hsched c2 s j2 h2) (t1.trans t2.symm)
    subst this
    exact H_sequential_jobs j1 s c1 c2 h1 h2
  have hlen := CaseStudies.WorkloadJobs.workload_le_length job_task sched k honce
  have hmemA : ∀ x T', arrives_in arr_seq x → job_arrival x < T' → x ∈ jobs_arrived_before arr_seq T' := by
    intro x T' harr hT'
    obtain ⟨t', ht'⟩ := harr
    have := H_arrival_times_are_consistent x t' (by simp [arrives_at, ht'])
    unfold jobs_arrived_before jobs_arrived_between
    exact Prosa.Util.Bigcat.mem_bigcat_nat (hRange := ⟨Nat.zero_le t', by tomega⟩) (hMem := ht')
  have harrA : ∀ x T', x ∈ jobs_arrived_before arr_seq T' → arrives_in arr_seq x := by
    intro x T' hx
    unfold jobs_arrived_before jobs_arrived_between at hx
    obtain ⟨t', ht', _, _⟩ := Prosa.Util.Bigcat.mem_bigcat_nat_exists (hMem := hx)
    exact ⟨t', ht'⟩
  have hcostk : ∀ x, arrives_in arr_seq x → job_task x = k → job_cost x ≤ task_cost k := by
    intro x hx htx
    have := (H_valid_job_parameters x hx).2.1
    simp only [job_cost_le_task_cost, decide_eq_true_eq, htx] at this
    exact this
  rcases Nat.lt_or_ge (task_cost k) R with hlt | hge
  · -- the tight chain of Lemma 1 (2014) ends with a job arriving at `critical_instant + x_p`
    obtain ⟨xi, jxi, ⟨⟨hxa, hxt, hxge⟩, ⟨hxi0, hcount⟩, hxarr, _, _, hprevxi⟩, hk⟩ :=
      Lemma1_14 k R hci' hmem hlt
    simp only at hk
    obtain ⟨hk0, hksat, hkmin⟩ := hk
    have hKspec := CaseStudies.WorkloadArith.div_ceil_spec (R - task_cost k)
      (task_period k - task_cost k) (by tomega)
    generalize hKdef : Prosa.Classic.Util.DivMod.div_ceil (R - task_cost k)
      (task_period k - task_cost k) = K at hKspec
    have hKpos : 0 < K := by
      by_contra h0
      have := hKspec.1
      rw [Nat.eq_zero_of_not_pos h0, Nat.zero_mul] at this
      omega
    generalize hn : number_of_carry_in_jobs job_cost job_task arr_seq num_cpus sched
      higher_eq_priority tsk k critical_instant = n at hk0 hksat hkmin hxarr
    have hKeq : n + (xi - 1) = K := by
      have hpe := Nat.le_of_lt hep
      apply le_antisymm
      · apply hkmin _ hKpos
        have h1 := hKspec.1
        have h2 : K * (task_period k - task_cost k) = K * task_period k - K * task_cost k :=
          Nat.mul_sub _ _ _
        have h3 := Nat.mul_le_mul_left K hpe
        have h4 : 1 ≤ K * task_cost k := Nat.mul_pos hKpos he0
        generalize K * task_period k = A at h2 h3 ⊢
        generalize K * task_cost k = B at h2 h3 h4 ⊢
        generalize K * (task_period k - task_cost k) = C at h1 h2
        tomega
      · apply hKspec.2
        have h4 : 1 ≤ (n + (xi - 1)) * task_cost k := Nat.mul_pos hk0 he0
        rw [Nat.mul_sub]
        have h3 := Nat.mul_le_mul_left (n + (xi - 1)) hpe
        generalize (n + (xi - 1)) * task_period k = A at hksat h3 ⊢
        generalize (n + (xi - 1)) * task_cost k = B at hksat h3 h4 ⊢
        tomega
    -- the carry-in jobs: `j0` is one of them
    have hn1 : 1 ≤ n := by
      rw [← hn]
      apply List.length_pos_of_mem (a := j0)
      simp only [carry_in_jobs_of, List.mem_filter, Bool.and_eq_true, decide_eq_true_eq]
      refine ⟨hmemA j0 _ harr0 hlt0, ⟨htask0, htask0 ▸ hhp0⟩, by simpa using hnc0⟩
    -- workload before the end of the chain
    have hbefore : workload job_task sched k critical_instant (job_arrival jxi) ≤
        K * task_cost k - 1 := by
      obtain ⟨L, hnd, hL, hw⟩ := CaseStudies.WorkloadJobs.workload_as_jobs job_task sched k
        critical_instant (job_arrival jxi)
      rw [hw]
      let g := fun x => job_cost x - service sched x critical_instant
      have h1 : sumSeq L (fun x => service_during sched x critical_instant (job_arrival jxi)) ≤
          sumSeq L g :=
        CaseStudies.Common.sumSeq_le_sumSeq L _ _ (fun x _ =>
          CaseStudies.WorkloadJobs.service_during_le_remaining job_cost sched
            H_completed_jobs_dont_execute x _ _ hxge)
      have hsub : ∀ x ∈ L, x ∈ carry_in_jobs_of job_cost job_task arr_seq num_cpus sched
          higher_eq_priority tsk k critical_instant ++
          (jobs_arrived_before arr_seq (job_arrival jxi)).filter (fun j0 =>
            decide (job_task j0 = k) && decide (critical_instant ≤ job_arrival j0)) := by
        intro x hx
        obtain ⟨htk, s, hs1, hs2, hsch⟩ := hL x hx
        have harr := H_jobs_come_from_arrival_sequence x s hsch
        have hax : job_arrival x ≤ s := by
          have := H_jobs_must_arrive_to_execute x s hsch
          simpa [has_arrived] using this
        rw [List.mem_append]
        rcases Nat.lt_or_ge (job_arrival x) critical_instant with hb | hb
        · left
          have hncx := CaseStudies.WorkloadJobs.not_completed_of_scheduled_later job_arrival job_cost
            sched H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute x _ s hs1 hsch
          simp only [carry_in_jobs_of, List.mem_filter, Bool.and_eq_true, decide_eq_true_eq]
          refine ⟨hmemA x _ harr hb, ⟨htk, by rw [htk, ← htask0]; exact hhp0⟩, by simp [hncx]⟩
        · right
          simp only [List.mem_filter, Bool.and_eq_true, decide_eq_true_eq]
          exact ⟨hmemA x _ harr (by tomega), htk, hb⟩
      have h2 := Prosa.Classic.Util.Sum.leq_sum_sub_uniq _ L _ g hnd hsub
      rw [CaseStudies.Common.sumSeq_append] at h2
      have h3 := Lemma1_09 k critical_instant hci'
      rw [hn] at h3
      have h4 : sumSeq ((jobs_arrived_before arr_seq (job_arrival jxi)).filter (fun j0 =>
          decide (job_task j0 = k) && decide (critical_instant ≤ job_arrival j0))) g ≤
          (xi - 1) * task_cost k := by
        rw [← hcount]
        calc _ ≤ sumSeq ((jobs_arrived_before arr_seq (job_arrival jxi)).filter (fun j0 =>
              decide (job_task j0 = k) && decide (critical_instant ≤ job_arrival j0)))
                (fun _ => task_cost k) := by
              apply CaseStudies.Common.sumSeq_le_sumSeq
              intro x hx
              rw [List.mem_filter] at hx
              simp only [Bool.and_eq_true, decide_eq_true_eq] at hx
              have := hcostk x (harrA x _ hx.1) hx.2.1
              show job_cost x - service sched x critical_instant ≤ task_cost k
              exact le_trans (Nat.sub_le _ _) this
          _ = _ := by unfold sumSeq; simp
      have hK : K * task_cost k = n * task_cost k + (xi - 1) * task_cost k := by
        rw [← hKeq, Nat.add_mul]
      have hne : 1 ≤ n * task_cost k := Nat.mul_pos hn1 he0
      have : carry_in_workload job_cost job_task arr_seq num_cpus sched higher_eq_priority tsk k
          critical_instant = sumSeq (carry_in_jobs_of job_cost job_task arr_seq num_cpus sched
            higher_eq_priority tsk k critical_instant) g := rfl
      rw [this] at h3
      tomega
    have hW : W_CI task_cost task_period k R t =
        CaseStudies.WorkloadArith.wnc (task_cost k) (task_period k)
          (t - (task_cost k - 1 + K * task_period k - R)) + min t (K * task_cost k - 1) := by
      rw [← hKdef]
      rfl
    rw [hW]
    have hxp : job_arrival jxi = critical_instant + (task_cost k - 1 + K * task_period k - R) := by
      rw [hxarr, hKeq]
    rcases Nat.le_total t (job_arrival jxi - critical_instant) with ht | ht
    · have h1 := CaseStudies.WorkloadJobs.workload_mono job_task sched k critical_instant
        (critical_instant + t) (job_arrival jxi) (by tomega)
      have h2 := hlen critical_instant t
      have h3 : min t (K * task_cost k - 1) ≤ CaseStudies.WorkloadArith.wnc (task_cost k) (task_period k)
          (t - (task_cost k - 1 + K * task_period k - R)) + min t (K * task_cost k - 1) :=
        Nat.le_add_left _ _
      have : workload job_task sched k critical_instant (critical_instant + t) ≤
          min t (K * task_cost k - 1) := le_min h2 (le_trans h1 hbefore)
      exact le_trans this h3
    · rw [CaseStudies.WorkloadJobs.workload_split job_task sched k critical_instant (job_arrival jxi)
        (critical_instant + t) hxge (by tomega)]
      have hafter := Lemma2 k R (job_arrival jxi) (critical_instant + t - job_arrival jxi)
        (fun j1 h1 h2 h3 => hprevxi j1 h1 h2 h3) hmem
      have hend : job_arrival jxi + (critical_instant + t - job_arrival jxi) = critical_instant + t := by
        tomega
      rw [hend] at hafter
      have h2 := hlen critical_instant (job_arrival jxi - critical_instant)
      have hend2 : critical_instant + (job_arrival jxi - critical_instant) = job_arrival jxi := by tomega
      rw [hend2] at h2
      have hsame : critical_instant + t - job_arrival jxi =
          t - (task_cost k - 1 + K * task_period k - R) := by rw [hxp]; tomega
      rw [hsame] at hafter
      have : W_NC task_cost task_period k (t - (task_cost k - 1 + K * task_period k - R)) =
          CaseStudies.WorkloadArith.wnc (task_cost k) (task_period k)
            (t - (task_cost k - 1 + K * task_period k - R)) := rfl
      rw [this] at hafter
      have hmin : workload job_task sched k critical_instant (job_arrival jxi) ≤ min t (K * task_cost k - 1) :=
        le_min (le_trans h2 (by tomega)) hbefore
      omega
  · -- `R = e`: a single carry-in job, which completes within `e` of its arrival
    have hRe : R = task_cost k := le_antisymm hge heR
    have hW : W_CI task_cost task_period k R t =
        CaseStudies.WorkloadArith.wnc (task_cost k) (task_period k) t := by
      have h0 : Prosa.Classic.Util.DivMod.div_ceil (R - task_cost k) (task_period k - task_cost k) = 0 := by
        rw [hRe, Nat.sub_self]; simp [Prosa.Classic.Util.DivMod.div_ceil]
      have hxp : x_p task_cost task_period k R = 0 := by
        unfold x_p; simp only; rw [h0]; tomega
      have hxd : x_delta task_cost task_period k R t = 0 := by
        unfold x_delta; simp only; rw [h0]; simp
      unfold W_CI
      rw [hxp, hxd, Nat.sub_zero, Nat.add_zero]
      rfl
    rw [hW]
    have hcomp0 := H_response_time_of_interfering_tasks_is_known k R hmem j0 harr0 htask0
    have hδR : critical_instant < job_arrival j0 + R := by
      by_contra h
      have := completion_monotonic job_cost sched j0 _ critical_instant (by tomega) hcomp0
      simp [this] at hnc0
    obtain ⟨L, hnd, hL, hw⟩ := CaseStudies.WorkloadJobs.workload_as_jobs job_task sched k
      critical_instant (critical_instant + t)
    rw [hw]
    -- the other contributing jobs arrive at least `p` after `j0`
    have hinfo : ∀ x ∈ L, x ≠ j0 → arrives_in arr_seq x ∧ job_task x = k ∧
        job_arrival j0 + task_period k ≤ job_arrival x := by
      intro x hx hne
      obtain ⟨htk, s, hs1, hs2, hsch⟩ := hL x hx
      have harr := H_jobs_come_from_arrival_sequence x s hsch
      refine ⟨harr, htk, ?_⟩
      rcases Nat.le_total (job_arrival x) (job_arrival j0) with h | h
      · have SPO := H_sporadic_tasks x j0 hne harr harr0 (htk.trans htask0.symm) h
        rw [htk] at SPO
        have hcx := H_response_time_of_interfering_tasks_is_known k R hmem x harr htk
        have := completion_monotonic job_cost sched x _ critical_instant (by tomega) hcx
        have hncx := CaseStudies.WorkloadJobs.not_completed_of_scheduled_later job_arrival job_cost
          sched H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute x _ s hs1 hsch
        rw [this] at hncx; exact absurd hncx (by simp)
      · have := H_sporadic_tasks j0 x (Ne.symm hne) harr0 harr (htask0.trans htk.symm) h
        rwa [htask0] at this
    have hsplit : sumSeq L (fun x => service_during sched x critical_instant (critical_instant + t)) ≤
        service_during sched j0 critical_instant (critical_instant + t) +
          sumSeq (L.erase j0) (fun x => service_during sched x critical_instant (critical_instant + t)) := by
      by_cases hj0 : j0 ∈ L
      · rw [CaseStudies.Common.sumSeq_perm _ (List.perm_cons_erase hj0)]
        unfold sumSeq; simp
      · rw [List.erase_of_not_mem hj0]; exact Nat.le_add_left _ _
    have herase : ∀ x ∈ L.erase j0, x ∈ L ∧ x ≠ j0 := by
      intro x hx
      exact ⟨List.mem_of_mem_erase hx, fun h => by subst h; exact (hnd.mem_erase_iff.mp hx).1 rfl⟩
    have hci1 := CaseStudies.WorkloadJobs.service_during_le_before_completion job_cost sched
      H_sequential_jobs H_completed_jobs_dont_execute j0 critical_instant (critical_instant + t) _ hcomp0
    have hci2 := cumulative_service_le_delta sched j0 H_sequential_jobs critical_instant t
    -- the later jobs, counted together with a virtual job at the arrival of `j0`
    have hbody : sumSeq (L.erase j0) (fun x => service_during sched x critical_instant (critical_instant + t)) +
        min (task_cost k) (t + (critical_instant - job_arrival j0)) ≤
        CaseStudies.WorkloadArith.wnc (task_cost k) (task_period k) (t + (critical_instant - job_arrival j0)) := by
      have hle : sumSeq (L.erase j0) (fun x => service_during sched x critical_instant (critical_instant + t)) ≤
          sumSeq ((L.erase j0).map (fun x => job_arrival x - job_arrival j0))
            (fun y => min (task_cost k) ((t + (critical_instant - job_arrival j0)) - y)) := by
        have : sumSeq ((L.erase j0).map (fun x => job_arrival x - job_arrival j0))
            (fun y => min (task_cost k) ((t + (critical_instant - job_arrival j0)) - y)) =
            sumSeq (L.erase j0) (fun x => min (task_cost k)
              ((t + (critical_instant - job_arrival j0)) - (job_arrival x - job_arrival j0))) := by
          unfold sumSeq; rw [List.map_map]; rfl
        rw [this]
        apply CaseStudies.Common.sumSeq_le_sumSeq
        intro x hx
        obtain ⟨hxL, hne⟩ := herase x hx
        obtain ⟨harr, htk, hsep⟩ := hinfo x hxL hne
        have hge : critical_instant ≤ job_arrival x := by tomega
        apply le_min
        · have h1 := CaseStudies.WorkloadJobs.service_during_le_remaining job_cost sched
            H_completed_jobs_dont_execute x critical_instant (critical_instant + t) (Nat.le_add_right _ _)
          have h2 := hcostk x harr htk
          tomega
        · have := CaseStudies.WorkloadJobs.service_during_le_after_arrival job_arrival sched
            H_sequential_jobs H_jobs_must_arrive_to_execute x critical_instant (critical_instant + t) hge
          tomega
      have hsum := CaseStudies.WorkloadArith.sum_sep_le (task_cost k) (task_period k) hp0
        (0 :: (L.erase j0).map (fun x => job_arrival x - job_arrival j0)) (by
          rw [List.pairwise_cons]
          refine ⟨?_, ?_⟩
          · intro y hy
            obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
            obtain ⟨hxL, hne⟩ := herase x hx
            obtain ⟨_, _, hsep⟩ := hinfo x hxL hne
            left; tomega
          · rw [List.pairwise_map]
            apply (hnd.sublist (List.erase_sublist)).imp_of_mem
            intro a b ha hb hab
            obtain ⟨haL, hane⟩ := herase a ha
            obtain ⟨hbL, hbne⟩ := herase b hb
            obtain ⟨harra, hta, hsa⟩ := hinfo a haL hane
            obtain ⟨harrb, htb, hsb⟩ := hinfo b hbL hbne
            rcases Nat.le_total (job_arrival a) (job_arrival b) with h | h
            · have := H_sporadic_tasks a b hab harra harrb (hta.trans htb.symm) h
              rw [hta] at this; left; tomega
            · have := H_sporadic_tasks b a (Ne.symm hab) harrb harra (htb.trans hta.symm) h
              rw [htb] at this; right; tomega)
        (t + (critical_instant - job_arrival j0))
      have hcons : sumSeq (0 :: (L.erase j0).map (fun x => job_arrival x - job_arrival j0))
          (fun y => min (task_cost k) ((t + (critical_instant - job_arrival j0)) - y)) =
          min (task_cost k) (t + (critical_instant - job_arrival j0)) +
            sumSeq ((L.erase j0).map (fun x => job_arrival x - job_arrival j0))
              (fun y => min (task_cost k) ((t + (critical_instant - job_arrival j0)) - y)) := by
        unfold sumSeq; simp
      rw [hcons] at hsum
      omega
    have hgrow := CaseStudies.WorkloadArith.wnc_le_add (task_cost k) (task_period k) t hp0
      (Nat.le_of_lt hep) (critical_instant - job_arrival j0)
    have hci2' : service_during sched j0 critical_instant (critical_instant + t) ≤ t := hci2
    generalize CaseStudies.WorkloadArith.wnc (task_cost k) (task_period k)
      (t + (critical_instant - job_arrival j0)) = Wd at hbody hgrow
    generalize sumSeq (L.erase j0) (fun x => service_during sched x critical_instant
      (critical_instant + t)) = Sb at hbody hsplit
    generalize service_during sched j0 critical_instant (critical_instant + t) = S0 at hci1 hci2' hsplit
    tomega

end CaseStudies.RTCSA2014.Lemma4.ResponseTimeAnalysisFP
