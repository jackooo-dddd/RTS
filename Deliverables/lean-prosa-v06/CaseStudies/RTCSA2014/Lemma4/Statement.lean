-- Case study 2014-RTCSA-Lemma4: Improving the Response Time Analysis of Global Fixed-Priority Multiprocessor Scheduling (RTCSA 2014).
-- Original Rocq statement: RTS_Papers/2014-RTCSA-Lemma4/lemma4.v.
-- Benchmark file: read-only.  Prove `CaseStudies.RTCSA2014.Lemma4.ResponseTimeAnalysisFP.Lemma4_14_statement` in `Solution.lean` (this folder).
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

/-!
Lemma 4 of the RTCSA 2014 paper ("Improving the Response Time Analysis of Global Fixed-Priority
Multiprocessor Scheduling") as stated by the case study `2014-RTCSA-Lemma4` (Rocq module
`ResponseTimeAnalysisFP`): the workload of a higher-priority task with a carry-in job in
`[critical_instant, critical_instant + t)` is at most the improved carry-in bound `W_CI R_k t`. The
carry-in workload bound (`Lemma1_09`), the no-carry-in workload bound (`Lemma2`) and the existence
of a tight release chain (`Lemma1_14`) are hypotheses; The conclusion quantifies its own `tsk_other`
and `R_other` (shadowing the section variables of the same names, which only the chain hypotheses
mention).

Representation notes: `minn` is `min`; `x %% p` is `x % p`; `\sum_(x <- s) F x` is `sumSeq s F` and
`\sum_(x <- s | P x) F x` is `sumFiltered s P F` (pair patterns are `fun (a, b) => …`); a Boolean
summed as a number is `Bool.toNat`; `sort r s` is `s.mergeSort r` with the relation decided; `take n
s` is `s.take n`; `n.-1` is `n - 1`; `[seq x <- s | P x]` is `s.filter P`; `x \notin s` is `!decide
(x ∈ s)`; `count P ts` is `ts.val.countP P`; Boolean tests in proposition position are `= true` (`~~
b` is `(!b) = true`), and chains `a <= t < b` are `(decide (a ≤ t) && decide (t < b)) = true`;
section-local `Let`s are unfolded. Binder lists follow the Rocq original: a definition abstracts
exactly the section variables it uses, a theorem every variable and hypothesis declared before it,
so some binders are unused.
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

/-- The statement of the case study's theorem `Lemma4_14`. -/
def Lemma4_14_statement : Prop :=
  ∀ {sporadic_task : Type u} [DecidableEq sporadic_task]
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
              k ≤ k0)),
    ∀ (tsk_other0 : sporadic_task) (R_other0 : time) (t : Nat), task_has_carry_in_job job_arrival job_cost job_task arr_seq num_cpus sched higher_eq_priority tsk tsk_other0 critical_instant →
      (tsk_other0, R_other0) ∈ hp_bounds →
      workload job_task sched tsk_other0 critical_instant (critical_instant + t) ≤
        W_CI task_cost task_period tsk_other0 R_other0 t

end CaseStudies.RTCSA2014.Lemma4.ResponseTimeAnalysisFP
