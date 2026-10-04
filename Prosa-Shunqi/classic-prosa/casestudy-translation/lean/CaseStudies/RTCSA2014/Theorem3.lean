-- Case study: RTS_Papers/2014-RTCSA-Theorem3/theorem3.v
-- sha256 0ead9070067f31360eb124ebffa7c0fa80ed46ea3322773627b672f1116b1741
-- (elaborated contract: classic-prosa/casestudy-translation/contracts/2014-RTCSA-Theorem3.txt)
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

/-!
Theorem 3 of the RTCSA 2014 paper as stated by the case study `2014-RTCSA-Theorem3` (Rocq module
`ResponseTimeAnalysisFP`): the least upper bound `R_global` of the solutions `R_of_CI CI` over all valid carry-in
sets `CI` is a response-time bound of `tsk`; Lemma 5 (for every carry-in set) is the hypothesis `lemma5`.

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

namespace CaseStudies.RTCSA2014.Theorem3.ResponseTimeAnalysisFP

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

def interference_bound_arbitrary_ci {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost task_period : sporadic_task → time) (tsk : sporadic_task) (delta : time) (tsk_R : sporadic_task × time) : Nat :=
  let tsk_other := tsk_R.1
  let R_other := tsk_R.2
  min (W_CI task_cost task_period tsk_other R_other delta) (delta - task_cost tsk + 1)

def interference_bound_arbitrary_nc {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost task_period : sporadic_task → time) (tsk : sporadic_task) (delta : time) (tsk_R : sporadic_task × time) : Nat :=
  let tsk_other := tsk_R.1
  min (W_NC task_cost task_period tsk_other delta) (delta - task_cost tsk + 1)

def total_interference_bound_CI {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost task_period : sporadic_task → time) (tsk : sporadic_task) (R_carryin : List (sporadic_task × time)) (delta : time) : Nat :=
  sumSeq R_carryin (fun (tsk_other, R_other) =>
    interference_bound_arbitrary_ci task_cost task_period tsk delta (tsk_other, R_other))

def total_interference_bound_NC {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost task_period : sporadic_task → time) (tsk : sporadic_task) (R_noncarryin : List (sporadic_task × time)) (delta : time) : Nat :=
  sumSeq R_noncarryin (fun (tsk_other, R_other) =>
    interference_bound_arbitrary_nc task_cost task_period tsk delta (tsk_other, R_other))

def total_interference_bound_rtcsa14 {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost task_period : sporadic_task → time) (tsk : sporadic_task) (R_carryin R_noncarryin : List (sporadic_task × time)) (delta : time) : Nat :=
  total_interference_bound_CI task_cost task_period tsk R_carryin delta +
    total_interference_bound_NC task_cost task_period tsk R_noncarryin delta

def hp_busy {sporadic_task : Type u} {Job : Type v} [DecidableEq sporadic_task] [DecidableEq Job]
    (job_task : Job → sporadic_task) (ts : taskset_of sporadic_task) (num_cpus : Nat)
    (sched : schedule Job num_cpus) (higher_eq_priority : FP_policy sporadic_task)
    (tsk : sporadic_task) (t : time) : Prop :=
  ts.val.countP (fun tsk_other =>
    task_is_scheduled job_task sched tsk_other t &&
      higher_priority_task higher_eq_priority tsk tsk_other) = num_cpus

def valid_CI_taskset {sporadic_task : Type u} {Job : Type v} [DecidableEq sporadic_task] [DecidableEq Job]
    (job_arrival job_cost : Job → time) (job_task : Job → sporadic_task) (arr_seq : arrival_sequence Job)
    (num_cpus : Nat) (sched : schedule Job num_cpus) (hp_bounds : List (sporadic_task × time))
    (critical_instant : time) (CI_taskset : List (sporadic_task × time)) : Prop :=
  (∀ p, p ∈ CI_taskset → p ∈ hp_bounds) ∧
    CI_taskset.Nodup ∧
    CI_taskset.length < num_cpus ∧
    ∀ (tsk_other : sporadic_task) (R_other : time), (tsk_other, R_other) ∈ CI_taskset →
      ∃ j0 : Job, arrives_in arr_seq j0 ∧ job_task j0 = tsk_other ∧ job_arrival j0 < critical_instant ∧
        (!completed job_cost sched j0 critical_instant) = true

theorem Theorem3_14 {sporadic_task : Type u} [DecidableEq sporadic_task]
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
    (tsk : sporadic_task) (task_in_ts : tsk ∈ ts)
    (hp_bounds : List (sporadic_task × time))
    (task_in_hpbound_in_ts : ∀ (hp_tsk : sporadic_task) (R : time), (hp_tsk, R) ∈ hp_bounds →
      hp_tsk ∈ ts ∧ higher_priority_task higher_eq_priority tsk hp_tsk = true)
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
    (exist_j_released_at_criticalinstant : ∃ j : Job,
      arrives_in arr_seq j ∧ job_task j = tsk → job_arrival j = critical_instant)
    (R_of_CI : List (sporadic_task × time) → time)
    (H_response_time_recurrence_holds : ∀ CI_taskset : List (sporadic_task × time), valid_CI_taskset job_arrival job_cost job_task arr_seq num_cpus sched hp_bounds critical_instant CI_taskset →
      let NC_taskset := hp_bounds.filter (fun x => !decide (x ∈ CI_taskset));
      let R := R_of_CI CI_taskset;
      R = task_cost tsk + div_floor (total_interference_bound_rtcsa14 task_cost task_period tsk CI_taskset NC_taskset R) num_cpus)
    (R_is_minimal_solution : ∀ CI_taskset : List (sporadic_task × time), valid_CI_taskset job_arrival job_cost job_task arr_seq num_cpus sched hp_bounds critical_instant CI_taskset →
      let NC_taskset := hp_bounds.filter (fun x => !decide (x ∈ CI_taskset));
      let R := R_of_CI CI_taskset;
      ∀ x : time, x = task_cost tsk + div_floor (total_interference_bound_rtcsa14 task_cost task_period tsk CI_taskset NC_taskset x) num_cpus → R ≤ x)
    (H_response_time_no_larger_than_deadline : ∀ CI_taskset : List (sporadic_task × time), valid_CI_taskset job_arrival job_cost job_task arr_seq num_cpus sched hp_bounds critical_instant CI_taskset →
      R_of_CI CI_taskset ≤ task_deadline tsk)
    (R_global : time)
    (H_R_global_upper : ∀ CI_taskset : List (sporadic_task × time), valid_CI_taskset job_arrival job_cost job_task arr_seq num_cpus sched hp_bounds critical_instant CI_taskset →
      R_of_CI CI_taskset ≤ R_global)
    (H_R_global_least : ∀ R' : Nat,
      (∀ CI_taskset : List (sporadic_task × time), valid_CI_taskset job_arrival job_cost job_task arr_seq num_cpus sched hp_bounds critical_instant CI_taskset → R_of_CI CI_taskset ≤ R') → R_global ≤ R')
    (lemma5 : ∀ CI_taskset : List (sporadic_task × time), is_response_time_bound_of_task job_arrival job_cost job_task arr_seq sched tsk (R_of_CI CI_taskset)) :
    is_response_time_bound_of_task job_arrival job_cost job_task arr_seq sched tsk R_global := by
  have hv : valid_CI_taskset job_arrival job_cost job_task arr_seq num_cpus sched hp_bounds critical_instant [] :=
    ⟨fun p hp => by simp at hp, List.nodup_nil, by simpa using H_at_least_one_cpu, fun _ _ h => by simp at h⟩
  exact CaseStudies.Common.rtb_mono (H_R_global_upper [] hv) (lemma5 [])

end CaseStudies.RTCSA2014.Theorem3.ResponseTimeAnalysisFP
