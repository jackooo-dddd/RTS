-- Case study 2009-RTSS-Lemma5: Guan, Stigge, Yi, Yu — New Response Time Bounds for Fixed Priority Multiprocessor Scheduling (RTSS 2009).
-- Original Rocq statement: RTS_Papers/2009-RTSS-Lemma5/Lemma5.v.
-- Benchmark file: read-only.  Prove `CaseStudies.RTSS2009.Lemma5.ResponseTimeAnalysisFP.Lemma5_09_statement` in `Solutions/RTSS2009/Lemma5.lean`.
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
Lemma 5 of Guan et al., RTSS 2009 (arbitrary deadlines), as stated by the case study
`2009-RTSS-Lemma5` (Rocq module `ResponseTimeAnalysisFP`): with `chi_min h` the least solution of
the `h`-job recurrence and `H_phi` the least `h ≥ 1` with `chi_min h ≤ h p + phi`, `max_{1≤h≤H_phi}
(chi_min h - ((h-1) p + phi))` is a response-time bound of `tsk`. Lemma 2 of the paper and the
selection of a worst-case job from a tight chain are hypotheses.

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

namespace CaseStudies.RTSS2009.Lemma5.ResponseTimeAnalysisFP

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

def max_jobs {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost task_period : sporadic_task → time) (tsk : sporadic_task) (delta : time) : Nat :=
  div_floor (delta - task_cost tsk) (task_period tsk)

def W {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost task_period : sporadic_task → time) (tsk : sporadic_task) (R_tsk delta : time) : Nat :=
  let e_k := task_cost tsk
  let p_k := task_period tsk
  min (e_k - 1) (delta + R_tsk - e_k - max_jobs task_cost task_period tsk delta * p_k - p_k) +
    max_jobs task_cost task_period tsk delta * e_k + e_k

def W_NC {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost task_period : sporadic_task → time) (tsk : sporadic_task) (delta : time) : Nat :=
  let e_i := task_cost tsk
  let p_i := task_period tsk
  div_floor delta p_i * e_i + min e_i (delta % p_i)

def interference_bound_arbitrary_ci {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost task_period : sporadic_task → time) (tsk : sporadic_task) (delta : time) (tsk_R : sporadic_task × time) (h : Nat) : Nat :=
  let tsk_other := tsk_R.1
  let R_other := tsk_R.2
  min (W task_cost task_period tsk_other R_other delta) (delta - h * task_cost tsk + 1)

def interference_bound_arbitrary_nc {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost task_period : sporadic_task → time) (tsk : sporadic_task) (delta : time) (tsk_R : sporadic_task × time) (h : Nat) : Nat :=
  let tsk_other := tsk_R.1
  min (W_NC task_cost task_period tsk_other delta) (delta - h * task_cost tsk + 1)

def interference_bound_delta {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost task_period : sporadic_task → time) (tsk : sporadic_task) (delta : time) (tsk_R : sporadic_task × time) (h : Nat) : Nat :=
  interference_bound_arbitrary_ci task_cost task_period tsk delta tsk_R h -
    interference_bound_arbitrary_nc task_cost task_period tsk delta tsk_R h

def sum_largest (n : Nat) (xs : List Nat) : Nat :=
  sumSeq ((xs.mergeSort (fun x y => decide (y ≤ x))).take n) (fun x => x)

def total_interference_bound_fp {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost task_period : sporadic_task → time) (tsk : sporadic_task) (R_prev : List (sporadic_task × time)) (delta : time) (h : Nat) : Nat :=
  sumSeq R_prev (fun (tsk_other, R_other) =>
    interference_bound_arbitrary_ci task_cost task_period tsk delta (tsk_other, R_other) h)

def CI_taskset {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost task_period : sporadic_task → time) (tsk : sporadic_task) (R_prev : List (sporadic_task × time)) (delta : time) (num_cpus h : Nat) :
    List (sporadic_task × time) :=
  (R_prev.mergeSort (fun p q =>
    decide (interference_bound_delta task_cost task_period tsk delta q h ≤
      interference_bound_delta task_cost task_period tsk delta p h))).take (num_cpus - 1)

def NC_taskset {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost task_period : sporadic_task → time) (tsk : sporadic_task) (R_prev : List (sporadic_task × time)) (delta : time) (num_cpus h : Nat) :
    List (sporadic_task × time) :=
  R_prev.filter (fun p => !decide (p ∈ CI_taskset task_cost task_period tsk R_prev delta num_cpus h))

def total_interference_bound_ci {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost task_period : sporadic_task → time) (tsk : sporadic_task) (R_prev : List (sporadic_task × time)) (delta : time) (num_cpus h : Nat) : Nat :=
  sumSeq (CI_taskset task_cost task_period tsk R_prev delta num_cpus h)
    (fun p => interference_bound_arbitrary_ci task_cost task_period tsk delta p h)

def total_interference_bound_nc {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost task_period : sporadic_task → time) (tsk : sporadic_task) (R_prev : List (sporadic_task × time)) (delta : time) (num_cpus h : Nat) : Nat :=
  sumSeq (NC_taskset task_cost task_period tsk R_prev delta num_cpus h)
    (fun p => interference_bound_arbitrary_nc task_cost task_period tsk delta p h)

def total_interference_bound_gn_arbitrary {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost task_period : sporadic_task → time) (tsk : sporadic_task) (R_prev : List (sporadic_task × time)) (delta : time) (num_cpus h : Nat) : Nat :=
  sumSeq (NC_taskset task_cost task_period tsk R_prev delta num_cpus h)
      (fun p => interference_bound_arbitrary_nc task_cost task_period tsk delta p h) +
    sumSeq (CI_taskset task_cost task_period tsk R_prev delta num_cpus h)
      (fun p => interference_bound_arbitrary_ci task_cost task_period tsk delta p h)

def f_chi {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost task_period : sporadic_task → time) (num_cpus : Nat) (tsk : sporadic_task)
    (hp_bounds : List (sporadic_task × time)) (h : Nat) (chi : time) : Nat :=
  h * task_cost tsk +
    div_floor (total_interference_bound_gn_arbitrary task_cost task_period tsk hp_bounds chi num_cpus h) num_cpus

def chi_is_least_solution {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost task_period : sporadic_task → time) (num_cpus : Nat) (tsk : sporadic_task)
    (hp_bounds : List (sporadic_task × time)) (h : Nat) (chi : time) : Prop :=
  chi = f_chi task_cost task_period num_cpus tsk hp_bounds h chi ∧
    ∀ x : time, x = f_chi task_cost task_period num_cpus tsk hp_bounds h x → chi ≤ x

def hp_busy {sporadic_task : Type u} {Job : Type v} [DecidableEq sporadic_task] [DecidableEq Job]
    (job_task : Job → sporadic_task) (ts : taskset_of sporadic_task) (num_cpus : Nat)
    (sched : schedule Job num_cpus) (higher_eq_priority : FP_policy sporadic_task)
    (tsk : sporadic_task) (t : time) : Prop :=
  ts.val.countP (fun tsk_other =>
    task_is_scheduled job_task sched tsk_other t &&
      higher_priority_task higher_eq_priority tsk tsk_other) = num_cpus

def H_phi_satisfy {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_period : sporadic_task → time) (tsk : sporadic_task) (chi_min : Nat → time) (phi : time) (h : Nat) : Bool :=
  decide (chi_min h ≤ h * task_period tsk + phi)

def R_phi_term {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_period : sporadic_task → time) (tsk : sporadic_task) (chi_min : Nat → time) (phi : time) (h : Nat) : time :=
  chi_min h - ((h - 1) * task_period tsk + phi)

def max_R_phi_term {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_period : sporadic_task → time) (tsk : sporadic_task) (chi_min : Nat → time) (phi : time) : Nat → time
  | 0 => 0
  | h' + 1 => max (max_R_phi_term task_period tsk chi_min phi h') (R_phi_term task_period tsk chi_min phi (h' + 1))

def jobs_of_tsk_between {sporadic_task : Type u} {Job : Type v} [DecidableEq sporadic_task] [DecidableEq Job]
    (job_task : Job → sporadic_task) (arr_seq : arrival_sequence Job) (tsk : sporadic_task) (t1 t2 : time) :
    List Job :=
  arrivals_of_task_between job_task arr_seq tsk t1 t2

def first_h_jobs_through {sporadic_task : Type u} {Job : Type v} [DecidableEq sporadic_task] [DecidableEq Job]
    (job_arrival : Job → time) (job_task : Job → sporadic_task) (arr_seq : arrival_sequence Job)
    (tsk : sporadic_task) (j j_h : Job) : List Job :=
  jobs_of_tsk_between job_task arr_seq tsk (job_arrival j) (job_arrival j_h + 1)

def job_finishes_at {Job : Type v} [DecidableEq Job] (job_cost : Job → time) (num_cpus : Nat)
    (sched : schedule Job num_cpus) (j_h : Job) (f_h : time) : Bool :=
  (!completed job_cost sched j_h (f_h - 1)) && completed job_cost sched j_h f_h

def job_is_hth_after_j {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_period : sporadic_task → time) {Job : Type v} [DecidableEq Job]
    (job_arrival : Job → time) (job_task : Job → sporadic_task) (arr_seq : arrival_sequence Job)
    (tsk : sporadic_task) (j : Job) (h : Nat) (j_h : Job) : Prop :=
  1 ≤ h ∧
    arrives_in arr_seq j_h ∧
    job_task j_h = tsk ∧
    job_arrival j_h = job_arrival j + (h - 1) * task_period tsk ∧
    (first_h_jobs_through job_arrival job_task arr_seq tsk j j_h).length = h ∧
    j_h ∈ first_h_jobs_through job_arrival job_task arr_seq tsk j j_h

def preceding_jobs_are_completed_before_first_job {sporadic_task : Type u} {Job : Type v} [DecidableEq sporadic_task] [DecidableEq Job]
    (job_arrival job_cost : Job → time) (job_task : Job → sporadic_task) (arr_seq : arrival_sequence Job)
    (num_cpus : Nat) (sched : schedule Job num_cpus) (tsk : sporadic_task) (j : Job) : Prop :=
  ∀ j_prev : Job, arrives_in arr_seq j_prev → job_task j_prev = tsk → job_arrival j_prev < job_arrival j →
    completed job_cost sched j_prev (job_arrival j) = true

def consecutive_jobs_exist_through {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_period : sporadic_task → time) {Job : Type v} [DecidableEq Job]
    (job_arrival : Job → time) (job_task : Job → sporadic_task) (arr_seq : arrival_sequence Job)
    (tsk : sporadic_task) (j : Job) (h_last : Nat) : Prop :=
  ∀ h : Nat, 1 ≤ h → h ≤ h_last → ∃ j_h : Job, job_is_hth_after_j task_period job_arrival job_task arr_seq tsk j h j_h

def consecutive_jobs_are_tight_through {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_period : sporadic_task → time) {Job : Type v} [DecidableEq Job]
    (job_arrival : Job → time) (job_task : Job → sporadic_task) (arr_seq : arrival_sequence Job)
    (tsk : sporadic_task) (j : Job) (h_last : Nat) : Prop :=
  ∀ (h : Nat) (j_h j_next : Job), 1 ≤ h → h < h_last → job_is_hth_after_j task_period job_arrival job_task arr_seq tsk j h j_h → job_is_hth_after_j task_period job_arrival job_task arr_seq tsk j (h + 1) j_next →
    job_arrival j_next = job_arrival j_h + task_period tsk

def consecutive_jobs_overlap_through {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_period : sporadic_task → time) {Job : Type v} [DecidableEq Job]
    (job_arrival job_cost : Job → time) (job_task : Job → sporadic_task) (arr_seq : arrival_sequence Job)
    (num_cpus : Nat) (sched : schedule Job num_cpus) (tsk : sporadic_task) (j : Job) (h_last : Nat) : Prop :=
  ∀ (h : Nat) (j_h j_next : Job), 1 ≤ h → h < h_last → job_is_hth_after_j task_period job_arrival job_task arr_seq tsk j h j_h → job_is_hth_after_j task_period job_arrival job_task arr_seq tsk j (h + 1) j_next →
    (!completed job_cost sched j_h (job_arrival j_next)) = true

def tight_chain_ending_at {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_period : sporadic_task → time) {Job : Type v} [DecidableEq Job]
    (job_arrival job_cost : Job → time) (job_task : Job → sporadic_task) (arr_seq : arrival_sequence Job)
    (num_cpus : Nat) (sched : schedule Job num_cpus) (tsk : sporadic_task) (j : Job) (h_last : Nat) (j_last : Job) : Prop :=
  job_is_hth_after_j task_period job_arrival job_task arr_seq tsk j h_last j_last ∧
    preceding_jobs_are_completed_before_first_job job_arrival job_cost job_task arr_seq num_cpus sched tsk j ∧
    consecutive_jobs_exist_through task_period job_arrival job_task arr_seq tsk j h_last ∧
    consecutive_jobs_are_tight_through task_period job_arrival job_task arr_seq tsk j h_last ∧
    consecutive_jobs_overlap_through task_period job_arrival job_cost job_task arr_seq num_cpus sched tsk j h_last

def job_has_worstcase_response_time {sporadic_task : Type u} {Job : Type v} [DecidableEq sporadic_task] [DecidableEq Job]
    (job_arrival job_cost : Job → time) (job_task : Job → sporadic_task) (arr_seq : arrival_sequence Job)
    (num_cpus : Nat) (sched : schedule Job num_cpus) (tsk : sporadic_task) (j_worst : Job) : Prop :=
  ∀ (j0 : Job) (x : Nat), arrives_in arr_seq j0 → job_task j0 = tsk →
    completed job_cost sched j_worst (job_arrival j_worst + x) = true →
    completed job_cost sched j0 (job_arrival j0 + x) = true

def worstcase_job_selected_from_tight_chain {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_period : sporadic_task → time) {Job : Type v} [DecidableEq Job]
    (job_arrival job_cost : Job → time) (job_task : Job → sporadic_task) (arr_seq : arrival_sequence Job)
    (num_cpus : Nat) (sched : schedule Job num_cpus) (tsk : sporadic_task) (j : Job) (h_last h_worst : Nat) (j_worst : Job) (f_worst : time) : Prop :=
  h_worst ≤ h_last ∧
    job_is_hth_after_j task_period job_arrival job_task arr_seq tsk j h_worst j_worst ∧
    job_finishes_at job_cost num_cpus sched j_worst f_worst = true ∧
    job_arrival j_worst < f_worst ∧
    job_has_worstcase_response_time job_arrival job_cost job_task arr_seq num_cpus sched tsk j_worst

/-- The statement of the case study's theorem `Lemma5_09`. -/
def Lemma5_09_statement : Prop :=
  ∀ {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost task_period task_deadline : sporadic_task → time)
    {Job : Type v} [DecidableEq Job] (job_arrival job_cost job_deadline : Job → time)
    (job_task : Job → sporadic_task) (arr_seq : arrival_sequence Job)
    (H_sporadic_tasks : sporadic_task_model task_period job_arrival job_task arr_seq)
    (H_arrival_times_are_consistent : arrival_times_are_consistent job_arrival arr_seq)
    (H_arrival_sequence_is_a_set : arrival_sequence_is_a_set arr_seq)
    (H_valid_job_parameters : ∀ j : Job, arrives_in arr_seq j →
      valid_sporadic_job task_cost task_deadline job_cost job_deadline job_task j)
    (ts : taskset_of sporadic_task)
    (H_valid_task_parameters : valid_sporadic_taskset task_cost task_period task_deadline ts.val)
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
    (chi_min : Nat → time)
    (chi_min_spec : ∀ h : Nat, chi_is_least_solution task_cost task_period num_cpus tsk hp_bounds h (chi_min h))
    (Huniq_hp_bounds : hp_bounds.Nodup)
    (j : Job) (t0 : schedule Job num_cpus → Job → time)
    (t0_leq_arrival_time : t0 sched j ≤ job_arrival j)
    (H_j_arrives : arrives_in arr_seq j) (H_job_of_tsk : job_task j = tsk)
    (H_previous_jobs_of_tsk_completed : ∀ j0 : Job, arrives_in arr_seq j0 → job_task j0 = tsk →
      job_arrival j0 < job_arrival j → completed job_cost sched j0 (job_arrival j) = true)
    (cpu_busy_during_t0_rk : ∀ t : Nat, (decide (t0 sched j ≤ t) && decide (t < job_arrival j)) = true →
      hp_busy job_task ts num_cpus sched higher_eq_priority tsk t)
    (t0_left_boundary : t0 sched j = 0 ∨ ¬ hp_busy job_task ts num_cpus sched higher_eq_priority tsk (t0 sched j - 1))
    (phi : time) (phi_is_defined : phi = job_arrival j - t0 sched j)
    (H_phi : Nat)
    (H_phi_is_minimal : 0 < H_phi ∧ H_phi_satisfy task_period tsk chi_min phi H_phi = true ∧
      ∀ x : Nat, 0 < x → H_phi_satisfy task_period tsk chi_min phi x = true → H_phi ≤ x)
    (H_Lemma2_1 : ∀ (tsk_other : sporadic_task) (R_other t1 : time) (h : Nat) (delta : time),
      (tsk_other, R_other) ∈ NC_taskset task_cost task_period tsk hp_bounds delta num_cpus h →
      workload job_task sched tsk_other t1 (t1 + delta) ≤ W_NC task_cost task_period tsk_other delta)
    (H_Lemma2_2 : ∀ (tsk_other : sporadic_task) (R_other t1 : time) (h : Nat) (delta : time),
      (tsk_other, R_other) ∈ CI_taskset task_cost task_period tsk hp_bounds delta num_cpus h →
      workload job_task sched tsk_other t1 (t1 + delta) ≤ W task_cost task_period tsk_other R_other delta)
    (H_jobs_before_H_phi_do_not_complete_by_next_release : ∀ (h : Nat) (j_h : Job), h < H_phi →
      job_is_hth_after_j task_period job_arrival job_task arr_seq tsk j h j_h → (!completed job_cost sched j_h (job_arrival j_h + task_period tsk)) = true)
    (H_current_chain_reaches_H_phi : ∃ j_H_phi : Job, job_is_hth_after_j task_period job_arrival job_task arr_seq tsk j H_phi j_H_phi)
    (H_Lemma1_selects_worstcase_job_from_tight_chain : ∀ (h_last : Nat) (j_last : Job),
      tight_chain_ending_at task_period job_arrival job_cost job_task arr_seq num_cpus sched tsk j h_last j_last →
      ∃ (h_worst : Nat) (j_worst : Job) (f_worst : time),
        worstcase_job_selected_from_tight_chain task_period job_arrival job_cost job_task arr_seq num_cpus sched
          tsk j h_last h_worst j_worst f_worst),
    is_response_time_bound_of_task job_arrival job_cost job_task arr_seq sched tsk (max_R_phi_term task_period tsk chi_min phi H_phi)

end CaseStudies.RTSS2009.Lemma5.ResponseTimeAnalysisFP
