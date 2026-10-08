-- Case study 2015-RTAS-Lemma8: Linux push/pull scheduler with arbitrary processor affinities (2015), Lemma 8 (APA).
-- Original Rocq statement: RTS_Papers/2015-RTAS-Lemma8/Lemma8.v.
-- Benchmark file: read-only.  Prove `CaseStudies.RTAS2015.Lemma8.ResponseTimeAnalysisFP.bertogna_cirinei_response_time_bound_fp_statement` in `Solution.lean` (this folder).
import Prosa.Util.Sum
import Prosa.Classic.Util.DivMod
import Prosa.Classic.Model.Arrival.Basic.Task
import Prosa.Classic.Model.Arrival.Basic.Job
import Prosa.Classic.Model.Arrival.Basic.TaskArrival
import Prosa.Classic.Model.Priority
import Prosa.Classic.Model.Schedule.Global.ResponseTime
import Prosa.Classic.Model.Schedule.Global.Basic.Schedule
import Prosa.Classic.Model.Schedule.Apa.Affinity
import Prosa.Classic.Model.Schedule.Apa.Interference
import Prosa.Classic.Model.Schedule.Apa.Platform

/-!
Lemma 8 of the APA paper as stated by the case study (Rocq module `ResponseTimeAnalysisFP`): any
fixed point `R ≤ d_tsk` of the response-time recurrence computed with a subaffinity `alpha'` is a
response-time bound. The case study defines its own workload bound: `W` and `max_jobs` use the
interfering task's *deadline* `d_k` where the classic `WorkloadBound.W` uses its response-time
bound, so `interference_bound_generic` takes only the interfering task, and
`total_interference_bound_fp` ignores the response-time component of each pair.

Representation notes: `minn` is `min`; `#|A|` is `(Finset.univ.filter (· ∈ A)).card`;
`\sum_((tsk_other, _) <- s | P tsk_other) F tsk_other` is `sumFiltered s (fun (tsk_other, _) => P
tsk_other) (fun (tsk_other, _) => F tsk_other)`; Boolean predicates in proposition position are `=
true`; the section-local `Let`s are unfolded (`hp_task_in a'` is `higher_priority_task_in alpha
higher_eq_priority tsk a'`, `total_interference_bound` is `interference_bound_generic … tsk delta`).
Binder lists follow the Rocq original (`num_cpus` is a `Context`, hence implicit).
-/

set_option linter.unusedVariables false

namespace CaseStudies.RTAS2015.Lemma8.ResponseTimeAnalysisFP

open Prosa.Classic.Model.Time.Time
open Prosa.Classic.Model.Arrival.Basic.ArrivalSequence.ArrivalSequence
open Prosa.Classic.Model.Arrival.Basic.Task.SporadicTaskset
open Prosa.Classic.Model.Arrival.Basic.Job.Job
open Prosa.Classic.Model.Arrival.Basic.TaskArrival.TaskArrival
open Prosa.Classic.Model.Priority.Priority
open Prosa.Classic.Model.Schedule.Global.Basic.Schedule.Schedule
open Prosa.Classic.Model.Schedule.Global.ResponseTime.ResponseTime
open Prosa.Classic.Model.Schedule.Apa.Affinity.Affinity
open Prosa.Classic.Model.Schedule.Apa.Interference.Interference
open Prosa.Classic.Model.Schedule.Apa.Platform.Platform
open Prosa.Classic.Util.DivMod (div_floor)
open Prosa.Util.Sum (sumFiltered)

universe u v

def max_jobs {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost task_period task_deadline : sporadic_task → time) (tsk : sporadic_task)
    (delta : time) : Nat :=
  div_floor (delta + task_deadline tsk - task_cost tsk) (task_period tsk)

def W {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost task_period task_deadline : sporadic_task → time) (tsk : sporadic_task)
    (delta : time) : Nat :=
  let e_k := task_cost tsk
  let p_k := task_period tsk
  let d_k := task_deadline tsk
  min e_k (delta + d_k - e_k - max_jobs task_cost task_period task_deadline tsk delta * p_k) +
    max_jobs task_cost task_period task_deadline tsk delta * e_k

def interference_bound_generic {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost task_period task_deadline : sporadic_task → time) (tsk : sporadic_task)
    (delta : time) (tsk_other : sporadic_task) : Nat :=
  min (W task_cost task_period task_deadline tsk_other delta) (delta - task_cost tsk + 1)

def total_interference_bound_fp {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost task_period task_deadline : sporadic_task → time) {num_cpus : Nat}
    (alpha : task_affinity sporadic_task num_cpus) (tsk : sporadic_task)
    (alpha' : affinity num_cpus) (R_prev : List (sporadic_task × time)) (delta : time)
    (higher_eq_priority : FP_policy sporadic_task) : Nat :=
  sumFiltered R_prev
    (fun (tsk_other, _) => higher_priority_task_in alpha higher_eq_priority tsk alpha' tsk_other)
    (fun (tsk_other, _) =>
      interference_bound_generic task_cost task_period task_deadline tsk delta tsk_other)

/-- The statement of the case study's theorem `bertogna_cirinei_response_time_bound_fp`. -/
def bertogna_cirinei_response_time_bound_fp_statement : Prop :=
  ∀ {sporadic_task : Type u} [DecidableEq sporadic_task]
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
    {num_cpus : Nat} (alpha : task_affinity sporadic_task num_cpus)
    (sched : schedule Job num_cpus)
    (H_jobs_come_from_arrival_sequence : jobs_come_from_arrival_sequence sched arr_seq)
    (H_sequential_jobs : sequential_jobs sched)
    (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute job_arrival sched)
    (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched)
    (H_arrival_times_are_consistent : arrival_times_are_consistent job_arrival arr_seq)
    (H_arr_seq_is_a_set : arrival_sequence_is_a_set arr_seq)
    (higher_eq_priority : FP_policy sporadic_task)
    (H_respects_affinity : respects_affinity job_task sched alpha)
    (H_work_conserving : apa_work_conserving job_arrival job_cost job_task arr_seq sched alpha)
    (H_respects_FP_policy : respects_FP_policy_under_weak_APA job_arrival job_cost job_task arr_seq
      sched alpha higher_eq_priority)
    (tsk : sporadic_task) (task_in_ts : tsk ∈ ts)
    (alpha' : task_affinity sporadic_task num_cpus)
    (H_affinity_subset : ∀ tsk0 : sporadic_task, tsk0 ∈ ts →
      is_subaffinity (alpha' tsk0) (alpha tsk0))
    (H_at_least_one_cpu : ∀ tsk0 : sporadic_task, tsk0 ∈ ts →
      0 < (Finset.univ.filter (fun x => x ∈ alpha' tsk0)).card)
    (hp_bounds : List (sporadic_task × time))
    (H_response_time_of_interfering_tasks_is_known : ∀ (hp_tsk : sporadic_task) (R : time),
      (hp_tsk, R) ∈ hp_bounds →
      is_response_time_bound_of_task job_arrival job_cost job_task arr_seq sched hp_tsk R)
    (H_hp_bounds_has_interfering_tasks : ∀ hp_tsk : sporadic_task, hp_tsk ∈ ts →
      higher_priority_task_in alpha higher_eq_priority tsk (alpha tsk) hp_tsk = true →
      ∃ R : time, (hp_tsk, R) ∈ hp_bounds)
    (H_response_time_bounds_ge_cost : ∀ (hp_tsk : sporadic_task) (R : time),
      (hp_tsk, R) ∈ hp_bounds → task_cost hp_tsk ≤ R)
    (H_interfering_tasks_miss_no_deadlines : ∀ (hp_tsk : sporadic_task) (R : time),
      (hp_tsk, R) ∈ hp_bounds → R ≤ task_deadline hp_tsk)
    (R : time)
    (H_response_time_recurrence_holds :
      R = task_cost tsk +
        div_floor (total_interference_bound_fp task_cost task_period task_deadline alpha tsk
          (alpha' tsk) hp_bounds R higher_eq_priority)
          (Finset.univ.filter (fun x => x ∈ alpha' tsk)).card)
    (H_response_time_no_larger_than_deadline : R ≤ task_deadline tsk),
    is_response_time_bound_of_task job_arrival job_cost job_task arr_seq sched tsk R

end CaseStudies.RTAS2015.Lemma8.ResponseTimeAnalysisFP
