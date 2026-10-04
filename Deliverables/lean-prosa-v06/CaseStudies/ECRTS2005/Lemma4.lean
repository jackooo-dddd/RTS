-- Case study 2005-ECRTS-Lemma4: Bertogna, Cirinei, Lipari — Improved Schedulability Analysis of EDF on Multiprocessor Platforms (ECRTS 2005).
-- Original Rocq statement: RTS_Papers/2005-ECRTS-Lemma4/Lemma4.v.
-- Benchmark file: read-only.  Prove `CaseStudies.ECRTS2005.Lemma4.ResponseTimeAnalysisEDF.Lemma4_05_statement` in `Solutions/ECRTS2005/Lemma4.lean`.
import Prosa.Util.Sum
import Prosa.Classic.Model.Arrival.Basic.Task
import Prosa.Classic.Model.Arrival.Basic.Job
import Prosa.Classic.Model.Arrival.Basic.TaskArrival
import Prosa.Classic.Model.Priority
import Prosa.Classic.Model.Schedule.Global.Basic.Schedule
import Prosa.Classic.Model.Schedule.Global.Basic.Platform
import Prosa.Classic.Model.Schedule.Global.Basic.Interference

/-!
Lemma 4 of ECRTS 2005: the total interference on a job of `tsk` in `[a, b)` is at least `c` iff the
interferences of the other tasks, each truncated at `c`, sum to at least `m c` (Rocq module
`ResponseTimeAnalysisEDF`, section `Lemma4_05`). The case study assumes Lemma 3 as the hypothesis
`Lemma_05` and adds the hypothesis `H_sequential_tasks`.

Representation notes: `\sum_(x <- ts | x != tsk) F x` is `sumFiltered ts.val (fun x => !decide (x =
tsk)) F`; `PeanoNat.Nat.min` is `min`; Boolean predicates in proposition position are `= true`.
Binder lists follow the Rocq original.
-/

set_option linter.unusedVariables false

namespace CaseStudies.ECRTS2005.Lemma4.ResponseTimeAnalysisEDF

open Prosa.Classic.Model.Time.Time
open Prosa.Classic.Model.Arrival.Basic.ArrivalSequence.ArrivalSequence
open Prosa.Classic.Model.Arrival.Basic.Task.SporadicTaskset
open Prosa.Classic.Model.Arrival.Basic.Job.Job
open Prosa.Classic.Model.Arrival.Basic.TaskArrival.TaskArrival
open Prosa.Classic.Model.Priority.Priority
open Prosa.Classic.Model.Schedule.Global.Basic.Schedule.Schedule
open Prosa.Classic.Model.Schedule.Global.Basic.Platform.Platform
open Prosa.Classic.Model.Schedule.Global.Basic.Interference.Interference
open Prosa.Util.Sum (sumFiltered)

universe u v

def cumulative_task_interference {sporadic_task : Type u} {Job : Type v}
    [DecidableEq sporadic_task] [DecidableEq Job] (job_arrival job_cost : Job → time)
    (job_task : Job → sporadic_task) (ts : taskset_of sporadic_task) (num_cpus : Nat)
    (sched : schedule Job num_cpus) (tsk : sporadic_task) (j : Job) (a b : time) : Nat :=
  sumFiltered ts.val (fun tsk_other => !decide (tsk_other = tsk))
    (fun tsk_other => task_interference job_arrival job_cost job_task sched j tsk_other a b)

/-- The statement of the case study's theorem `Lemma4_05`. -/
def Lemma4_05_statement : Prop :=
  ∀ {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost task_period task_deadline : sporadic_task → time)
    {Job : Type v} [DecidableEq Job] (job_arrival job_cost job_deadline : Job → time)
    (job_task : Job → sporadic_task) (arr_seq : arrival_sequence Job)
    (H_valid_job_parameters : ∀ j : Job, arrives_in arr_seq j →
      valid_sporadic_job task_cost task_deadline job_cost job_deadline job_task j)
    (ts : taskset_of sporadic_task)
    (H_valid_task_parameters : valid_sporadic_taskset task_cost task_period task_deadline ts.val)
    (H_sporadic_tasks : sporadic_task_model task_period job_arrival job_task arr_seq)
    (H_all_jobs_from_taskset : ∀ j : Job, arrives_in arr_seq j → job_task j ∈ ts)
    (num_cpus : Nat) (sched : schedule Job num_cpus)
    (H_edf_policy : respects_JLFP_policy job_arrival job_cost arr_seq sched
      (EDF job_arrival job_deadline))
    (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute job_arrival sched)
    (H_jobs_come_from_arrival_sequence : jobs_come_from_arrival_sequence sched arr_seq)
    (H_sequential_jobs : sequential_jobs sched)
    (H_sequential_tasks : ∀ (j1 j2 : Job) (t : time) (cpu : processor num_cpus),
      arrives_in arr_seq j1 → arrives_in arr_seq j2 → job_task j1 = job_task j2 →
      job_arrival j1 < job_arrival j2 → scheduled_on sched j2 cpu t = true →
      completed job_cost sched j1 t = true)
    (H_arrival_times_are_consistent : arrival_times_are_consistent job_arrival arr_seq)
    (H_arr_seq_is_a_set : arrival_sequence_is_a_set arr_seq)
    (H_at_least_one_cpu : 0 < num_cpus)
    (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched)
    (H_work_conserving : work_conserving job_arrival job_cost arr_seq sched)
    (H_constrained_deadlines : ∀ tsk : sporadic_task, tsk ∈ ts → task_deadline tsk ≤ task_period tsk)
    (tsk : sporadic_task) (task_in_ts : tsk ∈ ts)
    (H_previous_jobs_of_tsk_completed : ∀ (j0 : Job) (t : Nat) (j : Job),
      arrives_in arr_seq j0 → arrives_in arr_seq j → job_task j0 = tsk → job_task j = tsk →
      job_arrival j0 < job_arrival j → job_arrival j ≤ t → completed job_cost sched j0 t = true)
    (Lemma_05 : ∀ (j : Job) (a b : time), arrives_in arr_seq j → job_task j = tsk →
        cumulative_task_interference job_arrival job_cost job_task ts num_cpus sched tsk j a b =
          num_cpus * total_interference job_arrival job_cost sched j a b),
    ∀ (j : Job) (a b : time) (c : Nat), arrives_in arr_seq j → job_task j = tsk →
      (c ≤ total_interference job_arrival job_cost sched j a b ↔
        num_cpus * c ≤ sumFiltered ts.val (fun t => !decide (t = tsk))
          (fun t => min (task_interference job_arrival job_cost job_task sched j t a b) c))

end CaseStudies.ECRTS2005.Lemma4.ResponseTimeAnalysisEDF
