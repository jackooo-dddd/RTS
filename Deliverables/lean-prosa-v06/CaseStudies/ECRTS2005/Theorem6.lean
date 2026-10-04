-- Case study 2005-ECRTS-Theorem6: Bertogna, Cirinei, Lipari — Improved Schedulability Analysis of EDF on Multiprocessor Platforms (ECRTS 2005).
-- Original Rocq statement: RTS_Papers/2005-ECRTS-Theorem6/Theorem6.v.
-- Benchmark file: read-only.  Prove `CaseStudies.ECRTS2005.Theorem6.SchedulabilityAnalysisEDF.Theorem6_05_statement` in `Solutions/ECRTS2005/Theorem6.lean`.
import Prosa.Util.Sum
import Prosa.Classic.Model.Arrival.Basic.Task
import Prosa.Classic.Model.Arrival.Basic.Job
import Prosa.Classic.Model.Arrival.Basic.TaskArrival
import Prosa.Classic.Model.Priority
import Prosa.Classic.Model.Schedule.Global.Schedulability
import Prosa.Classic.Model.Schedule.Global.Basic.Schedule
import Prosa.Classic.Model.Schedule.Global.Basic.Platform
import Prosa.Classic.Model.Schedule.Global.Basic.Interference

/-!
Theorem 6 of ECRTS 2005 as stated by the case study (Rocq module `SchedulabilityAnalysisEDF`,
section `Theorem6_05`): under the stated hypotheses (Lemma 5 and Lemma 4 of the paper are assumed as
hypotheses `Lemma5_05` and `H_Lemma4_05`, and a worst-case job of each task is given), the task set
is schedulable **iff** every task satisfies the theorem's condition. The source states an
equivalence; it is translated as written.

Representation notes: `\sum_(x <- ts | x != tsk) F x` is `sumFiltered ts.val (fun x => !decide (x =
tsk)) F`; `PeanoNat.Nat.min` is `min`; the Boolean definition `theorem6_first_condition` (a `<`
test) is a `Bool`, used as `= true` in proposition position; `uniq ts` is `ts.val.Nodup`; the
section-local `Let total_interference_in_job_window` is unfolded. Binder lists follow the Rocq
original.
-/

set_option linter.unusedVariables false

namespace CaseStudies.ECRTS2005.Theorem6.SchedulabilityAnalysisEDF

open Prosa.Classic.Model.Time.Time
open Prosa.Classic.Model.Arrival.Basic.ArrivalSequence.ArrivalSequence
open Prosa.Classic.Model.Arrival.Basic.Task.SporadicTaskset
open Prosa.Classic.Model.Arrival.Basic.Job.Job
open Prosa.Classic.Model.Arrival.Basic.TaskArrival.TaskArrival
open Prosa.Classic.Model.Priority.Priority
open Prosa.Classic.Model.Schedule.Global.Basic.Schedule.Schedule
open Prosa.Classic.Model.Schedule.Global.Schedulability.Schedulability
open Prosa.Classic.Model.Schedule.Global.Basic.Platform.Platform
open Prosa.Classic.Model.Schedule.Global.Basic.Interference.Interference
open Prosa.Util.Sum (sumFiltered)

universe u v

def cumulative_task_interference {sporadic_task : Type u} {Job : Type v}
    [DecidableEq sporadic_task] [DecidableEq Job] (job_arrival job_cost : Job → time)
    (job_task : Job → sporadic_task) (ts : taskset_of sporadic_task) (num_cpus : Nat)
    (sched : schedule Job num_cpus) (j : Job) (a b : time) (tsk : sporadic_task) : Nat :=
  sumFiltered ts.val (fun tsk_other => !decide (tsk_other = tsk))
    (fun tsk_other => task_interference job_arrival job_cost job_task sched j tsk_other a b)

def slack {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost task_deadline : sporadic_task → time) (tsk : sporadic_task) : Nat :=
  task_deadline tsk - task_cost tsk

def task_interference_in_worst_case_window {sporadic_task : Type u} {Job : Type v}
    [DecidableEq sporadic_task] [DecidableEq Job] (job_arrival job_cost job_deadline : Job → time)
    (job_task : Job → sporadic_task) (num_cpus : Nat) (sched : schedule Job num_cpus)
    (worst_case_job_of_task : sporadic_task → Job) (tsk_other tsk : sporadic_task) : Nat :=
  let j := worst_case_job_of_task tsk
  task_interference job_arrival job_cost job_task sched j tsk_other
    (job_arrival j) (job_arrival j + job_deadline j)

def truncated_task_interference_sum {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost task_deadline : sporadic_task → time) {Job : Type v} [DecidableEq Job]
    (job_arrival job_cost job_deadline : Job → time) (job_task : Job → sporadic_task)
    (ts : taskset_of sporadic_task) (num_cpus : Nat) (sched : schedule Job num_cpus)
    (worst_case_job_of_task : sporadic_task → Job) (tsk : sporadic_task) : Nat :=
  sumFiltered ts.val (fun tsk_other => !decide (tsk_other = tsk))
    (fun tsk_other => min
      (task_interference_in_worst_case_window job_arrival job_cost job_deadline job_task num_cpus
        sched worst_case_job_of_task tsk_other tsk)
      (slack task_cost task_deadline tsk))

def theorem6_first_condition {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost task_deadline : sporadic_task → time) {Job : Type v} [DecidableEq Job]
    (job_arrival job_cost job_deadline : Job → time) (job_task : Job → sporadic_task)
    (ts : taskset_of sporadic_task) (num_cpus : Nat) (sched : schedule Job num_cpus)
    (worst_case_job_of_task : sporadic_task → Job) (tsk : sporadic_task) : Bool :=
  decide (truncated_task_interference_sum task_cost task_deadline job_arrival job_cost job_deadline
      job_task ts num_cpus sched worst_case_job_of_task tsk <
    num_cpus * slack task_cost task_deadline tsk)

def theorem6_second_condition {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost task_deadline : sporadic_task → time) {Job : Type v} [DecidableEq Job]
    (job_arrival job_cost job_deadline : Job → time) (job_task : Job → sporadic_task)
    (ts : taskset_of sporadic_task) (num_cpus : Nat) (sched : schedule Job num_cpus)
    (worst_case_job_of_task : sporadic_task → Job) (tsk : sporadic_task) : Prop :=
  truncated_task_interference_sum task_cost task_deadline job_arrival job_cost job_deadline
      job_task ts num_cpus sched worst_case_job_of_task tsk =
    num_cpus * slack task_cost task_deadline tsk ∧
  ∃ tsk_h : sporadic_task,
    tsk_h ∈ ts ∧
    (!decide (tsk_h = tsk)) = true ∧
    0 < task_interference_in_worst_case_window job_arrival job_cost job_deadline job_task num_cpus
          sched worst_case_job_of_task tsk_h tsk ∧
    task_interference_in_worst_case_window job_arrival job_cost job_deadline job_task num_cpus
        sched worst_case_job_of_task tsk_h tsk ≤ slack task_cost task_deadline tsk

def theorem6_task_condition {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost task_deadline : sporadic_task → time) {Job : Type v} [DecidableEq Job]
    (job_arrival job_cost job_deadline : Job → time) (job_task : Job → sporadic_task)
    (ts : taskset_of sporadic_task) (num_cpus : Nat) (sched : schedule Job num_cpus)
    (worst_case_job_of_task : sporadic_task → Job) (tsk : sporadic_task) : Prop :=
  theorem6_first_condition task_cost task_deadline job_arrival job_cost job_deadline job_task ts
      num_cpus sched worst_case_job_of_task tsk = true ∨
    theorem6_second_condition task_cost task_deadline job_arrival job_cost job_deadline job_task
      ts num_cpus sched worst_case_job_of_task tsk

def taskset_schedulable {sporadic_task : Type u} {Job : Type v} [DecidableEq sporadic_task]
    [DecidableEq Job] (job_arrival job_cost job_deadline : Job → time)
    (job_task : Job → sporadic_task) (arr_seq : arrival_sequence Job)
    (ts : taskset_of sporadic_task) (num_cpus : Nat) (sched : schedule Job num_cpus) : Prop :=
  ∀ tsk : sporadic_task, tsk ∈ ts →
    task_misses_no_deadline job_arrival job_cost job_deadline job_task arr_seq sched tsk

/-- The statement of the case study's theorem `Theorem6_05`. -/
def Theorem6_05_statement : Prop :=
  ∀ {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost task_period task_deadline : sporadic_task → time)
    {Job : Type v} [DecidableEq Job] (job_arrival job_cost job_deadline : Job → time)
    (job_task : Job → sporadic_task) (arr_seq : arrival_sequence Job)
    (H_valid_job_parameters : ∀ j : Job, arrives_in arr_seq j →
      0 < job_cost j ∧ job_cost j < job_deadline j ∧ 0 < job_deadline j ∧
        job_deadline j = task_deadline (job_task j) ∧ job_cost j = task_cost (job_task j))
    (ts : taskset_of sporadic_task)
    (H_valid_task_parameters : valid_sporadic_taskset task_cost task_period task_deadline ts.val)
    (H_sporadic_tasks : sporadic_task_model task_period job_arrival job_task arr_seq)
    (H_all_jobs_from_taskset : ∀ j : Job, arrives_in arr_seq j → job_task j ∈ ts)
    (num_cpus : Nat) (sched : schedule Job num_cpus)
    (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute job_arrival sched)
    (H_jobs_come_from_arrival_sequence : jobs_come_from_arrival_sequence sched arr_seq)
    (H_sequential_jobs : sequential_jobs sched)
    (H_at_least_one_cpu : 0 < num_cpus)
    (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched)
    (H_arrival_times_are_consistent : arrival_times_are_consistent job_arrival arr_seq)
    (H_no_duplicate_arrivals : arrival_sequence_is_a_set arr_seq)
    (H_work_conserving : work_conserving job_arrival job_cost arr_seq sched)
    (uniq_ts : ts.val.Nodup)
    (H_edf_policy : respects_JLFP_policy job_arrival job_cost arr_seq sched
      (EDF job_arrival job_deadline))
    (H_constrained_deadlines : ∀ tsk : sporadic_task, tsk ∈ ts → task_deadline tsk ≤ task_period tsk)
    (H_positive_slack : ∀ tsk : sporadic_task, tsk ∈ ts → task_cost tsk < task_deadline tsk)
    (Lemma5_05 : ∀ (j : Job) (a b : time) (tsk : sporadic_task),
      tsk ∈ ts → arrives_in arr_seq j → job_task j = tsk →
      cumulative_task_interference job_arrival job_cost job_task ts num_cpus sched j a b tsk =
        num_cpus * total_interference job_arrival job_cost sched j a b)
    (H_Lemma4_05 : ∀ (tsk_k : sporadic_task) (j : Job) (a b : time) (c : Nat),
      tsk_k ∈ ts → arrives_in arr_seq j → job_task j = tsk_k →
      (c ≤ total_interference job_arrival job_cost sched j a b ↔
        num_cpus * c ≤ sumFiltered ts.val (fun tsk_other => !decide (tsk_other = tsk_k))
          (fun tsk_other =>
            min (task_interference job_arrival job_cost job_task sched j tsk_other a b) c)))
    (worst_case_job_of_task : sporadic_task → Job)
    (H_worst_case_job_arrives : ∀ tsk : sporadic_task, tsk ∈ ts →
      arrives_in arr_seq (worst_case_job_of_task tsk))
    (H_worst_case_job_of_task : ∀ tsk : sporadic_task, tsk ∈ ts →
      job_task (worst_case_job_of_task tsk) = tsk)
    (H_worst_case_interference : ∀ (tsk : sporadic_task) (j : Job),
      tsk ∈ ts → arrives_in arr_seq j → job_task j = tsk →
      total_interference job_arrival job_cost sched j (job_arrival j)
          (job_arrival j + job_deadline j) ≤
        total_interference job_arrival job_cost sched (worst_case_job_of_task tsk)
          (job_arrival (worst_case_job_of_task tsk))
          (job_arrival (worst_case_job_of_task tsk) + job_deadline (worst_case_job_of_task tsk))),
    taskset_schedulable job_arrival job_cost job_deadline job_task arr_seq ts num_cpus sched ↔
      ∀ tsk : sporadic_task, tsk ∈ ts →
        theorem6_task_condition task_cost task_deadline job_arrival job_cost job_deadline job_task
          ts num_cpus sched worst_case_job_of_task tsk

end CaseStudies.ECRTS2005.Theorem6.SchedulabilityAnalysisEDF
