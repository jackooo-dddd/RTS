-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: analysis/definitions/interference.v

import Prosa.Analysis.Definitions.Service
import Prosa.Model.Aggregate.Workload

namespace Prosa.Analysis.Definitions.Interference

open Prosa.Behavior.Arrival_sequence
open Prosa.Behavior.Job
open Prosa.Behavior.Schedule
open Prosa.Behavior.Service
open Prosa.Behavior.Time
open Prosa.Model.Task.Concept
open Prosa.Model.Priority.Definitions
open Prosa.Analysis.Definitions.Service
open Prosa.Util.Sum

/-! Representation notes: MathComp's `has p s` is `s.any p`; `p^~ j` is
`fun x => p x j`; `a != b` is `decide (a ≠ b)`; a Boolean summand
`\sum_(t1 <= t < t2) b t` is `sumSeq (List.range' t1 (t2 - t1)) (fun t => (b t).toNat)`;
`\sum_(x <- s | P x) F x` is `sumFiltered s P F`. Binder orders follow the
elaborated types (section context absent where a definition does not use it). -/

section FPDefinitions

/-- Job `j` incurs interference from a strictly higher-priority task at `t`. -/
noncomputable def hp_task_interference {Task : TaskType} [DecidableEq Task] {Job : JobType}
    [DecidableEq Job] [JobTask Job Task] {PState : ProcessorState Job}
    (arr_seq : arrival_sequence Job) (sched : schedule PState) [FP : FP_policy Task]
    (j : Job) (t : instant) : Bool :=
  (arrivals_up_to arr_seq t).any (fun jhp =>
    hp_task (FP := FP) (job_task (Task := Task) jhp) (job_task (Task := Task) j) &&
      receives_service_at sched jhp t)

/-- Higher-or-equal-priority jobs of equal-priority tasks. -/
def ep_task_hep_job {Task : TaskType} [DecidableEq Task] {Job : JobType} [DecidableEq Job]
    [JobTask Job Task] [FP : FP_policy Task] [JLFP_policy Job] (j1 j2 : Job) : Bool :=
  hep_job j1 j2 && ep_task (FP := FP) (job_task (Task := Task) j1) (job_task (Task := Task) j2)

/-- ... that do not stem from the same task. -/
def other_ep_task_hep_job {Task : TaskType} [DecidableEq Task] {Job : JobType} [DecidableEq Job]
    [JobTask Job Task] [FP : FP_policy Task] [JLFP_policy Job] (j1 j2 : Job) : Bool :=
  ep_task_hep_job (Task := Task) j1 j2 &&
    decide (job_task (Task := Task) j1 ≠ job_task (Task := Task) j2)

/-- Interference from higher-or-equal-priority jobs of other equal-priority tasks. -/
noncomputable def hep_job_from_other_ep_task_interference {Task : TaskType} [DecidableEq Task]
    {Job : JobType} [DecidableEq Job] [JobTask Job Task] {PState : ProcessorState Job}
    (arr_seq : arrival_sequence Job) (sched : schedule PState) [FP : FP_policy Task] [JLFP_policy Job]
    (j : Job) (t : instant) : Bool :=
  (served_jobs_at arr_seq sched t).any (fun x => other_ep_task_hep_job (Task := Task) x j)

/-- Higher-or-equal-priority jobs of strictly higher-priority tasks. -/
def hp_task_hep_job {Task : TaskType} [DecidableEq Task] {Job : JobType} [DecidableEq Job]
    [JobTask Job Task] [FP : FP_policy Task] [JLFP_policy Job] : Job → Job → Bool :=
  fun j1 j2 => hep_job j1 j2 && hp_task (FP := FP) (job_task (Task := Task) j1) (job_task (Task := Task) j2)

/-- Interference from higher-or-equal-priority jobs of strictly higher-priority tasks. -/
noncomputable def hep_job_from_hp_task_interference {Task : TaskType} [DecidableEq Task]
    {Job : JobType} [DecidableEq Job] [JobTask Job Task] {PState : ProcessorState Job}
    (arr_seq : arrival_sequence Job) (sched : schedule PState) [FP : FP_policy Task] [JLFP_policy Job]
    (j : Job) (t : instant) : Bool :=
  (served_jobs_at arr_seq sched t).any (fun x => hp_task_hep_job (Task := Task) x j)

/-- Cumulative interference from higher-or-equal-priority jobs of higher-priority tasks. -/
noncomputable def cumulative_interference_from_hep_jobs_from_hp_tasks {Task : TaskType}
    [DecidableEq Task] {Job : JobType} [DecidableEq Job] [JobTask Job Task]
    {PState : ProcessorState Job} (arr_seq : arrival_sequence Job) (sched : schedule PState)
    [FP : FP_policy Task] [JLFP_policy Job] (j : Job) (t1 t2 : instant) : Nat :=
  sumSeq (List.range' t1 (t2 - t1))
    (fun t => (hep_job_from_hp_task_interference (Task := Task) arr_seq sched j t).toNat)

/-- Cumulative interference from higher-or-equal-priority jobs of other equal-priority tasks. -/
noncomputable def cumulative_interference_from_hep_jobs_from_other_ep_tasks {Task : TaskType}
    [DecidableEq Task] {Job : JobType} [DecidableEq Job] [JobTask Job Task]
    {PState : ProcessorState Job} (arr_seq : arrival_sequence Job) (sched : schedule PState)
    [FP : FP_policy Task] [JLFP_policy Job] (j : Job) (t1 t2 : instant) : Nat :=
  sumSeq (List.range' t1 (t2 - t1))
    (fun t => (hep_job_from_other_ep_task_interference (Task := Task) arr_seq sched j t).toNat)

end FPDefinitions

section JLFPDefinitions

/-- Interference from another higher-or-equal-priority job at `t`. -/
noncomputable def another_hep_job_interference {Job : JobType} [DecidableEq Job]
    {PState : ProcessorState Job} (arr_seq : arrival_sequence Job) (sched : schedule PState)
    [JLFP_policy Job] (j : Job) (t : instant) : Bool :=
  (served_jobs_at arr_seq sched t).any (fun x => another_hep_job x j)

/-- Interference from a higher-or-equal-priority job of another task at `t`. -/
noncomputable def another_task_hep_job_interference {Task : TaskType} [DecidableEq Task]
    {Job : JobType} [DecidableEq Job] [JobTask Job Task] {PState : ProcessorState Job}
    (arr_seq : arrival_sequence Job) (sched : schedule PState) [JLFP_policy Job]
    (j : Job) (t : instant) : Bool :=
  (served_jobs_at arr_seq sched t).any (fun x => another_task_hep_job (Task := Task) x j)

/-- Interference from another higher-or-equal-priority job of the same task at `t`. -/
noncomputable def another_hep_job_of_same_task_interference {Task : TaskType} [DecidableEq Task]
    {Job : JobType} [DecidableEq Job] [JobTask Job Task] {PState : ProcessorState Job}
    (arr_seq : arrival_sequence Job) (sched : schedule PState) [JLFP_policy Job]
    (j : Job) (t : instant) : Bool :=
  (arrivals_up_to arr_seq t).any (fun jhp =>
    another_hep_job_of_same_task (Task := Task) jhp j && receives_service_at sched jhp t)

/-- Workload released at `t` by other higher-or-equal-priority jobs. -/
def other_hep_jobs_interfering_workload {Job : JobType} [DecidableEq Job] [JobCost Job]
    (arr_seq : arrival_sequence Job) [JLFP_policy Job] (j : Job) (t : instant) : Nat :=
  sumFiltered (arrivals_at arr_seq t) (fun jhp => another_hep_job jhp j) (fun jhp => job_cost jhp)

/-- Cumulative interference from other higher-or-equal-priority jobs. -/
noncomputable def cumulative_another_hep_job_interference {Job : JobType} [DecidableEq Job]
    {PState : ProcessorState Job} (arr_seq : arrival_sequence Job) (sched : schedule PState)
    [JLFP_policy Job] (j : Job) (t1 t2 : instant) : Nat :=
  sumSeq (List.range' t1 (t2 - t1)) (fun t => (another_hep_job_interference arr_seq sched j t).toNat)

/-- Cumulative interference from higher-or-equal-priority jobs of other tasks. -/
noncomputable def cumulative_another_task_hep_job_interference {Task : TaskType}
    [DecidableEq Task] {Job : JobType} [DecidableEq Job] [JobTask Job Task]
    {PState : ProcessorState Job} (arr_seq : arrival_sequence Job) (sched : schedule PState)
    [JLFP_policy Job] (j : Job) (t1 t2 : instant) : Nat :=
  sumSeq (List.range' t1 (t2 - t1))
    (fun t => (another_task_hep_job_interference (Task := Task) arr_seq sched j t).toNat)

/-- Cumulative interfering workload of other higher-or-equal-priority jobs. -/
def cumulative_other_hep_jobs_interfering_workload {Job : JobType} [DecidableEq Job]
    [JobCost Job] (arr_seq : arrival_sequence Job) [JLFP_policy Job] (j : Job)
    (t1 t2 : instant) : Nat :=
  sumSeq (List.range' t1 (t2 - t1)) (fun t => other_hep_jobs_interfering_workload arr_seq j t)

end JLFPDefinitions

end Prosa.Analysis.Definitions.Interference
