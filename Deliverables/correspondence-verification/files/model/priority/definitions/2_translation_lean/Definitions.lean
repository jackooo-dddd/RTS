-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: model/priority/definitions.v

import Prosa.Model.Task.Concept
import Prosa.Util.Rel
import Prosa.Util.List

namespace Prosa.Model.Priority.Definitions

open Prosa.Behavior.Job
open Prosa.Behavior.Time
open Prosa.Model.Task.Concept

universe u v

/-- A fixed-priority policy compares tasks. -/
class FP_policy (Task : TaskType) [DecidableEq Task] where
  hep_task : Task → Task → Bool

export FP_policy (hep_task)

/-- A job-level fixed-priority policy compares jobs. -/
class JLFP_policy (Job : JobType) [DecidableEq Job] where
  hep_job : Job → Job → Bool

export JLFP_policy (hep_job)

/-- A job-level dynamic-priority policy compares jobs at each instant. -/
class JLDP_policy (Job : JobType) [DecidableEq Job] where
  hep_job_at : instant → Job → Job → Bool

export JLDP_policy (hep_job_at)

section JLDPProperties

variable {Job : JobType} [DecidableEq Job]
variable (JLDP : JLDP_policy Job)

/-- The dynamic job-priority relation is reflexive at every instant. -/
def reflexive_priorities : Prop :=
  ∀ t j, JLDP.hep_job_at t j j = true

/-- The dynamic job-priority relation is transitive at every instant. -/
def transitive_priorities : Prop :=
  ∀ t y x z,
    JLDP.hep_job_at t x y = true →
    JLDP.hep_job_at t y z = true →
    JLDP.hep_job_at t x z = true

/-- The dynamic job-priority relation is total at every instant. -/
def total_priorities : Prop :=
  ∀ t x y, (JLDP.hep_job_at t x y || JLDP.hep_job_at t y x) = true

end JLDPProperties

section JLFPProperties

variable {Job : JobType} [DecidableEq Job]
variable (JLFP : JLFP_policy Job)

/-- The fixed job-priority relation is reflexive. -/
def reflexive_job_priorities : Prop :=
  ∀ j, JLFP.hep_job j j = true

/-- The fixed job-priority relation is transitive. -/
def transitive_job_priorities : Prop :=
  ∀ y x z,
    JLFP.hep_job x y = true →
    JLFP.hep_job y z = true →
    JLFP.hep_job x z = true

/-- The fixed job-priority relation is total. -/
def total_job_priorities : Prop :=
  ∀ x y, (JLFP.hep_job x y || JLFP.hep_job y x) = true

end JLFPProperties

/-- Jobs of the same task respect their arrival order in priority. -/
def policy_respects_sequential_tasks
    {Task : TaskType} [DecidableEq Task]
    {Job : JobType} [DecidableEq Job]
    [JobTask Job Task] [JobArrival Job]
    (JLFP : JLFP_policy Job) : Prop :=
  ∀ j1 j2,
    decide (job_task (Task := Task) j1 = job_task (Task := Task) j2) = true →
    job_arrival j1 ≤ job_arrival j2 →
    JLFP.hep_job j1 j2 = true

/-- Priority is exactly no-later-than arrival order. -/
def policy_is_FIFO
    {Job : JobType} [DecidableEq Job] [JobArrival Job]
    (JLFP : JLFP_policy Job) : Prop :=
  ∀ j1 j2,
    JLFP.hep_job j1 j2 = decide (job_arrival j1 ≤ job_arrival j2)

section FPProperties

variable {Task : TaskType} [DecidableEq Task]
variable (FP : FP_policy Task)

/-- The fixed task-priority relation is reflexive. -/
def reflexive_task_priorities : Prop :=
  ∀ tsk, FP.hep_task tsk tsk = true

/-- The fixed task-priority relation is transitive. -/
def transitive_task_priorities : Prop :=
  ∀ y x z,
    FP.hep_task x y = true →
    FP.hep_task y z = true →
    FP.hep_task x z = true

/-- The fixed task-priority relation is total. -/
def total_task_priorities : Prop :=
  ∀ x y, (FP.hep_task x y || FP.hep_task y x) = true

/-- The task-priority relation is antisymmetric on the given ordered task set. -/
def antisymmetric_over_taskset (ts : List Task) : Prop :=
  Prosa.Util.Rel.antisymmetric_over_list FP.hep_task ts

end FPProperties

section JLFPDerived

variable {Job : JobType} [DecidableEq Job] [JLFP_policy Job]

/-- A distinct job of no lower priority. -/
def another_hep_job (j1 j2 : Job) : Bool :=
  hep_job j1 j2 && decide (j1 ≠ j2)

end JLFPDerived

/-- A no-lower-priority job belonging to another task. -/
def another_task_hep_job
    {Task : TaskType} [DecidableEq Task]
    {Job : JobType} [DecidableEq Job]
    [JobTask Job Task] [JLFP_policy Job]
    (j1 j2 : Job) : Bool :=
  hep_job j1 j2 &&
    decide (job_task (Task := Task) j1 ≠ job_task (Task := Task) j2)

/-- A distinct no-lower-priority job belonging to the same task. -/
def another_hep_job_of_same_task
    {Task : TaskType} [DecidableEq Task]
    {Job : JobType} [DecidableEq Job]
    [JobTask Job Task] [JLFP_policy Job]
    (j1 j2 : Job) : Bool :=
  another_hep_job j1 j2 &&
    decide (job_task (Task := Task) j1 = job_task (Task := Task) j2)

section FPDerived

variable {Task : TaskType} [DecidableEq Task]
variable {FP : FP_policy Task}

/-- Strict priority excludes reverse higher-or-equal priority. -/
def hp_task (tsk1 tsk2 : Task) : Bool :=
  FP.hep_task tsk1 tsk2 && !(FP.hep_task tsk2 tsk1)

/-- Equal priority is higher-or-equal priority in both directions. -/
def ep_task (tsk1 tsk2 : Task) : Bool :=
  FP.hep_task tsk1 tsk2 && FP.hep_task tsk2 tsk1

end FPDerived

end Prosa.Model.Priority.Definitions
