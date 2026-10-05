-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: model/preemption/limited_preemptive.v

import Prosa.Model.Preemption.Parameter

namespace Prosa.Model.Preemption.LimitedPreemptive

open Prosa.Behavior.Arrival_sequence
open Prosa.Behavior.Job
open Prosa.Behavior.Time
open Prosa.Model.Preemption.Parameter
open Prosa.Util.List
open Prosa.Util.Nondecreasing

/-! Representation notes: `seq work` is `List work`; `ρ \in s` is
`decide (ρ ∈ s) = true` (a Boolean in `Prop` position); `last0` and
`nondecreasing_sequence` are the accepted utilities. Binder orders follow the
elaborated types (unused section context such as `JobArrival` is absent). -/

/-- Job parameter: the progress values at which a job can be preempted. -/
class JobPreemptionPoints (Job : JobType) [DecidableEq Job] where
  job_preemptive_points : Job → List work

export JobPreemptionPoints (job_preemptive_points)

/-- The source's section-local instance `limited_preemptive_job_model`: a job
is preemptable exactly at its preemption points. Its instance registration is
section-local in the source, so here it is a plain definition that later
translations enable locally. -/
@[reducible] def limited_preemptive_job_model {Job : JobType} [DecidableEq Job]
    [JobPreemptionPoints Job] : JobPreemptable Job where
  job_preemptable j ρ := decide (ρ ∈ job_preemptive_points j)

section ValidLimitedPreemptiveModel

variable {Job : JobType} [DecidableEq Job]

/-- Every arriving job has a preemption point at progress `0`. -/
def beginning_of_execution_in_preemption_points [JobPreemptionPoints Job]
    (arr_seq : arrival_sequence Job) : Prop :=
  ∀ j, arrives_in arr_seq j → decide (0 ∈ job_preemptive_points j) = true

/-- The last preemption point of every arriving job is its cost. -/
def end_of_execution_in_preemption_points [JobCost Job] [JobPreemptionPoints Job]
    (arr_seq : arrival_sequence Job) : Prop :=
  ∀ j, arrives_in arr_seq j → last0 (job_preemptive_points j) = job_cost j

/-- The preemption points of every arriving job form a nondecreasing sequence. -/
def preemption_points_is_nondecreasing_sequence [JobPreemptionPoints Job]
    (arr_seq : arrival_sequence Job) : Prop :=
  ∀ j, arrives_in arr_seq j → nondecreasing_sequence (job_preemptive_points j)

/-- A valid limited-preemptive job model satisfies the three properties. -/
def valid_limited_preemptions_job_model [JobCost Job] [JobPreemptionPoints Job]
    (arr_seq : arrival_sequence Job) : Prop :=
  beginning_of_execution_in_preemption_points arr_seq ∧
  end_of_execution_in_preemption_points arr_seq ∧
  preemption_points_is_nondecreasing_sequence arr_seq

end ValidLimitedPreemptiveModel

end Prosa.Model.Preemption.LimitedPreemptive
