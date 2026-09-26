-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: model/preemption/parameter.v

import Prosa.Util.All
import Prosa.Behavior.All
import Prosa.Model.Priority.Classes

namespace Prosa.Model.Preemption.Parameter

open Prosa.Behavior.Arrival_sequence
open Prosa.Behavior.Job
open Prosa.Behavior.Schedule
open Prosa.Behavior.Service
open Prosa.Behavior.Time
open Prosa.Model.Priority.Definitions
open Prosa.Util.List
open Prosa.Util.Nondecreasing

/-- `omega` after unfolding the time/work aliases. -/
macro "omega'" : tactic => `(tactic| (try dsimp only [instant, duration, work] at *) <;> omega)

/-! Representation notes: `[seq ρ <- s | p ρ]` is `s.filter p`; `range a b`
is the accepted `Prosa.Util.List.range`; `distances`, `max0` and `last0` are
the accepted utilities; `ε` is the numeral `1`; `~~ b` is `!b`; a Boolean in
`Prop` position is `= true`; `ρ \in s` is `decide (ρ ∈ s) = true`; `t.-1` is
`t - 1`. Binder orders follow the elaborated types (unused section context
such as `JobArrival` is absent). -/

/-- Preemption model: whether a job is preemptable at a given progress. -/
class JobPreemptable (Job : JobType) [DecidableEq Job] where
  job_preemptable : Job → work → Bool

export JobPreemptable (job_preemptable)

section MaxAndLastNonpreemptiveSegment

variable {Job : JobType} [DecidableEq Job] [JobCost Job] [JobPreemptable Job]

/-- The progress values at which `j` is preemptable. -/
def job_preemption_points (j : Job) : List work :=
  (range 0 (job_cost j)).filter (fun ρ => job_preemptable j ρ)

/-- The preemption-point list is an equivalent representation. -/
theorem conversion_preserves_equivalence (j : Job) (ρ : work) :
    ρ ≤ job_cost j →
      (job_preemptable j ρ = true ↔ decide (ρ ∈ job_preemption_points j) = true) := by
  intro hle
  simp only [job_preemption_points, range, index_iota, decide_eq_true_eq, List.mem_filter,
    List.mem_range'_1]
  constructor
  · intro h; exact ⟨⟨Nat.zero_le _, by omega'⟩, h⟩
  · intro h; exact h.2

/-- Lengths of the nonpreemptive segments of `j`. -/
def lengths_of_segments (j : Job) : List Nat := distances (job_preemption_points j)

/-- Length of the longest nonpreemptive segment of `j`. -/
def job_max_nonpreemptive_segment (j : Job) : Nat := max0 (lengths_of_segments j)

/-- Length of the last nonpreemptive segment of `j`. -/
def job_last_nonpreemptive_segment (j : Job) : Nat := last0 (lengths_of_segments j)

/-- The run-to-completion threshold of `j`. -/
def job_rtct (j : Job) : Nat := job_cost j - (job_last_nonpreemptive_segment j - 1)

end MaxAndLastNonpreemptiveSegment

section PreemptionModel

/-- `j` is preempted at `t`: scheduled at `t - 1`, not completed and not
scheduled at `t`. -/
noncomputable def preempted_at {Job : JobType} [DecidableEq Job] [JobCost Job]
    {PState : ProcessorState Job} (sched : schedule PState) (j : Job) (t : instant) : Bool :=
  scheduled_at sched j (t - 1) && !completed_by sched j t && !scheduled_at sched j t

/-- A job must execute before it can become nonpreemptive. -/
def job_cannot_become_nonpreemptive_before_execution {Job : JobType} [DecidableEq Job]
    [JobPreemptable Job] (j : Job) : Bool :=
  job_preemptable j 0

/-- A job is preemptable once complete. -/
def job_cannot_be_nonpreemptive_after_completion {Job : JobType} [DecidableEq Job]
    [JobCost Job] [JobPreemptable Job] (j : Job) : Bool :=
  job_preemptable j (job_cost j)

/-- A nonpreemptable job is scheduled. -/
def not_preemptive_implies_scheduled {Job : JobType} [DecidableEq Job] [JobPreemptable Job]
    {PState : ProcessorState Job} (sched : schedule PState) (j : Job) : Prop :=
  ∀ t, (!job_preemptable j (service sched j t)) = true → scheduled_at sched j t = true

/-- Execution starts at a preemption point. -/
def execution_starts_with_preemption_point {Job : JobType} [DecidableEq Job]
    [JobPreemptable Job] {PState : ProcessorState Job} (sched : schedule PState) (j : Job) :
    Prop :=
  ∀ prt, (!scheduled_at sched j prt) = true → scheduled_at sched j (prt + 1) = true →
    job_preemptable j (service sched j (prt + 1)) = true

/-- A valid preemption model satisfies the four properties for every job. -/
def valid_preemption_model {Job : JobType} [DecidableEq Job] [JobCost Job]
    [JobPreemptable Job] {PState : ProcessorState Job} (arr_seq : arrival_sequence Job)
    (sched : schedule PState) : Prop :=
  ∀ j, arrives_in arr_seq j →
    job_cannot_become_nonpreemptive_before_execution j = true ∧
    job_cannot_be_nonpreemptive_after_completion j = true ∧
    not_preemptive_implies_scheduled sched j ∧
    execution_starts_with_preemption_point sched j

/-- Jobs are preempted only by strictly higher-priority jobs. -/
def no_superfluous_preemptions {Job : JobType} [DecidableEq Job] [JobCost Job]
    [JLDP_policy Job] {PState : ProcessorState Job} (sched : schedule PState) : Prop :=
  ∀ t j j_hp, preempted_at sched j t = true → scheduled_at sched j_hp t = true →
    (!hep_job_at t j j_hp) = true

end PreemptionModel

end Prosa.Model.Preemption.Parameter
