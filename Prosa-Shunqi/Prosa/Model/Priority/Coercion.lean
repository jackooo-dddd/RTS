-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: model/priority/coercion.v

import Prosa.Model.Priority.Definitions

namespace Prosa.Model.Priority.Coercion

open Prosa.Behavior.Job
open Prosa.Behavior.Time
open Prosa.Model.Task.Concept
open Prosa.Model.Priority.Definitions

/-- Any FP policy is a JLFP policy that compares the jobs' tasks.

The source declares this as a low-priority instance/coercion.  Lean's
typeclass search cannot determine `Task` from a `JLFP_policy Job` goal (the
source relies on Rocq resolving `JobTask Job ?Task` first), so it is a plain
definition here; the priority is recovered where it is used by naming it. -/
@[instance_reducible] def FP_to_JLFP {Job : JobType} [DecidableEq Job]
    {Task : TaskType} [DecidableEq Task] [tasks : JobTask Job Task]
    (FP : FP_policy Task) : JLFP_policy Job where
  hep_job j1 j2 := FP.hep_task (job_task j1) (job_task j2)

/-- Any JLFP policy is a JLDP policy that ignores the time parameter
(low priority, as in the source). -/
instance (priority := low) JLFP_to_JLDP {Job : JobType} [DecidableEq Job]
    [JLFP : JLFP_policy Job] : JLDP_policy Job where
  hep_job_at _ j1 j2 := JLFP.hep_job j1 j2

theorem hep_job_at_jlfp {Job : JobType} [DecidableEq Job] [JLFP_policy Job] :
    ∀ (j j' : Job) (t : instant), hep_job_at t j j' = hep_job j j' :=
  fun _ _ _ => rfl

theorem hep_job_at_fp {Task : TaskType} [DecidableEq Task]
    {Job : JobType} [DecidableEq Job] [JobTask Job Task] [fp : FP_policy Task] :
    ∀ (j j' : Job) (t : instant),
      @hep_job_at Job _ (JLFP_to_JLDP (JLFP := FP_to_JLFP fp)) t j j' =
        hep_task (job_task (Task := Task) j) (job_task (Task := Task) j') :=
  fun _ _ _ => rfl

theorem reflexive_priorities_FP_implies_JLFP {Task : TaskType} [DecidableEq Task]
    {Job : JobType} [DecidableEq Job] [JobTask Job Task] :
    ∀ fp : FP_policy Task,
      reflexive_task_priorities fp →
        reflexive_job_priorities (FP_to_JLFP (Job := Job) fp) :=
  fun _ h j => h (job_task j)

theorem transitive_priorities_FP_implies_JLFP {Task : TaskType} [DecidableEq Task]
    {Job : JobType} [DecidableEq Job] [JobTask Job Task] :
    ∀ fp : FP_policy Task,
      transitive_task_priorities fp →
        transitive_job_priorities (FP_to_JLFP (Job := Job) fp) :=
  fun _ h y x z hxy hyz => h (job_task y) (job_task x) (job_task z) hxy hyz

theorem total_priorities_FP_implies_JLFP {Task : TaskType} [DecidableEq Task]
    {Job : JobType} [DecidableEq Job] [JobTask Job Task] :
    ∀ fp : FP_policy Task,
      total_task_priorities fp →
        total_job_priorities (FP_to_JLFP (Job := Job) fp) :=
  fun _ h x y => h (job_task x) (job_task y)

theorem reflexive_priorities_JLFP_implies_JLDP {Job : JobType} [DecidableEq Job] :
    ∀ jlfp : JLFP_policy Job,
      reflexive_job_priorities jlfp → reflexive_priorities (JLFP_to_JLDP (JLFP := jlfp)) :=
  fun _ h _ j => h j

theorem transitive_priorities_JLFP_implies_JLDP {Job : JobType} [DecidableEq Job] :
    ∀ jlfp : JLFP_policy Job,
      transitive_job_priorities jlfp → transitive_priorities (JLFP_to_JLDP (JLFP := jlfp)) :=
  fun _ h _ _ _ _ hxy hyz => h _ _ _ hxy hyz

theorem total_priorities_JLFP_implies_JLDP {Job : JobType} [DecidableEq Job] :
    ∀ jlfp : JLFP_policy Job,
      total_job_priorities jlfp → total_priorities (JLFP_to_JLDP (JLFP := jlfp)) :=
  fun _ h _ x y => h x y

end Prosa.Model.Priority.Coercion
