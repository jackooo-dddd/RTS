-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: analysis/definitions/readiness.v

import Prosa.Behavior.Ready
import Prosa.Analysis.Definitions.SchedulePrefix
import Prosa.Model.Preemption.Parameter
import Prosa.Model.Priority.Classes
import Prosa.Model.Task.Sequentiality

namespace Prosa.Analysis.Definitions.Readiness

open Prosa.Behavior.Arrival_sequence
open Prosa.Behavior.Job
open Prosa.Behavior.Schedule
open Prosa.Behavior.Service
open Prosa.Behavior.Ready
open Prosa.Behavior.Time
open Prosa.Model.Task.Concept
open Prosa.Model.Task.Sequentiality
open Prosa.Model.Preemption.Parameter
open Prosa.Analysis.Definitions.SchedulePrefix

/-! Representation notes: the readiness model is passed explicitly (as in
the elaborated types); `~~ b` is `!b`; Booleans in `Prop` position are
`= true`; the Boolean readiness equality is `Bool` equality. -/

/-- A readiness model is non-clairvoyant if readiness depends only on the
schedule prefix. -/
def nonclairvoyant_readiness {Job : JobType} [DecidableEq Job] [JobCost Job] [JobArrival Job]
    {PState : ProcessorState Job} (ReadinessModel : JobReady Job PState) : Prop :=
  ∀ (sched sched' : schedule PState) (j : Job) (h : instant),
    identical_prefix sched sched' h →
      ∀ t, t ≤ h → ReadinessModel.job_ready sched j t = ReadinessModel.job_ready sched' j t

/-- A nonpreemptive job remains ready. -/
noncomputable def valid_nonpreemptive_readiness {Job : JobType} [DecidableEq Job] [JobCost Job]
    [JobArrival Job] {PState : ProcessorState Job} (ReadinessModel : JobReady Job PState)
    [JobPreemptable Job] (sched : schedule PState) : Prop :=
  ∀ (j : Job) (t : instant),
    (!job_preemptable j (service sched j t)) = true → ReadinessModel.job_ready sched j t = true

/-- A readiness model is sequential if only a task's earliest incomplete job
is ready. -/
noncomputable def sequential_readiness {Job : JobType} [DecidableEq Job] [JobCost Job]
    [JobArrival Job] {PState : ProcessorState Job} (ReadinessModel : JobReady Job PState)
    {Task : TaskType} [DecidableEq Task] [JobTask Job Task] (arr_seq : arrival_sequence Job) :
    Prop :=
  ∀ (sched : schedule PState) (j : Job) (t : instant),
    ReadinessModel.job_ready sched j t = true → prior_jobs_complete (Task := Task) arr_seq sched j t = true

end Prosa.Analysis.Definitions.Readiness
