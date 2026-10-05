-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: implementation/definitions/ideal_uni_scheduler.v

import Prosa.Implementation.Definitions.GenericScheduler
import Prosa.Model.Processor.Ideal
import Prosa.Model.Preemption.Parameter
import Prosa.Model.Schedule.WorkConserving
import Prosa.Model.Priority.Classes
import Prosa.Util.Supremum

namespace Prosa.Implementation.Definitions.IdealUniScheduler

open Prosa.Behavior.Arrival_sequence
open Prosa.Behavior.Job
open Prosa.Behavior.Ready
open Prosa.Behavior.Schedule
open Prosa.Behavior.Service
open Prosa.Behavior.Time
open Prosa.Model.Processor.Ideal
open Prosa.Model.Preemption.Parameter
open Prosa.Model.Schedule.WorkConserving
open Prosa.Model.Priority.Definitions
open Prosa.Util.Supremum
open Prosa.Implementation.Definitions.GenericScheduler

/-! The ideal uniprocessor scheduler. Binder orders follow the elaborated types
(each definition takes only the inputs it uses). Representation: the
section-local `PState` is the accepted ideal processor `processor_state Job`
(states `Option Job`) and the section-local idle state is `none`; the Boolean
`if b then x else y` is `bif b then x else y` (a match on the Boolean, as in
the source); `if e is Some j then … else …` is a `match`; `~~ b` is `!b`;
`t.-1` is `t - 1`; the readiness model, the preemption model and the JLDP
policy are instance binders, as in the source's `Context`. -/

section UniprocessorScheduler

variable {Job : JobType} [DecidableEq Job] [JobCost Job] [JobArrival Job]

/-- The job scheduled at the previous instant is still ready and not at a
preemption point. -/
noncomputable def prev_job_nonpreemptive [JobReady Job (processor_state Job)] [JobPreemptable Job]
    (sched_prefix : schedule (processor_state Job)) (t : instant) : Bool :=
  match t with
  | 0 => false
  | t' + 1 =>
    match sched_prefix t' with
    | some j => job_ready sched_prefix j t && !job_preemptable j (service sched_prefix j t)
    | none => false

/-- Continue a nonpreemptive job or let `choose_job` pick among the backlogged jobs. -/
noncomputable def allocation_at (arr_seq : arrival_sequence Job) [JobReady Job (processor_state Job)]
    [JobPreemptable Job] (choose_job : instant → List Job → Option Job)
    (sched_prefix : schedule (processor_state Job)) (t : instant) : Option Job :=
  bif prev_job_nonpreemptive sched_prefix t then
    sched_prefix (t - 1)
  else
    choose_job t (jobs_backlogged_at arr_seq sched_prefix t)

/-- The preemption-model-compliant uniprocessor schedule. -/
noncomputable def pmc_uni_schedule (arr_seq : arrival_sequence Job) [JobReady Job (processor_state Job)]
    [JobPreemptable Job] (choose_job : instant → List Job → Option Job) :
    schedule (processor_state Job) :=
  generic_schedule (allocation_at arr_seq choose_job) none

/-- The highest-priority job of `jobs` at `t`. -/
def choose_highest_prio_job [JLDP_policy Job] (t : instant) (jobs : List Job) : Option Job :=
  supremum (hep_job_at t) jobs

/-- The priority-aware uniprocessor schedule. -/
noncomputable def uni_schedule (arr_seq : arrival_sequence Job) [JobReady Job (processor_state Job)]
    [JobPreemptable Job] [JLDP_policy Job] : schedule (processor_state Job) :=
  pmc_uni_schedule arr_seq choose_highest_prio_job

end UniprocessorScheduler

end Prosa.Implementation.Definitions.IdealUniScheduler
