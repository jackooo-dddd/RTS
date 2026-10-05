-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: model/schedule/priority_driven.v

import Prosa.Model.Priority.Classes
import Prosa.Model.Schedule.PreemptionTime

namespace Prosa.Model.Schedule.PriorityDriven

open Prosa.Behavior.Arrival_sequence
open Prosa.Behavior.Job
open Prosa.Behavior.Ready
open Prosa.Behavior.Schedule
open Prosa.Behavior.Service
open Prosa.Model.Task.Concept
open Prosa.Model.Priority.Definitions
open Prosa.Model.Priority.Coercion
open Prosa.Model.Preemption.Parameter
open Prosa.Model.Schedule.PreemptionTime

/-! Representation notes: a Boolean in `Prop` position is `= true`; the
source's canonical conversions of a JLFP policy to a JLDP policy and of an
FP policy to a JLFP policy are the accepted `JLFP_to_JLDP` and `FP_to_JLFP`,
passed explicitly. Binder orders follow the elaborated types. -/

section Priority

variable {Task : TaskType} [DecidableEq Task] {Job : JobType} [DecidableEq Job]
variable [JobTask Job Task] [JobArrival Job] [JobCost Job]
variable {PState : ProcessorState Job} [JobPreemptable Job] [jr : JobReady Job PState]
variable (arr_seq : arrival_sequence Job) (sched : schedule PState)

/-- At every preemption time, the scheduled job has higher-or-equal priority
than every backlogged job. -/
def respects_JLDP_policy_at_preemption_point (policy : JLDP_policy Job) : Prop :=
  ∀ j j_hp t, arrives_in arr_seq j → preemption_time arr_seq sched t = true →
    backlogged sched j t = true → scheduled_at sched j_hp t = true →
      policy.hep_job_at t j_hp j = true

/-- The JLFP version, through the canonical JLDP conversion. -/
def respects_JLFP_policy_at_preemption_point (policy : JLFP_policy Job) : Prop :=
  respects_JLDP_policy_at_preemption_point arr_seq sched (JLFP_to_JLDP (JLFP := policy))

/-- The FP version, through the canonical JLFP and JLDP conversions. -/
def respects_FP_policy_at_preemption_point (policy : FP_policy Task) : Prop :=
  respects_JLDP_policy_at_preemption_point arr_seq sched
    (JLFP_to_JLDP (JLFP := FP_to_JLFP (Task := Task) policy))

end Priority

end Prosa.Model.Schedule.PriorityDriven
