-- Translated from: ../rt-proofs/model/schedule/priority_driven.v
import Prosa.Model.Priority.Classes
import Prosa.Model.Schedule.Preemption_time
import Prosa.Model.Processor.Ideal

namespace Prosa.Model.Schedule.Priority_driven

open Prosa.Behavior.Job
open Prosa.Behavior.Time
open Prosa.Behavior.Schedule
open Prosa.Behavior.Service
open Prosa.Behavior.Arrival_sequence
open Prosa.Behavior.Ready
open Prosa.Model.Task.Concept
open Prosa.Model.Preemption.Parameter
open Prosa.Model.Priority.Classes
open Prosa.Model.Schedule.Preemption_time
open Prosa.Model.Processor.Ideal

section Priority

  variable {Task : TaskType}
  variable {Job : JobType} [DecidableEq Job]
  variable [JobTask Job Task]
  variable [JobArrival Job]
  variable [JobCost Job]
  variable [JobPreemptable Job]
  variable [JobReady Job (processor_state Job)]
  variable (arr_seq : arrival_sequence Job)
  variable (sched : schedule (processor_state Job))
  variable [JLDP_policy Job]

  def respects_policy_at_preemption_point :=
    ∀ j j_hp t,
      arrives_in arr_seq j →
      preemption_time sched t = true →
      backlogged sched j t = true →
      scheduled_at sched j_hp t = true →
      hep_job_at t j_hp j = true

end Priority

end Prosa.Model.Schedule.Priority_driven
