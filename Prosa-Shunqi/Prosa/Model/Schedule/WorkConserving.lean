-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: model/schedule/work_conserving.v

import Prosa.Behavior.All

namespace Prosa.Model.Schedule.WorkConserving

open Prosa.Behavior.Arrival_sequence
open Prosa.Behavior.Job
open Prosa.Behavior.Ready
open Prosa.Behavior.Schedule
open Prosa.Behavior.Service
open Prosa.Behavior.Time

universe u

/-- Whenever an arriving job is backlogged, some job executes at that
instant. The definition intentionally imposes no priority order. -/
def work_conserving {Job : JobType} [DecidableEq Job]
    [JobArrival Job] [JobCost Job]
    {PState : ProcessorState Job} [JobReady Job PState]
    (arrSeq : arrival_sequence Job) (sched : schedule PState) : Prop :=
  ∀ (j : Job) (t : instant),
    arrives_in arrSeq j →
    backlogged sched j t = true →
    ∃ jOther : Job, scheduled_at sched jOther t = true

/-- Ordered arrival prefix restricted to jobs backlogged at `t`.
Duplicates and the original arrival order are preserved. -/
def jobs_backlogged_at {Job : JobType} [DecidableEq Job]
    [JobArrival Job] [JobCost Job]
    {PState : ProcessorState Job} [JobReady Job PState]
    (arrSeq : arrival_sequence Job) (sched : schedule PState)
    (t : instant) : List Job :=
  (arrivals_up_to arrSeq t).filter fun j => backlogged sched j t

end Prosa.Model.Schedule.WorkConserving
