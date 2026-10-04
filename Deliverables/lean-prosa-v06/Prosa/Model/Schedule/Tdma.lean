-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: model/schedule/tdma.v

import Prosa.Model.Task.Concept
import Prosa.Util.Rel
import Prosa.Util.Seqset

namespace Prosa.Model.Schedule.Tdma

open Prosa.Behavior.Arrival_sequence
open Prosa.Behavior.Job
open Prosa.Behavior.Ready
open Prosa.Behavior.Schedule
open Prosa.Behavior.Service
open Prosa.Behavior.Time
open Prosa.Model.Task.Concept
open Prosa.Util.Rel
open Prosa.Util.Seqset

universe u v

/-- The reserved duration of each task's slot. -/
def TDMA_slot (Task : Type u) [DecidableEq Task] : Type u := Task → duration

/-- Boolean ordering of task slots within one TDMA cycle. -/
def TDMA_slot_order (Task : Type u) [DecidableEq Task] : Type u :=
  Task → Task → Bool

/-- The two components of a TDMA scheduling policy. -/
class TDMAPolicy (Task : TaskType) [DecidableEq Task] where
  task_time_slot : TDMA_slot Task
  slot_order : TDMA_slot_order Task

export TDMAPolicy (task_time_slot slot_order)

variable {Task : TaskType} [DecidableEq Task] [TDMAPolicy Task]

/-- The slot order is transitive, independently of any task set. -/
def transitive_slot_order : Prop :=
  ∀ y x z : Task,
    slot_order x y = true → slot_order y z = true → slot_order x z = true

/-- Every pair of tasks in the ordered task set is comparable. -/
def total_slot_order (ts : set Task) : Prop :=
  total_over_list slot_order ts.val

/-- Mutual precedence on the task set implies equality. -/
def antisymmetric_slot_order (ts : set Task) : Prop :=
  antisymmetric_over_list slot_order ts.val

/-- Every task in the set has a positive slot length. -/
def valid_time_slot (ts : set Task) : Prop :=
  ∀ tsk : Task, tsk ∈ ts → 0 < task_time_slot tsk

/-- All four validity conditions of a TDMA policy. -/
def valid_TDMAPolicy (ts : set Task) : Prop :=
  transitive_slot_order (Task := Task) ∧
    total_slot_order ts ∧
    antisymmetric_slot_order ts ∧
    valid_time_slot ts

/-- Duration of one TDMA cycle, in the source task-set order. -/
def TDMA_cycle (ts : set Task) : Nat :=
  ts.val.foldr (fun tsk n => task_time_slot tsk + n) 0

/-- Sum of lengths of task slots preceding `tsk`. -/
def task_slot_offset (ts : set Task) (tsk : Task) : Nat :=
  (ts.val.filter (fun prevTask =>
      slot_order prevTask tsk && decide (prevTask ≠ tsk))).foldr
    (fun prevTask n => task_time_slot prevTask + n) 0

/-- Boolean test that time `t` falls inside `tsk`'s reserved slot. -/
def task_in_time_slot (ts : set Task) (tsk : Task) (t : instant) : Bool :=
  decide (((t + TDMA_cycle ts - task_slot_offset ts tsk % TDMA_cycle ts) %
    TDMA_cycle ts) < task_time_slot tsk)

variable {Job : JobType} [DecidableEq Job]
variable [JobTask Job Task]

/-- A job inherits its task's TDMA slot. -/
def job_in_time_slot (ts : set Task) (j : Job) (t : instant) : Bool :=
  task_in_time_slot ts (job_task j) t

variable {PState : ProcessorState Job}

/-- A scheduled job must execute only in its own slot. -/
def sched_implies_in_slot (sched : schedule PState) (ts : set Task)
    (j : Job) (t : instant) : Prop :=
  scheduled_at sched j t = true → job_in_time_slot ts j t = true

variable [JobArrival Job] [JobCost Job] [JobReady Job PState]

/-- A backlogged job in its slot requires an earlier same-task job to run. -/
def backlogged_implies_not_in_slot_or_other_job_sched
    (arrSeq : arrival_sequence Job) (sched : schedule PState)
    (ts : set Task) (j : Job) (t : instant) : Prop :=
  backlogged sched j t = true →
    ¬ (job_in_time_slot ts j t = true) ∨
      ∃ jOther : Job,
        arrives_in arrSeq jOther ∧
        job_arrival jOther < job_arrival j ∧
        job_task (Task := Task) j = job_task (Task := Task) jOther ∧
        scheduled_at sched jOther t = true

/-- A schedule respects the TDMA policy for every arriving job and time. -/
def respects_TDMA_policy (arrSeq : arrival_sequence Job)
    (sched : schedule PState) (ts : set Task) : Prop :=
  ∀ (j : Job) (t : instant),
    arrives_in arrSeq j →
      sched_implies_in_slot sched ts j t ∧
      backlogged_implies_not_in_slot_or_other_job_sched arrSeq sched ts j t

end Prosa.Model.Schedule.Tdma
