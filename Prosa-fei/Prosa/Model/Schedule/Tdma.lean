-- Translated from: ../rt-proofs/model/schedule/tdma.v
import Prosa.Model.Task.Concept
import Prosa.Util.Seqset
import Prosa.Util.Rel
import Prosa.Model.Processor.Ideal

namespace Prosa.Model.Schedule.Tdma

open Prosa.Behavior.Job
open Prosa.Behavior.Time
open Prosa.Behavior.Schedule
open Prosa.Behavior.Service
open Prosa.Behavior.Arrival_sequence
open Prosa.Behavior.Ready
open Prosa.Model.Task.Concept
open Prosa.Model.Processor.Ideal
open Prosa.Util.Seqset
open Prosa.Util.Rel

section TDMAPolicy

  variable (Task : Type _)

  abbrev TDMA_slot := Task → duration

  abbrev TDMA_slot_order := Task → Task → Bool

end TDMAPolicy

class TDMAPolicy (T : TaskType) where
  task_time_slot : TDMA_slot T
  slot_order : TDMA_slot_order T

export TDMAPolicy (task_time_slot slot_order)

section ValidTDMAPolicy

  variable {Task : Type _} [DecidableEq Task]

  variable (ts : SeqSet Task)

  variable [TDMAPolicy Task]

  def transitive_slot_order : Prop :=
    ∀ x y z : Task, slot_order x y = true → slot_order y z = true → slot_order x z = true

  def total_slot_order : Prop :=
    total_over_list slot_order (ts : List Task)

  def antisymmetric_slot_order : Prop :=
    antisymmetric_over_list slot_order (ts : List Task)

  def valid_time_slot : Prop :=
    ∀ tsk, tsk ∈ ts → task_time_slot tsk > 0

  def valid_TDMAPolicy : Prop :=
    transitive_slot_order (Task := Task) ∧
    total_slot_order ts ∧
    antisymmetric_slot_order ts ∧
    valid_time_slot ts

end ValidTDMAPolicy

section TDMADefinitions

  variable {Task : Type _} [DecidableEq Task]

  variable (ts : SeqSet Task)

  variable [TDMAPolicy Task]

  def TDMA_cycle : ℕ :=
    ((ts : List Task).map task_time_slot).sum

  def task_slot_offset (tsk : Task) : ℕ :=
    (((ts : List Task).filter (fun prev_task =>
      slot_order prev_task tsk && decide (prev_task ≠ tsk))).map task_time_slot).sum

  def task_in_time_slot (tsk : Task) (t : instant) : Prop :=
    ((t + TDMA_cycle ts - task_slot_offset ts tsk % TDMA_cycle ts) % TDMA_cycle ts) <
      task_time_slot tsk

end TDMADefinitions

section TDMASchedule

  variable {Task : TaskType} {Job : JobType}
  variable [DecidableEq Job] [DecidableEq Task]

  variable [JobArrival Job] [JobCost Job] [JobReady Job (processor_state Job)] [JobTask Job Task]

  variable (arr_seq : arrival_sequence Job)

  variable (sched : schedule (processor_state Job))

  variable (ts : SeqSet Task)

  variable [TDMAPolicy Task]

  def job_in_time_slot (job : Job) (t : instant) : Prop :=
    task_in_time_slot ts (job_task job) t

  def sched_implies_in_slot (j : Job) (t : instant) : Prop :=
    scheduled_at sched j t = true → job_in_time_slot ts j t

  def backlogged_implies_not_in_slot_or_other_job_sched (j : Job) (t : instant) : Prop :=
    backlogged sched j t = true →
    ¬ job_in_time_slot ts j t ∨
    ∃ j_other, arrives_in arr_seq j_other ∧
               job_arrival j_other < job_arrival j ∧
               job_task (Task := Task) j = job_task j_other ∧
               scheduled_at sched j_other t = true

  def respects_TDMA_policy : Prop :=
    ∀ (j : Job) (t : instant),
      arrives_in arr_seq j →
      sched_implies_in_slot sched ts j t ∧
      backlogged_implies_not_in_slot_or_other_job_sched (Task := Task) arr_seq sched ts j t

end TDMASchedule

end Prosa.Model.Schedule.Tdma
