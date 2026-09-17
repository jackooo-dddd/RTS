-- Translated from: ../rt-proofs/classic/model/schedule/uni/basic/platform_tdma.v
import Prosa.Classic.Model.Arrival.Basic.Task
import Prosa.Classic.Model.Arrival.Basic.Arrival_sequence
import Prosa.Classic.Model.Schedule.Uni.Schedule
import Prosa.Classic.Model.Policy_tdma

namespace Prosa.Classic.Model.Schedule.Uni.Basic.Platform_tdma

open Prosa.Classic.Model.Time
open Prosa.Util.Seqset
open Prosa.Classic.Model.Policy_tdma
open Prosa.Classic.Model.Arrival.Basic.Arrival_sequence
open Prosa.Classic.Model.Schedule.Uni.Schedule

section Properties

  variable {sporadic_task : Type _} [DecidableEq sporadic_task]
  variable {Job : Type _} [DecidableEq Job]
  variable (job_arrival : Job → Time)
  variable (job_cost : Job → Time)
  variable (job_deadline : Job → Time)
  variable (job_task : Job → sporadic_task)

  variable (arr_seq : arrival_sequence Job)

  variable (sched : schedule Job)

  variable (ts : SeqSet sporadic_task)

  variable (time_slot : TDMA_slot sporadic_task)

  variable (slot_order : TDMA_slot_order sporadic_task)

  private def job_in_time_slot (job : Job) (t : Instant) : Prop :=
    Task_in_time_slot ts slot_order (job_task job) time_slot t

  def sched_implies_in_slot (j : Job) (t : Time) : Prop :=
    scheduled_at sched j t = true → job_in_time_slot job_task ts time_slot slot_order j t

  def backlogged_implies_not_in_slot_or_other_job_sched (j : Job) (t : Time) : Prop :=
    backlogged job_arrival job_cost sched j t →
      ¬ job_in_time_slot job_task ts time_slot slot_order j t ∨
      (∃ j_other, arrives_in arr_seq j_other ∧
                   job_arrival j_other < job_arrival j ∧
                   job_task j = job_task j_other ∧
                   scheduled_at sched j_other t = true)

  def Respects_TDMA_policy : Prop :=
    ∀ (j : Job) (t : Time),
      arrives_in arr_seq j →
      sched_implies_in_slot job_task sched ts time_slot slot_order j t ∧
      backlogged_implies_not_in_slot_or_other_job_sched job_arrival job_cost job_task arr_seq sched ts time_slot slot_order j t

end Properties

end Prosa.Classic.Model.Schedule.Uni.Basic.Platform_tdma
