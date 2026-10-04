-- Authoritative source:
-- ProsaBuddy classic Prosa (prosabuddy commit f692cb7479780cf6009493f373a309e13165201c)
-- source: classic/model/schedule/uni/basic/platform_tdma.v
-- sha256: see Prosa-Shunqi/classic-prosa/comprehensive-classic/file_order.csv (rank 52)

import Prosa.Classic.Util.All
import Prosa.Classic.Model.Arrival.Basic.Task
import Prosa.Classic.Model.Arrival.Basic.Job
import Prosa.Classic.Model.Priority
import Prosa.Classic.Model.Arrival.Basic.TaskArrival
import Prosa.Classic.Model.Schedule.Uni.Schedule
import Prosa.Classic.Model.PolicyTdma

/-!
The TDMA platform (Rocq module `Platform_TDMA`, which `Export`s `PolicyTDMA`).

Representation notes: `{set sporadic_task}` is the v0.6 sequence-set; Boolean tests in proposition position are
`= true`; the section-local `Let job_in_time_slot` is unfolded. Binder lists follow the Rocq contract.
-/

namespace Prosa.Classic.Model.Schedule.Uni.Basic.PlatformTdma.Platform_TDMA

open Prosa.Classic.Model.Time.Time
open Prosa.Classic.Model.Arrival.Basic.ArrivalSequence.ArrivalSequence
open Prosa.Classic.Model.Schedule.Uni.Schedule.UniprocessorSchedule
open Prosa.Classic.Model.PolicyTdma.PolicyTDMA
open Prosa.Util.Seqset

universe u v

def sched_implies_in_slot {sporadic_task : Type u} [DecidableEq sporadic_task] {Job : Type v} [DecidableEq Job]
    (job_task : Job → sporadic_task) (sched : schedule Job) (ts : set sporadic_task)
    (time_slot : TDMA_slot sporadic_task) (slot_order : TDMA_slot_order sporadic_task) (j : Job) (t : time) : Prop :=
  scheduled_at sched j t = true → Task_in_time_slot ts slot_order (job_task j) time_slot t = true

def backlogged_implies_not_in_slot_or_other_job_sched {sporadic_task : Type u} [DecidableEq sporadic_task]
    {Job : Type v} [DecidableEq Job] (job_arrival job_cost : Job → time) (job_task : Job → sporadic_task)
    (arr_seq : arrival_sequence Job) (sched : schedule Job) (ts : set sporadic_task)
    (time_slot : TDMA_slot sporadic_task) (slot_order : TDMA_slot_order sporadic_task) (j : Job) (t : time) : Prop :=
  backlogged job_arrival job_cost sched j t = true →
    ¬ Task_in_time_slot ts slot_order (job_task j) time_slot t = true ∨
    ∃ j_other, arrives_in arr_seq j_other ∧ job_arrival j_other < job_arrival j ∧
      job_task j = job_task j_other ∧ scheduled_at sched j_other t = true

def Respects_TDMA_policy {sporadic_task : Type u} [DecidableEq sporadic_task] {Job : Type v} [DecidableEq Job]
    (job_arrival job_cost : Job → time) (job_task : Job → sporadic_task) (arr_seq : arrival_sequence Job)
    (sched : schedule Job) (ts : set sporadic_task) (time_slot : TDMA_slot sporadic_task)
    (slot_order : TDMA_slot_order sporadic_task) : Prop :=
  ∀ (j : Job) (t : time), arrives_in arr_seq j →
    sched_implies_in_slot job_task sched ts time_slot slot_order j t ∧
      backlogged_implies_not_in_slot_or_other_job_sched job_arrival job_cost job_task arr_seq sched ts time_slot
        slot_order j t

end Prosa.Classic.Model.Schedule.Uni.Basic.PlatformTdma.Platform_TDMA
