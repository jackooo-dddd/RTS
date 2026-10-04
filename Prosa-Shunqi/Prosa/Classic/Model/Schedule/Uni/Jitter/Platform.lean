-- Authoritative source:
-- ProsaBuddy classic Prosa (prosabuddy commit f692cb7479780cf6009493f373a309e13165201c)
-- source: classic/model/schedule/uni/jitter/platform.v
-- sha256: see Prosa-Shunqi/classic-prosa/comprehensive-classic/file_order.csv (rank 69)

import Prosa.Classic.Util.All
import Prosa.Classic.Model.Arrival.Basic.Task
import Prosa.Classic.Model.Arrival.Basic.Job
import Prosa.Classic.Model.Priority
import Prosa.Classic.Model.Arrival.Basic.TaskArrival
import Prosa.Classic.Model.Schedule.Uni.Jitter.Schedule

/-!
Properties of the platform in jitter-aware uniprocessor schedules (Rocq module `Platform`).

Representation notes: Boolean tests in proposition position are `= true`; `backlogged` is the jitter-aware
`UniprocessorScheduleWithJitter.backlogged`. Binder lists follow the Rocq contract (each definition takes only the
section variables it uses).
-/

set_option linter.unusedVariables false

namespace Prosa.Classic.Model.Schedule.Uni.Jitter.Platform.Platform

open Prosa.Classic.Model.Time.Time
open Prosa.Classic.Model.Arrival.Basic.ArrivalSequence.ArrivalSequence
open Prosa.Classic.Model.Priority.Priority
open Prosa.Classic.Model.Schedule.Uni.Schedule.UniprocessorSchedule (schedule scheduled_at)
open Prosa.Classic.Model.Schedule.Uni.Jitter.Schedule.UniprocessorScheduleWithJitter (backlogged)

universe u v

def work_conserving {Job : Type v} [DecidableEq Job] (job_arrival job_cost job_jitter : Job → time)
    (arr_seq : arrival_sequence Job) (sched : schedule Job) : Prop :=
  ∀ j t, arrives_in arr_seq j → backlogged job_arrival job_cost job_jitter sched j t = true →
    ∃ j_other, scheduled_at sched j_other t = true

def respects_FP_policy {sporadic_task : Type u} [DecidableEq sporadic_task] {Job : Type v} [DecidableEq Job]
    (job_arrival job_cost job_jitter : Job → time) (job_task : Job → sporadic_task) (arr_seq : arrival_sequence Job)
    (sched : schedule Job) (higher_eq_priority : FP_policy sporadic_task) : Prop :=
  ∀ j j_hp t, arrives_in arr_seq j → backlogged job_arrival job_cost job_jitter sched j t = true →
    scheduled_at sched j_hp t = true → higher_eq_priority (job_task j_hp) (job_task j) = true

def respects_JLFP_policy {Job : Type v} [DecidableEq Job] (job_arrival job_cost job_jitter : Job → time)
    (arr_seq : arrival_sequence Job) (sched : schedule Job) (higher_eq_priority : JLFP_policy Job) : Prop :=
  ∀ j j_hp t, arrives_in arr_seq j → backlogged job_arrival job_cost job_jitter sched j t = true →
    scheduled_at sched j_hp t = true → higher_eq_priority j_hp j = true

def respects_JLDP_policy {Job : Type v} [DecidableEq Job] (job_arrival job_cost job_jitter : Job → time)
    (arr_seq : arrival_sequence Job) (sched : schedule Job) (higher_eq_priority : JLDP_policy Job) : Prop :=
  ∀ j j_hp t, arrives_in arr_seq j → backlogged job_arrival job_cost job_jitter sched j t = true →
    scheduled_at sched j_hp t = true → higher_eq_priority t j_hp j = true

end Prosa.Classic.Model.Schedule.Uni.Jitter.Platform.Platform
