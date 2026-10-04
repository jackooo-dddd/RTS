-- Authoritative source:
-- ProsaBuddy classic Prosa (prosabuddy commit f692cb7479780cf6009493f373a309e13165201c)
-- source: classic/model/schedule/uni/susp/platform.v
-- sha256: see Prosa-Shunqi/classic-prosa/comprehensive-classic/file_order.csv (rank 108)

import Prosa.Classic.Util.All
import Prosa.Classic.Model.Arrival.Basic.ArrivalSequence
import Prosa.Classic.Model.Suspension
import Prosa.Classic.Model.Priority
import Prosa.Classic.Model.Schedule.Uni.Susp.Schedule

/-!
Platform constraints for suspension-aware uniprocessor schedules (Rocq module `PlatformWithSuspensions`, which
`Export`s `ScheduleWithSuspensions` and `Priority`).

Representation notes: `backlogged` is the suspension-aware `ScheduleWithSuspensions.backlogged`; Boolean tests in
proposition position are `= true`; the section-local `Let`s (`job_pending_at`, `job_scheduled_at`,
`job_backlogged_at`) are unfolded. Binder lists follow the Rocq contract.
-/

set_option linter.unusedVariables false

namespace Prosa.Classic.Model.Schedule.Uni.Susp.Platform.PlatformWithSuspensions

open Prosa.Classic.Model.Time.Time
open Prosa.Classic.Model.Arrival.Basic.ArrivalSequence.ArrivalSequence
open Prosa.Classic.Model.Suspension.Suspension
open Prosa.Classic.Model.Priority.Priority
open Prosa.Classic.Model.Schedule.Uni.Schedule.UniprocessorSchedule (schedule scheduled_at)
open Prosa.Classic.Model.Schedule.Uni.Susp.Schedule.ScheduleWithSuspensions (backlogged)

universe u v

def work_conserving {Job : Type v} [DecidableEq Job] (job_arrival job_cost : Job → time)
    (next_suspension : job_suspension Job) (arr_seq : arrival_sequence Job) (sched : schedule Job) : Prop :=
  ∀ j t, arrives_in arr_seq j → backlogged job_arrival job_cost next_suspension sched j t = true →
    ∃ j_other, scheduled_at sched j_other t = true

def respects_FP_policy {Task : Type u} [DecidableEq Task] {Job : Type v} [DecidableEq Job]
    (job_arrival job_cost : Job → time) (job_task : Job → Task) (next_suspension : job_suspension Job)
    (arr_seq : arrival_sequence Job) (sched : schedule Job) (higher_eq_priority : FP_policy Task) : Prop :=
  ∀ j j_hp t, arrives_in arr_seq j → backlogged job_arrival job_cost next_suspension sched j t = true →
    scheduled_at sched j_hp t = true → higher_eq_priority (job_task j_hp) (job_task j) = true

def respects_JLFP_policy {Job : Type v} [DecidableEq Job] (job_arrival job_cost : Job → time)
    (next_suspension : job_suspension Job) (arr_seq : arrival_sequence Job) (sched : schedule Job)
    (higher_eq_priority : JLFP_policy Job) : Prop :=
  ∀ j j_hp t, arrives_in arr_seq j → backlogged job_arrival job_cost next_suspension sched j t = true →
    scheduled_at sched j_hp t = true → higher_eq_priority j_hp j = true

def respects_JLDP_policy {Job : Type v} [DecidableEq Job] (job_arrival job_cost : Job → time)
    (next_suspension : job_suspension Job) (arr_seq : arrival_sequence Job) (sched : schedule Job)
    (higher_eq_priority : JLDP_policy Job) : Prop :=
  ∀ j j_hp t, arrives_in arr_seq j → backlogged job_arrival job_cost next_suspension sched j t = true →
    scheduled_at sched j_hp t = true → higher_eq_priority t j_hp j = true

end Prosa.Classic.Model.Schedule.Uni.Susp.Platform.PlatformWithSuspensions
