-- Translated from: ../rt-proofs/classic/model/schedule/uni/susp/platform.v
import Prosa.Classic.Util.All
import Prosa.Classic.Model.Arrival.Basic.Arrival_sequence
import Prosa.Classic.Model.Schedule.Uni.Susp.Schedule
import Prosa.Classic.Model.Priority

namespace Prosa.Classic.Model.Schedule.Uni.Susp.Platform

open Prosa.Classic.Model.Time
open Prosa.Classic.Model.Schedule.Uni.Schedule
open Prosa.Classic.Model.Schedule.Uni.Susp.Schedule
open Prosa.Classic.Model.Arrival.Basic.Arrival_sequence
open Prosa.Classic.Model.Priority
open Prosa.Classic.Model.Suspension

namespace PlatformWithSuspensions

section Definitions

variable {Task : Type _} [DecidableEq Task]
variable {Job : Type _} [DecidableEq Job]
variable (job_arrival : Job → Time)
variable (job_cost : Job → Time)
variable (job_task : Job → Task)
variable (next_suspension : job_suspension Job)
variable (arr_seq : arrival_sequence Job)
variable (sched : schedule Job)

private abbrev job_pending_at := pending job_arrival job_cost sched
private abbrev job_scheduled_at := scheduled_at sched
private abbrev job_backlogged_at :=
  Prosa.Classic.Model.Schedule.Uni.Susp.Schedule.backlogged job_arrival job_cost next_suspension sched

section ScheduleConstraints

section Execution

def work_conserving :=
  ∀ j t,
    arrives_in arr_seq j →
    job_backlogged_at job_arrival job_cost next_suspension sched j t →
    ∃ j_other, job_scheduled_at sched j_other t = true

end Execution

section FP

variable (higher_eq_priority : FP_policy Task)

def respects_FP_policy :=
  ∀ j j_hp t,
    arrives_in arr_seq j →
    job_backlogged_at job_arrival job_cost next_suspension sched j t →
    job_scheduled_at sched j_hp t = true →
    higher_eq_priority (job_task j_hp) (job_task j) = true

end FP

section JLFP

variable (higher_eq_priority : JLFP_policy Job)

def respects_JLFP_policy :=
  ∀ j j_hp t,
    arrives_in arr_seq j →
    job_backlogged_at job_arrival job_cost next_suspension sched j t →
    job_scheduled_at sched j_hp t = true →
    higher_eq_priority j_hp j = true

end JLFP

section JLDP

variable (higher_eq_priority : JLDP_policy Job)

def respects_JLDP_policy :=
  ∀ j j_hp t,
    arrives_in arr_seq j →
    job_backlogged_at job_arrival job_cost next_suspension sched j t →
    job_scheduled_at sched j_hp t = true →
    higher_eq_priority t j_hp j = true

end JLDP

end ScheduleConstraints

end Definitions

end PlatformWithSuspensions

end Prosa.Classic.Model.Schedule.Uni.Susp.Platform
