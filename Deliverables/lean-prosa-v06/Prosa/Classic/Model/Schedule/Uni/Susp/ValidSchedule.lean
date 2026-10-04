-- Authoritative source:
-- ProsaBuddy classic Prosa (prosabuddy commit f692cb7479780cf6009493f373a309e13165201c)
-- source: classic/model/schedule/uni/susp/valid_schedule.v
-- sha256: see Prosa-Shunqi/classic-prosa/comprehensive-classic/file_order.csv (rank 124)

import Prosa.Classic.Util.All
import Prosa.Classic.Model.Priority
import Prosa.Classic.Model.Suspension
import Prosa.Classic.Model.Arrival.Basic.ArrivalSequence
import Prosa.Classic.Model.Schedule.Uni.Susp.Schedule
import Prosa.Classic.Model.Schedule.Uni.Susp.Platform

/-!
Valid suspension-aware uniprocessor schedules (Rocq module `ValidSuspensionAwareSchedule`).

Representation notes: the section-local `Let`s `H1_…` … `H6_…` are unfolded into the conjunction;
`work_conserving`/`respects_JLDP_policy` are the suspension-aware `PlatformWithSuspensions` ones. Binder lists
follow the Rocq contract (neither `Task` nor `job_task` is taken).
-/

set_option linter.unusedVariables false

namespace Prosa.Classic.Model.Schedule.Uni.Susp.ValidSchedule.ValidSuspensionAwareSchedule

open Prosa.Classic.Model.Time.Time
open Prosa.Classic.Model.Arrival.Basic.ArrivalSequence.ArrivalSequence
open Prosa.Classic.Model.Priority.Priority
open Prosa.Classic.Model.Suspension.Suspension
open Prosa.Classic.Model.Schedule.Uni.Schedule.UniprocessorSchedule
  (schedule jobs_come_from_arrival_sequence jobs_must_arrive_to_execute completed_jobs_dont_execute)
open Prosa.Classic.Model.Schedule.Uni.Susp.SuspensionIntervals.SuspensionIntervals (respects_self_suspensions)
open Prosa.Classic.Model.Schedule.Uni.Susp.Platform.PlatformWithSuspensions (work_conserving respects_JLDP_policy)

universe v

def valid_suspension_aware_schedule {Job : Type v} [DecidableEq Job] (job_arrival : Job → time)
    (arr_seq : arrival_sequence Job) (higher_eq_priority : JLDP_policy Job)
    (job_suspension_duration : job_suspension Job) (job_cost : Job → time) (sched_susp : schedule Job) : Prop :=
  jobs_come_from_arrival_sequence sched_susp arr_seq ∧
  jobs_must_arrive_to_execute job_arrival sched_susp ∧
  completed_jobs_dont_execute job_cost sched_susp ∧
  work_conserving job_arrival job_cost job_suspension_duration arr_seq sched_susp ∧
  respects_JLDP_policy job_arrival job_cost job_suspension_duration arr_seq sched_susp higher_eq_priority ∧
  respects_self_suspensions job_arrival job_cost job_suspension_duration sched_susp

end Prosa.Classic.Model.Schedule.Uni.Susp.ValidSchedule.ValidSuspensionAwareSchedule
