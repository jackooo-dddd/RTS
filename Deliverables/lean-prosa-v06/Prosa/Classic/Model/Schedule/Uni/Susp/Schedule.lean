-- Authoritative source:
-- ProsaBuddy classic Prosa (prosabuddy commit f692cb7479780cf6009493f373a309e13165201c)
-- source: classic/model/schedule/uni/susp/schedule.v
-- sha256: see Prosa-Shunqi/classic-prosa/comprehensive-classic/file_order.csv (rank 85)

import Prosa.Classic.Util.All
import Prosa.Classic.Model.Arrival.Basic.ArrivalSequence
import Prosa.Classic.Model.Suspension
import Prosa.Classic.Model.Priority
import Prosa.Classic.Model.Schedule.Uni.Schedule
import Prosa.Classic.Model.Schedule.Uni.Susp.SuspensionIntervals

/-!
Suspension-aware uniprocessor schedules (Rocq module `ScheduleWithSuspensions`, which `Export`s
`UniprocessorSchedule` and `SuspensionIntervals` and redefines `backlogged`).

Representation notes: `~~ b` is `!b`; the section-local `Let`s (`job_pending_at`, `job_scheduled_at`,
`job_suspended_at`) are unfolded. Binder lists follow the Rocq contract (`Task` is not taken).
-/

set_option linter.unusedVariables false

namespace Prosa.Classic.Model.Schedule.Uni.Susp.Schedule.ScheduleWithSuspensions

open Prosa.Classic.Model.Time.Time
open Prosa.Classic.Model.Suspension.Suspension
open Prosa.Classic.Model.Schedule.Uni.Schedule.UniprocessorSchedule (schedule pending scheduled_at)
open Prosa.Classic.Model.Schedule.Uni.Susp.SuspensionIntervals.SuspensionIntervals (suspended_at)

universe v

def backlogged {Job : Type v} [DecidableEq Job] (job_arrival job_cost : Job → time)
    (next_suspension : job_suspension Job) (sched : schedule Job) (j : Job) (t : time) : Bool :=
  pending job_arrival job_cost sched j t && !scheduled_at sched j t &&
    !suspended_at job_arrival job_cost next_suspension sched j t

end Prosa.Classic.Model.Schedule.Uni.Susp.Schedule.ScheduleWithSuspensions
