-- Translated from: ../rt-proofs/classic/analysis/uni/susp/dynamic/jitter/jitter_taskset_generation.v
import Prosa.Classic.Util.All
import Prosa.Classic.Model.Priority
import Prosa.Classic.Model.Arrival.Basic.Arrival_sequence
import Prosa.Classic.Model.Schedule.Uni.Jitter.Schedule
import Prosa.Classic.Analysis.Uni.Susp.Dynamic.Jitter.Jitter_schedule

namespace Prosa.Classic.Analysis.Uni.Susp.Dynamic.Jitter.Jitter_taskset_generation

open Prosa.Classic.Model.Time
open Prosa.Classic.Model.Schedule.Uni.Jitter.Schedule
open Prosa.Classic.Model.Priority
open Prosa.Classic.Analysis.Uni.Susp.Dynamic.Jitter.Jitter_schedule

namespace JitterTaskSetGeneration

section GeneratingTaskset

  variable {Task : Type _} [DecidableEq Task]

  variable (ts : List Task)

  variable (original_task_cost : Task → Time)
  variable (task_suspension_bound : Task → Time)

  variable (higher_eq_priority : FP_policy Task)

  variable (tsk_i : Task)

  def other_hep_task (tsk_other : Task) : Bool :=
    higher_eq_priority tsk_other tsk_i && decide (tsk_other ≠ tsk_i)

  def inflated_task_cost (tsk : Task) : Time :=
    if tsk == tsk_i then
      original_task_cost tsk + task_suspension_bound tsk
    else original_task_cost tsk

  variable (R : Task → Time)

  def task_jitter (tsk : Task) : Time :=
    if other_hep_task higher_eq_priority tsk_i tsk then
      R tsk - original_task_cost tsk
    else 0

end GeneratingTaskset

end JitterTaskSetGeneration

end Prosa.Classic.Analysis.Uni.Susp.Dynamic.Jitter.Jitter_taskset_generation
