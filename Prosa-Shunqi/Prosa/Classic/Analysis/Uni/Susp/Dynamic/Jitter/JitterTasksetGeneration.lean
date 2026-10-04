-- Authoritative source:
-- ProsaBuddy classic Prosa (prosabuddy commit f692cb7479780cf6009493f373a309e13165201c)
-- source: classic/analysis/uni/susp/dynamic/jitter/jitter_taskset_generation.v
-- sha256: see Prosa-Shunqi/classic-prosa/comprehensive-classic/file_order.csv (rank 94)

import Prosa.Classic.Util.All
import Prosa.Classic.Model.Priority
import Prosa.Classic.Model.Suspension
import Prosa.Classic.Model.Arrival.Basic.ArrivalSequence
import Prosa.Classic.Model.Schedule.Uni.Jitter.Schedule
import Prosa.Classic.Analysis.Uni.Susp.Dynamic.Jitter.JitterSchedule

/-!
The jitter-aware task set of the suspension-to-jitter reduction (Rocq module `JitterTaskSetGeneration`).

Representation notes: `tsk == tsk_i` is `decide (tsk = tsk_i)`; `x != y` is `!decide (x = y)`; the section-local
`Let other_hep_task` is unfolded. Binder lists follow the Rocq contract (`ts` is not taken).
-/

set_option linter.unusedVariables false

namespace Prosa.Classic.Analysis.Uni.Susp.Dynamic.Jitter.JitterTasksetGeneration.JitterTaskSetGeneration

open Prosa.Classic.Model.Time.Time
open Prosa.Classic.Model.Priority.Priority

universe u

def inflated_task_cost {Task : Type u} [DecidableEq Task] (original_task_cost task_suspension_bound : Task → time)
    (tsk_i : Task) (tsk : Task) : Nat :=
  if tsk = tsk_i then original_task_cost tsk + task_suspension_bound tsk else original_task_cost tsk

def task_jitter {Task : Type u} [DecidableEq Task] (original_task_cost : Task → time)
    (higher_eq_priority : FP_policy Task) (tsk_i : Task) (R : Task → time) (tsk : Task) : Nat :=
  if (higher_eq_priority tsk tsk_i && !decide (tsk = tsk_i)) then R tsk - original_task_cost tsk else 0

end Prosa.Classic.Analysis.Uni.Susp.Dynamic.Jitter.JitterTasksetGeneration.JitterTaskSetGeneration
