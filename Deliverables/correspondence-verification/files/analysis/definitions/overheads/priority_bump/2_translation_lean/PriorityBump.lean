-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: analysis/definitions/overheads/priority_bump.v

import Prosa.Model.Priority.Classes
import Prosa.Model.Processor.Overheads

namespace Prosa.Analysis.Definitions.Overheads.PriorityBump

open Prosa.Behavior.Job
open Prosa.Behavior.Schedule
open Prosa.Behavior.Time
open Prosa.Model.Priority.Definitions
open Prosa.Model.Processor.Overheads

/-- A priority bump occurs at `t` if the job scheduled at `t` has strictly
higher priority than the job scheduled at `t - 1` (predecessor saturating at
zero), or if the processor was idle at `t - 1` and executes a job at `t`. -/
def priority_bump {Job : JobType} [DecidableEq Job] [JLFP : JLFP_policy Job]
    (sched : schedule (processor_state Job)) (t : instant) : Bool :=
  match scheduled_job sched (Nat.pred t), scheduled_job sched t with
  | none, none => false
  | none, some _ => true
  | some _, none => false
  | some j1, some j2 => !hep_job j1 j2

end Prosa.Analysis.Definitions.Overheads.PriorityBump
