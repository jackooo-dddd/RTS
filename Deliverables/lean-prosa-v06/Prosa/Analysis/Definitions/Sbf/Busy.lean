-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: analysis/definitions/sbf/busy.v

import Prosa.Util.All
import Prosa.Analysis.Definitions.Sbf.Pred
import Prosa.Analysis.Definitions.BusyInterval.Classical

namespace Prosa.Analysis.Definitions.Sbf.Busy

open Prosa.Behavior.Arrival_sequence
open Prosa.Behavior.Job
open Prosa.Behavior.Schedule
open Prosa.Behavior.Time
open Prosa.Model.Processor.Supply
open Prosa.Model.Task.Concept
open Prosa.Model.Priority.Definitions
open Prosa.Analysis.Definitions.BusyInterval.Classical
open Prosa.Analysis.Definitions.Sbf.Pred

section BusySupplyBoundFunctions

variable {Task : TaskType} [DecidableEq Task]
variable {Job : JobType} [DecidableEq Job]
variable [JobArrival Job] [JobCost Job] [JobTask Job Task]
variable {PState : ProcessorState Job}

variable (arr_seq : arrival_sequence Job)
variable (sched : schedule PState)
variable [JLFP_policy Job]
variable (tsk : Task)

-- As in the source, the JLFP policy follows arr_seq and sched; the
-- source-local `bi_prefix_of_tsk` (a `Let`) is inlined.

/-- The SBF is respected within every busy-interval prefix of a job of `tsk`. -/
def sbf_respected_in_busy_interval (SBF : duration → work) : Prop :=
  pred_sbf_respected arr_seq sched
    (fun j t1 t2 =>
      job_of_task tsk j = true ∧ busy_interval_prefix arr_seq sched j t1 t2) SBF

/-- A valid busy-interval SBF: `SBF 0 = 0` and respected within busy-interval prefixes. -/
def valid_busy_sbf (SBF : duration → work) : Prop :=
  valid_pred_sbf arr_seq sched
    (fun j t1 t2 =>
      job_of_task tsk j = true ∧ busy_interval_prefix arr_seq sched j t1 t2) SBF

end BusySupplyBoundFunctions

end Prosa.Analysis.Definitions.Sbf.Busy
