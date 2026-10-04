-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: analysis/abstract/IBF/supply_task.v

import Prosa.Analysis.Abstract.AbstractRta
import Prosa.Analysis.Abstract.IBF.Supply
import Prosa.Analysis.Abstract.IBF.Task

namespace Prosa.Analysis.Abstract.IBF.SupplyTask

open Prosa.Behavior.Arrival_sequence
open Prosa.Behavior.Job
open Prosa.Behavior.Schedule
open Prosa.Behavior.Time
open Prosa.Model.Task.Concept
open Prosa.Model.Processor.Supply
open Prosa.Analysis.Abstract.Definitions
open Prosa.Analysis.Abstract.AbstractRta
open Prosa.Analysis.Abstract.IBF.Task

/-! Task intra-supply interference: interference conditioned on the presence
of supply and on the absence of self-interference, and the corresponding
interference bound. Binders follow the elaborated source types (only the
section inputs each definition uses, in their elaborated order). -/

section TaskIntraInterferenceBound

variable {Job : JobType} [DecidableEq Job] {Task : TaskType} [DecidableEq Task]

/-- There is supply at `t` and the task of `j` is not scheduled at `t`. -/
noncomputable def nonself_intra [JobTask Job Task] {PState : ProcessorState Job}
    (arr_seq : arrival_sequence Job) (sched : schedule PState) (j : Job) (t : instant) : Bool :=
  nonself (Task := Task) arr_seq sched j t && has_supply sched t

/-- Interference while there is supply and no self-interference. -/
noncomputable def task_intra_interference [JobTask Job Task] {PState : ProcessorState Job}
    (arr_seq : arrival_sequence Job) (sched : schedule PState) [Interference Job] (j : Job)
    (t : instant) : Bool :=
  cond_interference (nonself_intra (Task := Task) arr_seq sched) j t

/-- Task intra-supply interference of the jobs of `tsk` is bounded by
`task_intra_IBF`, parametrised by the relative arrival time. -/
def task_intra_interference_is_bounded_by [JobTask Job Task] [JobArrival Job] [JobCost Job]
    {PState : ProcessorState Job} (arr_seq : arrival_sequence Job) (sched : schedule PState)
    (tsk : Task) [Interference Job] [InterferingWorkload Job]
    (task_intra_IBF : duration → duration → work) : Prop :=
  cond_interference_is_bounded_by arr_seq sched tsk task_intra_IBF
    (relative_arrival_time_of_job_is_A sched) (nonself_intra (Task := Task) arr_seq sched)

end TaskIntraInterferenceBound

end Prosa.Analysis.Abstract.IBF.SupplyTask
