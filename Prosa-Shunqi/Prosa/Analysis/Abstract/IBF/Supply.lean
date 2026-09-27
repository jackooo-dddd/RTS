-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: analysis/abstract/IBF/supply.v

import Prosa.Analysis.Abstract.AbstractRta
import Prosa.Model.Processor.Supply

namespace Prosa.Analysis.Abstract.IBF.Supply

open Prosa.Behavior.Arrival_sequence
open Prosa.Behavior.Job
open Prosa.Behavior.Schedule
open Prosa.Behavior.Time
open Prosa.Model.Task.Concept
open Prosa.Model.Processor.Supply
open Prosa.Analysis.Abstract.Definitions
open Prosa.Analysis.Abstract.AbstractRta

/-! Intra-supply interference: interference conditioned on the presence of
supply, its cumulative form, and the intra-supply interference bound.
Binders follow the elaborated source types (only the section inputs each
definition uses, in their elaborated order). -/

section IntraInterferenceBound

variable {Job : JobType} [DecidableEq Job]

/-- Job `j` incurs interference at `t` while supply is present. -/
noncomputable def intra_interference {PState : ProcessorState Job} (sched : schedule PState)
    [Interference Job] (j : Job) (t : instant) : Bool :=
  cond_interference (fun _ t => has_supply sched t) j t

/-- Cumulative intra-supply interference over `[t1, t2)`. -/
noncomputable def cumul_intra_interference {PState : ProcessorState Job}
    (sched : schedule PState) [Interference Job] (j : Job) (t1 t2 : Nat) : Nat :=
  cumul_cond_interference (fun _ t => has_supply sched t) j t1 t2

/-- Intra-supply interference of the jobs of `tsk` is bounded by `intra_IBF`,
parametrised by the relative arrival time. -/
def intra_interference_is_bounded_by {Task : TaskType} [DecidableEq Task] [JobTask Job Task]
    [JobArrival Job] [JobCost Job] {PState : ProcessorState Job}
    (arr_seq : arrival_sequence Job) (sched : schedule PState) (tsk : Task)
    [Interference Job] [InterferingWorkload Job] (intra_IBF : duration → duration → work) : Prop :=
  cond_interference_is_bounded_by arr_seq sched tsk intra_IBF
    (relative_arrival_time_of_job_is_A sched) (fun _ t => has_supply sched t)

end IntraInterferenceBound

end Prosa.Analysis.Abstract.IBF.Supply
