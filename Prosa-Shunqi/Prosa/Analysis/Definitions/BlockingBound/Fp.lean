-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: analysis/definitions/blocking_bound/fp.v

import Prosa.Util.Minmax
import Prosa.Model.Task.Preemption.Parameters

namespace Prosa.Analysis.Definitions.BlockingBound.Fp

open Prosa.Model.Task.Concept
open Prosa.Model.Priority.Definitions
open Prosa.Model.Task.Preemption.Parameters
open Prosa.Util.Minmax

/-! Representation notes: `\max_(x <- xs | P x) F x` is the accepted
`bigMaxListCond xs P F`; `~~ b` is `!b`; `ε` is `1`. Binder order follows the
elaborated type. -/

/-- FP blocking bound: the longest nonpreemptive segment (minus one) of a
lower-priority task. -/
def blocking_bound {Task : TaskType} [DecidableEq Task] [TaskMaxNonpreemptiveSegment Task]
    [FP : FP_policy Task] (ts : List Task) (tsk : Task) : Nat :=
  bigMaxListCond ts (fun tsk_other => !FP.hep_task tsk_other tsk)
    (fun tsk_other => task_max_nonpreemptive_segment tsk_other - 1)

end Prosa.Analysis.Definitions.BlockingBound.Fp
