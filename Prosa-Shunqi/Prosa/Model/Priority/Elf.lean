-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: model/priority/elf.v

import Prosa.Util.Int
import Prosa.Model.Priority.Classes
import Prosa.Model.Priority.Gel

namespace Prosa.Model.Priority.Elf

open Prosa.Behavior.Job
open Prosa.Model.Task.Concept
open Prosa.Model.Priority.Definitions
open Prosa.Model.Priority.Gel

/-! Representation notes: the source `#[export] Instance ELF (fp : FP_policy
Task)` is a reducible definition (like the accepted `GEL`, its `Task`
parameter is not determined by the result type, so it cannot be a Lean
global instance); the `let gel_hep_job := @hep_job _ (GEL Job Task)` binding
is inlined. Binder orders follow the elaborated type. -/

/-- ELF: an FP policy whose ties (equal task priorities) are broken by GEL. -/
@[reducible] def ELF {Task : TaskType} [DecidableEq Task] [PriorityPoint Task]
    {Job : JobType} [DecidableEq Job] [JobArrival Job] [JobTask Job Task]
    (fp : FP_policy Task) : JLFP_policy Job where
  hep_job j1 j2 :=
    hp_task (FP := fp) (job_task (Task := Task) j1) (job_task (Task := Task) j2)
      || (fp.hep_task (job_task (Task := Task) j1) (job_task (Task := Task) j2)
        && (GEL Job Task).hep_job j1 j2)

end Prosa.Model.Priority.Elf
