-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: analysis/definitions/priority/classes.v

import Prosa.Model.Priority.Classes

namespace Prosa.Analysis.Definitions.Priority.Classes

open Prosa.Behavior.Job
open Prosa.Model.Task.Concept
open Prosa.Model.Priority.Definitions

/-- A JLFP policy is compatible with an FP policy if higher-or-equal job
priority implies higher-or-equal task priority, and strictly higher task
priority implies higher-or-equal job priority. -/
def JLFP_FP_compatible {Task : TaskType} [DecidableEq Task]
    {Job : JobType} [DecidableEq Job] [JobTask Job Task]
    (JLFP : JLFP_policy Job) (FP : FP_policy Task) : Prop :=
  (∀ j1 j2 : Job, JLFP.hep_job j1 j2 = true →
      FP.hep_task (job_task (Task := Task) j1) (job_task (Task := Task) j2) = true) ∧
  (∀ j1 j2 : Job, hp_task (FP := FP) (job_task (Task := Task) j1) (job_task (Task := Task) j2) = true →
      JLFP.hep_job j1 j2 = true)

end Prosa.Analysis.Definitions.Priority.Classes
