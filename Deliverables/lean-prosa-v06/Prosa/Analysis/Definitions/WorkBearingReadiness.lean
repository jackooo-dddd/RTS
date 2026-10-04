-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: analysis/definitions/work_bearing_readiness.v

import Prosa.Model.Priority.Classes

namespace Prosa.Analysis.Definitions.WorkBearingReadiness

open Prosa.Behavior.Arrival_sequence
open Prosa.Behavior.Job
open Prosa.Behavior.Ready
open Prosa.Behavior.Schedule
open Prosa.Behavior.Service
open Prosa.Behavior.Time
open Prosa.Model.Priority.Definitions

/-- Work-bearing readiness: whenever an arrived job is pending, some arrived
job of higher-or-equal priority is ready. -/
noncomputable def work_bearing_readiness {Job : JobType} [DecidableEq Job]
    [JobArrival Job] [JobCost Job] {PState : ProcessorState Job}
    [jr : JobReady Job PState] (arr_seq : arrival_sequence Job)
    (sched : schedule PState) [JLFP_policy Job] : Prop :=
  ∀ (j : Job) (t : instant), arrives_in arr_seq j → pending sched j t = true →
    ∃ j_hp : Job, arrives_in arr_seq j_hp ∧ job_ready sched j_hp t = true ∧
      hep_job j_hp j = true

end Prosa.Analysis.Definitions.WorkBearingReadiness
