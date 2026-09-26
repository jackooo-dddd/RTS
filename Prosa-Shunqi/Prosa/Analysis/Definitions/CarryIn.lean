-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: analysis/definitions/carry_in.v

import Prosa.Model.Priority.Classes

namespace Prosa.Analysis.Definitions.CarryIn

open Prosa.Behavior.Arrival_sequence
open Prosa.Behavior.Job
open Prosa.Behavior.Schedule
open Prosa.Behavior.Service
open Prosa.Behavior.Time

/-- There is no carry-in at time `t` iff every job that arrived before `t`
has completed by `t`.  (The source section's unused task/cost context is not
part of the elaborated definition.) -/
noncomputable def no_carry_in {Job : JobType} [DecidableEq Job] [JobArrival Job] [JobCost Job]
    (arr_seq : arrival_sequence Job) {PState : ProcessorState Job}
    (sched : schedule PState) (t : instant) : Prop :=
  ∀ j_o : Job, arrives_in arr_seq j_o →
    arrived_before j_o t = true → completed_by sched j_o t = true

end Prosa.Analysis.Definitions.CarryIn
