-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: analysis/definitions/completion_sequence.v

import Prosa.Behavior.Service

namespace Prosa.Analysis.Definitions.CompletionSequence

open Prosa.Behavior.Job
open Prosa.Behavior.Schedule
open Prosa.Behavior.Service
open Prosa.Behavior.Arrival_sequence

universe u

/-- At each instant, retain in source-list order the arrivals up to that
instant whose Boolean completion predicate holds at the same instant. -/
noncomputable def completion_sequence
    {Job : JobType} [DecidableEq Job] [JobCost Job]
    {PState : ProcessorState Job}
    (arr_seq : arrival_sequence Job) (sched : schedule PState) :
    arrival_sequence Job :=
  fun t => (arrivals_up_to arr_seq t).filter
    (fun j => completes_at sched j t)

end Prosa.Analysis.Definitions.CompletionSequence
