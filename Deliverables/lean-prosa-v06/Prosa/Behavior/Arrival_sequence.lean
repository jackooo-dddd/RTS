-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: behavior/arrival_sequence.v

import Prosa.Behavior.Job
import Prosa.Util.Notation

namespace Prosa.Behavior.Arrival_sequence

open Prosa.Behavior.Job
open Prosa.Behavior.Time
open Prosa.Util.Notation

universe u

section ArrivalSequence

/-- An arrival sequence maps each instant to an ordered finite sequence of
jobs.  The list representation preserves both order and multiplicity. -/
def arrival_sequence (Job : JobType) [DecidableEq Job] := instant → List Job

end ArrivalSequence

section JobProperties

variable {Job : JobType} [DecidableEq Job]
variable (arr_seq : arrival_sequence Job)

/-- Jobs arriving at instant `t`. -/
def arrivals_at (t : instant) : List Job := arr_seq t

/-- Boolean observation that `j` occurs among the jobs arriving at `t`. -/
def arrives_at (j : Job) (t : instant) : Bool :=
  decide (j ∈ arrivals_at arr_seq t)

/-- Propositional existence of an instant at which `j` arrives. -/
def arrives_in (j : Job) : Prop :=
  ∃ t, arrives_at arr_seq j t = true

end JobProperties

section ValidArrivalSequence

variable {Job : JobType} [DecidableEq Job]
variable [JobArrival Job]
variable (arr_seq : arrival_sequence Job)

/-- Every job observed at an instant has that instant as its declared arrival
time. -/
def consistent_arrival_times : Prop :=
  ∀ j t, arrives_at arr_seq j t = true → job_arrival j = t

/-- No arrival bucket contains the same job more than once. -/
def arrival_sequence_uniq : Prop :=
  ∀ t, (arrivals_at arr_seq t).Nodup

/-- Validity combines arrival-time consistency and per-instant uniqueness. -/
def valid_arrival_sequence : Prop :=
  consistent_arrival_times arr_seq ∧ arrival_sequence_uniq arr_seq

end ValidArrivalSequence

section ArrivalTimeProperties

variable {Job : JobType} [DecidableEq Job]
variable [JobArrival Job]
variable (j : Job)

/-- Boolean observation that `j` has arrived no later than `t`. -/
def has_arrived (t : instant) : Bool :=
  decide (job_arrival j ≤ t)

/-- Boolean observation that `j` arrived strictly before `t`. -/
def arrived_before (t : instant) : Bool :=
  decide (job_arrival j < t)

/-- Boolean observation that the arrival instant lies in `[t1, t2)`. -/
def arrived_between (t1 t2 : instant) : Bool :=
  decide (t1 ≤ job_arrival j) && decide (job_arrival j < t2)

end ArrivalTimeProperties

section ArrivalSequencePrefix

variable {Job : JobType} [DecidableEq Job]
variable [JobArrival Job]
variable (arr_seq : arrival_sequence Job)

/-- Ordered concatenation of arrivals over the half-open interval `[t1,t2)`. -/
def arrivals_between (t1 t2 : instant) : List Job :=
  bigCat t1 t2 (arrivals_at arr_seq)

/-- Jobs arriving at or before `t`. -/
def arrivals_up_to (t : instant) : List Job :=
  arrivals_between arr_seq 0 (t + 1)

/-- Jobs arriving strictly before `t`. -/
def arrivals_before (t : instant) : List Job :=
  arrivals_between arr_seq 0 t

/-- Jobs arriving in `[t1,t2)` that satisfy Boolean predicate `P`. -/
def arrivals_between_P (P : Job → Bool) (t1 t2 : instant) : List Job :=
  (arrivals_between arr_seq t1 t2).filter P

end ArrivalSequencePrefix

end Prosa.Behavior.Arrival_sequence
