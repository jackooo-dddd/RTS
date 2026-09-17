-- Translated from: ../rt-proofs/behavior/arrival_sequence.v
import Prosa.Behavior.Job
import Prosa.Util.Notation

namespace Prosa.Behavior.Arrival_sequence

open Prosa.Behavior.Job
open Prosa.Behavior.Time
open Prosa.Util.Notation

section ArrivalSequence

variable (Job : JobType)

/-- An arrival sequence is a mapping from any time to a (finite) sequence of jobs. -/
def arrival_sequence := instant → List Job

end ArrivalSequence

section JobProperties

variable {Job : JobType}
variable (arr_seq : arrival_sequence Job)

/-- The sequence of jobs arriving at time t. -/
def arrivals_at (t : instant) := arr_seq t

/-- Job j arrives at a given time t iff it belongs to the corresponding sequence. -/
def arrives_at (j : Job) (t : instant) : Prop := j ∈ arrivals_at arr_seq t

/-- Job j arrives at some (unknown) time t, i.e., it belongs to the arrival sequence. -/
def arrives_in (j : Job) : Prop := ∃ t, j ∈ arrivals_at arr_seq t

end JobProperties

section ValidArrivalSequence

variable {Job : JobType}
variable [JobArrival Job]
variable (arr_seq : arrival_sequence Job)

/-- Arrival times are consistent if any job that arrives in the sequence has the
    corresponding arrival time. -/
def consistent_arrival_times :=
  ∀ j t, arrives_at arr_seq j t → job_arrival j = t

/-- The arrival sequence is a set iff it doesn't contain duplicate jobs at any given time. -/
def arrival_sequence_uniq := ∀ t, (arrivals_at arr_seq t).Nodup

/-- The arrival sequence is valid iff it is a set and arrival times are consistent. -/
def valid_arrival_sequence :=
  consistent_arrival_times arr_seq ∧ arrival_sequence_uniq arr_seq

end ValidArrivalSequence

section ArrivalTimeProperties

variable {Job : JobType}
variable [JobArrival Job]
variable (j : Job)

/-- Job j has arrived at time t iff it arrives at some time t_0 with t_0 ≤ t. -/
def has_arrived (t : instant) : Prop := job_arrival j ≤ t

/-- Job j arrived before t iff it arrives at some time t_0 with t_0 < t. -/
def arrived_before (t : instant) : Prop := job_arrival j < t

/-- Job j arrives between t1 and t2 iff it arrives at some time t with t1 ≤ t < t2. -/
def arrived_between (t1 t2 : instant) : Prop := t1 ≤ job_arrival j ∧ job_arrival j < t2

end ArrivalTimeProperties

section ArrivalSequencePrefix

variable {Job : JobType}
variable [JobArrival Job]
variable (arr_seq : arrival_sequence Job)

/-- The list of jobs that arrived in the interval [t1, t2). -/
def arrivals_between (t1 t2 : instant) : List Job :=
  bigCat t1 t2 (arrivals_at arr_seq)

/-- The list of jobs that arrived up to time t (i.e., in [0, t+1)). -/
def arrivals_up_to (t : instant) : List Job :=
  arrivals_between arr_seq 0 (t + 1)

/-- The list of jobs that arrived strictly before time t (i.e., in [0, t)). -/
def arrivals_before (t : instant) : List Job :=
  arrivals_between arr_seq 0 t

end ArrivalSequencePrefix

end Prosa.Behavior.Arrival_sequence
