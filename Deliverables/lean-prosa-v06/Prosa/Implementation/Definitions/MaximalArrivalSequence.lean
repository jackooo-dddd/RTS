-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: implementation/definitions/maximal_arrival_sequence.v

import Prosa.Model.Task.Arrival.Curves
import Prosa.Util.Supremum
import Prosa.Util.Sum
import Prosa.Util.Bigcat

namespace Prosa.Implementation.Definitions.MaximalArrivalSequence

open Prosa.Behavior.Job
open Prosa.Behavior.Time
open Prosa.Model.Task.Concept
open Prosa.Model.Task.Arrival.Curves
open Prosa.Util.Supremum
open Prosa.Util.Sum
open Prosa.Util.Bigcat

/-- Sum of the last `n` elements of `xs`: the source's
`\sum_(size xs - n <= t < size xs) nth 0 xs t`, i.e. a sum over
`index_iota (size xs - n) (size xs)`. -/
def suffix_sum (xs : List Nat) (n : Nat) : Nat :=
  sumSeq (List.range' (xs.length - n) (xs.length - (xs.length - n))) (fun t => xs.getD t 0)

/-- Number of jobs of `tsk` that can additionally be released after the
arrival prefix without violating the arrival curve (minimum over suffixes). -/
def jobs_remaining {Task : TaskType} [DecidableEq Task] [MaxArrivals Task]
    (tsk : Task) (arr_prefix : List Nat) : Option Nat :=
  supremum (fun a b => decide (a ≤ b))
    ((List.range' 0 (arr_prefix.length + 1)).map
      (fun Δ => max_arrivals tsk (Δ + 1) - suffix_sum arr_prefix Δ))

/-- Maximal number of jobs to release next (curve value at 1 on an empty prefix). -/
def next_max_arrival {Task : TaskType} [DecidableEq Task] [MaxArrivals Task]
    (tsk : Task) (arr_prefix : List Nat) : Nat :=
  match jobs_remaining tsk arr_prefix with
  | none => max_arrivals tsk 1
  | some n => n

/-- Extend the arrival prefix by the maximal next number of arrivals. -/
def extend_arrival_prefix {Task : TaskType} [DecidableEq Task] [MaxArrivals Task]
    (tsk : Task) (arr_prefix : List Nat) : List Nat :=
  arr_prefix ++ [next_max_arrival tsk arr_prefix]

/-- The maximal arrival prefix of size `t + 1`: MathComp's `iter t.+1 f [::]`,
which is Lean's `Nat.repeat` (same recursion `f (iter n f x)`). -/
def maximal_arrival_prefix {Task : TaskType} [DecidableEq Task] [MaxArrivals Task]
    (tsk : Task) (t : Nat) : List Nat :=
  Nat.repeat (extend_arrival_prefix tsk) (t + 1) []

/-- Maximal number of jobs of `tsk` released at `t`. -/
def max_arrivals_at {Task : TaskType} [DecidableEq Task] [MaxArrivals Task]
    (tsk : Task) (t : Nat) : Nat :=
  (maximal_arrival_prefix tsk t).getD t 0

/-- The maximal arrival sequence of task set `ts` at time `t`. -/
def concrete_arrival_sequence {Task : TaskType} [DecidableEq Task]
    {Job : JobType} [DecidableEq Job] [MaxArrivals Task]
    (generate_jobs_at : Task → Nat → instant → List Job)
    (ts : List Task) (t : instant) : List Job :=
  bigCatSeqAll ts (fun tsk => generate_jobs_at tsk (max_arrivals_at tsk t) t)

end Prosa.Implementation.Definitions.MaximalArrivalSequence
