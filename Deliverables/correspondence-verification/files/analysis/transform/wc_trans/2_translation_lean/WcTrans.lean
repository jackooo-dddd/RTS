-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: analysis/transform/wc_trans.v

import Prosa.Analysis.Transform.Swap
import Prosa.Analysis.Transform.Prefix
import Prosa.Util.SearchArg
import Prosa.Util.List
import Prosa.Model.Processor.Ideal

namespace Prosa.Analysis.Transform.WcTrans

open Prosa.Behavior.Arrival_sequence
open Prosa.Behavior.Job
open Prosa.Behavior.Schedule
open Prosa.Behavior.Time
open Prosa.Model.Processor.Ideal
open Prosa.Analysis.Transform.Prefix
open Prosa.Analysis.Transform.Swap
open Prosa.Util.SearchArg
open Prosa.Util.List

/-! The work-conserving transformation of a (finite prefix of a) schedule.
Binder orders and argument types follow the elaborated types: the state
predicates take `Nat`/`Option Job` and the pointwise functions take schedules
as `instant → Option Job` (the states of the accepted ideal processor
`processor_state Job`); the processor model of `swapped`/`prefix_map` is that
ideal processor, named explicitly (the source's local instance). The local
`let`s are kept; `map f s` is `s.map f`; `if e is Some t then t else u` is a
`match`; `t.+1` is `t + 1`. -/

section WCTransformation

variable {Job : JobType} [DecidableEq Job]

/-- A state is relevant if it is not idle and its job arrived by the reference time. -/
def relevant_pstate [JobArrival Job] (reference_time : Nat) (pstate : Option Job) : Bool :=
  match pstate with
  | none => false
  | some j => decide (job_arrival j ≤ reference_time)

/-- The latest deadline of the jobs arrived by the given time. -/
def max_deadline_for_jobs_arrived_before [JobDeadline Job] (arr_seq : arrival_sequence Job)
    (arrived_before : instant) : Nat :=
  let deadlines := (arrivals_up_to arr_seq arrived_before).map job_deadline
  max0 deadlines

/-- The first later instant, before the latest relevant deadline, at which a
relevant job is scheduled (or `t`). -/
def find_swap_candidate [JobArrival Job] [JobDeadline Job] (arr_seq : arrival_sequence Job)
    (sched : Nat → Option Job) (t : instant) : Nat :=
  let order := fun (_ _ : Option Job) => false
  let max_dl := max_deadline_for_jobs_arrived_before arr_seq t
  let search_result := search_arg sched (relevant_pstate t) order t max_dl
  match search_result with
  | some t_swap => t_swap
  | none => t

/-- Make the schedule work-conserving at `t1` by pulling a later job forward. -/
def make_wc_at [JobArrival Job] [JobDeadline Job] (arr_seq : arrival_sequence Job)
    (sched : instant → Option Job) (t1 : instant) : schedule (processor_state Job) :=
  match sched t1 with
  | some _ => sched
  | none =>
    let t2 := find_swap_candidate arr_seq sched t1
    swapped (PState := processor_state Job) sched t1 t2

/-- Apply `make_wc_at` to every point up to the horizon. -/
def wc_transform_prefix [JobArrival Job] [JobDeadline Job] (arr_seq : arrival_sequence Job)
    (sched : schedule (processor_state Job)) (horizon : instant) : schedule (processor_state Job) :=
  prefix_map sched (make_wc_at arr_seq) horizon

/-- The work-conserving schedule: the last point of the prefix through `t`. -/
def wc_transform [JobArrival Job] [JobDeadline Job] (arr_seq : arrival_sequence Job)
    (sched : schedule (processor_state Job)) (t : Nat) : (processor_state Job).State :=
  let wc_prefix := wc_transform_prefix arr_seq sched (t + 1)
  wc_prefix t

end WCTransformation

end Prosa.Analysis.Transform.WcTrans
