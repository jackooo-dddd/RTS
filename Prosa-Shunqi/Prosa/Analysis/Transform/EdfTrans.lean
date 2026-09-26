-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: analysis/transform/edf_trans.v

import Prosa.Analysis.Transform.Prefix
import Prosa.Analysis.Transform.Swap
import Prosa.Analysis.Facts.Model.Ideal.Schedule
import Prosa.Util.SearchArg

namespace Prosa.Analysis.Transform.EdfTrans

open Prosa.Behavior.Job
open Prosa.Behavior.Schedule
open Prosa.Behavior.Time
open Prosa.Model.Processor.Ideal
open Prosa.Analysis.Transform.Prefix
open Prosa.Analysis.Transform.Swap
open Prosa.Util.SearchArg

/-! The EDF transformation of a (finite prefix of a) schedule. Representation:
the section-local `PState := ideal.processor_state Job` is the accepted ideal
processor `processor_state Job`, whose states are `Option Job`; `oapp f d s` is
the corresponding `match`; `if e is Some t then t else 0` is a `match`; the
local `let`s are kept; `t.+1` is `t + 1`. Binder orders follow the elaborated
types (each definition takes only the job classes it uses). -/

section EDFTransformation

variable {Job : JobType} [DecidableEq Job]

/-- `s1` has an earlier-or-equal deadline than `s2` (idle states count as `0`). -/
def earlier_deadline [JobDeadline Job] (s1 s2 : (processor_state Job).State) : Bool :=
  decide ((match s1 with | none => 0 | some j => job_deadline j) ≤
    (match s2 with | none => 0 | some j => job_deadline j))

/-- A state is relevant if it is not idle and its job arrived by the reference time. -/
def relevant_pstate [JobArrival Job] (reference_time : instant)
    (s : (processor_state Job).State) : Bool :=
  match s with
  | none => false
  | some j' => decide (job_arrival j' ≤ reference_time)

/-- A later time before the deadline of `j` at which a relevant job with an
earlier-or-equal deadline is scheduled (or `0`). -/
def find_swap_candidate [JobDeadline Job] [JobArrival Job]
    (sched : schedule (processor_state Job)) (t1 : instant) (j : Job) : Nat :=
  match search_arg sched (relevant_pstate t1) earlier_deadline t1 (job_deadline j) with
  | some t => t
  | none => 0

/-- Ensure the EDF property at `t1` by swapping if necessary. -/
def make_edf_at [JobDeadline Job] [JobArrival Job]
    (sched : schedule (processor_state Job)) (t1 : instant) : schedule (processor_state Job) :=
  match sched t1 with
  | none => sched
  | some j =>
    let t2 := find_swap_candidate sched t1 j
    swapped sched t1 t2

/-- Apply `make_edf_at` to every point up to the horizon. -/
def edf_transform_prefix [JobDeadline Job] [JobArrival Job]
    (sched : schedule (processor_state Job)) (horizon : instant) : schedule (processor_state Job) :=
  prefix_map sched make_edf_at horizon

/-- The EDF schedule: the last point of the EDF prefix through `t`. -/
def edf_transform [JobDeadline Job] [JobArrival Job]
    (sched : schedule (processor_state Job)) (t : instant) : (processor_state Job).State :=
  let edf_prefix := edf_transform_prefix sched (t + 1)
  edf_prefix t

end EDFTransformation

end Prosa.Analysis.Transform.EdfTrans
