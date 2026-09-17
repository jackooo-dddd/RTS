-- Translated from: ../rt-proofs/analysis/transform/edf_trans.v
import Prosa.Analysis.Transform.Prefix
import Prosa.Analysis.Transform.Swap
import Prosa.Analysis.Facts.Model.Ideal_schedule

namespace Prosa.Analysis.Transform.Edf_trans

open Prosa.Behavior.Job
open Prosa.Behavior.Time
open Prosa.Behavior.Schedule
open Prosa.Model.Processor.Ideal
open Prosa.Analysis.Transform.Prefix
open Prosa.Analysis.Transform.Swap
open Prosa.Util.Search_arg

section EDFTransformation

variable {Job : JobType} [JobCost Job] [JobDeadline Job] [JobArrival Job]

abbrev PState (Job : JobType) := processor_state Job
abbrev SchedType (Job : JobType) := schedule (PState Job)

def earlier_deadline [DecidableEq Job] (s1 s2 : PState Job) : Bool :=
  decide ((s1.elim 0 job_deadline) ≤ (s2.elim 0 job_deadline))

def relevant_pstate (reference_time : instant) (s : PState Job) : Bool :=
  match s with
  | none => false
  | some j' => decide (job_arrival j' ≤ reference_time)

def find_swap_candidate [DecidableEq Job] (sched : SchedType Job) (t1 : instant) (j : Job) : instant :=
  match search_arg sched (relevant_pstate t1) (earlier_deadline (Job := Job)) t1 (job_deadline j) with
  | some t => t
  | none => 0

def make_edf_at [DecidableEq Job] (sched : SchedType Job) (t1 : instant) : SchedType Job :=
  match sched t1 with
  | none => sched
  | some j =>
    let t2 := find_swap_candidate sched t1 j
    swapped sched t1 t2

def edf_transform_prefix [DecidableEq Job] (sched : SchedType Job) (horizon : instant) : SchedType Job :=
  prefix_map sched (make_edf_at (Job := Job)) horizon

def edf_transform [DecidableEq Job] (sched : SchedType Job) (t : instant) : processor_state Job :=
  let edf_prefix := edf_transform_prefix sched (t + 1)
  edf_prefix t

end EDFTransformation

end Prosa.Analysis.Transform.Edf_trans
