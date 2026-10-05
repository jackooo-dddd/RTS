-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: model/task/arrival/sporadic_as_curve.v

import Prosa.Util.All
import Prosa.Model.Task.Arrival.Curves
import Prosa.Analysis.Facts.Sporadic.ArrivalBound

namespace Prosa.Model.Task.Arrival.SporadicAsCurve

open Prosa.Behavior.Arrival_sequence
open Prosa.Behavior.Job
open Prosa.Behavior.Time
open Prosa.Model.Task.Concept
open Prosa.Model.Task.Arrival.Sporadic
open Prosa.Model.Task.Arrival.Curves
open Prosa.Analysis.Facts.Sporadic.ArrivalBound
open Prosa.Util.Div_mod

/-! Representation notes: the source `Global Program Instance
MaxArrivalsSporadic : MaxArrivals Task := max_sporadic_arrivals` is a Lean
global instance; the Boolean `valid_task_min_inter_arrival_time` hypothesis
is `= true`; `tsk \in ts` is `decide (tsk ∈ ts) = true`. Binder orders follow
the elaborated types. -/

/-- The sporadic bound `⌈Δ / T⌉` is the arrival curve of a sporadic task. -/
instance MaxArrivalsSporadic {Task : TaskType} [DecidableEq Task] [SporadicModel Task] :
    MaxArrivals Task :=
  ⟨max_sporadic_arrivals⟩

/-- The sporadic bound is a valid arrival curve. -/
theorem sporadic_arrival_curve_valid {Task : TaskType} [DecidableEq Task] [SporadicModel Task]
    (tsk : Task) : valid_arrival_curve (max_sporadic_arrivals tsk) := by
  refine ⟨div_ceil0 _, ?_⟩
  intro d1 d2 h
  exact decide_eq_true (div_ceil_monotone1 _ _ _ (of_decide_eq_true h))

/-- Every task of a task set has a valid (sporadic) arrival curve. -/
theorem sporadic_task_sets_arrival_curve_valid {Task : TaskType} [DecidableEq Task]
    [SporadicModel Task] (ts : TaskSet Task) :
    valid_taskset_arrival_curve ts (MaxArrivalsSporadic (Task := Task)).max_arrivals :=
  fun tsk _ => sporadic_arrival_curve_valid tsk

/-- A sporadic task respects its sporadic arrival curve. -/
theorem sporadic_arrival_curve_respects_max_arrivals {Task : TaskType} [DecidableEq Task]
    [SporadicModel Task] {Job : JobType} [DecidableEq Job] [JobTask Job Task] [JobArrival Job]
    (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
      ∀ tsk : Task, respects_sporadic_task_model arr_seq tsk →
        valid_task_min_inter_arrival_time tsk = true →
          respects_max_arrivals arr_seq tsk (max_sporadic_arrivals tsk) := by
  intro hvalid tsk hspor hT t1 t2 _
  exact sporadic_task_arrivals_bound arr_seq hvalid tsk hspor hT t1 t2

/-- A sporadic task set respects its sporadic arrival curves. -/
theorem sporadic_task_sets_respects_max_arrivals {Task : TaskType} [DecidableEq Task]
    [SporadicModel Task] {Job : JobType} [DecidableEq Job] [JobTask Job Task] [JobArrival Job]
    (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
      ∀ ts : TaskSet Task, valid_taskset_inter_arrival_times ts →
        taskset_respects_sporadic_task_model ts arr_seq →
          @taskset_respects_max_arrivals Task _ Job _ _ arr_seq MaxArrivalsSporadic ts := by
  intro hvalid ts hval hspo tsk hin
  exact sporadic_arrival_curve_respects_max_arrivals arr_seq hvalid tsk (hspo tsk hin)
    (hval tsk hin)

end Prosa.Model.Task.Arrival.SporadicAsCurve
