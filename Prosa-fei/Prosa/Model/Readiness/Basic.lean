-- Translated from: ../rt-proofs/model/readiness/basic.v
import Prosa.Behavior.All

namespace Prosa.Model.Readiness.Basic

open Prosa.Behavior.Job
open Prosa.Behavior.Time
open Prosa.Behavior.Schedule
open Prosa.Behavior.Service
open Prosa.Behavior.Ready
open Prosa.Behavior.Arrival_sequence

section LiuAndLaylandReadiness

variable {Job : JobType}
variable {PState : Type _}
variable [ProcessorState Job PState]
variable [JobArrival Job] [JobCost Job]

noncomputable instance basic_ready_instance : JobReady Job PState where
  job_ready sched j t :=
    (job_arrival j ≤ t) && !(service sched j t ≥ job_cost j)
  ready_implies_pending := by
    intro sched j t h
    simp only [pending, has_arrived, completed_by]
    simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true_eq_eq_false,
      decide_eq_false_iff_not] at h
    exact h

end LiuAndLaylandReadiness

end Prosa.Model.Readiness.Basic
