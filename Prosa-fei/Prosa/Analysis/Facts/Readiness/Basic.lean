-- Translated from: ../rt-proofs/analysis/facts/readiness/basic.v
import Prosa.Analysis.Facts.Behavior.Completion
import Prosa.Model.Readiness.Basic

namespace Prosa.Analysis.Facts.Readiness.Basic

open Prosa.Behavior.Job
open Prosa.Behavior.Time
open Prosa.Behavior.Schedule
open Prosa.Behavior.Service
open Prosa.Behavior.Arrival_sequence
open Prosa.Behavior.Ready
open Prosa.Analysis.Facts.Behavior.Completion
open Prosa.Model.Readiness.Basic

section LiuAndLaylandReadiness

variable {Job : JobType}
variable {PState : Type _}
variable [ProcessorState Job PState]
variable [JobArrival Job] [JobCost Job]

theorem basic_readiness_compliance :
    ∀ sched : schedule PState,
      jobs_must_arrive_to_execute (Job := Job) sched →
      completed_jobs_dont_execute (Job := Job) sched →
      jobs_must_be_ready_to_execute (Job := Job) sched := by
  intro sched ARR COMP j t SCHED
  simp only [job_ready]
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true_eq_eq_false, decide_eq_false_iff_not]
  exact ⟨ARR j t SCHED, Nat.not_le.mpr (COMP j t SCHED)⟩

end LiuAndLaylandReadiness

end Prosa.Analysis.Facts.Readiness.Basic
