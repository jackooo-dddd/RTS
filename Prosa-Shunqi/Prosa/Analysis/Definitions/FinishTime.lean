-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: analysis/definitions/finish_time.v

import Mathlib.Data.Nat.Find
import Prosa.Behavior.Service

namespace Prosa.Analysis.Definitions.FinishTime

open Prosa.Behavior.Time
open Prosa.Behavior.Job
open Prosa.Behavior.Schedule
open Prosa.Behavior.Service

universe u v w

section JobFinishTime

variable {Job : JobType} [DecidableEq Job] [JobArrival Job] [JobCost Job]
variable {PState : ProcessorState Job}
variable (sched : schedule PState) (j : Job) (R : Nat)
variable (H_response_time_bounded : job_response_time_bound sched j R = true)
include R H_response_time_bounded

private theorem completion_witness :
    ∃ t : instant, completed_by sched j t = true := by
  refine ⟨job_arrival j + R, ?_⟩
  exact H_response_time_bounded

/-- The least instant at which `j` is complete, with the response-time bound
providing an existence witness. -/
noncomputable def finish_time : instant :=
  Nat.find (completion_witness sched j R H_response_time_bounded)

theorem finished_at_finish_time :
    completed_by sched j
      (finish_time sched j R H_response_time_bounded) = true := by
  exact Nat.find_spec (completion_witness sched j R H_response_time_bounded)

theorem earliest_finish_time (t : instant)
    (Hcompleted : completed_by sched j t = true) :
    finish_time sched j R H_response_time_bounded ≤ t := by
  exact Nat.find_min'
    (completion_witness sched j R H_response_time_bounded) Hcompleted

theorem completes_at_finish_time :
    completes_at sched j
      (finish_time sched j R H_response_time_bounded) = true := by
  let ft := finish_time sched j R H_response_time_bounded
  have Hfinished : completed_by sched j ft = true :=
    finished_at_finish_time sched j R H_response_time_bounded
  have Hpredecessor :
      ft = 0 ∨ completed_by sched j (ft - 1) = false := by
    by_cases Hzero : ft = 0
    · exact Or.inl Hzero
    · right
      cases Hbool : completed_by sched j (ft - 1) with
      | false => rfl
      | true =>
          have Hmin := earliest_finish_time sched j R
            H_response_time_bounded (ft - 1) Hbool
          have Hmin' : ft ≤ ft - 1 := by simpa [ft] using Hmin
          have Hlt : ft - 1 < ft :=
            Nat.sub_lt (Nat.pos_of_ne_zero Hzero) (by decide)
          exact (Nat.not_le_of_gt Hlt Hmin').elim
  change ((!completed_by sched j (ft - 1) || decide (ft = 0)) &&
    completed_by sched j ft) = true
  rcases Hpredecessor with Hzero | Hfalse
  · simpa [Hzero] using Hfinished
  · simp [Hfalse, Hfinished]

/-- Exact response time, with natural (truncated) subtraction. -/
noncomputable def response_time : duration :=
  finish_time sched j R H_response_time_bounded - job_arrival j

end JobFinishTime

end Prosa.Analysis.Definitions.FinishTime
