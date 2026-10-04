-- Authoritative source:
-- ProsaBuddy classic Prosa (prosabuddy commit f692cb7479780cf6009493f373a309e13165201c)
-- source: classic/model/schedule/uni/limited/rbf.v
-- sha256: see Prosa-Shunqi/classic-prosa/comprehensive-classic/file_order.csv (rank 106)

import Prosa.Classic.Util.All
import Prosa.Classic.Model.Time
import Prosa.Classic.Model.Arrival.Basic.Job
import Prosa.Classic.Model.Arrival.Basic.TaskArrival
import Prosa.Classic.Model.Priority
import Prosa.Classic.Model.Arrival.Basic.ArrivalSequence
import Prosa.Classic.Model.Schedule.Uni.Schedule
import Prosa.Classic.Model.Arrival.Curves.Bounds
import Prosa.Classic.Analysis.Uni.ArrivalCurves.WorkloadBound

/-!
Properties of the task request bound function (Rocq module `RBF`).

Representation notes: MathComp `monotone leq f` is `Prosa.Util.Rel.monotone (fun a b => decide (a ≤ b)) f`; the
section-local `Let task_rbf` is unfolded. Binder lists follow the Rocq contract (e.g. `task_rbf_0_zero` and
`task_rbf_monotone` take neither `job_arrival` nor the priority hypotheses).
-/

set_option linter.unusedVariables false

namespace Prosa.Classic.Model.Schedule.Uni.Limited.Rbf.RBF

open Prosa.Classic.Model.Time.Time
open Prosa.Classic.Model.Arrival.Basic.ArrivalSequence.ArrivalSequence
open Prosa.Classic.Model.Arrival.Basic.TaskArrival.TaskArrival
open Prosa.Classic.Model.Arrival.Curves.Bounds.ArrivalCurves
open Prosa.Classic.Analysis.Uni.ArrivalCurves.WorkloadBound.MaxArrivalsWorkloadBound (task_request_bound_function)

universe u v

local macro "omega'" : tactic =>
  `(tactic| ((try dsimp only [Prosa.Classic.Model.Time.Time.time,
    Prosa.Classic.Model.Time.Time.instant, Prosa.Classic.Model.Time.Time.duration] at *) <;>
    omega))

theorem task_rbf_0_zero {Task : Type u} [DecidableEq Task] (task_cost : Task → time) {Job : Type v} [DecidableEq Job]
    (job_task : Job → Task) (arr_seq : arrival_sequence Job) (tsk : Task) (max_arrivals : Task → time → Nat)
    (H_proper_arrival_curve : proper_arrival_curve job_task arr_seq max_arrivals tsk) :
    task_request_bound_function task_cost max_arrivals tsk 0 = 0 := by
  unfold task_request_bound_function
  rw [H_proper_arrival_curve.2.1, Nat.mul_zero]

theorem task_rbf_monotone {Task : Type u} [DecidableEq Task] (task_cost : Task → time) {Job : Type v}
    [DecidableEq Job] (job_task : Job → Task) (arr_seq : arrival_sequence Job) (tsk : Task)
    (max_arrivals : Task → time → Nat)
    (H_proper_arrival_curve : proper_arrival_curve job_task arr_seq max_arrivals tsk) :
    Prosa.Util.Rel.monotone (fun a b : Nat => decide (a ≤ b)) (task_request_bound_function task_cost max_arrivals tsk) := by
  intro x y LE
  have := H_proper_arrival_curve.2.2 x y LE
  simp only [decide_eq_true_eq] at this LE ⊢
  unfold task_request_bound_function
  exact Nat.mul_le_mul_left _ this

theorem task_rbf_1_ge_task_cost {Task : Type u} [DecidableEq Task] (task_cost : Task → time) {Job : Type v}
    [DecidableEq Job] (job_arrival : Job → time) (job_task : Job → Task) (arr_seq : arrival_sequence Job)
    (H_arrival_times_are_consistent : arrival_times_are_consistent job_arrival arr_seq) (tsk : Task)
    (max_arrivals : Task → time → Nat)
    (H_proper_arrival_curve : proper_arrival_curve job_task arr_seq max_arrivals tsk) (j : Job)
    (H_j_arrives : arrives_in arr_seq j) (H_job_of_tsk : job_task j = tsk) :
    task_cost tsk ≤ task_request_bound_function task_cost max_arrivals tsk 1 := by
  have ARRB := H_proper_arrival_curve.1 (job_arrival j) (job_arrival j + 1) (Nat.le_succ _)
  rw [show job_arrival j + 1 - job_arrival j = 1 by omega'] at ARRB
  have IN : j ∈ arrivals_of_task_between job_task arr_seq tsk (job_arrival j) (job_arrival j + 1) := by
    unfold arrivals_of_task_between
    rw [List.mem_filter]
    refine ⟨arrived_between_implies_in_arrivals job_arrival arr_seq H_arrival_times_are_consistent j _ _ H_j_arrives
      (by simp only [arrived_between, Bool.and_eq_true, decide_eq_true_eq]; constructor <;> omega'), ?_⟩
    simp [is_job_of_task, H_job_of_tsk]
  have POS : 1 ≤ num_arrivals_of_task job_task arr_seq tsk (job_arrival j) (job_arrival j + 1) :=
    List.length_pos_of_mem IN
  unfold task_request_bound_function
  calc task_cost tsk = task_cost tsk * 1 := (Nat.mul_one _).symm
    _ ≤ _ := Nat.mul_le_mul_left _ (by omega)

end Prosa.Classic.Model.Schedule.Uni.Limited.Rbf.RBF
