-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: model/task/arrival/curve_as_rbf.v

import Prosa.Model.Task.Arrival.RequestBoundFunctions
import Prosa.Model.Task.Arrival.Curves

namespace Prosa.Model.Task.Arrival.CurveAsRbf

open Prosa.Behavior.Arrival_sequence
open Prosa.Behavior.Job
open Prosa.Behavior.Time
open Prosa.Model.Task.Concept
open Prosa.Model.Task.Arrivals
open Prosa.Model.Task.Arrival.RequestBoundFunctions
open Prosa.Model.Task.Arrival.Curves

universe u

/-! ## Converting an arrival curve + WCET/BCET to a request-bound function -/

/-- Upper-bounding conversion: task cost times the number of arrivals. -/
def task_max_rbf {Task : TaskType} [DecidableEq Task] [TaskCost Task]
    (arrivals : Task → duration → Nat) (task : Task) (Δ : duration) : Nat :=
  task_cost task * arrivals task Δ

/-- Lower-bounding conversion: task min-cost times the number of arrivals. -/
def task_min_rbf {Task : TaskType} [DecidableEq Task] [TaskMinCost Task]
    (arrivals : Task → duration → Nat) (task : Task) (Δ : duration) : Nat :=
  task_min_cost task * arrivals task Δ

/-- The converted maximum arrival curve is a request-bound function (global,
as in the source). -/
instance MaxArrivalsRBF {Task : TaskType} [DecidableEq Task] [TaskCost Task]
    [MaxArrivals Task] : MaxRequestBound Task where
  max_request_bound := task_max_rbf max_arrivals

/-- The converted minimum arrival curve is a request-bound function. -/
instance MinArrivalsRBF {Task : TaskType} [DecidableEq Task] [TaskMinCost Task]
    [MinArrivals Task] : MinRequestBound Task where
  min_request_bound := task_min_rbf min_arrivals

/-! Proof-local fact: a sum over a list is bounded by a uniform bound times
its length (and conversely). -/

private theorem sum_map_le_mul {α : Type u} (f : α → Nat) (c : Nat) :
    ∀ xs : List α, (∀ x, x ∈ xs → f x ≤ c) → (xs.map f).sum ≤ c * xs.length
  | [] => fun _ => by simp
  | a :: xs => fun h => by
      have ih := sum_map_le_mul f c xs (fun x hx => h x (List.mem_cons_of_mem a hx))
      have ha := h a List.mem_cons_self
      simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.mul_succ]
      omega

private theorem mul_le_sum_map {α : Type u} (f : α → Nat) (c : Nat) :
    ∀ xs : List α, (∀ x, x ∈ xs → c ≤ f x) → c * xs.length ≤ (xs.map f).sum
  | [] => fun _ => by simp
  | a :: xs => fun h => by
      have ih := mul_le_sum_map f c xs (fun x hx => h x (List.mem_cons_of_mem a hx))
      have ha := h a List.mem_cons_self
      simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.mul_succ]
      omega

private theorem job_task_of_mem {Task : TaskType} [DecidableEq Task]
    {Job : JobType} [DecidableEq Job] [JobTask Job Task]
    (arr_seq : arrival_sequence Job) (tsk : Task) (t1 t2 : instant) (j : Job)
    (h : j ∈ task_arrivals_between arr_seq tsk t1 t2) : job_task (Task := Task) j = tsk := by
  unfold task_arrivals_between at h
  have := (List.mem_filter.mp h).2
  unfold job_of_task at this
  exact of_decide_eq_true this

section SingleTask

theorem valid_arrival_curve_to_max_rbf {Task : TaskType} [DecidableEq Task] [TaskCost Task]
    (tsk : Task) (arrivals : Task → duration → Nat) :
    valid_arrival_curve (arrivals tsk) →
      valid_request_bound_function (task_max_rbf arrivals tsk) := by
  intro ⟨hzero, hmono⟩
  refine ⟨?_, ?_⟩
  · simp only [task_max_rbf, hzero, Nat.mul_zero]
  · intro x y hxy
    have := of_decide_eq_true (hmono x y hxy)
    exact decide_eq_true (Nat.mul_le_mul_left _ this)

theorem valid_arrival_curve_to_min_rbf {Task : TaskType} [DecidableEq Task] [TaskMinCost Task]
    (tsk : Task) (arrivals : Task → duration → Nat) :
    valid_arrival_curve (arrivals tsk) →
      valid_request_bound_function (task_min_rbf arrivals tsk) := by
  intro ⟨hzero, hmono⟩
  refine ⟨?_, ?_⟩
  · simp only [task_min_rbf, hzero, Nat.mul_zero]
  · intro x y hxy
    have := of_decide_eq_true (hmono x y hxy)
    exact decide_eq_true (Nat.mul_le_mul_left _ this)

theorem respects_arrival_curve_to_max_rbf {Task : TaskType} [DecidableEq Task] [TaskCost Task]
    {Job : JobType} [DecidableEq Job] [JobTask Job Task] [JobCost Job]
    [MaxArr : MaxArrivals Task] (tsk : Task) (arr_seq : arrival_sequence Job) :
    jobs_have_valid_job_costs (Task := Task) (Job := Job) →
      respects_max_arrivals arr_seq tsk (max_arrivals tsk) →
        respects_max_request_bound arr_seq tsk (task_max_rbf max_arrivals tsk) := by
  intro hcost hresp t1 t2 hle
  have hr := hresp t1 t2 hle
  have hsum : cost_of_task_arrivals arr_seq tsk t1 t2 ≤
      task_cost tsk * number_of_task_arrivals arr_seq tsk t1 t2 := by
    unfold cost_of_task_arrivals number_of_task_arrivals
    refine sum_map_le_mul _ _ _ (fun j hj => ?_)
    have hv := of_decide_eq_true (hcost j)
    rw [job_task_of_mem arr_seq tsk t1 t2 j hj] at hv
    exact hv
  exact Nat.le_trans hsum (Nat.mul_le_mul_left _ hr)

theorem respects_arrival_curve_to_min_rbf {Task : TaskType} [DecidableEq Task] [TaskMinCost Task]
    {Job : JobType} [DecidableEq Job] [JobTask Job Task] [JobCost Job]
    [MinArr : MinArrivals Task] (tsk : Task) (arr_seq : arrival_sequence Job) :
    jobs_have_valid_min_job_costs (Task := Task) (Job := Job) →
      respects_min_arrivals arr_seq tsk (min_arrivals tsk) →
        respects_min_request_bound arr_seq tsk (task_min_rbf min_arrivals tsk) := by
  intro hcost hresp t1 t2 hle
  have hr := hresp t1 t2 hle
  have hsum : task_min_cost tsk * number_of_task_arrivals arr_seq tsk t1 t2 ≤
      cost_of_task_arrivals arr_seq tsk t1 t2 := by
    unfold cost_of_task_arrivals number_of_task_arrivals
    refine mul_le_sum_map _ _ _ (fun j hj => ?_)
    have hv := of_decide_eq_true (hcost j)
    rw [job_task_of_mem arr_seq tsk t1 t2 j hj] at hv
    exact hv
  exact Nat.le_trans (Nat.mul_le_mul_left _ hr) hsum

end SingleTask

section TaskSet

theorem valid_taskset_arrival_curve_to_max_rbf {Task : TaskType} [DecidableEq Task]
    [TaskCost Task] [MaxArr : MaxArrivals Task] (ts : TaskSet Task) :
    valid_taskset_arrival_curve ts max_arrivals →
      valid_taskset_request_bound_function ts max_request_bound :=
  fun h tsk hin => valid_arrival_curve_to_max_rbf tsk max_arrivals (h tsk hin)

theorem valid_taskset_arrival_curve_to_min_rbf {Task : TaskType} [DecidableEq Task]
    [TaskMinCost Task] [MinArr : MinArrivals Task] (ts : TaskSet Task) :
    valid_taskset_arrival_curve ts min_arrivals →
      valid_taskset_request_bound_function ts min_request_bound :=
  fun h tsk hin => valid_arrival_curve_to_min_rbf tsk min_arrivals (h tsk hin)

theorem taskset_respects_arrival_curve_to_max_rbf {Task : TaskType} [DecidableEq Task]
    [TaskCost Task] {Job : JobType} [DecidableEq Job] [JobTask Job Task] [JobCost Job]
    [MaxArr : MaxArrivals Task] (ts : TaskSet Task) (arr_seq : arrival_sequence Job) :
    jobs_have_valid_job_costs (Task := Task) (Job := Job) →
      taskset_respects_max_arrivals arr_seq ts →
        taskset_respects_max_request_bound arr_seq ts :=
  fun hcost h tsk hin => respects_arrival_curve_to_max_rbf tsk arr_seq hcost (h tsk hin)

theorem taskset_respects_arrival_curve_to_min_rbf {Task : TaskType} [DecidableEq Task]
    [TaskMinCost Task] {Job : JobType} [DecidableEq Job] [JobTask Job Task] [JobCost Job]
    [MinArr : MinArrivals Task] (ts : TaskSet Task) (arr_seq : arrival_sequence Job) :
    jobs_have_valid_min_job_costs (Task := Task) (Job := Job) →
      taskset_respects_min_arrivals arr_seq ts →
        taskset_respects_min_request_bound arr_seq ts :=
  fun hcost h tsk hin => respects_arrival_curve_to_min_rbf tsk arr_seq hcost (h tsk hin)

end TaskSet

end Prosa.Model.Task.Arrival.CurveAsRbf
