-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: analysis/facts/model/dbf.v

import Prosa.Model.Task.AbsoluteDeadline
import Prosa.Analysis.Definitions.DemandBoundFunction
import Prosa.Analysis.Facts.Model.Rbf
import Prosa.Analysis.Facts.Model.Workload

namespace Prosa.Analysis.Facts.Model.Dbf

open Prosa.Behavior.Arrival_sequence
open Prosa.Behavior.Job
open Prosa.Behavior.Time
open Prosa.Model.Task.Concept
open Prosa.Model.Task.Arrivals
open Prosa.Model.Task.Arrival.Curves
open Prosa.Model.Task.AbsoluteDeadline
open Prosa.Model.Aggregate.Workload
open Prosa.Util.Sum
open Prosa.Analysis.Definitions.RequestBoundFunction
open Prosa.Analysis.Definitions.DemandBoundFunction
open Prosa.Analysis.Facts.Behavior.Arrivals
open Prosa.Analysis.Facts.Model.Workload
open Prosa.Analysis.Facts.Model.Rbf

/-! Facts about the demand-bound function. Binders follow the elaborated source
types, including the task-cost, job-cost and arrival-curve instances that the
source section introduces after its first hypothesis (they are instance
binders at the same place). Representation: the job deadline is the accepted
`job_deadline_from_task_deadline` instance, named explicitly; the local
`let causing_demand` of the two definitions is kept; `x \in xs` in `Prop`
position is `decide (x ∈ xs) = true`; `\sum_(x <- xs) F x` is the accepted
`sumSeq xs F`. -/

macro "omega'" : tactic => `(tactic| (try dsimp only [instant, duration, work] at *) <;> omega)

/-- The demand of the jobs of `tsk` that arrive in `[t1, t2)` with a deadline
by `t2`. -/
def task_demand_within {Task : TaskType} [DecidableEq Task] [TaskDeadline Task]
    {Job : JobType} [DecidableEq Job] [JobTask Job Task] [JobArrival Job]
    (arr_seq : arrival_sequence Job) [JobCost Job] (tsk : Task) (t1 t2 : instant) : Nat :=
  let causing_demand := fun j : Job =>
    decide (@job_deadline Job _ (job_deadline_from_task_deadline Job Task) j ≤ t2) && job_of_task tsk j
  workload_of_jobs causing_demand (arrivals_between arr_seq t1 t2)

/-- The demand of all jobs that arrive in `[t1, t2)` with a deadline by `t2`. -/
def total_demand_within {Task : TaskType} [DecidableEq Task] [TaskDeadline Task]
    {Job : JobType} [DecidableEq Job] [JobTask Job Task] [JobArrival Job]
    (arr_seq : arrival_sequence Job) [JobCost Job] (t1 t2 : instant) : Nat :=
  let causing_demand := fun j : Job =>
    decide (@job_deadline Job _ (job_deadline_from_task_deadline Job Task) j ≤ t2)
  workload_of_jobs causing_demand (arrivals_between arr_seq t1 t2)

theorem task_arrivals_with_deadline_within_eq {Task : TaskType} [DecidableEq Task]
    [TaskDeadline Task] {Job : JobType} [DecidableEq Job] [JobTask Job Task] [JobArrival Job]
    (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
      ∀ (tsk : Task) (t : instant) (delta : duration),
        @task_arrivals_with_deadline_within Job _ Task _ _ arr_seq tsk
            (job_deadline_from_task_deadline Job Task) t (t + delta) =
          task_arrivals_between arr_seq tsk t (t + (delta - (task_deadline tsk - 1))) := by
  intro hva tsk t delta
  unfold task_arrivals_with_deadline_within task_arrivals_between
  have hm1 : t ≤ t + (delta - (task_deadline tsk - 1)) := Nat.le_add_right _ _
  have hm2 : t + (delta - (task_deadline tsk - 1)) ≤ t + delta := by omega'
  rw [arrivals_between_cat arr_seq t _ (t + delta) hm1 hm2, List.filter_append]
  have h2 : (arrivals_between arr_seq (t + (delta - (task_deadline tsk - 1))) (t + delta)).filter
      (fun j => job_of_task tsk j &&
        decide (@job_deadline Job _ (job_deadline_from_task_deadline Job Task) j ≤ t + delta)) = [] := by
    rw [List.filter_eq_nil_iff]
    intro j hj
    have hb := job_arrival_between arr_seq hva.1 j _ _ (decide_eq_true hj)
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hb ⊢
    intro ⟨hjt, hdl⟩
    have htsk : job_task (Task := Task) j = tsk := of_decide_eq_true hjt
    change job_arrival j + task_deadline (job_task (Task := Task) j) ≤ t + delta at hdl
    rw [htsk] at hdl
    omega'
  rw [h2, List.append_nil]
  apply List.filter_congr
  intro j hj
  have hb := job_arrival_between arr_seq hva.1 j _ _ (decide_eq_true hj)
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hb
  cases hjt : job_of_task tsk j with
  | false => rfl
  | true =>
      have htsk : job_task (Task := Task) j = tsk := of_decide_eq_true hjt
      simp only [Bool.true_and, decide_eq_true_eq]
      change job_arrival j + task_deadline (job_task (Task := Task) j) ≤ t + delta
      rw [htsk]
      omega'

theorem num_task_arrivals_with_deadline_within_eq {Task : TaskType} [DecidableEq Task]
    [TaskDeadline Task] {Job : JobType} [DecidableEq Job] [JobTask Job Task] [JobArrival Job]
    (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
      ∀ (tsk : Task) (t : instant) (delta : duration),
        @number_of_task_arrivals_with_deadline_within Job _ Task _ _ arr_seq tsk
            (job_deadline_from_task_deadline Job Task) t (t + delta) =
          number_of_task_arrivals arr_seq tsk t (t + (delta - (task_deadline tsk - 1))) := by
  intro hva tsk t delta
  unfold number_of_task_arrivals_with_deadline_within number_of_task_arrivals
  rw [task_arrivals_with_deadline_within_eq arr_seq hva tsk t delta]

/-- The task demand within `[t, t + delta)` is the task workload of the arrivals
in the shifted window. -/
private theorem task_demand_within_eq {Task : TaskType} [DecidableEq Task]
    [TaskDeadline Task] {Job : JobType} [DecidableEq Job] [JobTask Job Task] [JobArrival Job]
    (arr_seq : arrival_sequence Job) [JobCost Job] (hva : valid_arrival_sequence arr_seq)
    (tsk : Task) (t : instant) (delta : duration) :
    task_demand_within arr_seq tsk t (t + delta) =
      task_workload_between arr_seq tsk t (t + (delta - (task_deadline tsk - 1))) := by
  have h := task_arrivals_with_deadline_within_eq arr_seq hva tsk t delta
  unfold task_arrivals_with_deadline_within task_arrivals_between at h
  unfold task_demand_within task_workload_between task_workload workload_of_jobs sumFiltered
  simp only
  rw [← h]
  congr 2
  apply List.filter_congr
  intro j _
  rw [Bool.and_comm]

private theorem sumFiltered_true' {I : Type _} (r : List I) (F : I → Nat) :
    sumFiltered r (fun _ => true) F = sumSeq r F := by
  unfold sumFiltered sumSeq; rw [List.filter_true]

theorem task_demand_within_le_task_dbf {Task : TaskType} [DecidableEq Task] [TaskDeadline Task]
    {Job : JobType} [DecidableEq Job] [JobTask Job Task] [JobArrival Job]
    (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
      ∀ [TaskCost Task] [JobCost Job], arrivals_have_valid_job_costs (Task := Task) arr_seq →
        ∀ (ts : List Task) [MaxArrivals Task], taskset_respects_max_arrivals arr_seq ts →
          ∀ (tsk : Task) (t : instant) (delta : Nat), decide (tsk ∈ ts) = true →
            task_demand_within arr_seq tsk t (t + delta) ≤ task_demand_bound_function tsk delta := by
  intro hva _ _ hcost ts _ hresp tsk t delta hin
  rw [task_demand_within_eq arr_seq hva tsk t delta]
  exact rbf_spec arr_seq hcost tsk (hresp tsk hin) t _

theorem task_demand_within_le_task_rbf_shifted {Task : TaskType} [DecidableEq Task]
    [TaskDeadline Task] {Job : JobType} [DecidableEq Job] [JobTask Job Task] [JobArrival Job]
    (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
      ∀ [TaskCost Task] [JobCost Job], arrivals_have_valid_job_costs (Task := Task) arr_seq →
        ∀ (ts : List Task) [MaxArrivals Task], taskset_respects_max_arrivals arr_seq ts →
          ∀ (tsk : Task) (t : instant) (delta : Nat), decide (tsk ∈ ts) = true →
            task_demand_within arr_seq tsk t (t + delta) ≤
              task_request_bound_function tsk (delta - (task_deadline tsk - 1)) := by
  intro hva _ _ hcost ts _ hresp tsk t delta hin
  exact task_demand_within_le_task_dbf arr_seq hva hcost ts hresp tsk t delta hin

theorem total_demand_within_le_total_dbf {Task : TaskType} [DecidableEq Task] [TaskDeadline Task]
    {Job : JobType} [DecidableEq Job] [JobTask Job Task] [JobArrival Job]
    (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
      ∀ [TaskCost Task] [JobCost Job], arrivals_have_valid_job_costs (Task := Task) arr_seq →
        ∀ (ts : List Task) [MaxArrivals Task], taskset_respects_max_arrivals arr_seq ts →
          all_jobs_from_taskset arr_seq ts →
          ∀ (t : instant) (delta : duration),
            total_demand_within (Task := Task) arr_seq t (t + delta) ≤ total_demand_bound_function ts delta := by
  intro hva _ _ hcost ts _ hresp hall t delta
  have hpart := workload_of_jobs_le_sum_over_partitions (Task := Task)
    (fun j : Job => decide (@job_deadline Job _ (job_deadline_from_task_deadline Job Task) j ≤ t + delta))
    (fun _ => true) (arrivals_between arr_seq t (t + delta)) ts
    (fun j hj => hall j (in_arrivals_implies_arrived arr_seq j _ _ hj)) (fun _ _ _ => rfl)
  refine Nat.le_trans hpart ?_
  unfold total_demand_bound_function
  rw [← sumFiltered_true']
  apply leq_sum_seq
  intro tsk hin _
  refine Nat.le_trans (Nat.le_of_eq ?_)
    (task_demand_within_le_task_dbf arr_seq hva hcost ts hresp tsk t delta (decide_eq_true hin))
  rfl

theorem total_demand_within_le_sum_task_rbf_shifted {Task : TaskType} [DecidableEq Task]
    [TaskDeadline Task] {Job : JobType} [DecidableEq Job] [JobTask Job Task] [JobArrival Job]
    (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
      ∀ [TaskCost Task] [JobCost Job], arrivals_have_valid_job_costs (Task := Task) arr_seq →
        ∀ (ts : List Task) [MaxArrivals Task], taskset_respects_max_arrivals arr_seq ts →
          all_jobs_from_taskset arr_seq ts →
          ∀ t delta : instant,
            total_demand_within (Task := Task) arr_seq t (t + delta) ≤
              sumSeq ts (fun tsk => task_request_bound_function tsk (delta - (task_deadline tsk - 1))) := by
  intro hva _ _ hcost ts _ hresp hall t delta
  exact total_demand_within_le_total_dbf arr_seq hva hcost ts hresp hall t delta

end Prosa.Analysis.Facts.Model.Dbf
