-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: analysis/facts/priority/fifo_ahep_bound.v

import Prosa.Analysis.Facts.Interference
import Prosa.Analysis.Facts.Model.RestrictedSupply.Schedule
import Prosa.Analysis.Facts.Priority.Fifo
import Prosa.Analysis.Facts.Model.Rbf

namespace Prosa.Analysis.Facts.Priority.FifoAhepBound

open Prosa.Behavior.Arrival_sequence
open Prosa.Behavior.Job
open Prosa.Behavior.Ready
open Prosa.Behavior.Schedule
open Prosa.Behavior.Time
open Prosa.Model.Job.Properties
open Prosa.Model.Task.Concept
open Prosa.Model.Task.Arrival.Curves
open Prosa.Model.Priority.Definitions
open Prosa.Model.Priority.Fifo
open Prosa.Model.Processor.PlatformProperties
open Prosa.Model.Aggregate.Workload
open Prosa.Model.Aggregate.ServiceOfJobs
open Prosa.Util.Sum
open Prosa.Analysis.Definitions.Interference
open Prosa.Analysis.Definitions.RequestBoundFunction
open Prosa.Analysis.Facts.Interference
open Prosa.Analysis.Facts.Behavior.Arrivals
open Prosa.Analysis.Facts.Model.Workload
open Prosa.Analysis.Facts.Model.ServiceOfJobs
open Prosa.Analysis.Facts.Model.ArrivalCurves
open Prosa.Analysis.Facts.Model.Rbf

/-! Under FIFO on a unit-supply uniprocessor, the interference from other
higher-or-equal-priority jobs within a busy interval is bounded by the total
request-bound function at the job's relative arrival plus one, minus the cost
of the task under analysis.

Binders follow the elaborated source type: the section inputs and hypotheses
the lemma uses, in their elaborated order. The JLFP policy is the accepted
global FIFO instance, as elaborated. The busy interval is the classical one
of `analysis/definitions/busy_interval/classical.v`. Representation: a
Boolean in `Prop` position is `= true`; `x \in xs` is `decide (x ∈ xs) = true`;
`\sum_(x <- xs) F x` is the accepted `sumSeq xs F`; `ε` is `1`. -/

/-- A job's cost is at most the workload of any list containing it that it satisfies. -/
private theorem job_cost_le_workload {Job : JobType} [DecidableEq Job] [JobCost Job]
    (P : Job → Bool) (l : List Job) (j : Job) (hj : j ∈ l) (hP : P j = true) :
    job_cost j ≤ workload_of_jobs P l := by
  unfold workload_of_jobs sumFiltered
  exact List.le_sum_of_mem (List.mem_map.mpr ⟨j, List.mem_filter.mpr ⟨hj, hP⟩, rfl⟩)

/-- Splitting one member off a sum of differences. -/
private theorem sum_sub_le {α : Type _} [DecidableEq α] (l : List α) (x : α) (hx : x ∈ l)
    (f g : α → Nat) (c d : Nat) (hfg : ∀ y ∈ l, f y ≤ g y) (hxd : f x - c ≤ g x - d)
    (hc : c ≤ f x) (hd : d ≤ g x) :
    (l.map f).sum - c ≤ (l.map g).sum - d := by
  induction l with
  | nil => exact absurd hx (List.not_mem_nil)
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons]
    have hfa := hfg a List.mem_cons_self
    have hrest : (l.map f).sum ≤ (l.map g).sum :=
      List.sum_le_sum (fun y hy => hfg y (List.mem_cons_of_mem a hy))
    by_cases hax : a = x
    · subst hax; omega
    · have hxl : x ∈ l := by
        rcases List.mem_cons.mp hx with h | h
        · exact absurd h.symm hax
        · exact h
      have hfl : f x ≤ (l.map f).sum := List.le_sum_of_mem (List.mem_map_of_mem hxl)
      have hgl : g x ≤ (l.map g).sum := List.le_sum_of_mem (List.mem_map_of_mem hxl)
      have := ih hxl (fun y hy => hfg y (List.mem_cons_of_mem a hy))
      omega

theorem bound_on_hep_workload {Task : TaskType} [DecidableEq Task] [TaskCost Task] [MaxArrivals Task]
    {Job : JobType} [DecidableEq Job] [JobTask Job Task] [JobCost Job] [JobArrival Job]
    {PState : ProcessorState Job} :
    uniprocessor_model PState → unit_supply_proc_model PState →
    ∀ arr_seq : arrival_sequence Job, valid_arrival_sequence arr_seq →
      arrivals_have_valid_job_costs (Task := Task) arr_seq →
    ∀ ts : List Task, all_jobs_from_taskset arr_seq ts → taskset_respects_max_arrivals arr_seq ts →
      valid_taskset_arrival_curve ts max_arrivals →
    ∀ tsk : Task, decide (tsk ∈ ts) = true →
    ∀ sched : schedule PState, jobs_must_arrive_to_execute sched → completed_jobs_dont_execute sched →
    ∀ j : Job, job_of_task tsk j = true → arrives_in arr_seq j → job_cost_positive j = true →
    ∀ t1 t2 : instant, Prosa.Analysis.Definitions.BusyInterval.Classical.busy_interval arr_seq sched j t1 t2 →
    ∀ Δ : instant, t1 + Δ < t2 →
      cumulative_another_hep_job_interference arr_seq sched j t1 (t1 + Δ) ≤
        sumSeq ts (fun tsko => task_request_bound_function tsko (job_arrival j - t1 + 1)) - task_cost tsk := by
  intro huni hsup arr_seq hva hcost ts hall hresp hvalid tsk hin sched hmust hcde j hjob harr _ t1 t2 hbusy Δ hlt
  have hu := unit_supply_is_unit_service PState hsup
  obtain ⟨⟨_, hq1, _, harr1⟩, _⟩ := hbusy
  simp only [Bool.and_eq_true, decide_eq_true_eq] at harr1
  have hin' : tsk ∈ ts := of_decide_eq_true hin
  -- interference is service of other higher-or-equal-priority jobs, bounded by their workload
  rw [cumulative_i_ohep_eq_service_of_ohep huni arr_seq hva sched hmust hcde (FIFO Job) hu j t1 (t1 + Δ) hq1]
  refine Nat.le_trans (service_of_jobs_le_workload hu sched hcde _ _ t1 (t1 + Δ)) ?_
  -- under FIFO these jobs arrive no later than `j`
  have hw1 : workload_of_jobs (fun jhp => another_hep_job jhp j) (arrivals_between arr_seq t1 (t1 + Δ)) ≤
      workload_of_jobs (fun x => decide (x ≠ j)) (arrivals_between arr_seq t1 (job_arrival j + 1)) := by
    refine Nat.le_trans (workload_of_jobs_weaken _ (fun x => decide (job_arrival x ≤ job_arrival j) &&
      decide (x ≠ j)) _ (fun x h => h)) ?_
    exact workload_equal_subset arr_seq hva.1 hva t1 (t1 + Δ) (job_arrival j) (fun x => decide (x ≠ j))
  refine Nat.le_trans hw1 ?_
  have hjin : decide (j ∈ arrivals_between arr_seq t1 (job_arrival j + 1)) = true :=
    job_in_arrivals_between arr_seq hva.1 j t1 _ harr harr1.1 (Nat.lt_succ_self _)
  rw [workload_minus_job_cost j _ (arrivals_uniq arr_seq hva.1 hva.2 t1 _) hjin]
  -- partition the workload by tasks
  have hA : job_arrival j + 1 = t1 + (job_arrival j - t1 + 1) := by omega'
  have hpart := workload_of_jobs_le_sum_over_partitions (Task := Task) (fun _ => true) (fun _ => true)
    (arrivals_between arr_seq t1 (job_arrival j + 1)) ts
    (fun x hx => hall x (in_arrivals_implies_arrived arr_seq x _ _ hx)) (fun _ _ _ => rfl)
  have hpart2 : workload_of_jobs (fun _ => true) (arrivals_between arr_seq t1 (job_arrival j + 1)) ≤
      (ts.map (fun tsk_o => task_workload_between arr_seq tsk_o t1 (t1 + (job_arrival j - t1 + 1)))).sum := by
    refine Nat.le_trans hpart (Nat.le_of_eq ?_)
    unfold sumFiltered
    rw [List.filter_true, ← hA]
    rfl
  refine Nat.le_trans (Nat.sub_le_sub_right hpart2 _) ?_
  unfold sumSeq
  apply sum_sub_le ts tsk hin'
  · intro y hy
    exact rbf_spec arr_seq hcost y (hresp y (decide_eq_true hy)) t1 _
  · exact task_rbf_without_job_under_analysis arr_seq hva.1 hcost tsk (hresp tsk hin) j hjob harr t1 _
      (by omega') harr1.1
  · rw [← hA]
    exact job_cost_le_workload _ _ j (of_decide_eq_true hjin) hjob
  · have hma := non_pathological_max_arrivals tsk arr_seq (hresp tsk hin) j hjob harr
    have h1 := task_rbf_1_ge_task_cost tsk hma
    have hmono := of_decide_eq_true (task_rbf_monotone tsk (hvalid tsk hin) 1 (job_arrival j - t1 + 1)
      (decide_eq_true (by omega')))
    omega'

end Prosa.Analysis.Facts.Priority.FifoAhepBound
