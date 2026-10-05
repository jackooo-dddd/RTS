-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: analysis/facts/model/rbf.v

import Prosa.Model.Job.Properties
import Prosa.Analysis.Facts.Model.Workload
import Prosa.Analysis.Facts.Model.ArrivalCurves
import Prosa.Analysis.Facts.Model.TaskCost
import Prosa.Analysis.Definitions.RequestBoundFunction
import Prosa.Analysis.Definitions.Schedulability
import Prosa.Util.Tactics
import Prosa.Analysis.Definitions.Workload.Bounded

namespace Prosa.Analysis.Facts.Model.Rbf

open Prosa.Behavior.Arrival_sequence
open Prosa.Behavior.Job
open Prosa.Behavior.Schedule
open Prosa.Behavior.Service
open Prosa.Behavior.Time
open Prosa.Model.Task.Concept
open Prosa.Model.Task.Arrivals
open Prosa.Model.Task.Arrival.Curves
open Prosa.Model.Priority.Definitions
open Prosa.Model.Priority.Coercion
open Prosa.Model.Aggregate.Workload
open Prosa.Util.Sum
open Prosa.Analysis.Definitions.RequestBoundFunction
open Prosa.Analysis.Definitions.Schedulability
open Prosa.Analysis.Definitions.Workload.Bounded
open Prosa.Analysis.Facts.Behavior.Arrivals
open Prosa.Analysis.Facts.Behavior.Completion
open Prosa.Analysis.Facts.Model.Workload
open Prosa.Analysis.Facts.Model.TaskArrivals
open Prosa.Analysis.Facts.Model.ArrivalCurves
open Prosa.Analysis.Facts.Model.TaskCost

/-! Facts about request-bound functions. Binders follow the elaborated source
types (unused section context and hypotheses are absent, as in the
elaborated source). Representation: `pred T` is `T → Bool`; `x \in xs` in
`Prop` position is `decide (x ∈ xs) = true`; `uniq xs` is `xs.Nodup`;
`monotone leq f` is `Prosa.Util.Rel.monotone (fun x y => decide (x ≤ y)) f`;
`ε` is `1`; `f^~ y` is `fun x => f x y`; under an FP policy the job priority
is the accepted `FP_to_JLFP` coercion, named explicitly where the elaborated
source inserts it; `fun=> [eta f]` is `fun _ Δ => f Δ`. -/

macro "omega'" : tactic => `(tactic| (try dsimp only [instant, duration, work] at *) <;> omega)

/-- A job of `tsk` among the arrivals is a valid-cost job of `tsk`. -/
private theorem valid_task_jobs {Task : TaskType} [DecidableEq Task] [TaskCost Task]
    {Job : JobType} [DecidableEq Job] [JobTask Job Task] [JobCost Job]
    (arr_seq : arrival_sequence Job) (hvalid : arrivals_have_valid_job_costs (Task := Task) arr_seq)
    (tsk : Task) (t1 t2 : instant) :
    ∀ j, j ∈ (arrivals_between arr_seq t1 t2).filter (job_of_task tsk) →
      (job_of_task tsk j && valid_job_cost (Task := Task) j) = true := by
  intro j hj
  rw [List.mem_filter] at hj
  rw [hj.2, Bool.true_and]
  exact hvalid j (in_arrivals_implies_arrived arr_seq j t1 t2 (decide_eq_true hj.1))

/-- The workload of a task in an interval is at most its WCET times its number of
arrivals. -/
theorem task_workload_between_bounded {Task : TaskType} [DecidableEq Task] [TaskCost Task]
    {Job : JobType} [DecidableEq Job] [JobTask Job Task] [JobCost Job]
    (arr_seq : arrival_sequence Job) :
    arrivals_have_valid_job_costs (Task := Task) arr_seq →
      ∀ (tsk : Task) (t1 t2 : instant),
        task_workload_between arr_seq tsk t1 t2 ≤
          task_cost tsk * number_of_task_arrivals arr_seq tsk t1 t2 := by
  intro hvalid tsk t1 t2
  unfold task_workload_between task_workload workload_of_jobs sumFiltered number_of_task_arrivals
    task_arrivals_between
  exact sum_job_costs_bounded tsk _ (valid_task_jobs arr_seq hvalid tsk t1 t2)

/-- The RBF bounds the workload of a task in any interval. -/
theorem rbf_spec {Task : TaskType} [DecidableEq Task] [TaskCost Task] [MaxArrivals Task]
    {Job : JobType} [DecidableEq Job] [JobTask Job Task] [JobCost Job]
    (arr_seq : arrival_sequence Job) :
    arrivals_have_valid_job_costs (Task := Task) arr_seq →
      ∀ tsk : Task, respects_max_arrivals arr_seq tsk (max_arrivals tsk) →
        ∀ (t : instant) (Δ : Nat),
          task_workload_between arr_seq tsk t (t + Δ) ≤ task_request_bound_function tsk Δ := by
  intro hvalid tsk hresp t Δ
  refine Nat.le_trans (task_workload_between_bounded arr_seq hvalid tsk t (t + Δ)) ?_
  unfold task_request_bound_function
  apply Nat.mul_le_mul_left
  have := hresp t (t + Δ) (Nat.le_add_right t Δ)
  rwa [show t + Δ - t = Δ by omega'] at this

/-- The RBF bounds the workload of any subset of a task's jobs. -/
theorem rbf_spec' {Task : TaskType} [DecidableEq Task] [TaskCost Task] [MaxArrivals Task]
    {Job : JobType} [DecidableEq Job] [JobTask Job Task] [JobCost Job]
    (arr_seq : arrival_sequence Job) :
    arrivals_have_valid_job_costs (Task := Task) arr_seq →
      ∀ (P : Job → Bool) (tsk : Task), respects_max_arrivals arr_seq tsk (max_arrivals tsk) →
        (∀ j : Job, P j = true → job_of_task tsk j = true) →
        ∀ (t : instant) (Δ : Nat),
          workload_of_jobs P (arrivals_between arr_seq t (t + Δ)) ≤
            task_request_bound_function tsk Δ := by
  intro hvalid P tsk hresp hP t Δ
  refine Nat.le_trans ?_ (rbf_spec arr_seq hvalid tsk hresp t Δ)
  exact workload_of_jobs_weaken P (job_of_task tsk) _ hP

private theorem sumFiltered_true {I : Type _} (r : List I) (F : I → Nat) :
    sumFiltered r (fun _ => true) F = sumSeq r F := by
  unfold sumFiltered sumSeq; rw [List.filter_true]

/-- The workload of jobs satisfying `pred1` is bounded by the RBFs of the tasks
satisfying `pred2`. -/
theorem workload_of_jobs_bounded {Task : TaskType} [DecidableEq Task] [TaskCost Task]
    [MaxArrivals Task] {Job : JobType} [DecidableEq Job] [JobTask Job Task] [JobCost Job]
    (arr_seq : arrival_sequence Job) :
    arrivals_have_valid_job_costs (Task := Task) arr_seq →
      ∀ ts : List Task, all_jobs_from_taskset arr_seq ts → taskset_respects_max_arrivals arr_seq ts →
        ∀ (pred1 : Job → Bool) (pred2 : Task → Bool),
          (∀ j : Job, pred1 j = true → pred2 (job_task j) = true) →
          ∀ (t : instant) (Δ : Nat),
            workload_of_jobs pred1 (arrivals_between arr_seq t (t + Δ)) ≤
              sumFiltered ts pred2 (fun tsk' => task_request_bound_function tsk' Δ) := by
  intro hvalid ts hall hresp pred1 pred2 hsat t Δ
  have hpart := workload_of_jobs_le_sum_over_partitions pred1 pred2
    (arrivals_between arr_seq t (t + Δ)) ts
    (fun j hj => hall j (in_arrivals_implies_arrived arr_seq j _ _ hj))
    (fun j _ hp => hsat j hp)
  refine Nat.le_trans hpart ?_
  apply leq_sum_seq
  intro tsk' hin _
  refine Nat.le_trans ?_ (rbf_spec arr_seq hvalid tsk' (hresp tsk' (decide_eq_true hin)) t Δ)
  apply workload_of_jobs_weaken
  intro j hj
  simp only [Bool.and_eq_true] at hj
  exact hj.2

/-- The total workload is bounded by the total RBF. -/
theorem total_workload_le_total_rbf {Task : TaskType} [DecidableEq Task] [TaskCost Task]
    [MaxArrivals Task] {Job : JobType} [DecidableEq Job] [JobTask Job Task] [JobCost Job]
    (arr_seq : arrival_sequence Job) :
    arrivals_have_valid_job_costs (Task := Task) arr_seq →
      ∀ ts : List Task, all_jobs_from_taskset arr_seq ts → taskset_respects_max_arrivals arr_seq ts →
        ∀ (t : instant) (Δ : Nat),
          total_workload_between arr_seq t (t + Δ) ≤ total_request_bound_function ts Δ := by
  intro hvalid ts hall hresp t Δ
  have := workload_of_jobs_bounded arr_seq hvalid ts hall hresp (fun _ => true) (fun _ => true)
    (fun _ _ => rfl) t Δ
  unfold total_workload_between total_workload total_request_bound_function
  rwa [sumFiltered_true] at this

/-- Under an FP policy, the higher-or-equal-priority workload of other tasks is
bounded by the total other-higher-or-equal-priority RBF. -/
theorem athep_workload_le_total_ohep_rbf {Task : TaskType} [DecidableEq Task] [TaskCost Task]
    [MaxArrivals Task] {Job : JobType} [DecidableEq Job] [JobTask Job Task] [JobArrival Job]
    [JobCost Job] (arr_seq : arrival_sequence Job) {PState : ProcessorState Job}
    (sched : schedule PState) :
    arrivals_have_valid_job_costs (Task := Task) arr_seq →
      ∀ ts : List Task, all_jobs_from_taskset arr_seq ts → taskset_respects_max_arrivals arr_seq ts →
        ∀ (FP : FP_policy Task) (tsk : Task),
          @athep_workload_is_bounded Task _ Job _ _ _ _ PState (FP_to_JLFP FP) arr_seq sched tsk
            (fun _ Δ => total_ohep_request_bound_function_FP ts tsk Δ) := by
  intro hvalid ts hall hresp FP tsk j t1 Δ _ htsk _
  have hj : job_task (Task := Task) j = tsk := of_decide_eq_true htsk
  refine workload_of_jobs_bounded arr_seq hvalid ts hall hresp _
    (fun tsk_other => FP.hep_task tsk_other tsk && decide (tsk_other ≠ tsk)) ?_ t1 Δ
  intro j' hj'
  unfold another_task_hep_job at hj'
  rw [← hj]
  exact hj'

/-- Under an FP policy, the higher-or-equal-priority workload is bounded by the
total higher-or-equal-priority RBF. -/
theorem hep_workload_le_total_hep_rbf {Task : TaskType} [DecidableEq Task] [TaskCost Task]
    [MaxArrivals Task] {Job : JobType} [DecidableEq Job] [JobTask Job Task] [JobCost Job]
    (arr_seq : arrival_sequence Job) :
    arrivals_have_valid_job_costs (Task := Task) arr_seq →
      ∀ ts : List Task, all_jobs_from_taskset arr_seq ts → taskset_respects_max_arrivals arr_seq ts →
        ∀ (FP : FP_policy Task) (tsk : Task) (j : Job), job_of_task tsk j = true →
          ∀ (t : instant) (Δ : Nat),
            @workload_of_hep_jobs Job _ _ arr_seq (FP_to_JLFP FP) j t (t + Δ) ≤
              total_hep_request_bound_function_FP ts tsk Δ := by
  intro hvalid ts hall hresp FP tsk j htsk t Δ
  have hj : job_task (Task := Task) j = tsk := of_decide_eq_true htsk
  refine workload_of_jobs_bounded arr_seq hvalid ts hall hresp _
    (fun tsk_other => FP.hep_task tsk_other tsk) ?_ t Δ
  intro j' hj'
  rw [← hj]
  exact hj'

/-- Under any JLFP policy, the higher-or-equal-priority workload is bounded by
the total RBF. -/
theorem hep_workload_le_total_rbf {Task : TaskType} [DecidableEq Task] [TaskCost Task]
    [MaxArrivals Task] {Job : JobType} [DecidableEq Job] [JobTask Job Task] [JobCost Job]
    (arr_seq : arrival_sequence Job) :
    arrivals_have_valid_job_costs (Task := Task) arr_seq →
      ∀ ts : List Task, all_jobs_from_taskset arr_seq ts → taskset_respects_max_arrivals arr_seq ts →
        ∀ (JLFP : JLFP_policy Job) (j : Job) (t : instant) (Δ : Nat),
          workload_of_hep_jobs arr_seq j t (t + Δ) ≤ total_request_bound_function ts Δ := by
  intro hvalid ts hall hresp JLFP j t Δ
  refine Nat.le_trans ?_ (total_workload_le_total_rbf arr_seq hvalid ts hall hresp t Δ)
  exact workload_of_jobs_weaken _ (fun _ => true) _ (fun _ _ => rfl)

/-- A valid arrival curve makes the RBF zero on the empty interval. -/
theorem task_rbf_0_zero {Task : TaskType} [DecidableEq Task] [TaskCost Task] (tsk : Task)
    [MaxArrivals Task] :
    valid_arrival_curve (max_arrivals tsk) → task_request_bound_function tsk 0 = 0 := by
  intro hv
  unfold task_request_bound_function
  rw [hv.1, Nat.mul_zero]

/-- A valid arrival curve makes the RBF monotone. -/
theorem task_rbf_monotone {Task : TaskType} [DecidableEq Task] [TaskCost Task] (tsk : Task)
    [MaxArrivals Task] :
    valid_arrival_curve (max_arrivals tsk) →
      Prosa.Util.Rel.monotone (fun x y => decide (x ≤ y)) (task_request_bound_function tsk) := by
  intro hv x y hxy
  apply decide_eq_true
  unfold task_request_bound_function
  exact Nat.mul_le_mul_left _ (of_decide_eq_true (hv.2 x y hxy))

/-- With a positive arrival bound for `ε`, the RBF at `ε` is at least the task cost. -/
theorem task_rbf_1_ge_task_cost {Task : TaskType} [DecidableEq Task] [TaskCost Task] (tsk : Task)
    [MaxArrivals Task] :
    0 < max_arrivals tsk 1 → task_cost tsk ≤ task_request_bound_function tsk 1 := by
  intro hpos
  unfold task_request_bound_function
  exact Nat.le_mul_of_pos_right _ hpos

/-- The RBF at any positive point is at least the task cost. -/
theorem task_rbf_ge_task_cost {Task : TaskType} [DecidableEq Task] [TaskCost Task] (tsk : Task)
    [MaxArrivals Task] :
    valid_arrival_curve (max_arrivals tsk) → 0 < max_arrivals tsk 1 →
      ∀ A : Nat, 0 < A → task_cost tsk ≤ task_request_bound_function tsk A := by
  intro hv hpos A hA
  refine Nat.le_trans (task_rbf_1_ge_task_cost tsk hpos) ?_
  exact of_decide_eq_true (task_rbf_monotone tsk hv 1 A (decide_eq_true hA))

/-- With a positive cost and arrival bound, the RBF at `ε` is positive. -/
theorem task_rbf_epsilon_gt_0 {Task : TaskType} [DecidableEq Task] [TaskCost Task] (tsk : Task)
    [MaxArrivals Task] :
    0 < task_cost tsk → 0 < max_arrivals tsk 1 → 0 < task_request_bound_function tsk 1 := by
  intro hc hpos
  exact Nat.lt_of_lt_of_le hc (task_rbf_1_ge_task_cost tsk hpos)

private theorem le_sumSeq_of_mem {I : Type _} [DecidableEq I] (r : List I) (F : I → Nat) (x : I)
    (hx : x ∈ r) : F x ≤ sumSeq r F := by
  unfold sumSeq
  exact List.le_sum_of_mem (List.mem_map_of_mem hx)

/-- The task cost is at most the total RBF at any positive point. -/
theorem task_cost_le_sum_rbf {Task : TaskType} [DecidableEq Task] [TaskCost Task] (tsk : Task)
    [MaxArrivals Task] :
    valid_arrival_curve (max_arrivals tsk) → 0 < max_arrivals tsk 1 →
      ∀ ts : List Task, decide (tsk ∈ ts) = true →
        ∀ t : Nat, 0 < t → task_cost tsk ≤ total_request_bound_function ts t := by
  intro hv hpos ts hin t ht
  refine Nat.le_trans (task_rbf_ge_task_cost tsk hv hpos t ht) ?_
  exact le_sumSeq_of_mem ts (fun tsk => task_request_bound_function tsk t) tsk (of_decide_eq_true hin)

/-- The total RBF is monotone. -/
theorem total_rbf_monotone {Task : TaskType} [DecidableEq Task] [TaskCost Task]
    [MaxArrivals Task] (ts : List Task) :
    valid_taskset_arrival_curve ts max_arrivals →
      Prosa.Util.Rel.monotone (fun x y => decide (x ≤ y)) (total_request_bound_function ts) := by
  intro hv
  have := sum_leq_mono (fun _ => true) (fun tsk => task_request_bound_function tsk) ts
    (fun tsk hin => task_rbf_monotone tsk (hv tsk (decide_eq_true hin)))
  intro x y hxy
  have h := this x y hxy
  unfold total_request_bound_function
  simpa only [sumFiltered_true] using h

/-- The total higher-or-equal-priority RBF is monotone. -/
theorem total_hep_rbf_monotone {Task : TaskType} [DecidableEq Task] [TaskCost Task]
    [MaxArrivals Task] (ts : List Task) :
    valid_taskset_arrival_curve ts max_arrivals →
      ∀ (FP : FP_policy Task) (tsk : Task),
        Prosa.Util.Rel.monotone (fun x y => decide (x ≤ y))
          (total_hep_request_bound_function_FP ts tsk) := by
  intro hv FP tsk
  exact sum_leq_mono _ (fun tsk' => task_request_bound_function tsk') ts
    (fun tsk' hin => task_rbf_monotone tsk' (hv tsk' (decide_eq_true hin)))

/-- The total other-higher-or-equal-priority RBF is monotone. -/
theorem total_ohep_rbf_monotone {Task : TaskType} [DecidableEq Task] [TaskCost Task]
    [MaxArrivals Task] (ts : List Task) :
    valid_taskset_arrival_curve ts max_arrivals →
      ∀ (FP : FP_policy Task) (tsk : Task),
        Prosa.Util.Rel.monotone (fun x y => decide (x ≤ y))
          (total_ohep_request_bound_function_FP ts tsk) := by
  intro hv FP tsk
  exact sum_leq_mono _ (fun tsk' => task_request_bound_function tsk') ts
    (fun tsk' hin => task_rbf_monotone tsk' (hv tsk' (decide_eq_true hin)))

/-- A task whose RBF is zero at `ε` has the trivial response-time bound `0`. -/
theorem pathological_rbf_response_time_bound {Task : TaskType} [DecidableEq Task] [TaskCost Task]
    [MaxArrivals Task] (ts : List Task) {Job : JobType} [DecidableEq Job] [JobTask Job Task]
    [JobArrival Job] [JobCost Job] (arr_seq : arrival_sequence Job) :
    arrivals_have_valid_job_costs (Task := Task) arr_seq → taskset_respects_max_arrivals arr_seq ts →
      ∀ (PState : ProcessorState Job) (sched : schedule PState) (tsk : Task),
        decide (tsk ∈ ts) = true → task_request_bound_function tsk 1 = 0 →
        task_response_time_bound arr_seq sched tsk 0 := by
  intro hvalid hresp PState sched tsk hin hzero j harr htsk
  unfold task_request_bound_function at hzero
  rcases Nat.mul_eq_zero.mp hzero with hc | hm
  · unfold job_response_time_bound completed_by
    apply decide_eq_true
    have hv := hvalid j harr
    unfold valid_job_cost at hv
    have hj : job_task (Task := Task) j = tsk := of_decide_eq_true htsk
    rw [hj, hc] at hv
    have := of_decide_eq_true hv
    omega'
  · exfalso
    have := non_pathological_max_arrivals tsk arr_seq (hresp tsk hin) j htsk harr
    omega'

/-- If the total higher-or-equal-priority RBF is zero at `ε`, the response-time
bound is trivially `0`. -/
theorem pathological_total_hep_rbf_response_time_bound {Task : TaskType} [DecidableEq Task]
    [TaskCost Task] [MaxArrivals Task] (ts : List Task) {Job : JobType} [DecidableEq Job]
    [JobTask Job Task] [JobArrival Job] [JobCost Job] (arr_seq : arrival_sequence Job) :
    arrivals_have_valid_job_costs (Task := Task) arr_seq → taskset_respects_max_arrivals arr_seq ts →
      ∀ (PState : ProcessorState Job) (sched : schedule PState) (FP : FP_policy Task),
        reflexive_task_priorities FP →
        ∀ tsk : Task, decide (tsk ∈ ts) = true → total_hep_request_bound_function_FP ts tsk 1 = 0 →
          task_response_time_bound arr_seq sched tsk 0 := by
  intro hvalid hresp PState sched FP hrefl tsk hin hzero
  apply pathological_rbf_response_time_bound ts arr_seq hvalid hresp PState sched tsk hin
  have h := sum_nat_eq0_nat ts (fun tsk_other => FP.hep_task tsk_other tsk)
    (fun tsk_other => task_request_bound_function tsk_other 1)
  unfold total_hep_request_bound_function_FP at hzero
  rw [hzero] at h
  have hall := List.all_eq_true.mp h.symm tsk (of_decide_eq_true hin)
  simp only [hrefl tsk, Bool.not_true, Bool.false_or, decide_eq_true_eq] at hall
  exact hall

/-- If the total higher-or-equal-priority RBF is zero at `ε`, any response-time
bound holds. -/
theorem pathological_total_hep_rbf_any_bound {Task : TaskType} [DecidableEq Task]
    [TaskCost Task] [MaxArrivals Task] (ts : List Task) {Job : JobType} [DecidableEq Job]
    [JobTask Job Task] [JobArrival Job] [JobCost Job] (arr_seq : arrival_sequence Job) :
    arrivals_have_valid_job_costs (Task := Task) arr_seq → taskset_respects_max_arrivals arr_seq ts →
      ∀ (PState : ProcessorState Job) (sched : schedule PState) (FP : FP_policy Task),
        reflexive_task_priorities FP →
        ∀ tsk : Task, decide (tsk ∈ ts) = true → total_hep_request_bound_function_FP ts tsk 1 = 0 →
          ∀ R : duration, task_response_time_bound arr_seq sched tsk R := by
  intro hvalid hresp PState sched FP hrefl tsk hin hzero R j harr htsk
  have h0 := pathological_total_hep_rbf_response_time_bound ts arr_seq hvalid hresp PState sched FP
    hrefl tsk hin hzero j harr htsk
  unfold job_response_time_bound at h0 ⊢
  exact completion_monotonic sched j _ _ (by omega') h0

/-- The total higher-or-equal-priority RBF splits into the strictly-higher and the
equal-priority parts. -/
theorem hep_rbf_taskwise_partitioning {Task : TaskType} [DecidableEq Task] [TaskCost Task]
    [MaxArrivals Task] (FP : FP_policy Task) (ts : List Task) (tsk : Task) (L : duration) :
    total_hep_request_bound_function_FP ts tsk L =
      total_hp_request_bound_function_FP ts tsk L + total_ep_request_bound_function_FP ts tsk L := by
  unfold total_hep_request_bound_function_FP total_hp_request_bound_function_FP
    total_ep_request_bound_function_FP
  apply sum_split_exhaustive_mutually_exclusive_preds
  · intro x; unfold hp_task ep_task
    cases FP.hep_task x tsk <;> cases FP.hep_task tsk x <;> rfl
  · intro x; unfold hp_task ep_task
    cases FP.hep_task x tsk <;> cases FP.hep_task tsk x <;> rfl

private theorem sf_cons {I : Type _} (a : I) (l : List I) (P : I → Bool) (F : I → Nat) :
    sumFiltered (a :: l) P F = (bif P a then F a else 0) + sumFiltered l P F := by
  unfold sumFiltered; cases h : P a <;> simp [h]

/-- Splitting off `tsk` from the higher-or-equal-priority filter. -/
private theorem hep_split_self {Task : TaskType} [DecidableEq Task] (FP : FP_policy Task)
    (hrefl : reflexive_task_priorities FP) (tsk : Task) (F : Task → Nat) :
    ∀ ts : List Task,
      sumFiltered ts (fun t => FP.hep_task t tsk) F =
        sumFiltered ts (fun t => FP.hep_task t tsk && decide (t ≠ tsk)) F +
          sumFiltered ts (fun t => decide (t = tsk)) F := by
  intro ts
  apply sum_split_exhaustive_mutually_exclusive_preds
  · intro x
    by_cases hx : x = tsk
    · subst hx; simp [hrefl x]
    · simp [hx]
  · intro x
    by_cases hx : x = tsk <;> simp [hx]

private theorem sum_eq_self_uniq {Task : TaskType} [DecidableEq Task] (tsk : Task) (F : Task → Nat) :
    ∀ ts : List Task, tsk ∈ ts → ts.Nodup →
      sumFiltered ts (fun t => decide (t = tsk)) F = F tsk
  | [], h, _ => absurd h List.not_mem_nil
  | a :: l, h, hnd => by
    rw [List.nodup_cons] at hnd
    rw [sf_cons]
    by_cases ha : a = tsk
    · subst ha
      have : sumFiltered l (fun t => decide (t = a)) F = 0 := by
        unfold sumFiltered
        rw [List.filter_eq_nil_iff.mpr (fun x hx => by
          have : x ≠ a := fun e => hnd.1 (e ▸ hx)
          simp [this])]
        rfl
      simp [this]
    · have hl : tsk ∈ l := by
        rcases List.mem_cons.mp h with e | e
        · exact absurd e.symm ha
        · exact e
      rw [sum_eq_self_uniq tsk F l hl hnd.2]
      simp [ha]

private theorem sum_eq_self_ge {Task : TaskType} [DecidableEq Task] (tsk : Task) (F : Task → Nat) :
    ∀ ts : List Task, tsk ∈ ts → F tsk ≤ sumFiltered ts (fun t => decide (t = tsk)) F
  | [], h => absurd h List.not_mem_nil
  | a :: l, h => by
    rw [sf_cons]
    by_cases ha : a = tsk
    · subst ha; simp
    · have hl : tsk ∈ l := by
        rcases List.mem_cons.mp h with e | e
        · exact absurd e.symm ha
        · exact e
      have := sum_eq_self_ge tsk F l hl
      simp [ha]; exact this

/-- For a duplicate-free task set containing `tsk`, the total
higher-or-equal-priority RBF is the other-higher-or-equal-priority RBF plus the
RBF of `tsk`. -/
theorem split_hep_rbf {Task : TaskType} [DecidableEq Task] [TaskCost Task] [MaxArrivals Task]
    (FP : FP_policy Task) (ts : List Task) (tsk : Task) :
    reflexive_task_priorities FP →
      ∀ Δ : duration, decide (tsk ∈ ts) = true → ts.Nodup →
        total_hep_request_bound_function_FP ts tsk Δ =
          total_ohep_request_bound_function_FP ts tsk Δ + task_request_bound_function tsk Δ := by
  intro hrefl Δ hin hnd
  unfold total_hep_request_bound_function_FP total_ohep_request_bound_function_FP
  rw [hep_split_self FP hrefl tsk _ ts,
    sum_eq_self_uniq tsk (fun t => task_request_bound_function t Δ) ts (of_decide_eq_true hin) hnd]

/-- Without uniqueness, the other-higher-or-equal-priority RBF plus the RBF of
`tsk` is at most the total higher-or-equal-priority RBF. -/
theorem split_hep_rbf_weaken {Task : TaskType} [DecidableEq Task] [TaskCost Task]
    [MaxArrivals Task] (FP : FP_policy Task) (ts : List Task) (tsk : Task) :
    reflexive_task_priorities FP →
      ∀ Δ : duration, decide (tsk ∈ ts) = true →
        total_ohep_request_bound_function_FP ts tsk Δ + task_request_bound_function tsk Δ ≤
          total_hep_request_bound_function_FP ts tsk Δ := by
  intro hrefl Δ hin
  unfold total_hep_request_bound_function_FP total_ohep_request_bound_function_FP
  rw [hep_split_self FP hrefl tsk _ ts]
  have := sum_eq_self_ge tsk (fun t => task_request_bound_function t Δ) ts (of_decide_eq_true hin)
  omega

/-- With valid arrival curves, the other-higher-or-equal-priority RBF is zero on
the empty interval. -/
theorem total_ohep_rbf0 {Task : TaskType} [DecidableEq Task] [TaskCost Task]
    [MaxArrivals Task] (ts : List Task) :
    valid_taskset_arrival_curve ts max_arrivals →
      ∀ (FP : FP_policy Task) (tsk : Task), total_ohep_request_bound_function_FP ts tsk 0 = 0 := by
  intro hv FP tsk
  unfold total_ohep_request_bound_function_FP
  have h := sum_nat_eq0_nat ts (fun tsk_other => FP.hep_task tsk_other tsk && decide (tsk_other ≠ tsk))
    (fun tsk_other => task_request_bound_function tsk_other 0)
  have hall : ts.all (fun x => !(FP.hep_task x tsk && decide (x ≠ tsk)) ||
      decide (task_request_bound_function x 0 = 0)) = true := by
    apply List.all_eq_true.mpr
    intro x hx
    rw [task_rbf_0_zero x (hv x (decide_eq_true hx))]
    simp
  rw [← h] at hall
  exact of_decide_eq_true hall

/-- The workload of higher-or-equal-priority jobs of other tasks is bounded by the
total other-higher-or-equal-priority RBF. -/
theorem ohep_workload_le_rbf {Task : TaskType} [DecidableEq Task] [TaskCost Task]
    (ts : List Task) (FP : FP_policy Task) {Job : JobType} [DecidableEq Job] [JobTask Job Task]
    [JobCost Job] (arr_seq : arrival_sequence Job) :
    all_jobs_from_taskset arr_seq ts → arrivals_have_valid_job_costs (Task := Task) arr_seq →
      ∀ [MaxArrivals Task], taskset_respects_max_arrivals arr_seq ts →
        ∀ (j : Job) (tsk : Task), job_of_task tsk j = true →
          ∀ (Δ : Nat) (t1 : instant),
            workload_of_jobs (fun j' => @another_task_hep_job Task _ Job _ _ (FP_to_JLFP FP) j' j)
                (arrivals_between arr_seq t1 (t1 + Δ)) ≤
              total_ohep_request_bound_function_FP ts tsk Δ := by
  intro hall hvalid _ hresp j tsk htsk Δ t1
  have hj : job_task (Task := Task) j = tsk := of_decide_eq_true htsk
  refine workload_of_jobs_bounded arr_seq hvalid ts hall hresp _
    (fun tsk_other => FP.hep_task tsk_other tsk && decide (tsk_other ≠ tsk)) ?_ t1 Δ
  intro j' hj'
  unfold another_task_hep_job at hj'
  rw [← hj]
  exact hj'

/-- The workload of `tsk` from the arrival of `j` on, without the cost of `j`, is at
most the WCET bound without one task cost. -/
theorem task_rbf_without_job_under_analysis_from_arrival {Task : TaskType} [DecidableEq Task]
    [TaskCost Task] {Job : JobType} [DecidableEq Job] [JobTask Job Task] [JobArrival Job]
    [JobCost Job] (arr_seq : arrival_sequence Job) :
    consistent_arrival_times arr_seq → arrivals_have_valid_job_costs (Task := Task) arr_seq →
      ∀ (tsk : Task) (j : Job), job_of_task tsk j = true → arrives_in arr_seq j →
        ∀ (t1 : instant) (Δ : duration), job_arrival j < t1 + Δ →
          task_workload_between arr_seq tsk (job_arrival j) (t1 + Δ) - job_cost j ≤
            task_cost tsk * number_of_task_arrivals arr_seq tsk (job_arrival j) (t1 + Δ) -
              task_cost tsk := by
  intro hc hvalid tsk j htsk harr t1 Δ hlt
  have hmem : j ∈ (arrivals_between arr_seq (job_arrival j) (t1 + Δ)).filter (job_of_task tsk) :=
    List.mem_filter.mpr ⟨of_decide_eq_true
      (job_in_arrivals_between arr_seq hc j _ _ harr (Nat.le_refl _) hlt), htsk⟩
  unfold task_workload_between task_workload workload_of_jobs sumFiltered number_of_task_arrivals
    task_arrivals_between
  generalize hL : (arrivals_between arr_seq (job_arrival j) (t1 + Δ)).filter (job_of_task tsk) = L
    at hmem ⊢
  have hvalidL : ∀ x, x ∈ L → (job_of_task tsk x && valid_job_cost (Task := Task) x) = true := by
    rw [← hL]; exact valid_task_jobs arr_seq hvalid tsk _ _
  obtain ⟨l1, l2, rfl⟩ := List.append_of_mem hmem
  have h1 : (l1.map (fun x => job_cost x)).sum ≤ task_cost tsk * l1.length :=
    sum_job_costs_bounded tsk l1 (fun x hx => hvalidL x (by simp [hx]))
  have h2 : (l2.map (fun x => job_cost x)).sum ≤ task_cost tsk * l2.length :=
    sum_job_costs_bounded tsk l2 (fun x hx => hvalidL x (by simp [hx]))
  simp only [List.map_append, List.map_cons, List.sum_append, List.sum_cons, List.length_append,
    List.length_cons]
  rw [Nat.mul_add, Nat.mul_add]
  omega'

/-- The workload of `tsk` in `[t1, t1 + Δ)`, without the cost of a job `j` of `tsk`
arriving in the interval, is at most the RBF without one task cost. -/
theorem task_rbf_without_job_under_analysis {Task : TaskType} [DecidableEq Task] [TaskCost Task]
    {Job : JobType} [DecidableEq Job] [JobTask Job Task] [JobArrival Job] [JobCost Job]
    (arr_seq : arrival_sequence Job) :
    consistent_arrival_times arr_seq → arrivals_have_valid_job_costs (Task := Task) arr_seq →
      ∀ (tsk : Task) [MaxArrivals Task], respects_max_arrivals arr_seq tsk (max_arrivals tsk) →
        ∀ j : Job, job_of_task tsk j = true → arrives_in arr_seq j →
          ∀ (t1 : instant) (Δ : duration), job_arrival j < t1 + Δ → t1 ≤ job_arrival j →
            task_workload_between arr_seq tsk t1 (t1 + Δ) - job_cost j ≤
              task_request_bound_function tsk Δ - task_cost tsk := by
  intro hc hvalid tsk _ hresp j htsk harr t1 Δ hlt hge
  have hnum : number_of_task_arrivals arr_seq tsk t1 (t1 + Δ) ≤ max_arrivals tsk Δ := by
    have := hresp t1 (t1 + Δ) (Nat.le_add_right t1 Δ)
    rwa [show t1 + Δ - t1 = Δ by omega'] at this
  have hsplitN := num_arrivals_of_task_cat arr_seq tsk (job_arrival j) t1 (t1 + Δ)
    (by simp [hge, Nat.le_of_lt hlt])
  have hsplitW := workload_of_jobs_cat arr_seq (job_arrival j) t1 (t1 + Δ) (job_of_task tsk)
    (by simp [hge, Nat.le_of_lt hlt])
  have hbefore := task_workload_between_bounded arr_seq hvalid tsk t1 (job_arrival j)
  have hafter := task_rbf_without_job_under_analysis_from_arrival arr_seq hc hvalid tsk j htsk harr
    t1 Δ hlt
  -- the job itself lies in the second part, so both the workload and the count there are positive
  have hmem : j ∈ (arrivals_between arr_seq (job_arrival j) (t1 + Δ)).filter (job_of_task tsk) :=
    List.mem_filter.mpr ⟨of_decide_eq_true
      (job_in_arrivals_between arr_seq hc j _ _ harr (Nat.le_refl _) hlt), htsk⟩
  have hcnt : 1 ≤ number_of_task_arrivals arr_seq tsk (job_arrival j) (t1 + Δ) := by
    unfold number_of_task_arrivals task_arrivals_between
    exact List.length_pos_of_mem hmem
  have hcost : job_cost j ≤ task_workload_between arr_seq tsk (job_arrival j) (t1 + Δ) := by
    unfold task_workload_between task_workload workload_of_jobs sumFiltered
    exact List.le_sum_of_mem (List.mem_map_of_mem hmem)
  unfold task_workload_between task_workload at hbefore hafter hcost ⊢
  rw [hsplitW]
  unfold task_request_bound_function
  have hmul := Nat.mul_le_mul_left (task_cost tsk) hnum
  rw [hsplitN, Nat.mul_add] at hmul
  have hc1 : task_cost tsk ≤ task_cost tsk * number_of_task_arrivals arr_seq tsk (job_arrival j) (t1 + Δ) :=
    Nat.le_mul_of_pos_right _ hcnt
  omega'

end Prosa.Analysis.Facts.Model.Rbf
