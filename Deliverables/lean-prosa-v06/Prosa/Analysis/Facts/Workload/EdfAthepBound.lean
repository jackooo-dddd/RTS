-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: analysis/facts/workload/edf_athep_bound.v

import Prosa.Model.Priority.Edf
import Prosa.Model.Task.AbsoluteDeadline
import Prosa.Analysis.Definitions.Workload.Bounded
import Prosa.Analysis.Facts.Model.Rbf
import Prosa.Analysis.Definitions.Workload.EdfAthepBound

namespace Prosa.Analysis.Facts.Workload.EdfAthepBound

open Prosa.Behavior.Arrival_sequence
open Prosa.Behavior.Job
open Prosa.Behavior.Schedule
open Prosa.Behavior.Time
open Prosa.Model.Task.Concept
open Prosa.Model.Task.Arrival.Curves
open Prosa.Model.Job.Properties
open Prosa.Model.Priority.Definitions
open Prosa.Model.Priority.Edf
open Prosa.Model.Task.AbsoluteDeadline
open Prosa.Model.Aggregate.Workload
open Prosa.Util.Sum
open Prosa.Analysis.Definitions.RequestBoundFunction
open Prosa.Analysis.Definitions.Workload.Bounded
open Prosa.Analysis.Definitions.Workload.EdfAthepBound
open Prosa.Analysis.Facts.Behavior.Arrivals
open Prosa.Analysis.Facts.Model.Workload
open Prosa.Analysis.Facts.Model.Rbf

/-! Validity and monotonicity of the EDF bound on the higher-or-equal-priority
workload of other tasks. Binders follow the elaborated source types (unused
section context and hypotheses, including the busy-interval hypothesis, are
absent, as in the elaborated source). Representation: the EDF policy is the
accepted `EDF` instance over the accepted `job_deadline_from_task_deadline`
instance, named explicitly; the section-local `EDF_from tsk_o` is inlined as
`fun jo => hep_job jo j && decide (job_task jo = tsk_o)`; `A` is inlined as
`job_arrival j - t1`; `ε` is `1`; `x \in xs` and `a != b` in `Prop` position
are `decide (…) = true`; `\sum_(x <- xs | P x) F x` is the accepted
`sumFiltered xs P F`; `monotone leq f` is
`Prosa.Util.Rel.monotone (fun x y => decide (x ≤ y)) f`. -/

macro "omega'" : tactic => `(tactic| (try dsimp only [instant, duration, work] at *) <;> omega)

theorem total_workload_shorten_range {Task : TaskType} [DecidableEq Task] [TaskDeadline Task]
    {Job : JobType} [DecidableEq Job] [JobTask Job Task] [JobArrival Job] [JobCost Job]
    (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
      ∀ (ts : List Task) (tsk : Task) (j : Job), job_of_task tsk j = true →
        job_cost_positive j = true →
        ∀ (t1 t2 Δ : duration), t1 + Δ < t2 →
          ∀ tsk_o : Task, decide (tsk_o ∈ ts) = true → decide (tsk_o ≠ tsk) = true →
            job_arrival j - t1 + 1 + task_deadline tsk - task_deadline tsk_o ≤ Δ →
            workload_of_jobs
                (fun jo => @hep_job Job _ (@EDF Job _ (job_deadline_from_task_deadline Job Task)) jo j &&
                  decide (job_task jo = tsk_o))
                (arrivals_between arr_seq t1 (t1 + Δ)) ≤
              workload_of_jobs
                (fun jo => @hep_job Job _ (@EDF Job _ (job_deadline_from_task_deadline Job Task)) jo j &&
                  decide (job_task jo = tsk_o))
                (arrivals_between arr_seq t1
                  (t1 + (job_arrival j - t1 + 1 + task_deadline tsk - task_deadline tsk_o))) := by
  intro hvalid ts tsk j htsk _ t1 t2 Δ _ tsk_o _ _ hΔ
  have hj : job_task (Task := Task) j = tsk := of_decide_eq_true htsk
  refine Nat.le_of_eq (workload_of_jobs_nil_tail arr_seq hvalid.1 _ t1 (t1 + Δ) _ (by omega') ?_)
  intro j' hin' harr'
  have hge : t1 ≤ job_arrival j' := job_arrival_between_ge arr_seq hvalid.1 j' t1 (t1 + Δ) hin'
  cases hto : decide (job_task (Task := Task) j' = tsk_o) with
  | false => simp
  | true =>
    have hto' : job_task (Task := Task) j' = tsk_o := of_decide_eq_true hto
    simp only [Bool.and_true, Bool.not_eq_true']
    show decide (job_arrival j' + task_deadline (job_task (Task := Task) j') ≤
      job_arrival j + task_deadline (job_task (Task := Task) j)) = false
    rw [hto', hj]
    apply decide_eq_false
    omega'

theorem sum_of_workloads_is_at_most_bound_on_total_hep_workload {Task : TaskType} [DecidableEq Task]
    [TaskCost Task] [TaskDeadline Task] [MaxArrivals Task]
    {Job : JobType} [DecidableEq Job] [JobTask Job Task] [JobArrival Job] [JobCost Job]
    (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
      arrivals_have_valid_job_costs (Task := Task) arr_seq →
      ∀ ts : List Task, taskset_respects_max_arrivals arr_seq ts →
        ∀ (tsk : Task) (j : Job), job_of_task tsk j = true → job_cost_positive j = true →
          ∀ (t1 t2 Δ : duration), t1 + Δ < t2 →
            sumFiltered ts (fun tsk_o => decide (tsk_o ≠ tsk))
                (fun tsk_o => workload_of_jobs
                  (fun jo => @hep_job Job _ (@EDF Job _ (job_deadline_from_task_deadline Job Task)) jo j &&
                    decide (job_task jo = tsk_o))
                  (arrivals_between arr_seq t1 (t1 + Δ))) ≤
              bound_on_athep_workload ts tsk (job_arrival j - t1) Δ := by
  intro hvalid hcost ts hresp tsk j htsk hpos t1 t2 Δ hlt
  unfold bound_on_athep_workload
  apply leq_sum_seq
  intro tsko hin hneq
  have hresp' := hresp tsko (decide_eq_true hin)
  have hP : ∀ jo : Job,
      (@hep_job Job _ (@EDF Job _ (job_deadline_from_task_deadline Job Task)) jo j &&
        decide (job_task jo = tsko)) = true → job_of_task tsko jo = true := by
    intro jo h
    simp only [Bool.and_eq_true] at h
    exact h.2
  by_cases hle : Δ ≤ job_arrival j - t1 + 1 + task_deadline tsk - task_deadline tsko
  · rw [Nat.min_eq_right hle]
    exact rbf_spec' arr_seq hcost _ tsko hresp' hP t1 Δ
  · have hlt' : job_arrival j - t1 + 1 + task_deadline tsk - task_deadline tsko ≤ Δ := by omega'
    rw [Nat.min_eq_left hlt']
    exact Nat.le_trans
      (total_workload_shorten_range arr_seq hvalid ts tsk j htsk hpos t1 t2 Δ hlt tsko
        (decide_eq_true hin) hneq hlt')
      (rbf_spec' arr_seq hcost _ tsko hresp' hP t1 _)

theorem bound_on_athep_workload_is_valid {Task : TaskType} [DecidableEq Task]
    [TaskCost Task] [TaskDeadline Task] [MaxArrivals Task]
    {Job : JobType} [DecidableEq Job] [JobTask Job Task] [JobArrival Job] [JobCost Job]
    {PState : ProcessorState Job} (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
      arrivals_have_valid_job_costs (Task := Task) arr_seq →
      ∀ ts : List Task, all_jobs_from_taskset arr_seq ts → taskset_respects_max_arrivals arr_seq ts →
        ∀ (tsk : Task) (sched : schedule PState),
          @athep_workload_is_bounded Task _ Job _ _ _ _ PState
            (@EDF Job _ (job_deadline_from_task_deadline Job Task)) arr_seq sched tsk
            (bound_on_athep_workload ts tsk) := by
  intro hvalid hcost ts hall hresp tsk sched j t1 Δ hpos htsk _
  have hj : job_task (Task := Task) j = tsk := of_decide_eq_true htsk
  have hpart := @workload_of_jobs_le_sum_over_partitions Task _ Job _ _ _
    (fun j' => @another_task_hep_job Task _ Job _ _
      (@EDF Job _ (job_deadline_from_task_deadline Job Task)) j' j)
    (fun tsk_o => decide (tsk_o ≠ tsk))
    (arrivals_between arr_seq t1 (t1 + Δ)) ts
    (fun j' hj' => hall j' (in_arrivals_implies_arrived arr_seq j' _ _ hj'))
    (fun j' _ hp => by
      unfold another_task_hep_job at hp
      simp only [Bool.and_eq_true] at hp
      rw [← hj]
      exact hp.2)
  refine Nat.le_trans hpart (Nat.le_trans ?_
    (sum_of_workloads_is_at_most_bound_on_total_hep_workload arr_seq hvalid hcost ts hresp tsk j
      htsk hpos t1 (t1 + Δ + 1) Δ (by omega')))
  apply leq_sum_seq
  intro tsko _ _
  apply workload_of_jobs_weaken
  intro jo h
  unfold another_task_hep_job at h
  simp only [Bool.and_eq_true] at h ⊢
  exact ⟨h.1.1, h.2⟩

theorem bound_on_athep_workload_monotone {Task : TaskType} [DecidableEq Task]
    [TaskCost Task] [TaskDeadline Task] [MaxArrivals Task] (ts : List Task) :
    valid_taskset_arrival_curve ts max_arrivals →
      ∀ (tsk : Task) (A : Nat),
        Prosa.Util.Rel.monotone (fun x y => decide (x ≤ y)) (bound_on_athep_workload ts tsk A) := by
  intro hvalid tsk A x y hxy
  apply decide_eq_true
  unfold bound_on_athep_workload
  apply leq_sum_seq
  intro tsko hin _
  have hm := task_rbf_monotone tsko (hvalid tsko (decide_eq_true hin))
    (min (A + 1 + task_deadline tsk - task_deadline tsko) x)
    (min (A + 1 + task_deadline tsk - task_deadline tsko) y)
    (decide_eq_true (by have := of_decide_eq_true hxy; omega'))
  exact of_decide_eq_true hm

end Prosa.Analysis.Facts.Workload.EdfAthepBound
