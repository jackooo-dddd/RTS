-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: analysis/facts/workload/elf_athep_bound.v

import Prosa.Model.Priority.Elf
import Prosa.Model.Task.AbsoluteDeadline
import Prosa.Analysis.Definitions.Workload.Bounded
import Prosa.Analysis.Facts.Model.Workload
import Prosa.Analysis.Definitions.Workload.ElfAthepBound
import Prosa.Analysis.Facts.Model.Rbf

namespace Prosa.Analysis.Facts.Workload.ElfAthepBound

open Prosa.Behavior.Arrival_sequence
open Prosa.Behavior.Job
open Prosa.Behavior.Schedule
open Prosa.Behavior.Time
open Prosa.Model.Task.Concept
open Prosa.Model.Task.Arrival.Curves
open Prosa.Model.Job.Properties
open Prosa.Model.Priority.Definitions
open Prosa.Model.Priority.Gel
open Prosa.Model.Priority.Elf
open Prosa.Model.Aggregate.Workload
open Prosa.Util.Sum
open Prosa.Analysis.Definitions.RequestBoundFunction
open Prosa.Analysis.Definitions.Workload.Bounded
open Prosa.Analysis.Definitions.Workload.ElfAthepBound
open Prosa.Analysis.Facts.Behavior.Arrivals
open Prosa.Analysis.Facts.Model.Workload
open Prosa.Analysis.Facts.Model.Rbf

/-! Validity of the ELF bound on the higher-or-equal-priority workload of
other tasks. Binders follow the elaborated source types (unused section
context and hypotheses, including the busy-interval hypothesis, are absent,
as in the elaborated source). Representation: the ELF policy is the accepted
reducible `ELF FP`, passed explicitly; the section-local `hep_job_from_tsk
tsk_o` is inlined as `fun jo => hep_job jo j && decide (job_task jo =
tsk_o)`; `A` is inlined as `job_arrival j - t1`; `x \in xs`, `a != b` and
`a == b` are `decide (…)`; a Boolean in `Prop` position is `= true`;
`\sum_(x <- xs | P x) F x` is the accepted `sumFiltered xs P F`; as in the
accepted `model/priority/gel.v` and `analysis/definitions/workload/elf_athep_bound.v`,
`n%:R` on `int` is the cast `(n : Int)`, `(x <= y)%R` on `int` is
`decide (x ≤ y)`, `Num.max 0 x` is `max 0 x` and `` `|x| `` is `Int.natAbs`. -/

private theorem sf_cons {I : Type _} (a : I) (l : List I) (P : I → Bool) (F : I → Nat) :
    sumFiltered (a :: l) P F = (if P a = true then F a else 0) + sumFiltered l P F := by
  unfold sumFiltered
  cases h : P a <;> simp [List.filter_cons, h]

private theorem sf_nil {I : Type _} (P : I → Bool) (F : I → Nat) : sumFiltered [] P F = 0 := rfl

private theorem workload_of_jobs_false {Job : JobType} [DecidableEq Job] [JobCost Job]
    (P : Job → Bool) (jobs : List Job) (h : ∀ jo : Job, P jo = false) :
    workload_of_jobs P jobs = 0 := by
  unfold workload_of_jobs sumFiltered
  rw [List.filter_eq_nil_iff.mpr (fun x _ => by simp [h x])]
  rfl

/-- The higher-or-equal-priority workload of an equal-priority task `tsk_o`
in `[t1, t1 + delta)` is the one in `[t1, t1 + ep_task_interfering_interval_length)`. -/
theorem total_ep_tsk_workload_shorten_range {Task : TaskType} [DecidableEq Task] [PriorityPoint Task]
    {Job : JobType} [DecidableEq Job] [JobTask Job Task] [JobArrival Job] [JobCost Job]
    (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
      ∀ (tsk : Task) (FP : FP_policy Task) (j : Job), job_of_task tsk j = true →
        ∀ (t1 delta : duration) (tsk_o : Task),
          decide (ep_task_interfering_interval_length tsk tsk_o (job_arrival j - t1) ≤ (delta : Int)) = true →
          ep_task (FP := FP) tsk tsk_o = true →
          workload_of_jobs
              (fun jo => @hep_job Job _ (ELF (Job := Job) FP) jo j && decide (job_task (Task := Task) jo = tsk_o))
              (arrivals_between arr_seq t1 (t1 + delta)) ≤
            workload_of_jobs
              (fun jo => @hep_job Job _ (ELF (Job := Job) FP) jo j && decide (job_task (Task := Task) jo = tsk_o))
              (arrivals_between arr_seq t1
                (Int.natAbs (max 0 ((t1 : Int) +
                  ep_task_interfering_interval_length tsk tsk_o (job_arrival j - t1))))) := by
  intro hvalid tsk FP j htsk t1 delta tsk_o hle hep
  have hj : job_task (Task := Task) j = tsk := of_decide_eq_true htsk
  have hle' := of_decide_eq_true hle
  unfold ep_task_interfering_interval_length at hle' ⊢
  have hm : ((Int.natAbs (max 0 ((t1 : Int) + (((job_arrival j - t1 + ε : Nat) : Int) + task_priority_point tsk -
      task_priority_point tsk_o))) : Nat) : Int) = max 0 ((t1 : Int) + (((job_arrival j - t1 + ε : Nat) : Int) +
        task_priority_point tsk - task_priority_point tsk_o)) :=
    Int.natAbs_of_nonneg (le_max_left _ _)
  refine Nat.le_of_eq (workload_of_jobs_nil_tail arr_seq hvalid.1 _ t1 (t1 + delta) _ (by omega') ?_)
  intro j' hin' harr'
  have hge : t1 ≤ job_arrival j' := job_arrival_between_ge arr_seq hvalid.1 j' t1 (t1 + delta) hin'
  cases hto : decide (job_task (Task := Task) j' = tsk_o) with
  | false => simp
  | true =>
    have hto' : job_task (Task := Task) j' = tsk_o := of_decide_eq_true hto
    simp only [Bool.and_true, Bool.not_eq_true']
    have hep' : FP.hep_task tsk tsk_o = true ∧ FP.hep_task tsk_o tsk = true := by
      simpa [ep_task, Bool.and_eq_true] using hep
    show (hp_task (FP := FP) (job_task (Task := Task) j') (job_task (Task := Task) j) ||
      (FP.hep_task (job_task (Task := Task) j') (job_task (Task := Task) j) &&
        (GEL Job Task).hep_job j' j)) = false
    rw [hto', hj]
    simp only [hp_task, hep'.1, hep'.2, Bool.not_true, Bool.and_false, Bool.true_and, Bool.false_or]
    show decide ((job_arrival j' : Int) + task_priority_point (job_task (Task := Task) j') ≤
      (job_arrival j : Int) + task_priority_point (job_task (Task := Task) j)) = false
    rw [hto', hj]
    apply decide_eq_false
    omega'

/-- The workload of the higher-or-equal-priority jobs of the other
equal-priority tasks is bounded by `bound_on_ep_task_workload`. -/
theorem sum_of_ep_tsk_workloads_is_at_most_bound_on_ep_task_workload {Task : TaskType} [DecidableEq Task]
    [TaskCost Task] [MaxArrivals Task] [PriorityPoint Task]
    {Job : JobType} [DecidableEq Job] [JobTask Job Task] [JobArrival Job] [JobCost Job]
    (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
      arrivals_have_valid_job_costs (Task := Task) arr_seq →
      ∀ ts : List Task, taskset_respects_max_arrivals arr_seq ts →
        ∀ (tsk : Task) (FP : FP_policy Task) (j : Job), job_of_task tsk j = true →
          ∀ (t1 t2 delta : duration), t1 + delta < t2 →
            sumFiltered ts (fun tsk_o => ep_task (FP := FP) tsk tsk_o && decide (tsk_o ≠ tsk))
                (fun tsk_o => workload_of_jobs
                  (fun jo => @hep_job Job _ (ELF (Job := Job) FP) jo j &&
                    decide (job_task (Task := Task) jo = tsk_o))
                  (arrivals_between arr_seq t1 (t1 + delta))) ≤
              bound_on_ep_task_workload ts (FP := FP) tsk (job_arrival j - t1) delta := by
  intro hvalid hcost ts hresp tsk FP j htsk t1 t2 delta hlt
  unfold bound_on_ep_task_workload
  apply leq_sum_seq
  intro tsko hin hP
  have hep : ep_task (FP := FP) tsk tsko = true := by
    simp only [Bool.and_eq_true] at hP; exact hP.1
  have hresp' := hresp tsko (decide_eq_true hin)
  have hPj : ∀ jo : Job,
      (@hep_job Job _ (ELF (Job := Job) FP) jo j && decide (job_task (Task := Task) jo = tsko)) = true →
        job_of_task tsko jo = true := by
    intro jo h
    simp only [Bool.and_eq_true] at h
    exact h.2
  by_cases hge : delta ≤ Int.natAbs (max 0 (ep_task_interfering_interval_length tsk tsko (job_arrival j - t1)))
  · rw [Nat.min_eq_right hge]
    exact rbf_spec' arr_seq hcost _ tsko hresp' hPj t1 delta
  · have hlt' : Int.natAbs (max 0 (ep_task_interfering_interval_length tsk tsko (job_arrival j - t1))) ≤ delta := by
      omega'
    rw [Nat.min_eq_left hlt']
    have hm : ((Int.natAbs (max 0 (ep_task_interfering_interval_length tsk tsko (job_arrival j - t1))) : Nat) : Int) =
        max 0 (ep_task_interfering_interval_length tsk tsko (job_arrival j - t1)) :=
      Int.natAbs_of_nonneg (le_max_left _ _)
    have hb : ep_task_interfering_interval_length tsk tsko (job_arrival j - t1) ≤
        max 0 (ep_task_interfering_interval_length tsk tsko (job_arrival j - t1)) := le_max_right _ _
    have hdle : decide (ep_task_interfering_interval_length tsk tsko (job_arrival j - t1) ≤ (delta : Int)) = true := by
      apply decide_eq_true; omega'
    refine Nat.le_trans (total_ep_tsk_workload_shorten_range arr_seq hvalid tsk FP j htsk t1 delta tsko hdle hep) ?_
    by_cases hL : 0 ≤ ep_task_interfering_interval_length tsk tsko (job_arrival j - t1)
    · have heq : Int.natAbs (max 0 ((t1 : Int) + ep_task_interfering_interval_length tsk tsko (job_arrival j - t1))) =
          t1 + Int.natAbs (max 0 (ep_task_interfering_interval_length tsk tsko (job_arrival j - t1))) := by
        omega'
      rw [heq]
      exact rbf_spec' arr_seq hcost _ tsko hresp' hPj t1 _
    · rw [arrivals_between_geq arr_seq t1 _ (by omega'), workload_of_jobs0]
      exact Nat.zero_le _

/-- The workload of the higher-or-equal-priority jobs of the strictly
higher-priority tasks is bounded by `bound_on_hp_task_workload`. -/
theorem sum_of_hp_tsk_workloads_is_at_most_bound_on_hp_task_workload {Task : TaskType} [DecidableEq Task]
    [TaskCost Task] [MaxArrivals Task] [PriorityPoint Task]
    {Job : JobType} [DecidableEq Job] [JobTask Job Task] [JobArrival Job] [JobCost Job]
    (arr_seq : arrival_sequence Job) :
    arrivals_have_valid_job_costs (Task := Task) arr_seq →
      ∀ ts : List Task, taskset_respects_max_arrivals arr_seq ts →
        ∀ (tsk : Task) (FP : FP_policy Task) (j : Job) (t1 delta : duration),
          sumFiltered ts (fun tsk_o => hp_task (FP := FP) tsk_o tsk)
              (fun tsk_o => workload_of_jobs
                (fun jo => @hep_job Job _ (ELF (Job := Job) FP) jo j &&
                  decide (job_task (Task := Task) jo = tsk_o))
                (arrivals_between arr_seq t1 (t1 + delta))) ≤
            bound_on_hp_task_workload ts (FP := FP) tsk delta := by
  intro hcost ts hresp tsk FP j t1 delta
  unfold bound_on_hp_task_workload total_hp_request_bound_function_FP
  apply leq_sum_seq
  intro tsko hin _
  exact rbf_spec' arr_seq hcost _ tsko (hresp tsko (decide_eq_true hin))
    (fun jo h => by simp only [Bool.and_eq_true] at h; exact h.2) t1 delta

/-- The higher-or-equal-priority workload of the other tasks splits into the
equal-priority and the strictly higher-priority parts. -/
theorem sum_of_hep_workloads_partitioned {Task : TaskType} [DecidableEq Task] [PriorityPoint Task]
    {Job : JobType} [DecidableEq Job] [JobTask Job Task] [JobArrival Job] [JobCost Job]
    (arr_seq : arrival_sequence Job) (ts : List Task) (tsk : Task) (FP : FP_policy Task) (j : Job) :
    job_of_task tsk j = true →
      ∀ t1 delta : duration,
        sumFiltered ts (fun tsk_o => decide (tsk_o ≠ tsk))
            (fun tsk_o => workload_of_jobs
              (fun jo => @hep_job Job _ (ELF (Job := Job) FP) jo j &&
                decide (job_task (Task := Task) jo = tsk_o))
              (arrivals_between arr_seq t1 (t1 + delta))) =
          sumFiltered ts (fun tsk_o => ep_task (FP := FP) tsk tsk_o && decide (tsk_o ≠ tsk))
              (fun tsk_o => workload_of_jobs
                (fun jo => @hep_job Job _ (ELF (Job := Job) FP) jo j &&
                  decide (job_task (Task := Task) jo = tsk_o))
                (arrivals_between arr_seq t1 (t1 + delta))) +
            sumFiltered ts (fun tsk_o => hp_task (FP := FP) tsk_o tsk)
              (fun tsk_o => workload_of_jobs
                (fun jo => @hep_job Job _ (ELF (Job := Job) FP) jo j &&
                  decide (job_task (Task := Task) jo = tsk_o))
                (arrivals_between arr_seq t1 (t1 + delta))) := by
  intro htsk t1 delta
  have hj : job_task (Task := Task) j = tsk := of_decide_eq_true htsk
  induction ts with
  | nil => rfl
  | cons a l ih =>
    rw [sf_cons, sf_cons, sf_cons, ih]
    by_cases ha : a = tsk
    · subst ha
      simp [hp_task]
    · have hzero : FP.hep_task a tsk = false →
          workload_of_jobs
            (fun jo => @hep_job Job _ (ELF (Job := Job) FP) jo j &&
              decide (job_task (Task := Task) jo = a))
            (arrivals_between arr_seq t1 (t1 + delta)) = 0 := by
        intro hf
        apply workload_of_jobs_false
        intro jo
        show (@hep_job Job _ (ELF (Job := Job) FP) jo j && decide (job_task (Task := Task) jo = a)) = false
        cases hto : decide (job_task (Task := Task) jo = a) with
        | false => simp
        | true =>
          have hto' : job_task (Task := Task) jo = a := of_decide_eq_true hto
          show ((hp_task (FP := FP) (job_task (Task := Task) jo) (job_task (Task := Task) j) ||
            (FP.hep_task (job_task (Task := Task) jo) (job_task (Task := Task) j) &&
              (GEL Job Task).hep_job jo j)) && true) = false
          rw [hto', hj]
          simp [hp_task, hf]
      cases h1 : FP.hep_task a tsk <;> cases h2 : FP.hep_task tsk a <;>
        simp [ep_task, hp_task, ha, h1, h2, hzero] <;> omega

/-- The higher-or-equal-priority workload of the other tasks is bounded by
`bound_on_athep_workload`. -/
theorem sum_of_workloads_is_at_most_bound_on_total_hep_workload {Task : TaskType} [DecidableEq Task]
    [TaskCost Task] [MaxArrivals Task] [PriorityPoint Task]
    {Job : JobType} [DecidableEq Job] [JobTask Job Task] [JobArrival Job] [JobCost Job]
    (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
      arrivals_have_valid_job_costs (Task := Task) arr_seq →
      ∀ ts : List Task, taskset_respects_max_arrivals arr_seq ts →
        ∀ (tsk : Task) (FP : FP_policy Task) (j : Job), job_of_task tsk j = true →
          job_cost_positive j = true →
          ∀ (t1 t2 delta : duration), t1 + delta < t2 →
            sumFiltered ts (fun tsk_o => decide (tsk_o ≠ tsk))
                (fun tsk_o => workload_of_jobs
                  (fun jo => @hep_job Job _ (ELF (Job := Job) FP) jo j &&
                    decide (job_task (Task := Task) jo = tsk_o))
                  (arrivals_between arr_seq t1 (t1 + delta))) ≤
              bound_on_athep_workload ts (FP := FP) tsk (job_arrival j - t1) delta := by
  intro hvalid hcost ts hresp tsk FP j htsk _ t1 t2 delta hlt
  rw [sum_of_hep_workloads_partitioned arr_seq ts tsk FP j htsk t1 delta]
  unfold bound_on_athep_workload
  have hhp := sum_of_hp_tsk_workloads_is_at_most_bound_on_hp_task_workload arr_seq hcost ts hresp tsk FP j t1 delta
  have hep := sum_of_ep_tsk_workloads_is_at_most_bound_on_ep_task_workload arr_seq hvalid hcost ts hresp tsk FP j
    htsk t1 t2 delta hlt
  omega

/-- `bound_on_athep_workload` is a valid bound on the higher-or-equal-priority
workload of the other tasks under ELF. -/
theorem bound_on_athep_workload_is_valid {Task : TaskType} [DecidableEq Task]
    [TaskCost Task] [MaxArrivals Task] [PriorityPoint Task]
    {Job : JobType} [DecidableEq Job] [JobTask Job Task] [JobArrival Job] [JobCost Job]
    {PState : ProcessorState Job} (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
      arrivals_have_valid_job_costs (Task := Task) arr_seq →
      ∀ ts : List Task, all_jobs_from_taskset arr_seq ts → taskset_respects_max_arrivals arr_seq ts →
        ∀ (tsk : Task) (sched : schedule PState) (FP : FP_policy Task),
          @athep_workload_is_bounded Task _ Job _ _ _ _ PState
            (ELF (Job := Job) FP) arr_seq sched tsk
            (bound_on_athep_workload ts (FP := FP) tsk) := by
  intro hvalid hcost ts hall hresp tsk sched FP j t1 Δ hpos htsk _
  have hj : job_task (Task := Task) j = tsk := of_decide_eq_true htsk
  have hpart := @workload_of_jobs_le_sum_over_partitions Task _ Job _ _ _
    (fun j' => @another_task_hep_job Task _ Job _ _ (ELF (Job := Job) FP) j' j)
    (fun tsk_o => decide (tsk_o ≠ tsk))
    (arrivals_between arr_seq t1 (t1 + Δ)) ts
    (fun j' hj' => hall j' (in_arrivals_implies_arrived arr_seq j' _ _ hj'))
    (fun j' _ hp => by
      unfold another_task_hep_job at hp
      simp only [Bool.and_eq_true] at hp
      rw [← hj]
      exact hp.2)
  refine Nat.le_trans hpart (Nat.le_trans ?_
    (sum_of_workloads_is_at_most_bound_on_total_hep_workload arr_seq hvalid hcost ts hresp tsk FP j
      htsk hpos t1 (t1 + Δ + 1) Δ (by omega')))
  apply leq_sum_seq
  intro tsko _ _
  apply workload_of_jobs_weaken
  intro jo h
  unfold another_task_hep_job at h
  simp only [Bool.and_eq_true] at h ⊢
  exact ⟨h.1.1, h.2⟩

end Prosa.Analysis.Facts.Workload.ElfAthepBound
