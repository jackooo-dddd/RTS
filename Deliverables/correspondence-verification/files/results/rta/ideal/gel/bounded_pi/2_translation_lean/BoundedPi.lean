-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: results/rta/ideal/gel/bounded_pi.v

import Prosa.Analysis.Abstract.Ideal.AbstractSeqRta
import Prosa.Analysis.Abstract.Ideal.CumulativeBounds
import Prosa.Analysis.Facts.Readiness.Basic
import Prosa.Model.Schedule.PriorityDriven
import Prosa.Model.Priority.Gel
import Prosa.Analysis.Facts.Priority.Gel
import Prosa.Analysis.Facts.Model.TaskCost

namespace Prosa.Results.Rta.Ideal.Gel.BoundedPi

open Prosa.Behavior.Arrival_sequence
open Prosa.Behavior.Job
open Prosa.Behavior.Ready
open Prosa.Behavior.Schedule
open Prosa.Behavior.Service
open Prosa.Behavior.Time
open Prosa.Model.Job.Properties
open Prosa.Model.Task.Concept
open Prosa.Model.Task.Arrival.Curves
open Prosa.Model.Task.Sequentiality
open Prosa.Model.Preemption.Parameter
open Prosa.Model.Task.Preemption.Parameters
open Prosa.Model.Priority.Definitions
open Prosa.Model.Priority.Gel
open Prosa.Model.Processor.Ideal
open Prosa.Model.Readiness.Basic
open Prosa.Model.Schedule.PriorityDriven
open Prosa.Model.Aggregate.Workload
open Prosa.Model.Aggregate.ServiceOfJobs
open Prosa.Util.Sum
open Prosa.Analysis.Definitions.Schedulability
open Prosa.Analysis.Definitions.RequestBoundFunction
open Prosa.Analysis.Definitions.PriorityInversion
open Prosa.Analysis.Definitions.Interference
open Prosa.Analysis.Facts.Model.Rbf
open Prosa.Analysis.Facts.Model.Workload
open Prosa.Analysis.Facts.Model.ArrivalCurves
open Prosa.Analysis.Facts.Model.ServiceOfJobs
open Prosa.Analysis.Facts.Model.Ideal.Schedule
open Prosa.Analysis.Facts.Priority.Gel
open Prosa.Analysis.Facts.Readiness.Basic
open Prosa.Analysis.Facts.Interference
open Prosa.Analysis.Facts.Behavior.Arrivals
open Prosa.Analysis.Facts.Behavior.Completion
open Prosa.Analysis.Abstract.Definitions
open Prosa.Analysis.Abstract.IBF.Task
open Prosa.Analysis.Abstract.Ideal.IwInstantiation
open Prosa.Analysis.Abstract.Ideal.CumulativeBounds
open Prosa.Analysis.Abstract.Ideal.AbstractSeqRta

/-! Abstract RTA for GEL schedulers with bounded priority inversion on ideal uniprocessors.

Binders follow the elaborated source types: every declaration takes only the section inputs and hypotheses it uses,
in their elaborated order. The section's readiness (the accepted `basic_ready_instance`) and the GEL policy (the
accepted reducible `GEL Job Task`) are passed explicitly where the elaborated statements use them implicitly; the
section-local instances `ideal_jlfp_interference` / `ideal_jlfp_interfering_workload` re-expose the accepted
instantiation of `iw_instantiation` at the section's arrival sequence and schedule and the GEL policy. The section-local
`interval`, `bound_on_total_hep_workload`, `task_IBF`, `PP`, `A`, `jobs`, `GEL_from` and `total_interference_bound`
are inlined. Representation: `ε` is `1`; a Boolean in `Prop` position is `= true`; `a != b` and `a == b` are
`decide (…)`; `x \in xs` is `decide (x ∈ xs) = true`; `has P xs` is `xs.any P`; `\sum_(x <- xs | P x) F x` is the
accepted `sumFiltered xs P F`; `minn` is `min`; as in the accepted `model/priority/gel.v` and
`analysis/definitions/workload/elf_athep_bound.v`, `n%:R` on `int` is the cast `(n : Int)`, `(x <= y)%R` on `int` is
`decide (x ≤ y)`, `Num.max 0 x` is `max 0 x` and `` `|x| `` is `Int.natAbs`; `search_space.is_in_search_space` is the
accepted abstract search-space predicate. -/

/-- `omega` after unfolding the time aliases. -/
macro "omega'" : tactic => `(tactic| (try dsimp only [instant, duration, work] at *) <;> omega)

variable {Task : TaskType} [DecidableEq Task] {Job : JobType} [DecidableEq Job]

/-- If `Δ` exceeds the interval in which jobs of `tsk_o` can have higher-or-equal priority, the higher-or-equal-priority
workload of `tsk_o` in `[t1, t1 + Δ)` is the one before the end of that interval. -/
theorem total_workload_shorten_range [TaskCost Task] [MaxArrivals Task] [JobTask Job Task] [JobArrival Job]
    [JobCost Job] [PriorityPoint Task] (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
    ∀ (ts : List Task) (tsk : Task), decide (tsk ∈ ts) = true →
    ∀ L : duration, 0 < L → L = total_request_bound_function ts L →
    ∀ j : Job, job_of_task tsk j = true → job_cost_positive j = true →
    ∀ t1 t2 Δ : duration, t1 + Δ < t2 →
    ∀ tsk_o : Task, decide (tsk_o ∈ ts) = true → decide (tsk_o ≠ tsk) = true →
      decide (((job_arrival j - t1 + 1 : Nat) : Int) + task_priority_point tsk - task_priority_point tsk_o ≤
        (Δ : Int)) = true →
      workload_of_jobs (fun jo => @hep_job Job _ (GEL Job Task) jo j && decide (job_task (Task := Task) jo = tsk_o))
          (arrivals_between arr_seq t1 (t1 + Δ)) ≤
        workload_of_jobs (fun jo => @hep_job Job _ (GEL Job Task) jo j && decide (job_task (Task := Task) jo = tsk_o))
          (arrivals_between arr_seq t1
            (Int.natAbs (max 0 ((t1 : Int) + (((job_arrival j - t1 + 1 : Nat) : Int) + task_priority_point tsk -
              task_priority_point tsk_o))))) := by
  intro hvalid ts tsk _ L _ _ j htsk _ t1 t2 Δ _ tsk_o _ _ hle
  have hj : job_task (Task := Task) j = tsk := of_decide_eq_true htsk
  have hle' := of_decide_eq_true hle
  have hm : ((Int.natAbs (max 0 ((t1 : Int) + (((job_arrival j - t1 + 1 : Nat) : Int) + task_priority_point tsk -
      task_priority_point tsk_o))) : Nat) : Int) = max 0 ((t1 : Int) + (((job_arrival j - t1 + 1 : Nat) : Int) +
        task_priority_point tsk - task_priority_point tsk_o)) :=
    Int.natAbs_of_nonneg (le_max_left _ _)
  refine Nat.le_of_eq (workload_of_jobs_nil_tail arr_seq hvalid.1 _ t1 (t1 + Δ) _ (by omega') ?_)
  intro j' _ harr'
  cases hto : decide (job_task (Task := Task) j' = tsk_o) with
  | false => simp
  | true =>
    have hto' : job_task (Task := Task) j' = tsk_o := of_decide_eq_true hto
    simp only [Bool.and_true, Bool.not_eq_true']
    show decide (job_priority_point (Task := Task) j' ≤ job_priority_point (Task := Task) j) = false
    unfold job_priority_point
    rw [hto', hj]
    apply decide_eq_false
    omega'

/-- The bound on the total higher-or-equal-priority workload bounds the sum of the higher-or-equal-priority workloads
of the other tasks. -/
theorem sum_of_workloads_is_at_most_bound_on_total_hep_workload [TaskCost Task] [MaxArrivals Task]
    [JobTask Job Task] [JobArrival Job] [JobCost Job] [PriorityPoint Task] (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq → arrivals_have_valid_job_costs (Task := Task) arr_seq →
    ∀ ts : List Task, taskset_respects_max_arrivals arr_seq ts →
    ∀ tsk : Task, decide (tsk ∈ ts) = true →
    ∀ L : duration, 0 < L → L = total_request_bound_function ts L →
    ∀ j : Job, job_of_task tsk j = true → job_cost_positive j = true →
    ∀ t1 t2 Δ : duration, t1 + Δ < t2 →
      sumFiltered ts (fun tsk_o => decide (tsk_o ≠ tsk))
          (fun tsk_o => workload_of_jobs
            (fun jo => @hep_job Job _ (GEL Job Task) jo j && decide (job_task (Task := Task) jo = tsk_o))
            (arrivals_between arr_seq t1 (t1 + Δ))) ≤
        sumFiltered ts (fun tsk_o => decide (tsk_o ≠ tsk))
          (fun tsk_o => task_request_bound_function tsk_o
            (min (Int.natAbs (max 0 (((job_arrival j - t1 + 1 : Nat) : Int) + task_priority_point tsk -
              task_priority_point tsk_o))) Δ)) := by
  intro hvalid hcost ts hresp tsk hin L hL hfix j htsk hcp t1 t2 Δ hlt
  apply leq_sum_seq
  intro tsko hino hne
  have hresp' := hresp tsko (decide_eq_true hino)
  have hPj : ∀ jo : Job,
      (@hep_job Job _ (GEL Job Task) jo j && decide (job_task (Task := Task) jo = tsko)) = true →
        job_of_task tsko jo = true := by
    intro jo h
    simp only [Bool.and_eq_true] at h
    exact h.2
  by_cases hge : Δ ≤ Int.natAbs (max 0 (((job_arrival j - t1 + 1 : Nat) : Int) + task_priority_point tsk -
      task_priority_point tsko))
  · rw [Nat.min_eq_right hge]
    exact rbf_spec' arr_seq hcost _ tsko hresp' hPj t1 Δ
  · have hlt' : Int.natAbs (max 0 (((job_arrival j - t1 + 1 : Nat) : Int) + task_priority_point tsk -
        task_priority_point tsko)) ≤ Δ := by omega'
    rw [Nat.min_eq_left hlt']
    have hm : ((Int.natAbs (max 0 (((job_arrival j - t1 + 1 : Nat) : Int) + task_priority_point tsk -
        task_priority_point tsko)) : Nat) : Int) = max 0 (((job_arrival j - t1 + 1 : Nat) : Int) +
          task_priority_point tsk - task_priority_point tsko) :=
      Int.natAbs_of_nonneg (le_max_left _ _)
    have hb : ((job_arrival j - t1 + 1 : Nat) : Int) + task_priority_point tsk - task_priority_point tsko ≤
        max 0 (((job_arrival j - t1 + 1 : Nat) : Int) + task_priority_point tsk - task_priority_point tsko) :=
      le_max_right _ _
    have hdle : decide (((job_arrival j - t1 + 1 : Nat) : Int) + task_priority_point tsk -
        task_priority_point tsko ≤ (Δ : Int)) = true := by
      apply decide_eq_true; omega'
    refine Nat.le_trans (total_workload_shorten_range arr_seq hvalid ts tsk hin L hL hfix j htsk hcp t1 t2 Δ hlt
      tsko (decide_eq_true hino) hne hdle) ?_
    by_cases hL0 : 0 ≤ ((job_arrival j - t1 + 1 : Nat) : Int) + task_priority_point tsk - task_priority_point tsko
    · have heq : Int.natAbs (max 0 ((t1 : Int) + (((job_arrival j - t1 + 1 : Nat) : Int) + task_priority_point tsk -
          task_priority_point tsko))) = t1 + Int.natAbs (max 0 (((job_arrival j - t1 + 1 : Nat) : Int) +
            task_priority_point tsk - task_priority_point tsko)) := by
        omega'
      rw [heq]
      exact rbf_spec' arr_seq hcost _ tsko hresp' hPj t1 _
    · rw [arrivals_between_geq arr_seq t1 _ (by omega'), workload_of_jobs0]
      exact Nat.zero_le _

/-- The priority-inversion bound plus the bound on the total higher-or-equal-priority workload bounds the task
interference. -/
theorem instantiated_task_interference_is_bounded [TaskCost Task] [MaxArrivals Task] [JobTask Job Task]
    [JobArrival Job] [JobCost Job] [PriorityPoint Task] (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
    ∀ sched : schedule (processor_state Job),
      @valid_schedule Job _ _ (processor_state Job) sched _ basic_ready_instance arr_seq →
      arrivals_have_valid_job_costs (Task := Task) arr_seq →
    ∀ ts : List Task, all_jobs_from_taskset arr_seq ts → taskset_respects_max_arrivals arr_seq ts →
    ∀ tsk : Task, decide (tsk ∈ ts) = true →
    ∀ priority_inversion_bound : duration → duration,
      @priority_inversion_is_bounded_by Task _ Job _ _ _ _ (processor_state Job) arr_seq sched (GEL Job Task) tsk
        priority_inversion_bound →
    ∀ L : duration, 0 < L → L = total_request_bound_function ts L →
      @task_interference_is_bounded_by Job _ Task _ _ _ _ (processor_state Job) arr_seq sched tsk
        (@ideal_jlfp_interference Job _ arr_seq sched (GEL Job Task))
        (@ideal_jlfp_interfering_workload Job _ _ arr_seq sched (GEL Job Task))
        (fun A R => priority_inversion_bound A +
          sumFiltered ts (fun tsk_o => decide (tsk_o ≠ tsk))
            (fun tsk_o => task_request_bound_function tsk_o
              (min (Int.natAbs (max 0 (((A + 1 : Nat) : Int) + task_priority_point tsk -
                task_priority_point tsk_o))) R))) := by
  intro hva sched hvs hvjc ts hall hresp tsk hin pib hpib L hL hfix t1 t2 Δ j hj htsk hbi hlt hncomp A hA
  let _ : JobReady Job (processor_state Job) := basic_ready_instance
  let _ : JLFP_policy Job := GEL Job Task
  have hfrom := hvs.1
  have hmust := jobs_must_arrive_to_be_ready sched hvs.2
  have hcde := completed_jobs_are_not_ready sched hvs.2
  have hreflJ : reflexive_job_priorities (GEL Job Task) := GEL_is_reflexive
  have hj' : job_task (Task := Task) j = tsk := of_decide_eq_true htsk
  have hpos : 0 < job_cost j := by
    rcases Nat.eq_zero_or_pos (job_cost j) with h0 | h
    · exfalso
      unfold completed_by at hncomp
      rw [h0] at hncomp
      simp at hncomp
    · exact h
  have hcp : job_cost_positive j = true := by unfold job_cost_positive; exact decide_eq_true hpos
  have hA' : A = job_arrival j - t1 := hA t1 t2 hbi
  subst hA'
  have hcl := (instantiated_busy_interval_equivalent_busy_interval arr_seq hva sched hfrom hmust hcde hreflJ j hj hcp
    t1 t2).mpr hbi
  have hsplit := cumulative_task_interference_split arr_seq hva sched hfrom hmust (JLFP := GEL Job Task) hreflJ
    tsk j t1 (t1 + Δ) hj htsk hncomp
  -- priority inversion
  have hpi : cumulative_priority_inversion arr_seq sched j t1 (t1 + Δ) ≤ pib (job_arrival j - t1) :=
    cumulative_priority_inversion_is_bounded hreflJ arr_seq hva sched hvs tsk j hj htsk hcp t1 t2 hbi Δ
      (Nat.le_of_lt hlt) pib hpib
  -- other higher-or-equal-priority tasks
  have hathep : cumulative_another_task_hep_job_interference (Task := Task) arr_seq sched j t1 (t1 + Δ) ≤
      sumFiltered ts (fun tsk_o => decide (tsk_o ≠ tsk))
        (fun tsk_o => task_request_bound_function tsk_o
          (min (Int.natAbs (max 0 (((job_arrival j - t1 + 1 : Nat) : Int) + task_priority_point tsk -
            task_priority_point tsk_o))) Δ)) := by
    rw [cumulative_i_thep_eq_service_of_othep (ideal_proc_model_is_a_uniprocessor_model Job) arr_seq hva sched hmust
      hcde (GEL Job Task) (ideal_proc_model_provides_unit_service Job) j t1 (t1 + Δ) hcl.1.2.1]
    unfold service_of_other_task_hep_jobs
    refine Nat.le_trans (service_of_jobs_le_workload (ideal_proc_model_provides_unit_service Job) sched hcde _ _ _ _) ?_
    have hpart := @workload_of_jobs_le_sum_over_partitions Task _ Job _ _ _
      (fun j' => @another_task_hep_job Task _ Job _ _ (GEL Job Task) j' j)
      (fun tsk_o => decide (tsk_o ≠ tsk))
      (arrivals_between arr_seq t1 (t1 + Δ)) ts
      (fun j' hj'' => hall j' (in_arrivals_implies_arrived arr_seq j' _ _ hj''))
      (fun j' _ hp => by
        unfold another_task_hep_job at hp
        simp only [Bool.and_eq_true] at hp
        rw [← hj']
        exact hp.2)
    refine Nat.le_trans hpart (Nat.le_trans ?_
      (sum_of_workloads_is_at_most_bound_on_total_hep_workload arr_seq hva hvjc ts hresp tsk hin L hL hfix j htsk hcp
        t1 t2 Δ hlt))
    apply leq_sum_seq
    intro tsko _ _
    apply workload_of_jobs_weaken
    intro jo h
    unfold another_task_hep_job at h
    simp only [Bool.and_eq_true] at h ⊢
    exact ⟨h.1.1, h.2⟩
  refine Nat.le_trans hsplit ?_
  omega'

/-- The RBF of `tsk` changes at `A`. -/
def task_rbf_changes_at [TaskCost Task] [MaxArrivals Task] (tsk : Task) (A : duration) : Bool :=
  decide (task_request_bound_function tsk A ≠ task_request_bound_function tsk (A + 1))

/-- The interval of some other task `tsko` changes at `A`. -/
def bound_on_total_hep_workload_changes_at [PriorityPoint Task] (ts : List Task) (tsk : Task) (A : Nat) : Bool :=
  ts.any (fun tsko => decide (tsk ≠ tsko) &&
    decide (((A - 1 + 1 : Nat) : Int) + task_priority_point tsk - task_priority_point tsko ≠
      ((A + 1 : Nat) : Int) + task_priority_point tsk - task_priority_point tsko))

/-- The priority-inversion bound changes at `A`. -/
def priority_inversion_changes_at (priority_inversion_bound : duration → duration) (A : duration) : Bool :=
  decide (priority_inversion_bound (A - 1) ≠ priority_inversion_bound A)

/-- The concrete GEL search space: offsets below `L` at which the priority-inversion bound, the RBF of `tsk` or the
bound on the total higher-or-equal-priority workload changes. -/
def is_in_search_space [TaskCost Task] [MaxArrivals Task] [PriorityPoint Task] (ts : List Task) (tsk : Task)
    (priority_inversion_bound : duration → duration) (L A : duration) : Bool :=
  decide (A < L) &&
    (priority_inversion_changes_at priority_inversion_bound A || task_rbf_changes_at tsk A ||
      bound_on_total_hep_workload_changes_at ts tsk A)

/-- Any offset of the abstract search space is in the concrete GEL search space. -/
theorem A_is_in_concrete_search_space [TaskCost Task] [MaxArrivals Task] [PriorityPoint Task] (ts : List Task) :
    valid_taskset_arrival_curve ts max_arrivals →
    ∀ tsk : Task, decide (tsk ∈ ts) = true →
    ∀ (priority_inversion_bound : duration → duration) (L : duration), 0 < L → 0 < task_cost tsk →
      0 < max_arrivals tsk 1 →
    ∀ A : duration,
      Prosa.Analysis.Abstract.SearchSpace.is_in_search_space L
          (fun A0 Δ => task_request_bound_function tsk (A0 + 1) - task_cost tsk +
            (priority_inversion_bound A0 +
              sumFiltered ts (fun tsk_o => decide (tsk_o ≠ tsk))
                (fun tsk_o => task_request_bound_function tsk_o
                  (min (Int.natAbs (max 0 (((A0 + 1 : Nat) : Int) + task_priority_point tsk -
                    task_priority_point tsk_o))) Δ)))) A →
        is_in_search_space ts tsk priority_inversion_bound L A = true := by
  intro hv tsk hin pib L hL hc hpos A h
  unfold is_in_search_space
  rcases h with hA | ⟨hA0, hAL, x, _, hne⟩
  · subst hA
    have h0 := task_rbf_0_zero tsk (hv tsk hin)
    have h1 := task_rbf_1_ge_task_cost tsk hpos
    simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq]
    refine ⟨hL, Or.inl (Or.inr ?_)⟩
    unfold task_rbf_changes_at
    apply decide_eq_true
    rw [h0, Nat.zero_add]
    omega'
  · simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq]
    refine ⟨hAL, ?_⟩
    apply Classical.byContradiction
    intro hno
    simp only [not_or] at hno
    obtain ⟨⟨hpi, hrbf⟩, hwl⟩ := hno
    apply hne
    have hA1 : A - 1 + 1 = A := Nat.sub_add_cancel hA0
    have hpi' : pib (A - 1) = pib A := by
      unfold priority_inversion_changes_at at hpi
      simpa using hpi
    have hrbf' : task_request_bound_function tsk A = task_request_bound_function tsk (A + 1) := by
      unfold task_rbf_changes_at at hrbf
      simpa using hrbf
    dsimp only
    rw [hA1, hpi', hrbf']
    congr 2
    unfold sumFiltered
    congr 1
    apply List.map_congr_left
    intro tsko hmem
    simp only [List.mem_filter, decide_eq_true_eq] at hmem
    have hw : ¬ (((A - 1 + 1 : Nat) : Int) + task_priority_point tsk - task_priority_point tsko ≠
        ((A + 1 : Nat) : Int) + task_priority_point tsk - task_priority_point tsko) := by
      intro hneq
      apply hwl
      unfold bound_on_total_hep_workload_changes_at
      rw [List.any_eq_true]
      exact ⟨tsko, hmem.1, by simp only [Bool.and_eq_true, decide_eq_true_eq]; exact ⟨Ne.symm hmem.2, hneq⟩⟩
    rw [hA1] at hw
    simp only [ne_eq, Decidable.not_not] at hw
    rw [hw]

/-- Every offset of the abstract search space has a solution of the response-time recurrence. -/
theorem correct_search_space [TaskCost Task] [TaskRunToCompletionThreshold Task] [MaxArrivals Task]
    [PriorityPoint Task] (ts : List Task) :
    valid_taskset_arrival_curve ts max_arrivals →
    ∀ tsk : Task, decide (tsk ∈ ts) = true →
    ∀ (priority_inversion_bound : duration → duration) (L : duration), 0 < L →
    ∀ R : duration,
      (∀ A : duration, is_in_search_space ts tsk priority_inversion_bound L A = true →
        ∃ F : duration,
          priority_inversion_bound A + (task_request_bound_function tsk (A + 1) - (task_cost tsk - task_rtct tsk)) +
              sumFiltered ts (fun tsk_o => decide (tsk_o ≠ tsk))
                (fun tsk_o => task_request_bound_function tsk_o
                  (min (Int.natAbs (max 0 (((A + 1 : Nat) : Int) + task_priority_point tsk -
                    task_priority_point tsk_o))) (A + F))) ≤ A + F ∧
            F + (task_cost tsk - task_rtct tsk) ≤ R) →
      0 < task_cost tsk → 0 < max_arrivals tsk 1 →
    ∀ A : Nat,
      Prosa.Analysis.Abstract.SearchSpace.is_in_search_space L
          (fun A0 Δ => task_request_bound_function tsk (A0 + 1) - task_cost tsk +
            (priority_inversion_bound A0 +
              sumFiltered ts (fun tsk_o => decide (tsk_o ≠ tsk))
                (fun tsk_o => task_request_bound_function tsk_o
                  (min (Int.natAbs (max 0 (((A0 + 1 : Nat) : Int) + task_priority_point tsk -
                    task_priority_point tsk_o))) Δ)))) A →
        ∃ F : Nat,
          task_request_bound_function tsk (A + 1) - (task_cost tsk - task_rtct tsk) +
              (priority_inversion_bound A +
                sumFiltered ts (fun tsk_o => decide (tsk_o ≠ tsk))
                  (fun tsk_o => task_request_bound_function tsk_o
                    (min (Int.natAbs (max 0 (((A + 1 : Nat) : Int) + task_priority_point tsk -
                      task_priority_point tsk_o))) (A + F)))) ≤ A + F ∧
            F + (task_cost tsk - task_rtct tsk) ≤ R := by
  intro hv tsk hin pib L hL R hR hc hpos A hA
  obtain ⟨F, hF, hFR⟩ := hR A (A_is_in_concrete_search_space ts hv tsk hin pib L hL hc hpos A hA)
  exact ⟨F, by omega', hFR⟩

/-- Response-time bound for GEL schedulers with bounded priority inversion on ideal uniprocessors. -/
theorem uniprocessor_response_time_bound_edf [TaskCost Task] [TaskRunToCompletionThreshold Task] [MaxArrivals Task]
    [JobTask Job Task] [JobArrival Job] [JobCost Job] [JobPreemptable Job] [PriorityPoint Task]
    (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
    ∀ sched : schedule (processor_state Job),
      @valid_schedule Job _ _ (processor_state Job) sched _ basic_ready_instance arr_seq →
      @respects_JLFP_policy_at_preemption_point Job _ _ _ (processor_state Job) _ basic_ready_instance arr_seq sched
        (GEL Job Task) →
      arrivals_have_valid_job_costs (Task := Task) arr_seq →
    ∀ ts : List Task, all_jobs_from_taskset arr_seq ts → valid_taskset_arrival_curve ts max_arrivals →
      taskset_respects_max_arrivals arr_seq ts →
    ∀ tsk : Task, decide (tsk ∈ ts) = true →
      valid_preemption_model arr_seq sched →
      valid_task_run_to_completion_threshold arr_seq tsk →
    ∀ priority_inversion_bound : duration → duration,
      @priority_inversion_is_bounded_by Task _ Job _ _ _ _ (processor_state Job) arr_seq sched (GEL Job Task) tsk
        priority_inversion_bound →
      @Prosa.Model.Schedule.WorkConserving.work_conserving Job _ _ _ (processor_state Job) basic_ready_instance
        arr_seq sched →
    ∀ L : duration, 0 < L → L = total_request_bound_function ts L →
    ∀ R : duration,
      (∀ A : duration, is_in_search_space ts tsk priority_inversion_bound L A = true →
        ∃ F : duration,
          priority_inversion_bound A + (task_request_bound_function tsk (A + 1) - (task_cost tsk - task_rtct tsk)) +
              sumFiltered ts (fun tsk_o => decide (tsk_o ≠ tsk))
                (fun tsk_o => task_request_bound_function tsk_o
                  (min (Int.natAbs (max 0 (((A + 1 : Nat) : Int) + task_priority_point tsk -
                    task_priority_point tsk_o))) (A + F))) ≤ A + F ∧
            F + (task_cost tsk - task_rtct tsk) ≤ R) →
      task_response_time_bound arr_seq sched tsk R := by
  intro hva sched hvs hrespG hvjc ts hall hvalid hresp tsk hin hvpm hrtct pib hpib hwc L hL hfix R hR js harrs htsks
  rcases Nat.eq_zero_or_pos (job_cost js) with h0 | hjpos
  · unfold job_response_time_bound completed_by
    apply decide_eq_true; rw [h0]; exact Nat.zero_le _
  let _ : JobReady Job (processor_state Job) := basic_ready_instance
  let _ : JLFP_policy Job := GEL Job Task
  have hfrom := hvs.1
  have hmust := jobs_must_arrive_to_be_ready sched hvs.2
  have hcde := completed_jobs_are_not_ready sched hvs.2
  have hreflJ : reflexive_job_priorities (GEL Job Task) := GEL_is_reflexive
  have htsk : job_task (Task := Task) js = tsk := of_decide_eq_true htsks
  have hma := non_pathological_max_arrivals tsk arr_seq (hresp tsk hin) js htsks harrs
  have hcpos : 0 < task_cost tsk := by
    have hv := hvjc js harrs
    unfold valid_job_cost at hv
    rw [htsk] at hv
    exact Nat.lt_of_lt_of_le hjpos (of_decide_eq_true hv)
  have hwbr := basic_readiness_is_work_bearing_readiness arr_seq sched hreflJ
  let _ := ideal_jlfp_interference arr_seq sched
  let _ := ideal_jlfp_interfering_workload arr_seq sched
  have hwcA := instantiated_i_and_w_are_coherent_with_schedule arr_seq hva sched hfrom hmust hcde hreflJ hwbr hwc
    hreflJ
  have hseq := GEL_implies_sequential_tasks arr_seq hva (processor_state Job)
    (ideal_proc_model_is_a_uniprocessor_model Job) sched hwbr hvs hvpm hrespG
  have hcons := instantiated_interference_and_workload_consistent_with_sequential_tasks arr_seq hva sched hfrom hmust
    hcde hreflJ tsk GEL_respects_sequential_tasks
  have hbounded := Prosa.Analysis.Abstract.Ideal.IwInstantiation.instantiated_busy_intervals_are_bounded arr_seq hva
    sched hfrom hmust hcde hreflJ tsk hwbr hwc ts hresp hall L hL hfix hvjc
  have hibf := instantiated_task_interference_is_bounded arr_seq hva sched hvs hvjc ts hall hresp tsk hin pib hpib L
    hL hfix
  exact uniprocessor_response_time_bound_seq (ideal_proc_model_is_a_uniprocessor_model Job)
    (ideal_proc_model_provides_unit_service Job) (ideal_proc_model_ensures_ideal_progress Job) arr_seq hva sched
    hfrom hmust hcde hvjc ts tsk hin hvpm hrtct hvalid hresp hwcA hseq hcons L hbounded _ hibf R
    (fun A hA => correct_search_space ts hvalid tsk hin pib L hL R hR hcpos hma A hA) js harrs htsks

end Prosa.Results.Rta.Ideal.Gel.BoundedPi
