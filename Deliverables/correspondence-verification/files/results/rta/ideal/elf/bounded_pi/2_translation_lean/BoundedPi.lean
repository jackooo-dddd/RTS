-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: results/rta/ideal/elf/bounded_pi.v

import Prosa.Analysis.Abstract.Ideal.CumulativeBounds
import Prosa.Analysis.Facts.Priority.Elf
import Prosa.Analysis.Facts.Interference
import Prosa.Analysis.Facts.Readiness.Basic
import Prosa.Analysis.Facts.Priority.JlfpWithFp
import Prosa.Analysis.Facts.Model.Rbf
import Prosa.Analysis.Facts.BusyInterval.Pi
import Prosa.Analysis.Facts.BusyInterval.PiCond
import Prosa.Analysis.Facts.BusyInterval.Existence
import Prosa.Analysis.Abstract.Ideal.AbstractSeqRta
import Prosa.Analysis.Facts.Model.TaskCost
import Prosa.Analysis.Facts.Workload.ElfAthepBound

namespace Prosa.Results.Rta.Ideal.Elf.BoundedPi

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
open Prosa.Model.Priority.Elf
open Prosa.Model.Processor.Ideal
open Prosa.Model.Readiness.Basic
open Prosa.Model.Schedule.PriorityDriven
open Prosa.Model.Schedule.Scheduled
open Prosa.Model.Aggregate.Workload
open Prosa.Model.Aggregate.ServiceOfJobs
open Prosa.Util.Sum
open Prosa.Util.Notation
open Prosa.Analysis.Definitions.Schedulability
open Prosa.Analysis.Definitions.RequestBoundFunction
open Prosa.Analysis.Definitions.PriorityInversion
open Prosa.Analysis.Definitions.Interference
open Prosa.Analysis.Definitions.WorkBearingReadiness
open Prosa.Analysis.Facts.Model.Rbf
open Prosa.Analysis.Facts.Model.Workload
open Prosa.Analysis.Facts.Model.ArrivalCurves
open Prosa.Analysis.Facts.Model.ServiceOfJobs
open Prosa.Analysis.Facts.Model.Scheduled
open Prosa.Analysis.Facts.Model.Ideal.Schedule
open Prosa.Analysis.Facts.Priority.Classes
open Prosa.Analysis.Facts.Priority.Elf
open Prosa.Analysis.Facts.Priority.JlfpWithFp
open Prosa.Analysis.Facts.Readiness.Basic
open Prosa.Analysis.Facts.Interference
open Prosa.Analysis.Facts.Behavior.Arrivals
open Prosa.Analysis.Facts.Behavior.Completion
open Prosa.Analysis.Facts.BusyInterval.Pi
open Prosa.Analysis.Facts.BusyInterval.PiCond
open Prosa.Analysis.Facts.BusyInterval.Existence
open Prosa.Analysis.Abstract.Definitions
open Prosa.Analysis.Abstract.IBF.Task
open Prosa.Analysis.Abstract.Ideal.IwInstantiation
open Prosa.Analysis.Abstract.Ideal.CumulativeBounds
open Prosa.Analysis.Abstract.Ideal.AbstractSeqRta

/-! Abstract RTA for ELF schedulers with bounded priority inversion on ideal uniprocessors.

Binders follow the elaborated source types: every declaration takes only the section inputs and hypotheses it uses,
in their elaborated order. The section's readiness (the accepted `basic_ready_instance`) and the ELF policy (the
accepted reducible `ELF FP`) are passed explicitly where the elaborated statements use them implicitly; the
section-local instances `ideal_elf_interference` / `ideal_elf_interfering_workload` re-expose the accepted
instantiation of `iw_instantiation` at the section's arrival sequence and schedule and the ELF policy. The
section-local `is_lower_priority`, `is_equal_priority`, `blocking_relevant`, `is_ep_causing_intf`,
`ep_task_blocking_relevant`, `total_hep_rbf`, `hep_jobs_from`, `A`, `total_interference_bound` and the source's
`let any_task_bound_changes` are inlined; the definitions take the section inputs they depend on. Representation:
`ε` is `1`; a Boolean in `Prop` position is `= true`; `a != b`, `a == b` and `a < b` in `bool` position are
`decide (…)`; `~~ b` is `!b`; `[&& a, b & c]` is `a && (b && c)`; `x \in xs` is `decide (x ∈ xs) = true`; `uniq xs`
is `xs.Nodup`; `has P xs` is `xs.any P`; `\sum_(x <- xs | P x) F x` and `\max_(x <- xs | P x) F x` are the accepted
`sumFiltered xs P F` and `maxFiltered xs P F`; `maxn` is `Nat.max`; `minn` is `min`; `[eta f]` is `f`; as in the
accepted `model/priority/gel.v` and `analysis/definitions/workload/elf_athep_bound.v`, `n%:R` on `int` is the cast
`(n : Int)`, `(x <= y)%R` on `int` is `decide (x ≤ y)`, `Num.max 0 x` is `max 0 x` and `` `|x| `` is `Int.natAbs`;
`search_space.is_in_search_space` is the accepted abstract search-space predicate. -/

/-- `omega` after unfolding the time aliases. -/
macro "omega'" : tactic => `(tactic| (try dsimp only [instant, duration, work] at *) <;> omega)

variable {Task : TaskType} [DecidableEq Task] {Job : JobType} [DecidableEq Job]

private theorem sf_cons {I : Type _} (a : I) (l : List I) (P : I → Bool) (F : I → Nat) :
    sumFiltered (a :: l) P F = (if P a = true then F a else 0) + sumFiltered l P F := by
  unfold sumFiltered
  cases h : P a <;> simp [h]

private theorem sf_split {I : Type _} (l : List I) (P Q : I → Bool) (F : I → Nat) :
    sumFiltered l P F = sumFiltered l (fun x => P x && Q x) F + sumFiltered l (fun x => P x && !Q x) F := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [sf_cons, sf_cons, sf_cons, ih]
    cases hp : P a <;> cases hq : Q a <;> simp <;> omega

private theorem sf_mono {I : Type _} (l : List I) (P Q : I → Bool) (F : I → Nat)
    (h : ∀ x, P x = true → Q x = true) : sumFiltered l P F ≤ sumFiltered l Q F := by
  induction l with
  | nil => exact Nat.le_refl _
  | cons a l ih =>
    rw [sf_cons, sf_cons]
    cases hp : P a
    · simp only [Bool.false_eq_true, if_false]; omega
    · simp only [if_true, h a hp]; omega

private theorem sumSeq_range'_eq_ico (a b : Nat) (f : Nat → Nat) :
    sumSeq (List.range' a (b - a)) f = ∑ t ∈ (Finset.Ico a b : Finset Nat), f t := by
  unfold sumSeq
  rw [Finset.sum_Ico_eq_sum_range]
  have : ∀ n a, ((List.range' a n).map f).sum = ∑ k ∈ Finset.range n, f (a + k) := by
    intro n
    induction n with
    | zero => intro a; simp
    | succ n ih =>
      intro a
      rw [List.range'_succ, List.map_cons, List.sum_cons, ih (a + 1), Finset.sum_range_succ']
      simp only [Nat.add_zero]
      rw [Nat.add_comm]
      congr 1
      apply Finset.sum_congr rfl
      intro k _
      rw [Nat.add_assoc, Nat.add_comm 1 k]
  exact this (b - a) a

/-- The bound on the priority inversion: the larger of the bounds for lower- and equal-priority tasks. -/
def priority_inversion_bound (priority_inversion_lp_tasks_bound : duration)
    (priority_inversion_ep_tasks_bound : duration → duration) (A : duration) : Nat :=
  Nat.max priority_inversion_lp_tasks_bound (priority_inversion_ep_tasks_bound A)

/-- The priority inversion of any job of `tsk` is bounded by `priority_inversion_bound`. -/
theorem priority_inversion_is_bounded [PriorityPoint Task] [JobTask Job Task] [JobArrival Job] [JobCost Job]
    [JobPreemptable Job] (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
    ∀ (tsk : Task) (sched : schedule (processor_state Job)),
      @valid_schedule Job _ _ (processor_state Job) sched _ basic_ready_instance arr_seq →
    ∀ FP : FP_policy Task, reflexive_task_priorities FP → transitive_task_priorities FP →
      total_task_priorities FP → valid_preemption_model arr_seq sched →
      @respects_JLFP_policy_at_preemption_point Job _ _ _ (processor_state Job) _ basic_ready_instance arr_seq sched
        (ELF (Job := Job) FP) →
    ∀ priority_inversion_lp_tasks_bound : duration,
      @priority_inversion_cond_is_bounded_by Task _ Job _ _ _ _ (processor_state Job) arr_seq sched
        (ELF (Job := Job) FP) tsk (fun j' => hp_task (FP := FP) tsk (job_task (Task := Task) j'))
        (constant priority_inversion_lp_tasks_bound) →
    ∀ priority_inversion_ep_tasks_bound : duration → duration,
      @priority_inversion_cond_is_bounded_by Task _ Job _ _ _ _ (processor_state Job) arr_seq sched
        (ELF (Job := Job) FP) tsk (fun j' => ep_task (FP := FP) tsk (job_task (Task := Task) j'))
        priority_inversion_ep_tasks_bound →
      @priority_inversion_is_bounded_by Task _ Job _ _ _ _ (processor_state Job) arr_seq sched
        (ELF (Job := Job) FP) tsk
        (priority_inversion_bound priority_inversion_lp_tasks_bound priority_inversion_ep_tasks_bound) := by
  intro hva tsk sched hvs FP hrefl htrans htot hvpm hresp lp hlp ep hep j hj htsk hpos t1 t2 hpref
  let _ : JobReady Job (processor_state Job) := basic_ready_instance
  let _ : JLFP_policy Job := ELF (Job := Job) FP
  have hreflJ := ELF_is_reflexive (Job := Job) FP hrefl
  have htransJ := ELF_is_transitive (Job := Job) FP htrans
  have hwbr := basic_readiness_is_work_bearing_readiness arr_seq sched hreflJ
  have hcp : job_cost_positive j = true := by unfold job_cost_positive; exact decide_eq_true hpos
  have htskj : job_task (Task := Task) j = tsk := of_decide_eq_true htsk
  have htot' : ∀ x y : Task, (FP.hep_task x y || FP.hep_task y x) = true := htot
  rcases busy_interval_pi_cases arr_seq hva (ideal_proc_model_is_a_uniprocessor_model Job) sched
      (ELF (Job := Job) FP) hreflJ htransJ hvpm hwbr hvs hresp j hj hcp t1 t2 hpref with h0 | hpi
  · show cumulative_priority_inversion arr_seq sched j t1 t2 ≤ _
    rw [h0]; exact Nat.zero_le _
  · unfold priority_inversion at hpi
    simp only [Bool.and_eq_true, List.any_eq_true, Bool.not_eq_true'] at hpi
    obtain ⟨_, jlp, hjlp, hnhep⟩ := hpi
    have hsched : scheduled_at sched jlp t1 = true := by
      rw [← scheduled_jobs_at_iff arr_seq hva sched hvs.1 (jobs_must_arrive_to_be_ready sched hvs.2) jlp t1]
      exact decide_eq_true hjlp
    have hnhp : hp_task (FP := FP) (job_task (Task := Task) jlp) (job_task (Task := Task) j) = false := by
      have h : (hp_task (FP := FP) (job_task (Task := Task) jlp) (job_task (Task := Task) j) ||
          (FP.hep_task (job_task (Task := Task) jlp) (job_task (Task := Task) j) &&
            (GEL Job Task).hep_job jlp j)) = false := hnhep
      simp only [Bool.or_eq_false_iff] at h
      exact h.1
    have hcase := nhp_ep_nhep_task FP htot' (job_task (Task := Task) jlp) (job_task (Task := Task) j)
    rw [hnhp] at hcase
    simp only [Bool.not_false, Bool.true_eq, Bool.or_eq_true, Bool.not_eq_true'] at hcase
    unfold priority_inversion_bound
    rcases hcase with hlp' | hep'
    · have hP : hp_task (FP := FP) tsk (job_task (Task := Task) jlp) = true := by
        rw [← htskj, ← not_hep_hp_task FP htot', hlp']; rfl
      rw [cum_task_pi_eq arr_seq hva (ideal_proc_model_is_a_uniprocessor_model Job) sched (ELF (Job := Job) FP)
        hreflJ htransJ hvpm hwbr hvs hresp j hj hcp t1 t2 hpref jlp
        (fun j' => hp_task (FP := FP) tsk (job_task (Task := Task) j')) hsched hP]
      exact Nat.le_trans (hlp j hj htsk hpos t1 t2 hpref) (Nat.le_max_left _ _)
    · have hP : ep_task (FP := FP) tsk (job_task (Task := Task) jlp) = true := by
        rw [← htskj, ep_task_sym]; exact hep'
      rw [cum_task_pi_eq arr_seq hva (ideal_proc_model_is_a_uniprocessor_model Job) sched (ELF (Job := Job) FP)
        hreflJ htransJ hvpm hwbr hvs hresp j hj hcp t1 t2 hpref jlp
        (fun j' => ep_task (FP := FP) tsk (job_task (Task := Task) j')) hsched hP]
      exact Nat.le_trans (hep j hj htsk hpos t1 t2 hpref) (Nat.le_max_right _ _)

/-- A positive fixed point of the busy-window recurrence bounds every (abstract) busy interval. -/
theorem instantiated_busy_intervals_are_bounded [TaskCost Task] [MaxArrivals Task] [PriorityPoint Task]
    [JobTask Job Task] [JobArrival Job] [JobCost Job] [JobPreemptable Job] (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq → arrivals_have_valid_job_costs (Task := Task) arr_seq →
    ∀ ts : List Task, ts.Nodup → all_jobs_from_taskset arr_seq ts → taskset_respects_max_arrivals arr_seq ts →
      valid_taskset_arrival_curve ts max_arrivals →
    ∀ tsk : Task, decide (tsk ∈ ts) = true →
    ∀ sched : schedule (processor_state Job),
      @valid_schedule Job _ _ (processor_state Job) sched _ basic_ready_instance arr_seq →
    ∀ FP : FP_policy Task, reflexive_task_priorities FP → transitive_task_priorities FP →
      total_task_priorities FP → valid_preemption_model arr_seq sched →
      @respects_JLFP_policy_at_preemption_point Job _ _ _ (processor_state Job) _ basic_ready_instance arr_seq sched
        (ELF (Job := Job) FP) →
      @Prosa.Model.Schedule.WorkConserving.work_conserving Job _ _ _ (processor_state Job) basic_ready_instance
        arr_seq sched →
    ∀ priority_inversion_lp_tasks_bound : duration,
      @priority_inversion_cond_is_bounded_by Task _ Job _ _ _ _ (processor_state Job) arr_seq sched
        (ELF (Job := Job) FP) tsk (fun j' => hp_task (FP := FP) tsk (job_task (Task := Task) j'))
        (constant priority_inversion_lp_tasks_bound) →
    ∀ priority_inversion_ep_tasks_bound : duration → duration,
      @priority_inversion_cond_is_bounded_by Task _ Job _ _ _ _ (processor_state Job) arr_seq sched
        (ELF (Job := Job) FP) tsk (fun j' => ep_task (FP := FP) tsk (job_task (Task := Task) j'))
        priority_inversion_ep_tasks_bound →
      (∀ (j : Job) (t1 : Nat), job_task (Task := Task) j = tsk →
        priority_inversion_ep_tasks_bound (job_arrival j - t1) ≤
          maxFiltered ts
            (fun i => (ep_task (FP := FP) i tsk &&
                !decide (0 ≤ (job_arrival j : Int) - (t1 : Int) + task_priority_point tsk - task_priority_point i)) &&
              (decide (0 < max_arrivals i 1) && decide (0 < task_cost i)))
            (fun i => task_cost i)) →
    ∀ L : duration, 0 < L →
      L = priority_inversion_lp_tasks_bound + total_hep_request_bound_function_FP ts (FP := FP) tsk L →
      @busy_intervals_are_bounded_by Job _ (@ideal_jlfp_interference Job _ arr_seq sched (ELF (Job := Job) FP))
        (@ideal_jlfp_interfering_workload Job _ _ arr_seq sched (ELF (Job := Job) FP)) _ _ (processor_state Job)
        arr_seq sched Task _ _ tsk L := by
  intro hva hvjc ts _ hall hresp hvalid tsk _ sched hvs FP hrefl htrans htot hvpm hrespE hwc lp hlp ep hep hepc
    L hL hfix j hj htsk hpos
  let _ : JobReady Job (processor_state Job) := basic_ready_instance
  let _ : JLFP_policy Job := ELF (Job := Job) FP
  have hfrom := hvs.1
  have hmust := jobs_must_arrive_to_be_ready sched hvs.2
  have hcde := completed_jobs_are_not_ready sched hvs.2
  have hreflJ := ELF_is_reflexive (Job := Job) FP hrefl
  have hwbr := basic_readiness_is_work_bearing_readiness arr_seq sched hreflJ
  have hcp : job_cost_positive j = true := by unfold job_cost_positive; exact decide_eq_true hpos
  have htskj : job_task (Task := Task) j = tsk := of_decide_eq_true htsk
  have hcompat := ELF_is_JLFP_FP_compatible (Job := Job) FP
  have hpib := priority_inversion_is_bounded arr_seq hva tsk sched hvs FP hrefl htrans htot hvpm hrespE lp hlp ep hep
  have hW : ∀ t : Nat, priority_inversion_bound lp ep (job_arrival j - t) +
      workload_of_hep_jobs arr_seq j t (t + L) ≤ L := by
    intro t
    -- the hep workload splits into the strictly higher-priority and the equal-priority tasks
    have hsplitW := hep_workload_partitioning_taskwise (Task := Task) (FP := FP) (JLFP := ELF (Job := Job) FP)
      hcompat arr_seq j t (t + L)
    have hhpW := hep_hp_workload_hp (Task := Task) (FP := FP) (JLFP := ELF (Job := Job) FP) hcompat arr_seq j t
      (t + L)
    have hsplitR := hep_rbf_taskwise_partitioning FP ts tsk L
    let C : Task → Bool := fun i =>
      decide (0 ≤ (job_arrival j : Int) - (t : Int) + task_priority_point tsk - task_priority_point i)
    have hsplitE := sf_split ts (fun o => ep_task (FP := FP) o tsk) C (fun o => task_request_bound_function o L)
    -- strictly higher-priority tasks
    have hhp : workload_of_jobs (from_hp_task (Task := Task) (FP := FP) j) (arrivals_between arr_seq t (t + L)) ≤
        total_hp_request_bound_function_FP ts (FP := FP) tsk L :=
      workload_of_jobs_bounded arr_seq hvjc ts hall hresp _ (fun o => hp_task (FP := FP) o tsk)
        (by intro jo h; unfold from_hp_task at h; rw [htskj] at h; exact h) t L
    -- equal-priority tasks whose jobs can have higher-or-equal priority
    have hepW : workload_of_jobs (hep_from_ep_task (Task := Task) (FP := FP) (JLFP := ELF (Job := Job) FP) j)
        (arrivals_between arr_seq t (t + L)) ≤
        sumFiltered ts (fun o => ep_task (FP := FP) o tsk && C o) (fun o => task_request_bound_function o L) := by
      rw [workload_of_jobs_equiv_pred _ _
        (fun jo => hep_from_ep_task (Task := Task) (FP := FP) (JLFP := ELF (Job := Job) FP) j jo &&
          decide (t ≤ job_arrival jo))
        (fun jo hjo => by
          have := job_arrival_between_ge arr_seq hva.1 jo t (t + L) hjo
          simp [this])]
      refine workload_of_jobs_bounded arr_seq hvjc ts hall hresp _ _ ?_ t L
      intro jo h
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨h1, h2⟩ := h
      unfold hep_from_ep_task at h1
      simp only [Bool.and_eq_true] at h1
      obtain ⟨hh, hepo⟩ := h1
      rw [htskj] at hepo
      have hgel := hep_job_elf_gel (Job := Job) FP jo j (by rw [htskj]; exact hepo)
      have hh' : (GEL Job Task).hep_job jo j = true := by rw [← hgel]; exact hh
      have hpp : job_priority_point (Task := Task) jo ≤ job_priority_point (Task := Task) j :=
        of_decide_eq_true hh'
      unfold job_priority_point at hpp
      rw [htskj] at hpp
      simp only [Bool.and_eq_true, decide_eq_true_eq, C]
      refine ⟨hepo, ?_⟩
      omega'
    -- equal-priority tasks that can only block
    have hblk : ep (job_arrival j - t) ≤
        sumFiltered ts (fun o => ep_task (FP := FP) o tsk && !C o) (fun o => task_request_bound_function o L) := by
      refine Nat.le_trans (hepc j t htskj) (Nat.le_trans (bigmax_leq_sum _ _ _) ?_)
      refine Nat.le_trans (leq_sum_seq ts _ (fun i => task_cost i) (fun o => task_request_bound_function o L) ?_)
        (sf_mono ts _ _ _ ?_)
      · intro i hi hP
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hP
        obtain ⟨_, hma, hc⟩ := hP
        have hv := (hvalid i (decide_eq_true hi)).2
        have hmono : max_arrivals i 1 ≤ max_arrivals i L := of_decide_eq_true (hv 1 L (decide_eq_true hL))
        unfold task_request_bound_function
        calc task_cost i = task_cost i * 1 := (Nat.mul_one _).symm
          _ ≤ task_cost i * max_arrivals i L := Nat.mul_le_mul_left _ (by omega')
      · intro i hP
        simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq] at hP ⊢
        simp only [C, decide_eq_false_iff_not]
        exact hP.1
    unfold priority_inversion_bound
    have hmax : Nat.max lp (ep (job_arrival j - t)) ≤ lp + ep (job_arrival j - t) := by
      simp only [Nat.max_def]; split <;> omega'
    have : workload_of_hep_jobs arr_seq j t (t + L) + ep (job_arrival j - t) ≤
        total_hep_request_bound_function_FP ts (FP := FP) tsk L := by
      rw [hsplitW, hhpW, hsplitR]
      unfold total_ep_request_bound_function_FP
      rw [hsplitE]
      omega'
    omega'
  obtain ⟨t1, t2, hin', hle, hbi⟩ := exists_busy_interval arr_seq hva sched hfrom hmust hcde (ELF (Job := Job) FP)
    hwbr tsk j hj htsk hcp hwc hva.2 hreflJ (ideal_proc_model_is_a_uniprocessor_model Job)
    (ideal_proc_model_provides_unit_service Job) (ideal_proc_model_ensures_ideal_progress Job)
    (priority_inversion_bound lp ep) (hpib j hj htsk hpos) L hL
    hW hpos
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hin'
  exact ⟨t1, t2, hin', hle, (instantiated_busy_interval_equivalent_busy_interval arr_seq hva sched hfrom hmust hcde
    hreflJ j hj hcp t1 t2).mp hbi⟩

/-- The RBF of the strictly higher-priority tasks. -/
def total_hp_rbf [TaskCost Task] [MaxArrivals Task] (ts : List Task) (tsk : Task) (FP : FP_policy Task) :
    duration → Nat :=
  total_hp_request_bound_function_FP ts (FP := FP) tsk

/-- The end point of the interval in which interfering jobs of the equal-priority task `tsk_o` must arrive. -/
def ep_task_intf_interval [PriorityPoint Task] (tsk tsk_o : Task) (A : instant) : Int :=
  ((A + 1 : Nat) : Int) + task_priority_point tsk - task_priority_point tsk_o

/-- The bound on the total workload of the other equal-priority tasks. -/
def bound_on_total_ep_workload [TaskCost Task] [MaxArrivals Task] [PriorityPoint Task] (ts : List Task) (tsk : Task)
    (FP : FP_policy Task) (A Δ : duration) : Nat :=
  sumFiltered ts (fun tsk_o => ep_task (FP := FP) tsk tsk_o && decide (tsk_o ≠ tsk))
    (fun tsk_o => task_request_bound_function tsk_o
      (min (Int.natAbs (max 0 (ep_task_intf_interval tsk tsk_o A))) Δ))

/-- The interference bound function for jobs of other tasks. -/
def task_IBF [TaskCost Task] [MaxArrivals Task] [PriorityPoint Task] (ts : List Task) (tsk : Task)
    (FP : FP_policy Task) (priority_inversion_lp_tasks_bound : duration)
    (priority_inversion_ep_tasks_bound : duration → duration) (A Δ : duration) : Nat :=
  priority_inversion_bound priority_inversion_lp_tasks_bound priority_inversion_ep_tasks_bound A +
    bound_on_total_ep_workload ts tsk FP A Δ + total_hp_rbf ts tsk FP Δ

/-- The service of the higher-or-equal-priority jobs of the other equal-priority tasks. -/
noncomputable def service_of_hp_jobs_from_other_ep_tasks [PriorityPoint Task] [JobTask Job Task] [JobArrival Job]
    (arr_seq : arrival_sequence Job) (sched : schedule (processor_state Job)) (FP : FP_policy Task) (j : Job)
    (t1 t2 : instant) : Nat :=
  service_of_jobs sched
    (fun jhp => @other_ep_task_hep_job Task _ Job _ _ FP (ELF (Job := Job) FP) jhp j)
    (arrivals_between arr_seq t1 t2) t1 t2

/-- The cumulative interference from the other equal-priority tasks is their service. -/
theorem cumulative_intf_ep_task_service_equiv [PriorityPoint Task] [JobTask Job Task] [JobArrival Job]
    [JobCost Job] (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
    ∀ sched : schedule (processor_state Job),
      @valid_schedule Job _ _ (processor_state Job) sched _ basic_ready_instance arr_seq →
    ∀ FP : FP_policy Task, reflexive_task_priorities FP →
    ∀ j : Job, job_cost_positive j = true → arrives_in arr_seq j →
    ∀ t1 t2 : instant,
      @Prosa.Analysis.Abstract.Definitions.busy_interval Job _
        (@ideal_jlfp_interference Job _ arr_seq sched (ELF (Job := Job) FP))
        (@ideal_jlfp_interfering_workload Job _ _ arr_seq sched (ELF (Job := Job) FP)) _ _ (processor_state Job)
        sched j t1 t2 →
    ∀ Δ : duration,
      @cumulative_interference_from_hep_jobs_from_other_ep_tasks Task _ Job _ _ (processor_state Job) arr_seq sched
          FP (ELF (Job := Job) FP) j t1 (t1 + Δ) =
        service_of_hp_jobs_from_other_ep_tasks arr_seq sched FP j t1 (t1 + Δ) := by
  intro hva sched hvs FP hrefl j hcp hj t1 t2 hbi Δ
  let _ : JobReady Job (processor_state Job) := basic_ready_instance
  let _ : JLFP_policy Job := ELF (Job := Job) FP
  have hfrom := hvs.1
  have hmust := jobs_must_arrive_to_be_ready sched hvs.2
  have hcde := completed_jobs_are_not_ready sched hvs.2
  have hreflJ := ELF_is_reflexive (Job := Job) FP hrefl
  have hcl := (instantiated_busy_interval_equivalent_busy_interval arr_seq hva sched hfrom hmust hcde hreflJ j hj hcp
    t1 t2).mpr hbi
  unfold cumulative_interference_from_hep_jobs_from_other_ep_tasks service_of_hp_jobs_from_other_ep_tasks
    hep_job_from_other_ep_task_interference
  rw [sumSeq_range'_eq_ico]
  exact cumulative_pred_served_eq_service (ideal_proc_model_provides_unit_service Job)
    (ideal_proc_model_is_a_uniprocessor_model Job) arr_seq hva.1 sched hmust hcde _ hva.2 (ELF (Job := Job) FP) j t1
    (t1 + Δ) hcl.1.2.1
    (fun j' h => by
      unfold other_ep_task_hep_job ep_task_hep_job at h
      simp only [Bool.and_eq_true] at h
      exact h.1.1)

/-- The service of the higher-or-equal-priority jobs of the strictly higher-priority tasks. -/
noncomputable def service_of_hp_jobs_from_other_hp_tasks [PriorityPoint Task] [JobTask Job Task] [JobArrival Job]
    (arr_seq : arrival_sequence Job) (sched : schedule (processor_state Job)) (FP : FP_policy Task) (j : Job)
    (t1 t2 : instant) : Nat :=
  service_of_jobs sched
    (fun jhp => @hp_task_hep_job Task _ Job _ _ FP (ELF (Job := Job) FP) jhp j)
    (arrivals_between arr_seq t1 t2) t1 t2

/-- The cumulative interference from the strictly higher-priority tasks is their service. -/
theorem cumulative_intf_hp_task_service_equiv [PriorityPoint Task] [JobTask Job Task] [JobArrival Job]
    [JobCost Job] (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
    ∀ sched : schedule (processor_state Job),
      @valid_schedule Job _ _ (processor_state Job) sched _ basic_ready_instance arr_seq →
    ∀ FP : FP_policy Task, reflexive_task_priorities FP →
    ∀ j : Job, job_cost_positive j = true → arrives_in arr_seq j →
    ∀ t1 t2 : instant,
      @Prosa.Analysis.Abstract.Definitions.busy_interval Job _
        (@ideal_jlfp_interference Job _ arr_seq sched (ELF (Job := Job) FP))
        (@ideal_jlfp_interfering_workload Job _ _ arr_seq sched (ELF (Job := Job) FP)) _ _ (processor_state Job)
        sched j t1 t2 →
    ∀ Δ : duration,
      @cumulative_interference_from_hep_jobs_from_hp_tasks Task _ Job _ _ (processor_state Job) arr_seq sched
          FP (ELF (Job := Job) FP) j t1 (t1 + Δ) =
        service_of_hp_jobs_from_other_hp_tasks arr_seq sched FP j t1 (t1 + Δ) := by
  intro hva sched hvs FP hrefl j hcp hj t1 t2 hbi Δ
  let _ : JobReady Job (processor_state Job) := basic_ready_instance
  let _ : JLFP_policy Job := ELF (Job := Job) FP
  have hfrom := hvs.1
  have hmust := jobs_must_arrive_to_be_ready sched hvs.2
  have hcde := completed_jobs_are_not_ready sched hvs.2
  have hreflJ := ELF_is_reflexive (Job := Job) FP hrefl
  have hcl := (instantiated_busy_interval_equivalent_busy_interval arr_seq hva sched hfrom hmust hcde hreflJ j hj hcp
    t1 t2).mpr hbi
  unfold cumulative_interference_from_hep_jobs_from_hp_tasks service_of_hp_jobs_from_other_hp_tasks
    hep_job_from_hp_task_interference
  rw [sumSeq_range'_eq_ico]
  exact cumulative_pred_served_eq_service (ideal_proc_model_provides_unit_service Job)
    (ideal_proc_model_is_a_uniprocessor_model Job) arr_seq hva.1 sched hmust hcde _ hva.2 (ELF (Job := Job) FP) j t1
    (t1 + Δ) hcl.1.2.1
    (fun j' h => by
      unfold hp_task_hep_job at h
      simp only [Bool.and_eq_true] at h
      exact h.1)

/-- If `Δ` exceeds the interval in which the equal-priority task `tsk_o` can interfere, the higher-or-equal-priority
workload of `tsk_o` in `[t1, t1 + Δ)` is the one before the end of that interval. -/
theorem total_workload_shorten_range [PriorityPoint Task] [JobTask Job Task] [JobArrival Job] [JobCost Job]
    (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
    ∀ (tsk : Task) (FP : FP_policy Task) (j : Job), job_of_task tsk j = true →
    ∀ (t1 : instant) (Δ : duration) (tsk_o : Task),
      decide (ep_task_intf_interval tsk tsk_o (job_arrival j - t1) ≤ (Δ : Int)) = true →
      workload_of_jobs
          (fun x => @hep_job Job _ (ELF (Job := Job) FP) x j &&
            ep_task (FP := FP) (job_task (Task := Task) x) (job_task (Task := Task) j) &&
            decide (job_task (Task := Task) x = tsk_o))
          (arrivals_between arr_seq t1 (t1 + Δ)) ≤
        workload_of_jobs
          (fun x => @hep_job Job _ (ELF (Job := Job) FP) x j &&
            ep_task (FP := FP) (job_task (Task := Task) x) (job_task (Task := Task) j) &&
            decide (job_task (Task := Task) x = tsk_o))
          (arrivals_between arr_seq t1
            (Int.natAbs (max 0 ((t1 : Int) + ep_task_intf_interval tsk tsk_o (job_arrival j - t1))))) := by
  intro hvalid tsk FP j htsk t1 Δ tsk_o hle
  have hj : job_task (Task := Task) j = tsk := of_decide_eq_true htsk
  have hle' := of_decide_eq_true hle
  unfold ep_task_intf_interval at hle' ⊢
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
    cases hep : ep_task (FP := FP) (job_task (Task := Task) j') (job_task (Task := Task) j) with
    | false => simp
    | true =>
      simp only [Bool.and_true]
      rw [hep_job_elf_gel (Job := Job) FP j' j hep]
      show decide (job_priority_point (Task := Task) j' ≤ job_priority_point (Task := Task) j) = false
      unfold job_priority_point
      rw [hto', hj]
      apply decide_eq_false
      omega'

/-- The interference from the other equal-priority tasks is bounded by `bound_on_total_ep_workload`. -/
theorem bound_on_ep_workload [TaskCost Task] [MaxArrivals Task] [PriorityPoint Task] [JobTask Job Task]
    [JobArrival Job] [JobCost Job] (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq → arrivals_have_valid_job_costs (Task := Task) arr_seq →
    ∀ ts : List Task, ts.Nodup → all_jobs_from_taskset arr_seq ts → taskset_respects_max_arrivals arr_seq ts →
    ∀ (tsk : Task) (sched : schedule (processor_state Job)),
      @valid_schedule Job _ _ (processor_state Job) sched _ basic_ready_instance arr_seq →
    ∀ FP : FP_policy Task, reflexive_task_priorities FP →
    ∀ j : Job, job_of_task tsk j = true → job_cost_positive j = true → arrives_in arr_seq j →
    ∀ t1 t2 : instant,
      @Prosa.Analysis.Abstract.Definitions.busy_interval Job _
        (@ideal_jlfp_interference Job _ arr_seq sched (ELF (Job := Job) FP))
        (@ideal_jlfp_interfering_workload Job _ _ arr_seq sched (ELF (Job := Job) FP)) _ _ (processor_state Job)
        sched j t1 t2 →
    ∀ Δ : duration, t1 + Δ ≤ t2 →
      @cumulative_interference_from_hep_jobs_from_other_ep_tasks Task _ Job _ _ (processor_state Job) arr_seq sched
          FP (ELF (Job := Job) FP) j t1 (t1 + Δ) ≤
        bound_on_total_ep_workload ts tsk FP (job_arrival j - t1) Δ := by
  intro hva hvjc ts huniq hall hresp tsk sched hvs FP hrefl j htsk hcp hj t1 t2 hbi Δ _
  let _ : JobReady Job (processor_state Job) := basic_ready_instance
  let _ : JLFP_policy Job := ELF (Job := Job) FP
  have hcde := completed_jobs_are_not_ready sched hvs.2
  rw [cumulative_intf_ep_task_service_equiv arr_seq hva sched hvs FP hrefl j hcp hj t1 t2 hbi Δ]
  unfold service_of_hp_jobs_from_other_ep_tasks
  refine Nat.le_trans (service_of_jobs_le_workload (ideal_proc_model_provides_unit_service Job) sched hcde _ _ _ _) ?_
  have hpart := hep_workload_from_other_ep_partitioned_by_tasks (Task := Task) (FP := FP)
    (JLFP := ELF (Job := Job) FP) arr_seq hva ts huniq hall tsk j htsk t1 (t1 + Δ)
  have heq : workload_of_jobs (fun jhp => @other_ep_task_hep_job Task _ Job _ _ FP (ELF (Job := Job) FP) jhp j)
      (arrivals_between arr_seq t1 (t1 + Δ)) =
      workload_of_jobs (hep_job_of_ep_other_task (Task := Task) (FP := FP) (JLFP := ELF (Job := Job) FP) j)
        (arrivals_between arr_seq t1 (t1 + Δ)) := rfl
  rw [heq, hpart]
  refine Nat.le_trans ?_ (Prosa.Analysis.Facts.Workload.ElfAthepBound.sum_of_ep_tsk_workloads_is_at_most_bound_on_ep_task_workload
    arr_seq hva hvjc ts hresp tsk FP j htsk t1 (t1 + Δ + 1) Δ (by omega'))
  apply leq_sum_seq
  intro tsko _ _
  apply workload_of_jobs_weaken
  intro jo h
  unfold hep_job_of_ep_other_task at h
  simp only [Bool.and_eq_true] at h ⊢
  exact ⟨h.1.1.1, h.2⟩

/-- The interference from the strictly higher-priority tasks is bounded by `total_hp_rbf`. -/
theorem bound_on_hp_workload [TaskCost Task] [MaxArrivals Task] [PriorityPoint Task] [JobTask Job Task]
    [JobArrival Job] [JobCost Job] (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq → arrivals_have_valid_job_costs (Task := Task) arr_seq →
    ∀ ts : List Task, all_jobs_from_taskset arr_seq ts → taskset_respects_max_arrivals arr_seq ts →
    ∀ (tsk : Task) (sched : schedule (processor_state Job)),
      @valid_schedule Job _ _ (processor_state Job) sched _ basic_ready_instance arr_seq →
    ∀ FP : FP_policy Task, reflexive_task_priorities FP →
    ∀ j : Job, job_of_task tsk j = true → job_cost_positive j = true → arrives_in arr_seq j →
    ∀ t1 t2 : instant,
      @Prosa.Analysis.Abstract.Definitions.busy_interval Job _
        (@ideal_jlfp_interference Job _ arr_seq sched (ELF (Job := Job) FP))
        (@ideal_jlfp_interfering_workload Job _ _ arr_seq sched (ELF (Job := Job) FP)) _ _ (processor_state Job)
        sched j t1 t2 →
    ∀ Δ : duration,
      @cumulative_interference_from_hep_jobs_from_hp_tasks Task _ Job _ _ (processor_state Job) arr_seq sched
          FP (ELF (Job := Job) FP) j t1 (t1 + Δ) ≤ total_hp_rbf ts tsk FP Δ := by
  intro hva hvjc ts hall hresp tsk sched hvs FP hrefl j htsk hcp hj t1 t2 hbi Δ
  let _ : JobReady Job (processor_state Job) := basic_ready_instance
  let _ : JLFP_policy Job := ELF (Job := Job) FP
  have hcde := completed_jobs_are_not_ready sched hvs.2
  have htskj : job_task (Task := Task) j = tsk := of_decide_eq_true htsk
  rw [cumulative_intf_hp_task_service_equiv arr_seq hva sched hvs FP hrefl j hcp hj t1 t2 hbi Δ]
  unfold service_of_hp_jobs_from_other_hp_tasks total_hp_rbf
  refine Nat.le_trans (service_of_jobs_le_workload (ideal_proc_model_provides_unit_service Job) sched hcde _ _ _ _) ?_
  exact workload_of_jobs_bounded arr_seq hvjc ts hall hresp _ (fun o => hp_task (FP := FP) o tsk)
    (by
      intro jo h
      unfold hp_task_hep_job at h
      simp only [Bool.and_eq_true] at h
      rw [← htskj]; exact h.2) t1 Δ

/-- `task_IBF` bounds the interference incurred by any job of `tsk` from jobs of other tasks. -/
theorem instantiated_task_interference_is_bounded [TaskCost Task] [MaxArrivals Task] [PriorityPoint Task]
    [JobTask Job Task] [JobArrival Job] [JobCost Job] [JobPreemptable Job] (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq → arrivals_have_valid_job_costs (Task := Task) arr_seq →
    ∀ ts : List Task, ts.Nodup → all_jobs_from_taskset arr_seq ts → taskset_respects_max_arrivals arr_seq ts →
    ∀ (tsk : Task) (sched : schedule (processor_state Job)),
      @valid_schedule Job _ _ (processor_state Job) sched _ basic_ready_instance arr_seq →
    ∀ FP : FP_policy Task, reflexive_task_priorities FP → transitive_task_priorities FP →
      total_task_priorities FP → valid_preemption_model arr_seq sched →
      @respects_JLFP_policy_at_preemption_point Job _ _ _ (processor_state Job) _ basic_ready_instance arr_seq sched
        (ELF (Job := Job) FP) →
    ∀ priority_inversion_lp_tasks_bound : duration,
      @priority_inversion_cond_is_bounded_by Task _ Job _ _ _ _ (processor_state Job) arr_seq sched
        (ELF (Job := Job) FP) tsk (fun j' => hp_task (FP := FP) tsk (job_task (Task := Task) j'))
        (constant priority_inversion_lp_tasks_bound) →
    ∀ priority_inversion_ep_tasks_bound : duration → duration,
      @priority_inversion_cond_is_bounded_by Task _ Job _ _ _ _ (processor_state Job) arr_seq sched
        (ELF (Job := Job) FP) tsk (fun j' => ep_task (FP := FP) tsk (job_task (Task := Task) j'))
        priority_inversion_ep_tasks_bound →
      @task_interference_is_bounded_by Job _ Task _ _ _ _ (processor_state Job) arr_seq sched tsk
        (@ideal_jlfp_interference Job _ arr_seq sched (ELF (Job := Job) FP))
        (@ideal_jlfp_interfering_workload Job _ _ arr_seq sched (ELF (Job := Job) FP))
        (task_IBF ts tsk FP priority_inversion_lp_tasks_bound priority_inversion_ep_tasks_bound) := by
  intro hva hvjc ts huniq hall hresp tsk sched hvs FP hrefl htrans htot hvpm hrespE lp hlp ep hep
    t1 t2 Δ j hj htsk hbi hlt hncomp A hA
  let _ : JobReady Job (processor_state Job) := basic_ready_instance
  let _ : JLFP_policy Job := ELF (Job := Job) FP
  have hfrom := hvs.1
  have hmust := jobs_must_arrive_to_be_ready sched hvs.2
  have hreflJ := ELF_is_reflexive (Job := Job) FP hrefl
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
  have hsplit := cumulative_task_interference_split arr_seq hva sched hfrom hmust (JLFP := ELF (Job := Job) FP)
    hreflJ tsk j t1 (t1 + Δ) hj htsk hncomp
  have hpib := priority_inversion_is_bounded arr_seq hva tsk sched hvs FP hrefl htrans htot hvpm hrespE lp hlp ep hep
  have hpi : cumulative_priority_inversion arr_seq sched j t1 (t1 + Δ) ≤
      priority_inversion_bound lp ep (job_arrival j - t1) :=
    cumulative_priority_inversion_is_bounded hreflJ arr_seq hva sched hvs tsk j hj htsk hcp t1 t2 hbi Δ
      (Nat.le_of_lt hlt) _ hpib
  have hsplit2 := cumulative_hep_interference_split_tasks_new arr_seq sched FP (ELF (Job := Job) FP)
    (ELF_is_JLFP_FP_compatible (Job := Job) FP) (ideal_proc_model_is_a_uniprocessor_model Job) j t1 Δ
  have hepb := bound_on_ep_workload arr_seq hva hvjc ts huniq hall hresp tsk sched hvs FP hrefl j htsk hcp hj t1 t2 hbi
    Δ (Nat.le_of_lt hlt)
  have hhpb := bound_on_hp_workload arr_seq hva hvjc ts hall hresp tsk sched hvs FP hrefl j htsk hcp hj t1 t2 hbi Δ
  refine Nat.le_trans hsplit ?_
  unfold task_IBF
  omega'

/-- The RBF of `tsk` changes at `A`. -/
def task_rbf_changes_at [TaskCost Task] [MaxArrivals Task] (tsk : Task) (A : duration) : Bool :=
  decide (task_request_bound_function tsk A ≠ task_request_bound_function tsk (A + 1))

/-- The interval of some other equal-priority task changes at `A`. -/
def bound_on_total_ep_workload_changes_at [PriorityPoint Task] (ts : List Task) (tsk : Task) (FP : FP_policy Task)
    (A : Nat) : Bool :=
  ts.any (fun tsk_o => ep_task (FP := FP) tsk tsk_o && decide (tsk_o ≠ tsk) &&
    decide (ep_task_intf_interval tsk tsk_o (A - 1) ≠ ep_task_intf_interval tsk tsk_o A))

/-- The priority-inversion bound changes at `A`. -/
def priority_inversion_changes_at (priority_inversion_lp_tasks_bound : duration)
    (priority_inversion_ep_tasks_bound : duration → duration) (A : duration) : Bool :=
  decide (priority_inversion_bound priority_inversion_lp_tasks_bound priority_inversion_ep_tasks_bound (A - 1) ≠
    priority_inversion_bound priority_inversion_lp_tasks_bound priority_inversion_ep_tasks_bound A)

/-- The concrete ELF search space. -/
def is_in_search_space [TaskCost Task] [MaxArrivals Task] [PriorityPoint Task] (ts : List Task) (tsk : Task)
    (FP : FP_policy Task) (priority_inversion_lp_tasks_bound : duration)
    (priority_inversion_ep_tasks_bound : duration → duration) (L A : duration) : Bool :=
  decide (A < L) &&
    (priority_inversion_changes_at priority_inversion_lp_tasks_bound priority_inversion_ep_tasks_bound A ||
      task_rbf_changes_at tsk A || bound_on_total_ep_workload_changes_at ts tsk FP A)

/-- Any offset of the abstract search space is in the concrete ELF search space. -/
theorem A_is_in_concrete_search_space [TaskCost Task] [MaxArrivals Task] [PriorityPoint Task] (ts : List Task) :
    valid_taskset_arrival_curve ts max_arrivals →
    ∀ tsk : Task, decide (tsk ∈ ts) = true →
    ∀ (FP : FP_policy Task) (priority_inversion_lp_tasks_bound : duration)
      (priority_inversion_ep_tasks_bound : duration → duration) (L : duration), 0 < L → 0 < task_cost tsk →
      0 < max_arrivals tsk 1 →
    ∀ A : duration,
      Prosa.Analysis.Abstract.SearchSpace.is_in_search_space L
          (fun A0 Δ => task_request_bound_function tsk (A0 + 1) - task_cost tsk +
            task_IBF ts tsk FP priority_inversion_lp_tasks_bound priority_inversion_ep_tasks_bound A0 Δ) A →
        is_in_search_space ts tsk FP priority_inversion_lp_tasks_bound priority_inversion_ep_tasks_bound L A = true := by
  intro hv tsk hin FP lp ep L hL hc hpos A h
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
    have hpi' : priority_inversion_bound lp ep (A - 1) = priority_inversion_bound lp ep A := by
      unfold priority_inversion_changes_at at hpi
      simpa using hpi
    have hrbf' : task_request_bound_function tsk A = task_request_bound_function tsk (A + 1) := by
      unfold task_rbf_changes_at at hrbf
      simpa using hrbf
    dsimp only
    unfold task_IBF
    rw [hA1, hpi', hrbf']
    congr 2
    unfold bound_on_total_ep_workload sumFiltered
    congr 1
    refine congrArg (fun l : List Nat => l.sum) (List.map_congr_left (l := List.filter (fun tsk_o => ep_task (FP := FP) tsk tsk_o &&
      decide (tsk_o ≠ tsk)) ts) ?_)
    intro tsko hmem
    simp only [List.mem_filter, Bool.and_eq_true, decide_eq_true_eq] at hmem
    have hw : ¬ (ep_task_intf_interval tsk tsko (A - 1) ≠ ep_task_intf_interval tsk tsko A) := by
      intro hneq
      apply hwl
      unfold bound_on_total_ep_workload_changes_at
      rw [List.any_eq_true]
      exact ⟨tsko, hmem.1, by simp only [Bool.and_eq_true, decide_eq_true_eq]; exact ⟨hmem.2, hneq⟩⟩
    simp only [ne_eq, Decidable.not_not] at hw
    rw [hw]

/-- Every offset of the abstract search space has a solution of the response-time recurrence. -/
theorem response_time_recurrence_solution_exists [TaskCost Task] [TaskRunToCompletionThreshold Task]
    [MaxArrivals Task] [PriorityPoint Task] (ts : List Task) :
    valid_taskset_arrival_curve ts max_arrivals →
    ∀ tsk : Task, decide (tsk ∈ ts) = true →
    ∀ (FP : FP_policy Task) (priority_inversion_lp_tasks_bound : duration)
      (priority_inversion_ep_tasks_bound : duration → duration) (L : duration), 0 < L →
    ∀ R : duration,
      (∀ A : duration,
        is_in_search_space ts tsk FP priority_inversion_lp_tasks_bound priority_inversion_ep_tasks_bound L A = true →
        ∃ F : duration,
          priority_inversion_bound priority_inversion_lp_tasks_bound priority_inversion_ep_tasks_bound A +
                bound_on_total_ep_workload ts tsk FP A (A + F) + total_hp_rbf ts tsk FP (A + F) +
              (task_request_bound_function tsk (A + 1) - (task_cost tsk - task_rtct tsk)) ≤ A + F ∧
            F + (task_cost tsk - task_rtct tsk) ≤ R) →
      0 < task_cost tsk → 0 < max_arrivals tsk 1 →
    ∀ A : Nat,
      Prosa.Analysis.Abstract.SearchSpace.is_in_search_space L
          (fun A0 Δ => task_request_bound_function tsk (A0 + 1) - task_cost tsk +
            task_IBF ts tsk FP priority_inversion_lp_tasks_bound priority_inversion_ep_tasks_bound A0 Δ) A →
        ∃ F : Nat,
          task_request_bound_function tsk (A + 1) - (task_cost tsk - task_rtct tsk) +
              task_IBF ts tsk FP priority_inversion_lp_tasks_bound priority_inversion_ep_tasks_bound A (A + F) ≤
            A + F ∧
          F + (task_cost tsk - task_rtct tsk) ≤ R := by
  intro hv tsk hin FP lp ep L hL R hR hc hpos A hA
  obtain ⟨F, hF, hFR⟩ := hR A (A_is_in_concrete_search_space ts hv tsk hin FP lp ep L hL hc hpos A hA)
  refine ⟨F, ?_, hFR⟩
  unfold task_IBF
  omega'

/-- Response-time bound for ELF schedulers with bounded priority inversion on ideal uniprocessors. -/
theorem uniprocessor_response_time_bound_elf [TaskCost Task] [TaskRunToCompletionThreshold Task] [MaxArrivals Task]
    [PriorityPoint Task] [JobTask Job Task] [JobArrival Job] [JobCost Job] [JobPreemptable Job]
    (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq → arrivals_have_valid_job_costs (Task := Task) arr_seq →
    ∀ ts : List Task, ts.Nodup → all_jobs_from_taskset arr_seq ts → taskset_respects_max_arrivals arr_seq ts →
      valid_taskset_arrival_curve ts max_arrivals →
    ∀ tsk : Task, decide (tsk ∈ ts) = true → valid_task_run_to_completion_threshold arr_seq tsk →
    ∀ sched : schedule (processor_state Job),
      @valid_schedule Job _ _ (processor_state Job) sched _ basic_ready_instance arr_seq →
    ∀ FP : FP_policy Task, reflexive_task_priorities FP → transitive_task_priorities FP →
      total_task_priorities FP → valid_preemption_model arr_seq sched →
      @respects_JLFP_policy_at_preemption_point Job _ _ _ (processor_state Job) _ basic_ready_instance arr_seq sched
        (ELF (Job := Job) FP) →
      @Prosa.Model.Schedule.WorkConserving.work_conserving Job _ _ _ (processor_state Job) basic_ready_instance
        arr_seq sched →
    ∀ priority_inversion_lp_tasks_bound : duration,
      @priority_inversion_cond_is_bounded_by Task _ Job _ _ _ _ (processor_state Job) arr_seq sched
        (ELF (Job := Job) FP) tsk (fun j' => hp_task (FP := FP) tsk (job_task (Task := Task) j'))
        (constant priority_inversion_lp_tasks_bound) →
    ∀ priority_inversion_ep_tasks_bound : duration → duration,
      @priority_inversion_cond_is_bounded_by Task _ Job _ _ _ _ (processor_state Job) arr_seq sched
        (ELF (Job := Job) FP) tsk (fun j' => ep_task (FP := FP) tsk (job_task (Task := Task) j'))
        priority_inversion_ep_tasks_bound →
      (∀ (j : Job) (t1 : Nat), job_task (Task := Task) j = tsk →
        priority_inversion_ep_tasks_bound (job_arrival j - t1) ≤
          maxFiltered ts
            (fun i => (ep_task (FP := FP) i tsk &&
                !decide (0 ≤ (job_arrival j : Int) - (t1 : Int) + task_priority_point tsk - task_priority_point i)) &&
              (decide (0 < max_arrivals i 1) && decide (0 < task_cost i)))
            (fun i => task_cost i)) →
    ∀ L : duration, 0 < L →
      L = priority_inversion_lp_tasks_bound + total_hep_request_bound_function_FP ts (FP := FP) tsk L →
    ∀ R : duration,
      (∀ A : duration,
        is_in_search_space ts tsk FP priority_inversion_lp_tasks_bound priority_inversion_ep_tasks_bound L A = true →
        ∃ F : duration,
          priority_inversion_bound priority_inversion_lp_tasks_bound priority_inversion_ep_tasks_bound A +
                bound_on_total_ep_workload ts tsk FP A (A + F) + total_hp_rbf ts tsk FP (A + F) +
              (task_request_bound_function tsk (A + 1) - (task_cost tsk - task_rtct tsk)) ≤ A + F ∧
            F + (task_cost tsk - task_rtct tsk) ≤ R) →
      task_response_time_bound arr_seq sched tsk R := by
  intro hva hvjc ts huniq hall hresp hvalid tsk hin hrtct sched hvs FP hrefl htrans htot hvpm hrespE hwc lp hlp ep
    hep hepc L hL hfix R hR js harrs htsks
  rcases Nat.eq_zero_or_pos (job_cost js) with h0 | hjpos
  · unfold job_response_time_bound completed_by
    apply decide_eq_true; rw [h0]; exact Nat.zero_le _
  let _ : JobReady Job (processor_state Job) := basic_ready_instance
  let _ : JLFP_policy Job := ELF (Job := Job) FP
  have hfrom := hvs.1
  have hmust := jobs_must_arrive_to_be_ready sched hvs.2
  have hcde := completed_jobs_are_not_ready sched hvs.2
  have hreflJ := ELF_is_reflexive (Job := Job) FP hrefl
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
  have hseq := ELF_implies_sequential_tasks (Job := Job) FP hrefl htrans arr_seq hva (processor_state Job)
    (ideal_proc_model_is_a_uniprocessor_model Job) sched hwbr hvs hvpm hrespE
  have hcons := instantiated_interference_and_workload_consistent_with_sequential_tasks arr_seq hva sched hfrom hmust
    hcde hreflJ tsk (ELF_respects_sequential_tasks (Job := Job) FP hrefl)
  have hbounded := instantiated_busy_intervals_are_bounded arr_seq hva hvjc ts huniq hall hresp hvalid tsk hin sched hvs
    FP hrefl htrans htot hvpm hrespE hwc lp hlp ep hep hepc L hL hfix
  have hibf := instantiated_task_interference_is_bounded arr_seq hva hvjc ts huniq hall hresp tsk sched hvs FP hrefl
    htrans htot hvpm hrespE lp hlp ep hep
  exact uniprocessor_response_time_bound_seq (ideal_proc_model_is_a_uniprocessor_model Job)
    (ideal_proc_model_provides_unit_service Job) (ideal_proc_model_ensures_ideal_progress Job) arr_seq hva sched
    hfrom hmust hcde hvjc ts tsk hin hvpm hrtct hvalid hresp hwcA hseq hcons L hbounded _ hibf R
    (fun A hA => response_time_recurrence_solution_exists ts hvalid tsk hin FP lp ep L hL R hR hcpos hma A hA)
    js harrs htsks

end Prosa.Results.Rta.Ideal.Elf.BoundedPi
