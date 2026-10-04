-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: analysis/facts/priority/elf.v

import Prosa.Model.Priority.Elf
import Prosa.Model.Aggregate.Workload
import Prosa.Analysis.Definitions.Priority.Classes
import Prosa.Analysis.Facts.Priority.Classes
import Prosa.Model.Schedule.PriorityDriven
import Prosa.Analysis.Facts.Model.Sequential
import Prosa.Analysis.Facts.Priority.Sequential
import Prosa.Analysis.Facts.Priority.Gel

namespace Prosa.Analysis.Facts.Priority.Elf

open Prosa.Behavior.Arrival_sequence
open Prosa.Behavior.Job
open Prosa.Behavior.Ready
open Prosa.Behavior.Schedule
open Prosa.Behavior.Service
open Prosa.Behavior.Time
open Prosa.Model.Task.Concept
open Prosa.Model.Task.Sequentiality
open Prosa.Model.Priority.Definitions
open Prosa.Model.Priority.Gel
open Prosa.Model.Priority.Elf
open Prosa.Model.Preemption.Parameter
open Prosa.Model.Processor.PlatformProperties
open Prosa.Model.Schedule.PriorityDriven
open Prosa.Analysis.Definitions.AlwaysHigherPriority
open Prosa.Analysis.Definitions.WorkBearingReadiness
open Prosa.Analysis.Definitions.Priority.Classes
open Prosa.Analysis.Facts.Priority.Sequential
open Prosa.Analysis.Facts.Priority.Gel

/-! Basic facts about the ELF policy.

Binders follow the elaborated source types: every declaration takes only the
section inputs and hypotheses it uses, in their elaborated order; instance
inputs quantified after a hypothesis are `∀ [..]` binders at that position.
The source's exported `ELF FP` and `GEL` instances are the accepted reducible
definitions, passed explicitly as JLFP policies wherever the elaborated
statements resolve them. Representation: a Boolean in `Prop` position is
`= true`; `a <= b` between arrival times is `decide (a ≤ b)`. -/

section ELFBasicFacts

variable {Task : TaskType} [DecidableEq Task] {Job : JobType} [DecidableEq Job]

/-- ELF reduces to GEL for jobs of equal-priority tasks. -/
theorem hep_job_elf_gel [PriorityPoint Task] [JobTask Job Task] [AR : JobArrival Job] (FP : FP_policy Task) :
    ∀ j j' : Job, ep_task (FP := FP) (job_task (Task := Task) j) (job_task (Task := Task) j') = true →
      (ELF (Job := Job) FP).hep_job j j' = (GEL Job Task).hep_job j j' := by
  intro j j' hep
  simp only [ep_task, Bool.and_eq_true] at hep
  show (hp_task (FP := FP) _ _ || (FP.hep_task _ _ && (GEL Job Task).hep_job j j')) = _
  simp [hp_task, hep.1, hep.2]

/-- For two jobs of the same task, ELF compares arrival times. -/
theorem hep_job_arrival_elf [PriorityPoint Task] [JobTask Job Task] [AR : JobArrival Job] (FP : FP_policy Task) :
    reflexive_task_priorities FP →
    ∀ j j' : Job, same_task (Task := Task) j j' = true →
      (ELF (Job := Job) FP).hep_job j j' = decide (job_arrival j ≤ job_arrival j') := by
  intro hrefl j j' hsame
  have htask : job_task (Task := Task) j = job_task (Task := Task) j' := of_decide_eq_true hsame
  rw [hep_job_elf_gel FP j j' (by simp only [ep_task, htask, Bool.and_self]; exact hrefl _)]
  exact hep_job_arrival_gel j j' hsame

/-- ELF is reflexive. -/
theorem ELF_is_reflexive [PriorityPoint Task] [JobTask Job Task] [AR : JobArrival Job] (FP : FP_policy Task) :
    reflexive_task_priorities FP → reflexive_job_priorities (ELF (Job := Job) FP) := by
  intro hrefl j
  show (hp_task (FP := FP) _ _ || (FP.hep_task _ _ && (GEL Job Task).hep_job j j)) = true
  rw [hrefl, GEL_is_reflexive j]
  simp

/-- ELF is transitive. -/
theorem ELF_is_transitive [PriorityPoint Task] [JobTask Job Task] [AR : JobArrival Job] (FP : FP_policy Task) :
    transitive_task_priorities FP → transitive_job_priorities (ELF (Job := Job) FP) := by
  intro htrans y x z hxy hyz
  change (hp_task (FP := FP) _ _ || (FP.hep_task _ _ && (GEL Job Task).hep_job x y)) = true at hxy
  change (hp_task (FP := FP) _ _ || (FP.hep_task _ _ && (GEL Job Task).hep_job y z)) = true at hyz
  show (hp_task (FP := FP) _ _ || (FP.hep_task _ _ && (GEL Job Task).hep_job x z)) = true
  have hgel := @GEL_is_transitive Task _ _ Job _ _ _ y x z
  simp only [hp_task, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at hxy hyz ⊢
  have ha : FP.hep_task (job_task (Task := Task) x) (job_task (Task := Task) y) = true := by
    rcases hxy with h | h <;> exact h.1
  have hc : FP.hep_task (job_task (Task := Task) y) (job_task (Task := Task) z) = true := by
    rcases hyz with h | h <;> exact h.1
  have he := htrans _ _ _ ha hc
  cases hf : FP.hep_task (job_task (Task := Task) z) (job_task (Task := Task) x)
  · exact Or.inl ⟨he, rfl⟩
  · right
    refine ⟨he, ?_⟩
    rcases hxy with ⟨_, hnb⟩ | ⟨_, hgxy⟩
    · exact absurd (htrans _ _ _ hc hf) (by rw [hnb]; decide)
    · rcases hyz with ⟨_, hnd⟩ | ⟨_, hgyz⟩
      · exact absurd (htrans _ _ _ hf ha) (by rw [hnd]; decide)
      · exact hgel hgxy hgyz

/-- ELF is total. -/
theorem ELF_is_total [PriorityPoint Task] [JobTask Job Task] [AR : JobArrival Job] (FP : FP_policy Task) :
    total_task_priorities FP → total_job_priorities (ELF (Job := Job) FP) := by
  intro htot x y
  show ((hp_task (FP := FP) _ _ || (FP.hep_task _ _ && (GEL Job Task).hep_job x y)) ||
    (hp_task (FP := FP) _ _ || (FP.hep_task _ _ && (GEL Job Task).hep_job y x))) = true
  have ht := htot (job_task (Task := Task) x) (job_task (Task := Task) y)
  have hg := @GEL_is_total Task _ _ Job _ _ _ x y
  simp only [hp_task]
  cases h1 : FP.hep_task (job_task (Task := Task) x) (job_task (Task := Task) y) <;>
    cases h2 : FP.hep_task (job_task (Task := Task) y) (job_task (Task := Task) x) <;>
    simp_all

/-- ELF is compatible with its underlying FP policy. -/
theorem ELF_is_JLFP_FP_compatible [PriorityPoint Task] [JobTask Job Task] [AR : JobArrival Job]
    (FP : FP_policy Task) : JLFP_FP_compatible (ELF (Job := Job) FP) FP := by
  refine ⟨fun j1 j2 h => ?_, fun j1 j2 h => ?_⟩
  · change (hp_task (FP := FP) _ _ || (FP.hep_task _ _ && (GEL Job Task).hep_job j1 j2)) = true at h
    simp only [hp_task, Bool.or_eq_true, Bool.and_eq_true] at h
    rcases h with h | h <;> exact h.1
  · show (hp_task (FP := FP) _ _ || (FP.hep_task _ _ && (GEL Job Task).hep_job j1 j2)) = true
    rw [h]; rfl

/-- ELF respects sequential tasks. -/
theorem ELF_respects_sequential_tasks [PriorityPoint Task] [JobTask Job Task] [AR : JobArrival Job]
    (FP : FP_policy Task) :
    reflexive_task_priorities FP → policy_respects_sequential_tasks (Task := Task) (ELF (Job := Job) FP) := by
  intro hrefl j1 j2 hsame hle
  rw [hep_job_arrival_elf FP hrefl j1 j2 hsame]
  exact decide_eq_true hle

/-- In a schedule respecting ELF at preemption points, tasks are sequential. -/
theorem ELF_implies_sequential_tasks [PriorityPoint Task] [JobTask Job Task] [JobCost Job]
    [AR : JobArrival Job] (FP : FP_policy Task) :
    reflexive_task_priorities FP → transitive_task_priorities FP →
    ∀ arr_seq : arrival_sequence Job, valid_arrival_sequence arr_seq →
    ∀ PState : ProcessorState Job, uniprocessor_model PState →
    ∀ (sched : schedule PState) [H2 : JobReady Job PState],
      @work_bearing_readiness Job _ _ _ PState H2 arr_seq sched (ELF (Job := Job) FP) →
      valid_schedule sched arr_seq →
    ∀ [JobPreemptable Job], valid_preemption_model arr_seq sched →
      respects_JLFP_policy_at_preemption_point arr_seq sched (ELF (Job := Job) FP) →
      sequential_tasks (Task := Task) arr_seq sched := by
  intro hrefl htrans arr_seq hva PState huni sched _ hwb hvs _ hvpm hresp j1 j2 t ha1 _ hsame hlt hs
  refine early_hep_job_is_scheduled arr_seq hva (ELF (Job := Job) FP) (ELF_is_transitive FP htrans) PState huni
    sched hwb hvs hvpm hresp j1 j2 ha1 hlt ?_ t hs
  refine (@always_higher_priority_jlfp Job _ (ELF (Job := Job) FP) j1 j2).mpr ?_
  have hsame' : same_task (Task := Task) j2 j1 = true := by
    have : job_task (Task := Task) j1 = job_task (Task := Task) j2 := of_decide_eq_true hsame
    exact decide_eq_true this.symm
  rw [hep_job_arrival_elf FP hrefl j1 j2 hsame, hep_job_arrival_elf FP hrefl j2 j1 hsame']
  simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq, decide_eq_false_iff_not]
  exact ⟨Nat.le_of_lt hlt, Nat.not_le.mpr hlt⟩

end ELFBasicFacts

end Prosa.Analysis.Facts.Priority.Elf
