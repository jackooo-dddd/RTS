-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: results/generality/elf.v

import Prosa.Util.Int
import Prosa.Model.Schedule.PriorityDriven
import Prosa.Model.Priority.Elf
import Prosa.Analysis.Facts.Priority.Gel
import Prosa.Analysis.Facts.Priority.Elf
import Prosa.Analysis.Facts.Priority.Classes
import Prosa.Analysis.Facts.Model.Sequential

namespace Prosa.Results.Generality.Elf

open Prosa.Behavior.Arrival_sequence
open Prosa.Behavior.Job
open Prosa.Behavior.Ready
open Prosa.Behavior.Schedule
open Prosa.Behavior.Service
open Prosa.Behavior.Time
open Prosa.Model.Task.Concept
open Prosa.Model.Task.Sequentiality
open Prosa.Model.Priority.Definitions
open Prosa.Model.Priority.Coercion
open Prosa.Model.Priority.Gel
open Prosa.Model.Priority.Elf
open Prosa.Model.Preemption.Parameter
open Prosa.Model.Schedule.PriorityDriven
open Prosa.Analysis.Facts.Behavior.Completion
open Prosa.Analysis.Facts.Priority.Gel
open Prosa.Analysis.Facts.Priority.Elf

/-! Generality of ELF w.r.t. fixed-priority and GEL scheduling.

Binders follow the elaborated source types (the section inputs, including the
readiness model, are leading inputs of every remark). The source's exported
`ELF fp` and `GEL` instances are the accepted reducible definitions, passed
explicitly as JLFP policies. Representation: a Boolean in `Prop` position is
`= true`; `~~ b` is `(!b) = true`; `x != y` is `decide (x ≠ y) = true`. -/

section GeneralityOfELF

variable {Task : TaskType} [DecidableEq Task] {Job : JobType} [DecidableEq Job]

/-- If all tasks have equal priority, ELF reduces to GEL. -/
theorem elf_generalizes_gel [PriorityPoint Task] [JobTask Job Task] {PState : ProcessorState Job}
    [Arrival : JobArrival Job] [Cost : JobCost Job] [JobPreemptable Job] [JR : JobReady Job PState]
    (fp : FP_policy Task) :
    (∀ tsk1 tsk2 : Task, ep_task (FP := fp) tsk1 tsk2 = true) →
    ∀ (sched : schedule PState) (arr_seq : arrival_sequence Job),
      respects_JLFP_policy_at_preemption_point arr_seq sched (ELF (Job := Job) fp) ↔
        respects_JLFP_policy_at_preemption_point arr_seq sched (GEL Job Task) := by
  intro hsame sched arr_seq
  have heq : ∀ j j' : Job, (ELF (Job := Job) fp).hep_job j j' = (GEL Job Task).hep_job j j' :=
    fun j j' => hep_job_elf_gel fp j j' (hsame _ _)
  constructor
  · intro h j jhp t ha hpt hbl hs
    have := h j jhp t ha hpt hbl hs
    change (ELF (Job := Job) fp).hep_job jhp j = true at this
    change (GEL Job Task).hep_job jhp j = true
    rw [← heq]; exact this
  · intro h j jhp t ha hpt hbl hs
    have := h j jhp t ha hpt hbl hs
    change (GEL Job Task).hep_job jhp j = true at this
    change (ELF (Job := Job) fp).hep_job jhp j = true
    rw [heq]; exact this

/-- An ELF schedule respects the underlying fixed-priority policy. -/
theorem elf_is_fixed_priority [PriorityPoint Task] [JobTask Job Task] {PState : ProcessorState Job}
    [Arrival : JobArrival Job] [Cost : JobCost Job] [JobPreemptable Job] [JR : JobReady Job PState]
    (fp : FP_policy Task) (sched : schedule PState) (arr_seq : arrival_sequence Job) :
    respects_JLFP_policy_at_preemption_point arr_seq sched (ELF (Job := Job) fp) →
      respects_FP_policy_at_preemption_point arr_seq sched fp := by
  intro h j jhp t ha hpt hbl hs
  have := h j jhp t ha hpt hbl hs
  change (ELF (Job := Job) fp).hep_job jhp j = true at this
  exact (ELF_is_JLFP_FP_compatible fp).1 jhp j this

/-- With distinct task priorities and sequential tasks, ELF and FP coincide. -/
theorem elf_generalizes_fixed_priority [PriorityPoint Task] [JobTask Job Task] {PState : ProcessorState Job}
    [Arrival : JobArrival Job] [Cost : JobCost Job] [JobPreemptable Job] [JR : JobReady Job PState]
    (fp : FP_policy Task) :
    (∀ tsk1 tsk2 : Task, decide (tsk1 ≠ tsk2) = true → (!ep_task (FP := fp) tsk1 tsk2) = true) →
    ∀ (arr_seq : arrival_sequence Job) (sched : schedule PState),
      valid_schedule sched arr_seq → sequential_tasks (Task := Task) arr_seq sched →
      (respects_JLFP_policy_at_preemption_point arr_seq sched (ELF (Job := Job) fp) ↔
        respects_FP_policy_at_preemption_point arr_seq sched fp) := by
  intro hdist arr_seq sched hvs hseq
  refine ⟨elf_is_fixed_priority fp sched arr_seq, ?_⟩
  intro h j jhp t ha hpt hbl hs
  have hep : fp.hep_task (job_task (Task := Task) jhp) (job_task (Task := Task) j) = true := h j jhp t ha hpt hbl hs
  change (hp_task (FP := fp) _ _ || (fp.hep_task _ _ && (GEL Job Task).hep_job jhp j)) = true
  by_cases htask : job_task (Task := Task) jhp = job_task (Task := Task) j
  · have hsame : same_task (Task := Task) jhp j = true := decide_eq_true htask
    rw [hep_job_arrival_gel jhp j hsame, hep]
    by_cases hle : job_arrival jhp ≤ job_arrival j
    · simp [hle]
    · exfalso
      have hlt : job_arrival j < job_arrival jhp := Nat.lt_of_not_le hle
      have hsame' : same_task (Task := Task) j jhp = true := decide_eq_true htask.symm
      have hcomp : completed_by sched j t = true :=
        hseq j jhp t ha (hvs.1 jhp t hs) hsame' hlt hs
      simp only [backlogged, Bool.and_eq_true] at hbl
      have hinc := ready_implies_incomplete sched j t hbl.1
      rw [hcomp] at hinc
      exact absurd hinc (by decide)
  · have hnep := hdist _ _ (decide_eq_true htask)
    simp only [ep_task, Bool.not_eq_true', Bool.and_eq_false_iff] at hnep
    simp only [hp_task, hep, Bool.true_and, Bool.or_eq_true, Bool.and_eq_true]
    left
    rcases hnep with h1 | h1
    · rw [hep] at h1; exact absurd h1 (by decide)
    · simp [h1]

end GeneralityOfELF

end Prosa.Results.Generality.Elf
