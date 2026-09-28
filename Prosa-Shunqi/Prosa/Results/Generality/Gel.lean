-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: results/generality/gel.v

import Prosa.Util.Int
import Prosa.Model.Schedule.PriorityDriven
import Prosa.Model.Priority.Gel
import Prosa.Model.Priority.Fifo
import Prosa.Model.Priority.Edf
import Prosa.Model.Task.AbsoluteDeadline
import Prosa.Analysis.Facts.Priority.Classes
import Prosa.Analysis.Facts.Model.Sequential
import Prosa.Analysis.Facts.Priority.Edf
import Prosa.Analysis.Facts.Priority.Gel
import Prosa.Analysis.Facts.Priority.Fifo

namespace Prosa.Results.Generality.Gel

open Prosa.Behavior.Arrival_sequence
open Prosa.Behavior.Job
open Prosa.Behavior.Ready
open Prosa.Behavior.Schedule
open Prosa.Behavior.Service
open Prosa.Behavior.Time
open Prosa.Model.Task.Concept
open Prosa.Model.Task.Sequentiality
open Prosa.Model.Task.AbsoluteDeadline
open Prosa.Model.Priority.Definitions
open Prosa.Model.Priority.Coercion
open Prosa.Model.Priority.Gel
open Prosa.Model.Priority.Fifo
open Prosa.Model.Priority.Edf
open Prosa.Model.Preemption.Parameter
open Prosa.Model.Schedule.PriorityDriven
open Prosa.Analysis.Facts.Behavior.Arrivals
open Prosa.Analysis.Facts.Behavior.Completion
open Prosa.Analysis.Facts.Model.Sequential
open Prosa.Analysis.Facts.Priority.Classes
open Prosa.Analysis.Facts.Priority.Edf
open Prosa.Analysis.Facts.Priority.Gel
open Prosa.Analysis.Facts.Priority.Fifo

/-! Generality of GEL w.r.t. EDF and FIFO, and its conditional generality
w.r.t. fixed-priority scheduling.

Binders follow the elaborated source types (the section inputs, including the
readiness model, are leading inputs of every declaration; unused ones are
absent, as in the elaborated types). The source's exported `GEL` instance is
the accepted reducible definition, passed explicitly as the JLFP policy; the
EDF policy is the accepted `EDF` instance over the accepted
`job_deadline_from_task_deadline` instance and FIFO the accepted global
instance, named explicitly. The section-local `tsk`, `tsk'` and
`gel_hep_job` are inlined. Representation: a Boolean in `Prop` position is
`= true`; `~~ b` is `(!b) = true`; as in the accepted `model/priority/gel.v`,
an offset is an `Int`, `n%:R`/the implicit `nat`-to-`int` coercion is the cast
`(n : Int)`, `(x <= y)%R` on `int` is `decide (x ≤ y)` and `` `|x| `` is
`Int.natAbs`. -/

section GeneralityOfGEL

variable {Task : TaskType} [DecidableEq Task] {Job : JobType} [DecidableEq Job]

private theorem int_add_le_iff (a b c d : Nat) :
    ((a : Int) + (b : Int) ≤ (c : Int) + (d : Int)) ↔ a + b ≤ c + d := by omega

private theorem int_add_zero_le_iff (a c : Nat) : ((a : Int) + 0 ≤ (c : Int) + 0) ↔ a ≤ c := by omega

/-- The difference between the priority-point offsets of two tasks. -/
def pp_delta [PriorityPoint Task] (tsk tsk' : Task) : Int :=
  task_priority_point tsk' - task_priority_point tsk

/-- With priority points equal to relative deadlines, GEL is EDF. -/
theorem gel_generalizes_edf [PriorityPoint Task] [JobTask Job Task] {PState : ProcessorState Job}
    [Arrival : JobArrival Job] [Cost : JobCost Job] [JobPreemptable Job] [JR : JobReady Job PState]
    [TaskDeadline Task] :
    (∀ tsk : Task, task_priority_point tsk = (task_deadline tsk : Int)) →
    ∀ (sched : schedule PState) (arr_seq : arrival_sequence Job),
      respects_JLFP_policy_at_preemption_point arr_seq sched (GEL Job Task) ↔
        respects_JLFP_policy_at_preemption_point arr_seq sched
          (@EDF Job _ (job_deadline_from_task_deadline Job Task)) := by
  intro hpp sched arr_seq
  have heq : ∀ j j' : Job, (GEL Job Task).hep_job j j' =
      (@EDF Job _ (job_deadline_from_task_deadline Job Task)).hep_job j j' := by
    intro j j'
    rw [hep_job_priority_point, hep_job_task_deadline, hpp, hpp]
    simp only [decide_eq_decide]
    exact int_add_le_iff _ _ _ _
  constructor
  · intro h j jhp t ha hpt hbl hs
    have := h j jhp t ha hpt hbl hs
    change (GEL Job Task).hep_job jhp j = true at this
    change (@EDF Job _ (job_deadline_from_task_deadline Job Task)).hep_job jhp j = true
    rw [← heq]; exact this
  · intro h j jhp t ha hpt hbl hs
    have := h j jhp t ha hpt hbl hs
    change (@EDF Job _ (job_deadline_from_task_deadline Job Task)).hep_job jhp j = true at this
    change (GEL Job Task).hep_job jhp j = true
    rw [heq]; exact this

/-- With all priority points equal to zero, GEL is FIFO. -/
theorem gel_generalizes_fifo [PriorityPoint Task] [JobTask Job Task] {PState : ProcessorState Job}
    [Arrival : JobArrival Job] [Cost : JobCost Job] [JobPreemptable Job] [JR : JobReady Job PState] :
    (∀ tsk : Task, task_priority_point tsk = 0) →
    ∀ (sched : schedule PState) (arr_seq : arrival_sequence Job),
      respects_JLFP_policy_at_preemption_point arr_seq sched (GEL Job Task) ↔
        respects_JLFP_policy_at_preemption_point arr_seq sched (FIFO Job) := by
  intro hpp sched arr_seq
  have heq : ∀ j j' : Job, (GEL Job Task).hep_job j j' = (FIFO Job).hep_job j j' := by
    intro j j'
    rw [hep_job_priority_point, hep_job_arrival_FIFO, hpp, hpp]
    simp only [decide_eq_decide]
    exact int_add_zero_le_iff _ _
  constructor
  · intro h j jhp t ha hpt hbl hs
    have := h j jhp t ha hpt hbl hs
    change (GEL Job Task).hep_job jhp j = true at this
    change (FIFO Job).hep_job jhp j = true
    rw [← heq]; exact this
  · intro h j jhp t ha hpt hbl hs
    have := h j jhp t ha hpt hbl hs
    change (FIFO Job).hep_job jhp j = true at this
    change (GEL Job Task).hep_job jhp j = true
    rw [heq]; exact this

/-- If the priority-point offset of `j'`'s task is not smaller than that of
`j`'s task and bounds `j'`'s response time, then an arrived `j` has
higher-or-equal GEL priority than a backlogged `j'`. -/
theorem backlogged_job_has_lower_gel_prio [PriorityPoint Task] [JobTask Job Task] {PState : ProcessorState Job}
    [Arrival : JobArrival Job] [Cost : JobCost Job] [JR : JobReady Job PState]
    (j j' : Job) (sched : schedule PState) (t : instant) :
    decide (0 ≤ pp_delta (job_task (Task := Task) j) (job_task (Task := Task) j')) = true →
    job_response_time_bound sched j'
        (Int.natAbs (pp_delta (job_task (Task := Task) j) (job_task (Task := Task) j'))) = true →
    has_arrived j t = true → backlogged sched j' t = true →
    (GEL Job Task).hep_job j j' = true := by
  intro hpos hrt harr hbl
  have hpos' := of_decide_eq_true hpos
  have hδ := Int.natAbs_of_nonneg hpos'
  generalize Int.natAbs (pp_delta (job_task (Task := Task) j) (job_task (Task := Task) j')) = n at hrt hδ
  have hδ' : (n : Int) = (task_priority_point (job_task (Task := Task) j') : Int) -
      (task_priority_point (job_task (Task := Task) j) : Int) := hδ
  have harr' : job_arrival j ≤ t := by unfold has_arrived at harr; exact of_decide_eq_true harr
  rw [hep_job_priority_point]
  apply decide_eq_true
  show ((job_arrival j : Nat) : Int) + (task_priority_point (job_task (Task := Task) j) : Int) ≤
    ((job_arrival j' : Nat) : Int) + (task_priority_point (job_task (Task := Task) j') : Int)
  by_cases hle : job_arrival j ≤ job_arrival j' + n
  · omega'
  · exfalso
    have hinc := backlogged_implies_incomplete sched j' t hbl
    unfold job_response_time_bound at hrt
    have hcomp := completion_monotonic sched j' _ t (by omega') hrt
    rw [hcomp] at hinc
    exact absurd hinc (by decide)

/-- Under unique fixed task priorities, suitably separated priority points
that bound the response times of lower-priority tasks, and sequential tasks,
GEL and the fixed-priority policy coincide. -/
theorem gel_conditionally_generalizes_fp [PriorityPoint Task] [JobTask Job Task] {PState : ProcessorState Job}
    [Arrival : JobArrival Job] [Cost : JobCost Job] [JobPreemptable Job] [JR : JobReady Job PState]
    (fp : FP_policy Task) :
    reflexive_task_priorities fp → total_task_priorities fp →
    ∀ arr_seq : arrival_sequence Job,
      (∀ j j' : Job, arrives_in arr_seq j → arrives_in arr_seq j' →
        (!same_task (Task := Task) j j') = true →
        fp.hep_task (job_task (Task := Task) j) (job_task (Task := Task) j') = true →
        hp_task (FP := fp) (job_task (Task := Task) j) (job_task (Task := Task) j') = true) →
      (∀ j j' : Job, arrives_in arr_seq j → arrives_in arr_seq j' →
        hp_task (FP := fp) (job_task (Task := Task) j) (job_task (Task := Task) j') = true →
        decide (0 ≤ pp_delta (job_task (Task := Task) j) (job_task (Task := Task) j')) = true) →
      ∀ sched : schedule PState, valid_schedule sched arr_seq →
      (∀ j j' : Job, arrives_in arr_seq j → arrives_in arr_seq j' →
        hp_task (FP := fp) (job_task (Task := Task) j) (job_task (Task := Task) j') = true →
        job_response_time_bound sched j'
          (Int.natAbs (pp_delta (job_task (Task := Task) j) (job_task (Task := Task) j'))) = true) →
      sequential_tasks (Task := Task) arr_seq sched →
      (respects_JLFP_policy_at_preemption_point arr_seq sched (GEL Job Task) ↔
        respects_FP_policy_at_preemption_point arr_seq sched fp) := by
  intro hrefl htot arr_seq huniq hdpos sched hvs hdrtb hseq
  have hmust := valid_schedule_implies_jobs_must_arrive_to_execute sched arr_seq hvs
  have hcde := valid_schedule_implies_completed_jobs_dont_execute sched arr_seq hvs
  constructor
  · -- GEL respects imply FP respects
    intro h j jhp t ha hpt hbl hs
    have hgel := h j jhp t ha hpt hbl hs
    change (GEL Job Task).hep_job jhp j = true at hgel
    show fp.hep_task (job_task (Task := Task) jhp) (job_task (Task := Task) j) = true
    by_cases htask : job_task (Task := Task) jhp = job_task (Task := Task) j
    · rw [htask]; exact hrefl _
    · cases hh : fp.hep_task (job_task (Task := Task) jhp) (job_task (Task := Task) j) with
      | true => rfl
      | false =>
        exfalso
        have hjhp : arrives_in arr_seq jhp := hvs.1 jhp t hs
        have hhp : hp_task (FP := fp) (job_task (Task := Task) j) (job_task (Task := Task) jhp) = true := by
          rw [← not_hep_hp_task fp htot, hh]; rfl
        have hrt := hdrtb j jhp ha hjhp hhp
        have hpos' := of_decide_eq_true (hdpos j jhp ha hjhp hhp)
        have hδ := Int.natAbs_of_nonneg hpos'
        generalize Int.natAbs (pp_delta (job_task (Task := Task) j) (job_task (Task := Task) jhp)) = n at hrt hδ
        have hδ' : (n : Int) = (task_priority_point (job_task (Task := Task) jhp) : Int) -
            (task_priority_point (job_task (Task := Task) j) : Int) := hδ
        rw [hep_job_priority_point] at hgel
        have hgel' : ((job_arrival jhp : Nat) : Int) + (task_priority_point (job_task (Task := Task) jhp) : Int) ≤
            ((job_arrival j : Nat) : Int) + (task_priority_point (job_task (Task := Task) j) : Int) :=
          of_decide_eq_true hgel
        have harrj : job_arrival j ≤ t := by
          have := backlogged_implies_arrived sched j t hbl
          unfold has_arrived at this; exact of_decide_eq_true this
        unfold job_response_time_bound at hrt
        have hcomp := completion_monotonic sched jhp _ t (by omega') hrt
        have hninc := scheduled_implies_not_completed sched jhp hcde t hs
        rw [hcomp] at hninc
        exact absurd hninc (by decide)
  · -- FP respects imply GEL respects
    intro h j jhp t ha hpt hbl hs
    have hfp : fp.hep_task (job_task (Task := Task) jhp) (job_task (Task := Task) j) = true :=
      h j jhp t ha hpt hbl hs
    change (GEL Job Task).hep_job jhp j = true
    have hjhp : arrives_in arr_seq jhp := hvs.1 jhp t hs
    by_cases hsame : same_task (Task := Task) jhp j = true
    · rw [hep_job_arrival_gel jhp j hsame]
      apply decide_eq_true
      apply Nat.le_of_not_lt
      intro hlt
      have hinc := backlogged_implies_incomplete sched j t hbl
      have hdiff := sequential_tasks_different_tasks arr_seq sched hseq j jhp t ha hjhp hlt hinc hs
      have hsame' : same_task (Task := Task) j jhp = true := by
        unfold same_task at hsame ⊢
        exact decide_eq_true (of_decide_eq_true hsame).symm
      rw [hsame'] at hdiff
      exact absurd hdiff (by decide)
    · have hhp := huniq jhp j hjhp ha (by simpa using hsame) hfp
      exact backlogged_job_has_lower_gel_prio jhp j sched t (hdpos jhp j hjhp ha hhp) (hdrtb jhp j hjhp ha hhp)
        (hmust jhp t hs) hbl

end GeneralityOfGEL

end Prosa.Results.Generality.Gel
