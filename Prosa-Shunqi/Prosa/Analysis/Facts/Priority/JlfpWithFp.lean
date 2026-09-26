-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: analysis/facts/priority/jlfp_with_fp.v

import Prosa.Analysis.Facts.Priority.Classes
import Prosa.Analysis.Definitions.Priority.Classes
import Prosa.Analysis.Facts.Model.Workload

namespace Prosa.Analysis.Facts.Priority.JlfpWithFp

open Prosa.Behavior.Arrival_sequence
open Prosa.Behavior.Job
open Prosa.Behavior.Time
open Prosa.Model.Task.Concept
open Prosa.Model.Priority.Definitions
open Prosa.Model.Aggregate.Workload
open Prosa.Util.Sum
open Prosa.Analysis.Facts.Behavior.Arrivals
open Prosa.Analysis.Facts.Model.Workload
open Prosa.Analysis.Definitions.Priority.Classes
open Prosa.Analysis.Facts.Priority.Classes

/-! Representation notes: `a != b` is `decide (a ≠ b)`; `a == b` is
`decide (a = b)`; `\sum_(x <- xs | P x) F x` is the accepted
`sumFiltered xs P F`; `uniq` is `List.Nodup`; a Boolean in `Prop` position is
`= true`. The FP and JLFP policies are instance binders named `FP` and
`JLFP` as in the source. Binder orders and hypothesis sets follow the
elaborated types (unused section hypotheses are absent). -/

section WorkloadTaskSum

variable {Task : TaskType} [DecidableEq Task] {Job : JobType} [DecidableEq Job]
variable [JobArrival Job] [JobTask Job Task] [JobCost Job]
variable [FP : FP_policy Task] [JLFP : JLFP_policy Job]

/-- A task other than `tsk` with equal priority. -/
def other_ep_task (tsk tsk_o : Task) : Bool :=
  ep_task (FP := FP) tsk tsk_o && decide (tsk_o ≠ tsk)

/-- A higher-or-equal-priority job of another task with equal priority. -/
def hep_job_of_ep_other_task (j j' : Job) : Bool :=
  JLFP.hep_job j' j && ep_task (FP := FP) (job_task (Task := Task) j') (job_task (Task := Task) j) &&
    decide (job_task (Task := Task) j' ≠ job_task (Task := Task) j)

/-- A job of a task with strictly higher priority than `j`'s task. -/
def from_hp_task (j j' : Job) : Bool :=
  hp_task (FP := FP) (job_task (Task := Task) j') (job_task (Task := Task) j)

/-- A higher-or-equal-priority job of a strictly higher-priority task. -/
def hep_from_hp_task (j j' : Job) : Bool :=
  JLFP.hep_job j' j && hp_task (FP := FP) (job_task (Task := Task) j') (job_task (Task := Task) j)

/-- A higher-or-equal-priority job of an equal-priority task. -/
def hep_from_ep_task (j j' : Job) : Bool :=
  JLFP.hep_job j' j && ep_task (FP := FP) (job_task (Task := Task) j') (job_task (Task := Task) j)

end WorkloadTaskSum

/-- The workload of equal-priority jobs of other tasks splits by task. -/
theorem hep_workload_from_other_ep_partitioned_by_tasks {Task : TaskType} [DecidableEq Task]
    {Job : JobType} [DecidableEq Job] [JobArrival Job] [JobTask Job Task] [JobCost Job]
    [FP : FP_policy Task] [JLFP : JLFP_policy Job] (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
      ∀ ts : List Task, ts.Nodup → all_jobs_from_taskset arr_seq ts →
        ∀ (tsk : Task) (j : Job), job_of_task tsk j = true →
          ∀ t1 t2 : duration,
            workload_of_jobs (hep_job_of_ep_other_task (Task := Task) j) (arrivals_between arr_seq t1 t2) =
              sumFiltered ts (other_ep_task tsk)
                (fun tsk_o => workload_of_jobs
                  (fun j0 => hep_job_of_ep_other_task (Task := Task) j j0 &&
                    decide (job_task (Task := Task) j0 = tsk_o))
                  (arrivals_between arr_seq t1 t2)) := by
  intro hvalid ts huniq hfrom tsk j hj t1 t2
  have htsk : job_task (Task := Task) j = tsk := of_decide_eq_true hj
  refine workload_of_jobs_partitioned_by_tasks _ _ _ _ ?_ ?_
    (arrivals_uniq arr_seq hvalid.1 hvalid.2 t1 t2) huniq
  · intro j' hin
    exact hfrom j' (in_arrivals_implies_arrived arr_seq j' t1 t2 hin)
  · intro j' _ hp
    simp only [hep_job_of_ep_other_task, Bool.and_eq_true, decide_eq_true_eq] at hp
    obtain ⟨⟨_, hep⟩, hne⟩ := hp
    rw [htsk] at hep hne
    simp only [other_ep_task, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨by rw [ep_task_sym]; exact hep, hne⟩

/-- Under compatibility, restricting to higher-or-equal priority is vacuous
for jobs of strictly higher-priority tasks. -/
theorem hep_hp_workload_hp {Task : TaskType} [DecidableEq Task] {Job : JobType} [DecidableEq Job]
    [JobTask Job Task] [JobCost Job] [FP : FP_policy Task] [JLFP : JLFP_policy Job] :
    JLFP_FP_compatible JLFP FP →
      ∀ (arr_seq : arrival_sequence Job) (j : Job) (t1 t2 : duration),
        workload_of_jobs (hep_from_hp_task (Task := Task) j) (arrivals_between arr_seq t1 t2) =
          workload_of_jobs (from_hp_task (Task := Task) j) (arrivals_between arr_seq t1 t2) := by
  intro hc arr_seq j t1 t2
  unfold workload_of_jobs sumFiltered
  congr 2
  apply List.filter_congr
  intro j0 _
  unfold hep_from_hp_task from_hp_task
  cases hhp : hp_task (FP := FP) (job_task (Task := Task) j0) (job_task (Task := Task) j)
  · simp
  · simp [hp_task_implies_hep_job JLFP FP hc j0 j hhp]

/-- Under compatibility, the higher-or-equal-priority workload splits into
the parts from strictly-higher and equal-priority tasks. -/
theorem hep_workload_partitioning_taskwise {Task : TaskType} [DecidableEq Task] {Job : JobType}
    [DecidableEq Job] [JobTask Job Task] [JobCost Job] [FP : FP_policy Task] [JLFP : JLFP_policy Job] :
    JLFP_FP_compatible JLFP FP →
      ∀ (arr_seq : arrival_sequence Job) (j : Job) (t1 t2 : duration),
        workload_of_hep_jobs arr_seq j t1 t2 =
          workload_of_jobs (hep_from_hp_task (Task := Task) j) (arrivals_between arr_seq t1 t2) +
            workload_of_jobs (hep_from_ep_task (Task := Task) j) (arrivals_between arr_seq t1 t2) := by
  intro hc arr_seq j t1 t2
  unfold workload_of_hep_jobs workload_of_jobs
  apply sum_split_exhaustive_mutually_exclusive_preds
  · intro j0
    unfold hep_from_hp_task hep_from_ep_task hp_task ep_task
    cases hhep : JLFP.hep_job j0 j
    · simp
    · have ht := hep_job_implies_hep_task JLFP FP hc j0 j hhep
      simp [ht]
  · intro j0
    unfold hep_from_hp_task hep_from_ep_task hp_task ep_task
    cases FP.hep_task (job_task (Task := Task) j) (job_task (Task := Task) j0) <;> simp

end Prosa.Analysis.Facts.Priority.JlfpWithFp
