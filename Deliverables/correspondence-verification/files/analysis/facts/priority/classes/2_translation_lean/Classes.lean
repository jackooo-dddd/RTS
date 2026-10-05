-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: analysis/facts/priority/classes.v

import Prosa.Model.Priority.Classes
import Prosa.Analysis.Definitions.Priority.Classes

namespace Prosa.Analysis.Facts.Priority.Classes

open Prosa.Behavior.Job
open Prosa.Model.Task.Concept
open Prosa.Model.Priority.Definitions
open Prosa.Model.Priority.Coercion
open Prosa.Analysis.Definitions.Priority.Classes

/-! Basic facts about the priority classes. Binders follow the elaborated
source types (unused section classes are absent). Representation: `~ P` is
`¬ P`; `~~ b` is `(!b) = true`; Booleans in `Prop` position are `= true`;
`a != b` is `decide (a ≠ b)`; `same_task j j'` is
`decide (job_task j = job_task j')`; MathComp `irreflexive R`/`reflexive R`/
`transitive R`/`total R` are `∀ x, R x x = false`, `∀ x, R x x = true`,
`∀ y x z, R x y = true → R y z = true → R x z = true` and
`∀ x y, (R x y || R y x) = true`. -/

/-- A job is not another higher-or-equal-priority job of itself. -/
theorem another_hep_job_antireflexive {Job : JobType} [DecidableEq Job] [JLFP_policy Job]
    (j : Job) : ¬ another_hep_job j j = true := by
  unfold another_hep_job; simp

/-- For jobs of different tasks, `another_hep_job` is `hep_job`. -/
theorem another_hep_job_diff_task {Task : TaskType} [DecidableEq Task] {Job : JobType}
    [DecidableEq Job] [JobTask Job Task] [JLFP_policy Job] (j j' : Job) :
    (!same_task (Task := Task) j j') = true →
    another_hep_job j j' = hep_job j j' := by
  intro h
  unfold same_task at h
  unfold another_hep_job
  have hne : j ≠ j' := by
    intro e; subst e; simp at h
  simp [hne]

/-- Two jobs of the same task are not another-task higher-or-equal-priority jobs. -/
theorem another_task_hep_job_taskwise_antireflexive {Task : TaskType} [DecidableEq Task]
    {Job : JobType} [DecidableEq Job] [JobTask Job Task] [JLFP_policy Job]
    (tsk : Task) (j j' : Job) :
    job_of_task tsk j = true → job_of_task tsk j' = true →
    ¬ another_task_hep_job (Task := Task) j' j = true := by
  intro h1 h2
  unfold job_of_task at h1 h2
  unfold another_task_hep_job
  have e1 := of_decide_eq_true h1
  have e2 := of_decide_eq_true h2
  simp [e1, e2]

/-- `another_task_hep_job` restated through `another_hep_job`. -/
theorem another_task_hep_job_another_hep_job {Task : TaskType} [DecidableEq Task]
    {Job : JobType} [DecidableEq Job] [JobTask Job Task] [JLFP_policy Job] (j1 j2 : Job) :
    another_task_hep_job (Task := Task) j1 j2 =
      (another_hep_job j1 j2 &&
        decide (job_task (Task := Task) j1 ≠ job_task (Task := Task) j2)) := by
  unfold another_task_hep_job another_hep_job
  by_cases he : j1 = j2
  · subst he; simp
  · simp [he]

/-- `another_hep_job` splits into other-task and same-task parts. -/
theorem another_hep_job_split_task {Task : TaskType} [DecidableEq Task]
    {Job : JobType} [DecidableEq Job] [JobTask Job Task] [JLFP_policy Job] (j1 j2 : Job) :
    another_hep_job j1 j2 =
      (another_task_hep_job (Task := Task) j1 j2 ||
        another_hep_job_of_same_task (Task := Task) j1 j2) := by
  unfold another_task_hep_job another_hep_job_of_same_task another_hep_job
  by_cases he : j1 = j2
  · subst he; simp
  · by_cases ht : job_task (Task := Task) j1 = job_task (Task := Task) j2 <;>
      cases hep_job j1 j2 <;> simp [he, ht]

/-- The other-task and same-task parts are mutually exclusive. -/
theorem another_hep_job_exclusive {Task : TaskType} [DecidableEq Task]
    {Job : JobType} [DecidableEq Job] [JobTask Job Task] [JLFP_policy Job] (j1 j2 : Job) :
    (!(another_task_hep_job (Task := Task) j1 j2 &&
        another_hep_job_of_same_task (Task := Task) j1 j2)) = true := by
  unfold another_task_hep_job another_hep_job_of_same_task another_hep_job
  by_cases ht : job_task (Task := Task) j1 = job_task (Task := Task) j2 <;> simp [ht]

/-- Strict task priority is irreflexive. -/
theorem hp_task_irrefl {Task : TaskType} [DecidableEq Task] (FP_policy : FP_policy Task) :
    ∀ tsk : Task, hp_task (FP := FP_policy) tsk tsk = false := by
  intro tsk; unfold hp_task; cases FP_policy.hep_task tsk tsk <;> rfl

/-- Strict task priority implies higher-or-equal task priority. -/
theorem hp_hep_task {Task : TaskType} [DecidableEq Task] (FP_policy : FP_policy Task)
    (tsk1 tsk2 : Task) :
    hp_task (FP := FP_policy) tsk1 tsk2 = true → FP_policy.hep_task tsk1 tsk2 = true := by
  unfold hp_task; intro h; simp at h; exact h.1

/-- Equal task priority implies higher-or-equal task priority. -/
theorem ep_hep_task {Task : TaskType} [DecidableEq Task] (FP_policy : FP_policy Task)
    (tsk1 tsk2 : Task) :
    ep_task (FP := FP_policy) tsk1 tsk2 = true → FP_policy.hep_task tsk1 tsk2 = true := by
  unfold ep_task; intro h; simp at h; exact h.1

/-- Equal task priority excludes strict task priority. -/
theorem ep_not_hp_task {Task : TaskType} [DecidableEq Task] (FP_policy : FP_policy Task)
    (tsk1 tsk2 : Task) :
    ep_task (FP := FP_policy) tsk1 tsk2 = true → (!hp_task (FP := FP_policy) tsk1 tsk2) = true := by
  unfold ep_task hp_task; intro h; simp at h; simp [h.2]

/-- Equal task priority is symmetric. -/
theorem ep_task_sym {Task : TaskType} [DecidableEq Task] (FP_policy : FP_policy Task)
    (tsk1 tsk2 : Task) :
    ep_task (FP := FP_policy) tsk1 tsk2 = ep_task (FP := FP_policy) tsk2 tsk1 := by
  unfold ep_task; cases FP_policy.hep_task tsk1 tsk2 <;> cases FP_policy.hep_task tsk2 tsk1 <;> rfl

/-- Higher-or-equal task priority is strict or equal priority. -/
theorem hep_hp_ep_task {Task : TaskType} [DecidableEq Task] (FP_policy : FP_policy Task)
    (tsk1 tsk2 : Task) :
    FP_policy.hep_task tsk1 tsk2 =
      (hp_task (FP := FP_policy) tsk1 tsk2 || ep_task (FP := FP_policy) tsk1 tsk2) := by
  unfold hp_task ep_task
  cases FP_policy.hep_task tsk1 tsk2 <;> cases FP_policy.hep_task tsk2 tsk1 <;> rfl

/-- Equal task priority is reflexive when task priority is. -/
theorem eq_reflexive {Task : TaskType} [DecidableEq Task] (FP_policy : FP_policy Task) :
    (∀ tsk : Task, FP_policy.hep_task tsk tsk = true) →
    ∀ tsk : Task, ep_task (FP := FP_policy) tsk tsk = true := by
  intro h tsk; unfold ep_task; simp [h tsk]

/-- Strict task priority is transitive when task priority is. -/
theorem hp_trans {Task : TaskType} [DecidableEq Task] (FP_policy : FP_policy Task) :
    (∀ y x z : Task, FP_policy.hep_task x y = true → FP_policy.hep_task y z = true →
      FP_policy.hep_task x z = true) →
    ∀ y x z : Task, hp_task (FP := FP_policy) x y = true → hp_task (FP := FP_policy) y z = true →
      hp_task (FP := FP_policy) x z = true := by
  intro htr y x z hxy hyz
  unfold hp_task at *
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hxy hyz ⊢
  refine ⟨htr y x z hxy.1 hyz.1, ?_⟩
  cases hzx : FP_policy.hep_task z x
  · rfl
  · have := htr z y x hyz.1 hzx
    rw [this] at hxy; exact absurd hxy.2 (by decide)

/-- Strict then higher-or-equal task priority is strict. -/
theorem hp_hep_trans {Task : TaskType} [DecidableEq Task] (FP_policy : FP_policy Task) :
    (∀ y x z : Task, FP_policy.hep_task x y = true → FP_policy.hep_task y z = true →
      FP_policy.hep_task x z = true) →
    ∀ tsk1 tsk2 tsk3 : Task,
      hp_task (FP := FP_policy) tsk1 tsk2 = true → FP_policy.hep_task tsk2 tsk3 = true →
        hp_task (FP := FP_policy) tsk1 tsk3 = true := by
  intro htr x y z hxy hyz
  unfold hp_task at *
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hxy ⊢
  refine ⟨htr y x z hxy.1 hyz, ?_⟩
  cases hzx : FP_policy.hep_task z x
  · rfl
  · have := htr z y x hyz hzx
    rw [this] at hxy; exact absurd hxy.2 (by decide)

/-- Higher-or-equal then strict task priority is strict. -/
theorem hep_hp_trans {Task : TaskType} [DecidableEq Task] (FP_policy : FP_policy Task) :
    (∀ y x z : Task, FP_policy.hep_task x y = true → FP_policy.hep_task y z = true →
      FP_policy.hep_task x z = true) →
    ∀ tsk1 tsk2 tsk3 : Task,
      FP_policy.hep_task tsk1 tsk2 = true → hp_task (FP := FP_policy) tsk2 tsk3 = true →
        hp_task (FP := FP_policy) tsk1 tsk3 = true := by
  intro htr x y z hxy hyz
  unfold hp_task at *
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hyz ⊢
  refine ⟨htr y x z hxy hyz.1, ?_⟩
  cases hzx : FP_policy.hep_task z x
  · rfl
  · have := htr x z y hzx hxy
    rw [this] at hyz; exact absurd hyz.2 (by decide)

/-- Under a total task priority, not higher-or-equal is reverse strict. -/
theorem not_hep_hp_task {Task : TaskType} [DecidableEq Task] (FP_policy : FP_policy Task) :
    (∀ x y : Task, (FP_policy.hep_task x y || FP_policy.hep_task y x) = true) →
    ∀ tsk1 tsk2 : Task,
      (!FP_policy.hep_task tsk1 tsk2) = hp_task (FP := FP_policy) tsk2 tsk1 := by
  intro htot x y
  unfold hp_task
  have h := htot x y
  cases hxy : FP_policy.hep_task x y <;> cases hyx : FP_policy.hep_task y x <;>
    simp_all

/-- Under a total task priority, not strict is reverse higher-or-equal. -/
theorem not_hp_hep_task {Task : TaskType} [DecidableEq Task] (FP_policy : FP_policy Task) :
    (∀ x y : Task, (FP_policy.hep_task x y || FP_policy.hep_task y x) = true) →
    ∀ tsk1 tsk2 : Task,
      (!hp_task (FP := FP_policy) tsk1 tsk2) = FP_policy.hep_task tsk2 tsk1 := by
  intro htot x y
  unfold hp_task
  have h := htot x y
  cases hxy : FP_policy.hep_task x y <;> cases hyx : FP_policy.hep_task y x <;>
    simp_all

/-- Under a total task priority, not strict is not higher-or-equal or equal. -/
theorem nhp_ep_nhep_task {Task : TaskType} [DecidableEq Task] (FP_policy : FP_policy Task) :
    (∀ x y : Task, (FP_policy.hep_task x y || FP_policy.hep_task y x) = true) →
    ∀ tsk1 tsk2 : Task,
      (!hp_task (FP := FP_policy) tsk1 tsk2) =
        ((!FP_policy.hep_task tsk1 tsk2) || ep_task (FP := FP_policy) tsk1 tsk2) := by
  intro htot x y
  unfold hp_task ep_task
  have h := htot x y
  cases hxy : FP_policy.hep_task x y <;> cases hyx : FP_policy.hep_task y x <;>
    simp_all

/-- A reflexive FP policy respects sequential tasks. -/
theorem respects_sequential_tasks {Task : TaskType} [DecidableEq Task] {Job : JobType}
    [DecidableEq Job] [JobTask Job Task] [JobArrival Job] (FP : FP_policy Task) :
    reflexive_task_priorities FP →
    policy_respects_sequential_tasks (Task := Task) (FP_to_JLFP (Job := Job) FP) := by
  intro hrefl j1 j2 hsame _
  have e := of_decide_eq_true hsame
  show FP.hep_task (job_task (Task := Task) j1) (job_task (Task := Task) j2) = true
  rw [e]; exact hrefl _

/-- Compatibility: higher-or-equal job priority implies higher-or-equal task priority. -/
theorem hep_job_implies_hep_task {Task : TaskType} [DecidableEq Task] {Job : JobType}
    [DecidableEq Job] [JobTask Job Task] (JLFP : JLFP_policy Job) (FP : FP_policy Task) :
    JLFP_FP_compatible JLFP FP →
    ∀ j1 j2 : Job, JLFP.hep_job j1 j2 = true →
      FP.hep_task (job_task (Task := Task) j1) (job_task (Task := Task) j2) = true :=
  fun h => h.1

/-- Compatibility: strict task priority implies higher-or-equal job priority. -/
theorem hp_task_implies_hep_job {Task : TaskType} [DecidableEq Task] {Job : JobType}
    [DecidableEq Job] [JobTask Job Task] (JLFP : JLFP_policy Job) (FP : FP_policy Task) :
    JLFP_FP_compatible JLFP FP →
    ∀ j1 j2 : Job,
      hp_task (FP := FP) (job_task (Task := Task) j1) (job_task (Task := Task) j2) = true →
        JLFP.hep_job j1 j2 = true :=
  fun h => h.2

end Prosa.Analysis.Facts.Priority.Classes
