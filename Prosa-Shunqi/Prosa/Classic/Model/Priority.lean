-- Authoritative source:
-- ProsaBuddy classic Prosa (prosabuddy commit f692cb7479780cf6009493f373a309e13165201c)
-- source: classic/model/priority.v
-- sha256: see Prosa-Shunqi/classic-prosa/casestudy-translation/file_order.csv (rank 26)

import Prosa.Classic.Util.List
import Prosa.Classic.Model.Arrival.Basic.Task
import Prosa.Classic.Model.Arrival.Basic.Job
import Prosa.Classic.Model.Arrival.Basic.ArrivalSequence

/-!
Priority policies (Rocq module `Priority`).

Representation notes:
* `rel T` is `T → T → Bool`; MathComp's relation properties are kept with their
  binder order: `reflexive R := ∀ x, R x x`, `irreflexive R := ∀ x, R x x = false`,
  `transitive R := ∀ y x z, R x y → R y z → R x z` (Boolean results `= true`).
* Boolean comparisons are `Bool` (`decide …`); `a == b` is `decide (a = b)` and
  `a != b` is `!decide (a = b)`.
* Binder lists follow the Rocq contract, e.g.
  `any_reflexive_FP_respects_sequential_jobs {Job Task} job_arrival job_task …`.
-/

set_option linter.dupNamespace false

namespace Prosa.Classic.Model.Priority.Priority

open Prosa.Classic.Model.Time.Time
open Prosa.Classic.Model.Arrival.Basic.ArrivalSequence.ArrivalSequence
open Prosa.Classic.Util.List (total_over_list antisymmetric_over_list)

universe u v

/-! ### Policies -/

abbrev FP_policy (Task : Type u) [DecidableEq Task] := Task → Task → Bool

abbrev JLFP_policy (Job : Type u) [DecidableEq Job] := Job → Job → Bool

abbrev JLDP_policy (Job : Type u) [DecidableEq Job] := time → Job → Job → Bool

/-- LEAN_HELPER: MathComp `reflexive`. -/
def reflexiveB {T : Type u} (R : T → T → Bool) : Prop := ∀ x, R x x = true

/-- LEAN_HELPER: MathComp `irreflexive`. -/
def irreflexiveB {T : Type u} (R : T → T → Bool) : Prop := ∀ x, R x x = false

/-- LEAN_HELPER: MathComp `transitive` (binder order `y x z`). -/
def transitiveB {T : Type u} (R : T → T → Bool) : Prop :=
  ∀ y x z, R x y = true → R y z = true → R x z = true

/-! ### Generalization -/

def FP_to_JLFP {Task : Type u} {Job : Type v} [DecidableEq Task] [DecidableEq Job]
    (job_task : Job → Task) (task_hp : FP_policy Task) : JLFP_policy Job :=
  fun (jhigh jlow : Job) => task_hp (job_task jhigh) (job_task jlow)

def FP_to_JLDP {Task : Type u} {Job : Type v} [DecidableEq Task] [DecidableEq Job]
    (job_task : Job → Task) (task_hp : FP_policy Task) : JLDP_policy Job :=
  fun (_t : time) => FP_to_JLFP job_task task_hp

def JLFP_to_JLDP {Job : Type u} [DecidableEq Job] (job_hp : JLFP_policy Job) :
    JLDP_policy Job :=
  fun (_t : time) => job_hp

/-! ### Properties of FP policies -/

def FP_is_reflexive {Task : Type u} [DecidableEq Task] (task_priority : FP_policy Task) :
    Prop :=
  reflexiveB task_priority

def FP_is_irreflexive {Task : Type u} [DecidableEq Task] (task_priority : FP_policy Task) :
    Prop :=
  irreflexiveB task_priority

def FP_is_transitive {Task : Type u} [DecidableEq Task] (task_priority : FP_policy Task) :
    Prop :=
  transitiveB task_priority

def FP_is_total_over_task_set {Task : Type u} [DecidableEq Task]
    (task_priority : FP_policy Task) (ts : List Task) : Prop :=
  total_over_list task_priority ts

def FP_is_antisymmetric_over_task_set {Task : Type u} [DecidableEq Task]
    (task_priority : FP_policy Task) (ts : List Task) : Prop :=
  antisymmetric_over_list task_priority ts

/-! ### Properties of JLFP policies -/

def JLFP_is_reflexive {Job : Type u} [DecidableEq Job] (job_priority : JLFP_policy Job) :
    Prop :=
  reflexiveB job_priority

def JLFP_is_irreflexive {Job : Type u} [DecidableEq Job] (job_priority : JLFP_policy Job) :
    Prop :=
  irreflexiveB job_priority

def JLFP_is_transitive {Job : Type u} [DecidableEq Job] (job_priority : JLFP_policy Job) :
    Prop :=
  transitiveB job_priority

def JLFP_is_total {Job : Type u} [DecidableEq Job] (arr_seq : arrival_sequence Job)
    (job_priority : JLFP_policy Job) : Prop :=
  ∀ j1 j2,
    arrives_in arr_seq j1 →
    arrives_in arr_seq j2 →
    (job_priority j1 j2 || job_priority j2 j1) = true

def JLFP_respects_sequential_jobs {Task : Type u} {Job : Type v} [DecidableEq Task]
    [DecidableEq Job] (job_task : Job → Task) (job_arrival : Job → time)
    (job_priority : JLFP_policy Job) : Prop :=
  ∀ j1 j2,
    decide (job_task j1 = job_task j2) = true →
    job_arrival j1 ≤ job_arrival j2 →
    job_priority j1 j2 = true

/-! ### Properties of JLDP policies -/

def JLDP_is_reflexive {Job : Type u} [DecidableEq Job] (job_priority : JLDP_policy Job) :
    Prop :=
  ∀ t, reflexiveB (job_priority t)

def JLDP_is_irreflexive {Job : Type u} [DecidableEq Job] (job_priority : JLDP_policy Job) :
    Prop :=
  ∀ t, irreflexiveB (job_priority t)

def JLDP_is_transitive {Job : Type u} [DecidableEq Job] (job_priority : JLDP_policy Job) :
    Prop :=
  ∀ t, transitiveB (job_priority t)

def JLDP_is_total {Job : Type u} [DecidableEq Job] (arr_seq : arrival_sequence Job)
    (job_priority : JLDP_policy Job) : Prop :=
  ∀ j1 j2 t,
    arrives_in arr_seq j1 →
    arrives_in arr_seq j2 →
    (job_priority t j1 j2 || job_priority t j2 j1) = true

/-! ### Known FP policies -/

def RM {Task : Type u} [DecidableEq Task] (task_period : Task → time) (tsk1 tsk2 : Task) :
    Bool :=
  decide (task_period tsk1 ≤ task_period tsk2)

def DM {Task : Type u} [DecidableEq Task] (task_deadline : Task → time) (tsk1 tsk2 : Task) :
    Bool :=
  decide (task_deadline tsk1 ≤ task_deadline tsk2)

theorem RM_is_reflexive {Task : Type u} [DecidableEq Task] (task_period : Task → time) :
    FP_is_reflexive (RM task_period) := by
  intro tsk
  simp [RM]

theorem RM_is_transitive {Task : Type u} [DecidableEq Task] (task_period : Task → time) :
    FP_is_transitive (RM task_period) := by
  intro y x z h1 h2
  simp only [RM, decide_eq_true_eq] at *
  exact Nat.le_trans h1 h2

theorem DM_is_reflexive {Task : Type u} [DecidableEq Task] (task_deadline : Task → time) :
    FP_is_reflexive (DM task_deadline) := by
  intro tsk
  simp [DM]

theorem DM_is_transitive {Task : Type u} [DecidableEq Task] (task_deadline : Task → time) :
    FP_is_transitive (DM task_deadline) := by
  intro y x z h1 h2
  simp only [DM, decide_eq_true_eq] at *
  exact Nat.le_trans h1 h2

theorem any_reflexive_FP_respects_sequential_jobs {Job : Type u} {Task : Type v}
    [DecidableEq Job] [DecidableEq Task] (job_arrival : Job → time) (job_task : Job → Task) :
    ∀ job_priority : FP_policy Task,
      FP_is_reflexive job_priority →
      JLFP_respects_sequential_jobs job_task job_arrival (FP_to_JLFP job_task job_priority) := by
  intro HP REFL j1 j2 TSK _
  simp only [decide_eq_true_eq] at TSK
  simp only [FP_to_JLFP, TSK]
  exact REFL _

/-! ### Known JLFP policies -/

def EDF {Job : Type u} [DecidableEq Job] (job_arrival job_deadline : Job → time)
    (j1 j2 : Job) : Bool :=
  decide (job_arrival j1 + job_deadline j1 ≤ job_arrival j2 + job_deadline j2)

theorem EDF_is_reflexive {Job : Type u} [DecidableEq Job]
    (job_arrival job_deadline : Job → time) :
    JLFP_is_reflexive (EDF job_arrival job_deadline) := by
  intro j
  simp [EDF]

theorem EDF_is_transitive {Job : Type u} [DecidableEq Job]
    (job_arrival job_deadline : Job → time) :
    JLFP_is_transitive (EDF job_arrival job_deadline) := by
  intro y x z h1 h2
  simp only [EDF, decide_eq_true_eq] at *
  exact Nat.le_trans h1 h2

theorem EDF_is_total {Job : Type u} [DecidableEq Job]
    (job_arrival job_deadline : Job → time) (arr_seq : arrival_sequence Job) :
    JLFP_is_total arr_seq (EDF job_arrival job_deadline) := by
  intro x y _ _
  simp only [EDF, Bool.or_eq_true, decide_eq_true_eq]
  exact Nat.le_total _ _

def job_relative_dealine {Task : Type u} [DecidableEq Task] (task_deadline : Task → time)
    {Job : Type v} [DecidableEq Job] (job_task : Job → Task) (j : Job) : time :=
  task_deadline (job_task j)

theorem EDF_respects_sequential_jobs {Task : Type u} [DecidableEq Task]
    (task_deadline : Task → time) {Job : Type v} [DecidableEq Job]
    (job_arrival : Job → time) (job_task : Job → Task) :
    JLFP_respects_sequential_jobs job_task job_arrival
      (EDF job_arrival (job_relative_dealine task_deadline job_task)) := by
  intro j1 j2 TSK ARR
  simp only [decide_eq_true_eq] at TSK
  simp only [EDF, job_relative_dealine, TSK, decide_eq_true_eq]
  exact Nat.add_le_add_right ARR _

/-! ### Possibly interfering tasks -/

def higher_priority_task {sporadic_task : Type u} [DecidableEq sporadic_task]
    (higher_eq_priority : FP_policy sporadic_task) (tsk tsk_other : sporadic_task) : Bool :=
  higher_eq_priority tsk_other tsk && !decide (tsk_other = tsk)

def different_task {sporadic_task : Type u} [DecidableEq sporadic_task]
    (tsk tsk_other : sporadic_task) : Bool :=
  !decide (tsk_other = tsk)

end Prosa.Classic.Model.Priority.Priority
