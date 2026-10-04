-- Authoritative source:
-- ProsaBuddy classic Prosa (prosabuddy commit f692cb7479780cf6009493f373a309e13165201c)
-- source: classic/model/schedule/uni/sustainability.v
-- sha256: see Prosa-Shunqi/classic-prosa/comprehensive-classic/file_order.csv (rank 86)

import Prosa.Classic.Util.All
import Prosa.Classic.Model.Arrival.Basic.ArrivalSequence
import Prosa.Classic.Model.Schedule.Uni.Schedule
import Prosa.Classic.Model.Schedule.Uni.Schedulability

/-!
Sustainability of scheduling policies (Rocq module `Sustainability`).

Representation notes:
* `parameter_label` is a Lean `inductive` with the same constructors; Rocq's auto-generated eliminators
  (`parameter_label_rect/_ind/_rec/_sind`) correspond to Lean's auto-generated `rec`/`recOn`/`casesOn`.
* `Scheme Equality for parameter_label` generates `parameter_label_beq`, `internal_parameter_label_dec_bl`,
  `internal_parameter_label_dec_lb` and `parameter_label_eq_dec`; these are restated with the same names. The
  sumbool `{x = y} + {x <> y}` is Lean's informative `Decidable (x = y)`, built (as by `Scheme Equality`) from the
  Boolean equality and its two reflection lemmas.
* the MathComp equality specification of `parameter_label_beq` (`eqlabelP`) is the informative reflection
  `∀ x y, BoolReflect (x = y) (parameter_label_beq x y)`; the `HB.instance` (`hasDecEq`) registration is the derived
  `DecidableEq` instance, which is what `==` on labels (`decide (_ = _)`) uses.
* `type_of_label`/`default_val` are the same dependent definitions; the record `job_parameter` (constructor
  `param`) is a Lean structure with a dependently typed second field; `eq_rect` in the section-local
  `Let convert_parameter_type` (unfolded into `get_param_function`) is `Eq.rec` with the same motive.
* MathComp `find P s` (an index, `size s` when not found) is `s.findIdx P`; `nth d s i` is `s.getD i d`;
  `List.In x s` is `x ∈ s`; `l \notin s` is `l ∉ s`; `[seq p_label p | p <- s]` is `s.map p_label`;
  `uniq s` (a Boolean, the body of `has_unique_labels`) is `decide s.Nodup`.
* The section-local `Let example_params` is unfolded in the two examples.
* `H_classical_forall_exists` quantifies over `T : Type u`, the universe of `Job` (Rocq's floating `Type` is
  instantiated in the proof at `seq job_parameter`, which lives there).
-/

set_option linter.dupNamespace false
set_option linter.unusedVariables false

namespace Prosa.Classic.Model.Schedule.Uni.Sustainability.Sustainability

open Prosa.Classic.Model.Time.Time
open Prosa.Classic.Model.Arrival.Basic.ArrivalSequence.ArrivalSequence
open Prosa.Classic.Model.Schedule.Uni.Schedule.UniprocessorSchedule
open Prosa.Classic.Util.List (BoolReflect)

universe u

inductive parameter_label where
  | JOB_ARRIVAL
  | JOB_COST
  | JOB_DEADLINE
  | JOB_JITTER
  | JOB_SUSPENSION
  deriving DecidableEq

open parameter_label

def parameter_label_beq : parameter_label → parameter_label → Bool
  | JOB_ARRIVAL, JOB_ARRIVAL => true
  | JOB_COST, JOB_COST => true
  | JOB_DEADLINE, JOB_DEADLINE => true
  | JOB_JITTER, JOB_JITTER => true
  | JOB_SUSPENSION, JOB_SUSPENSION => true
  | _, _ => false

theorem internal_parameter_label_dec_bl :
    ∀ x : parameter_label, ∀ y : parameter_label, parameter_label_beq x y = true → x = y := by
  intro x y h
  cases x <;> cases y <;> first | rfl | exact absurd h (by decide)

theorem internal_parameter_label_dec_lb :
    ∀ x : parameter_label, ∀ y : parameter_label, x = y → parameter_label_beq x y = true := by
  intro x y h
  subst h
  cases x <;> rfl

def parameter_label_eq_dec (x y : parameter_label) : Decidable (x = y) :=
  if h : parameter_label_beq x y = true then isTrue (internal_parameter_label_dec_bl x y h)
  else isFalse (fun e => h (internal_parameter_label_dec_lb x y e))

def eqlabelP (x y : parameter_label) : BoolReflect (x = y) (parameter_label_beq x y) := by
  cases h : parameter_label_beq x y
  · exact BoolReflect.isFalse (fun e => by rw [internal_parameter_label_dec_lb x y e] at h; exact Bool.noConfusion h)
  · exact BoolReflect.isTrue (internal_parameter_label_dec_bl x y h)

def type_of_label {Job : Type u} [DecidableEq Job] (l : parameter_label) : Type u :=
  match l with
  | JOB_ARRIVAL => Job → instant
  | JOB_COST => Job → time
  | JOB_DEADLINE => Job → time
  | JOB_JITTER => Job → time
  | JOB_SUSPENSION => Job → time → duration

def default_val {Job : Type u} [DecidableEq Job] (l : parameter_label) : type_of_label (Job := Job) l :=
  match l with
  | JOB_ARRIVAL => fun _ => 0
  | JOB_COST => fun _ => 0
  | JOB_DEADLINE => fun _ => 0
  | JOB_JITTER => fun _ => 0
  | JOB_SUSPENSION => fun _ _ => 0

structure job_parameter (Job : Type u) [DecidableEq Job] where
  param ::
  p_label : parameter_label
  p_function : type_of_label (Job := Job) p_label

def find_param {Job : Type u} [DecidableEq Job] (l : parameter_label) (s : List (job_parameter Job)) :
    job_parameter Job :=
  s.getD (s.findIdx (fun x => decide (x.p_label = l))) (job_parameter.param l (default_val l))

def get_param_function {Job : Type u} [DecidableEq Job] (l : parameter_label) (p : job_parameter Job) :
    type_of_label (Job := Job) l :=
  match parameter_label_eq_dec p.p_label l with
  | isTrue EQ_PROOF => Eq.rec (motive := fun x _ => type_of_label (Job := Job) x) p.p_function EQ_PROOF
  | isFalse _ => default_val l

def return_param {Job : Type u} [DecidableEq Job] (l : parameter_label) (s : List (job_parameter Job)) :
    type_of_label (Job := Job) l :=
  get_param_function l (find_param l s)

theorem return_param_works1 {Job : Type u} [DecidableEq Job] (example_job_cost : Job → time)
    (example_job_suspension : Job → time → duration) :
    return_param JOB_COST [job_parameter.param JOB_COST example_job_cost,
      job_parameter.param JOB_SUSPENSION example_job_suspension] = example_job_cost := rfl

theorem return_param_works2 {Job : Type u} [DecidableEq Job] (example_job_cost : Job → time)
    (example_job_suspension : Job → time → duration) :
    return_param JOB_SUSPENSION [job_parameter.param JOB_COST example_job_cost,
      job_parameter.param JOB_SUSPENSION example_job_suspension] = example_job_suspension := rfl

def differ_only_by {Job : Type u} [DecidableEq Job] (variable_labels : List parameter_label)
    (s1 s2 : List (job_parameter Job)) : Prop :=
  ∀ (param param' : job_parameter Job), param ∈ s1 → param' ∈ s2 → param.p_label = param'.p_label →
    param.p_label ∉ variable_labels → param = param'

def labels_of {Job : Type u} [DecidableEq Job] (params : List (job_parameter Job)) : List parameter_label :=
  params.map (fun p => p.p_label)

def has_unique_labels {Job : Type u} [DecidableEq Job] (params : List (job_parameter Job)) : Bool :=
  decide (labels_of params).Nodup

def corresponding_labels {Job : Type u} [DecidableEq Job] (params : List (job_parameter Job))
    (labels : List parameter_label) : Prop :=
  ∀ l, l ∈ labels_of params ↔ l ∈ labels

/-- LEAN_HELPER: `find_param` on a non-empty list. -/
private theorem find_param_cons {Job : Type u} [DecidableEq Job] (l : parameter_label) (p0 : job_parameter Job)
    (s : List (job_parameter Job)) :
    find_param l (p0 :: s) = if p0.p_label = l then p0 else find_param l s := by
  unfold find_param
  rw [List.findIdx_cons]
  by_cases h : p0.p_label = l <;> simp [h]

theorem found_param_label {Job : Type u} [DecidableEq Job] :
    ∀ (params : List (job_parameter Job)) (p : job_parameter Job) (label : parameter_label),
      has_unique_labels params = true → p ∈ params → p.p_label = label →
        p = job_parameter.param label (return_param label params) := by
  intro params
  induction params with
  | nil => intro p label _ IN; simp at IN
  | cons p0 params' IH =>
    intro p label UNIQ IN EQ
    simp only [has_unique_labels, labels_of, List.map_cons, List.nodup_cons, decide_eq_true_eq] at UNIQ
    obtain ⟨NOTIN, UNIQ'⟩ := UNIQ
    rcases List.mem_cons.mp IN with EQ0 | IN'
    · subst EQ0
      subst EQ
      unfold return_param
      rw [find_param_cons, if_pos rfl]
      obtain ⟨lab, f⟩ := p
      cases lab <;> rfl
    · have NE : p0.p_label ≠ label := by
        intro E
        apply NOTIN
        rw [E, ← EQ]
        exact List.mem_map_of_mem IN'
      unfold return_param
      rw [find_param_cons, if_neg NE]
      exact IH p label (by unfold has_unique_labels labels_of; exact decide_eq_true UNIQ') IN' EQ

def sustainable_param_becomes_better {Job : Type u} [DecidableEq Job] (sustainable_param : parameter_label)
    (has_better_params : type_of_label (Job := Job) sustainable_param → type_of_label (Job := Job) sustainable_param →
      Prop)
    (params params' : List (job_parameter Job)) : Prop :=
  let P := return_param sustainable_param params
  let P' := return_param sustainable_param params'
  has_better_params P P'

def sustainable_and_varying_params_in {Job : Type u} [DecidableEq Job] (sustainable_param : parameter_label)
    (variable_params : List parameter_label) (params : List (job_parameter Job)) : Prop :=
  ∀ label, label ∈ sustainable_param :: variable_params → label ∈ labels_of params

def has_consistent_labels {Job : Type u} [DecidableEq Job] (all_labels : List parameter_label)
    (sustainable_param : parameter_label) (variable_params : List parameter_label)
    (params : List (job_parameter Job)) : Prop :=
  has_unique_labels params = true ∧
  corresponding_labels params all_labels ∧
  sustainable_and_varying_params_in sustainable_param variable_params params

def jobs_are_schedulable_with {Job : Type u} [DecidableEq Job]
    (is_schedulable : List (job_parameter Job) → schedule Job → Job → Bool)
    (belongs_to_task_model : List (job_parameter Job) → arrival_sequence Job → schedule Job → Prop)
    (params : List (job_parameter Job)) : Prop :=
  ∀ arr_seq sched j, belongs_to_task_model params arr_seq sched → is_schedulable params sched j = true

def jobs_are_V_schedulable_with {Job : Type u} [DecidableEq Job] (all_labels : List parameter_label)
    (is_schedulable : List (job_parameter Job) → schedule Job → Job → Bool)
    (belongs_to_task_model : List (job_parameter Job) → arrival_sequence Job → schedule Job → Prop)
    (sustainable_param : parameter_label) (variable_params : List parameter_label)
    (params : List (job_parameter Job)) : Prop :=
  ∀ (similar_params : List (job_parameter Job)),
    has_consistent_labels all_labels sustainable_param variable_params similar_params →
    differ_only_by variable_params params similar_params →
    jobs_are_schedulable_with is_schedulable belongs_to_task_model similar_params

def weakly_sustainable {Job : Type u} [DecidableEq Job] (all_labels : List parameter_label)
    (is_schedulable : List (job_parameter Job) → schedule Job → Job → Bool)
    (belongs_to_task_model : List (job_parameter Job) → arrival_sequence Job → schedule Job → Prop)
    (sustainable_param : parameter_label)
    (has_better_params : type_of_label (Job := Job) sustainable_param → type_of_label (Job := Job) sustainable_param →
      Prop)
    (variable_params : List parameter_label) : Prop :=
  ∀ (params better_params : List (job_parameter Job)),
    has_consistent_labels all_labels sustainable_param variable_params params →
    has_consistent_labels all_labels sustainable_param variable_params better_params →
    differ_only_by [sustainable_param] params better_params →
    sustainable_param_becomes_better sustainable_param has_better_params params better_params →
    jobs_are_V_schedulable_with all_labels is_schedulable belongs_to_task_model sustainable_param variable_params
      params →
    jobs_are_schedulable_with is_schedulable belongs_to_task_model better_params

def sustainable_param_becomes_worse {Job : Type u} [DecidableEq Job] (sustainable_param : parameter_label)
    (has_better_params : type_of_label (Job := Job) sustainable_param → type_of_label (Job := Job) sustainable_param →
      Prop)
    (params params' : List (job_parameter Job)) : Prop :=
  let P := return_param sustainable_param params
  let P' := return_param sustainable_param params'
  has_better_params P' P

def jobs_are_not_schedulable_with {Job : Type u} [DecidableEq Job]
    (is_schedulable : List (job_parameter Job) → schedule Job → Job → Bool)
    (belongs_to_task_model : List (job_parameter Job) → arrival_sequence Job → schedule Job → Prop)
    (params : List (job_parameter Job)) : Prop :=
  ∃ arr_seq sched j, belongs_to_task_model params arr_seq sched ∧ (!is_schedulable params sched j) = true

def weakly_sustainable_contrapositive {Job : Type u} [DecidableEq Job] (all_labels : List parameter_label)
    (is_schedulable : List (job_parameter Job) → schedule Job → Job → Bool)
    (belongs_to_task_model : List (job_parameter Job) → arrival_sequence Job → schedule Job → Prop)
    (sustainable_param : parameter_label)
    (has_better_params : type_of_label (Job := Job) sustainable_param → type_of_label (Job := Job) sustainable_param →
      Prop)
    (variable_params : List parameter_label) : Prop :=
  ∀ params params_worse,
    has_consistent_labels all_labels sustainable_param variable_params params →
    has_consistent_labels all_labels sustainable_param variable_params params_worse →
    jobs_are_not_schedulable_with is_schedulable belongs_to_task_model params →
    differ_only_by [sustainable_param] params params_worse →
    sustainable_param_becomes_worse sustainable_param has_better_params params params_worse →
    ∃ params_worse',
      has_consistent_labels all_labels sustainable_param variable_params params_worse' ∧
      differ_only_by variable_params params_worse params_worse' ∧
      jobs_are_not_schedulable_with is_schedulable belongs_to_task_model params_worse'

/-- LEAN_HELPER: `differ_only_by [l]` is symmetric. -/
private theorem differ_only_by_symm {Job : Type u} [DecidableEq Job] (labels : List parameter_label)
    (s1 s2 : List (job_parameter Job)) (DIFF : differ_only_by labels s1 s2) : differ_only_by labels s2 s1 := by
  intro p p' IN IN' EQ NOTIN
  exact (DIFF p' p IN' IN EQ.symm (EQ ▸ NOTIN)).symm

theorem weak_sustainability_equivalence {Job : Type u} [DecidableEq Job] (all_labels : List parameter_label)
    (is_schedulable : List (job_parameter Job) → schedule Job → Job → Bool)
    (belongs_to_task_model : List (job_parameter Job) → arrival_sequence Job → schedule Job → Prop)
    (sustainable_param : parameter_label)
    (has_better_params : type_of_label (Job := Job) sustainable_param → type_of_label (Job := Job) sustainable_param →
      Prop)
    (variable_params : List parameter_label)
    (H_classical_forall_exists : ∀ (T : Type u) (P : T → Prop), ¬ (∀ x, ¬ P x) → ∃ x, P x)
    (H_classical_and_or : ∀ (P Q : Prop), ¬ (P ∧ Q) → ¬ P ∨ ¬ Q) :
    weakly_sustainable all_labels is_schedulable belongs_to_task_model sustainable_param has_better_params
        variable_params ↔
      weakly_sustainable_contrapositive all_labels is_schedulable belongs_to_task_model sustainable_param
        has_better_params variable_params := by
  constructor
  · intro WEAK params params_worse CONS CONSworse NOTSCHED DIFF WORSE
    apply H_classical_forall_exists
    intro ALL
    have W := WEAK params_worse params CONSworse CONS (differ_only_by_symm _ _ _ DIFF) WORSE (by
      intro params' CONS' DIFF'
      rcases H_classical_and_or _ _ (ALL params') with BUG | A
      · exact absurd CONS' BUG
      rcases H_classical_and_or _ _ A with BUG | A
      · exact absurd DIFF' BUG
      intro arr_seq sched j BELONGS
      by_contra NOTSCHED'
      exact A ⟨arr_seq, sched, j, BELONGS, by simpa using NOTSCHED'⟩)
    obtain ⟨arr_seq, sched, j, BELONGS, NS⟩ := NOTSCHED
    rw [W arr_seq sched j BELONGS] at NS
    exact Bool.noConfusion NS
  · intro WEAK params better_params CONS CONSbetter DIFF BETTER VSCHED arr_seq sched j BELONGS
    by_contra NOTSCHED
    obtain ⟨pw, CONS', DIFF', NOTSCHED'⟩ := WEAK better_params params CONSbetter CONS
      ⟨arr_seq, sched, j, BELONGS, by simpa using NOTSCHED⟩ (differ_only_by_symm _ _ _ DIFF) BETTER
    obtain ⟨a', s', j', B', NS'⟩ := NOTSCHED'
    rw [VSCHED pw CONS' DIFF' a' s' j' B'] at NS'
    exact Bool.noConfusion NS'

def strongly_sustainable {Job : Type u} [DecidableEq Job] (all_labels : List parameter_label)
    (is_schedulable : List (job_parameter Job) → schedule Job → Job → Bool)
    (belongs_to_task_model : List (job_parameter Job) → arrival_sequence Job → schedule Job → Prop)
    (sustainable_param : parameter_label)
    (has_better_params : type_of_label (Job := Job) sustainable_param → type_of_label (Job := Job) sustainable_param →
      Prop) : Prop :=
  weakly_sustainable all_labels is_schedulable belongs_to_task_model sustainable_param has_better_params []

end Prosa.Classic.Model.Schedule.Uni.Sustainability.Sustainability
