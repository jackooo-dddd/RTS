-- Translated from: ../rt-proofs/classic/model/schedule/uni/sustainability.v
import Prosa.Classic.Model.Arrival.Basic.Arrival_sequence
import Prosa.Classic.Model.Schedule.Uni.Schedule
import Prosa.Classic.Model.Schedule.Uni.Schedulability
import Prosa.Classic.Model.Time
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Nodup
import Mathlib.Tactic

namespace Prosa.Classic.Model.Schedule.Uni.Sustainability

open Prosa.Classic.Model.Time
open Prosa.Classic.Model.Arrival.Basic.Arrival_sequence
open Prosa.Classic.Model.Schedule.Uni.Schedule

section SustainabilityDefs

variable (Job : Type _) [DecidableEq Job]

section DefiningParameters

section ParameterType

inductive parameter_label : Type
  | JOB_ARRIVAL
  | JOB_COST
  | JOB_DEADLINE
  | JOB_JITTER
  | JOB_SUSPENSION
  deriving DecidableEq, BEq

def type_of_label (l : parameter_label) : Type :=
  match l with
  | parameter_label.JOB_ARRIVAL => Job → Instant
  | parameter_label.JOB_COST => Job → Time
  | parameter_label.JOB_DEADLINE => Job → Time
  | parameter_label.JOB_JITTER => Job → Time
  | parameter_label.JOB_SUSPENSION => Job → Time → Duration

def default_val (l : parameter_label) : type_of_label Job l :=
  match l with
  | parameter_label.JOB_ARRIVAL => fun _ => 0
  | parameter_label.JOB_COST => fun _ => 0
  | parameter_label.JOB_DEADLINE => fun _ => 0
  | parameter_label.JOB_JITTER => fun _ => 0
  | parameter_label.JOB_SUSPENSION => fun _ _ => 0

structure job_parameter where
  p_label : parameter_label
  p_function : type_of_label Job p_label

def param (l : parameter_label) (f : type_of_label Job l) : job_parameter Job :=
  ⟨l, f⟩

end ParameterType

section ParameterLookup

def find_param (l : parameter_label) (s : List (job_parameter Job)) : job_parameter Job :=
  s.getD (s.findIdx (fun x => x.p_label == l)) (param Job l (default_val Job l))

def get_param_function (l : parameter_label) (p : job_parameter Job) : type_of_label Job l :=
  if h : p.p_label = l then
    h ▸ p.p_function
  else
    default_val Job l

def return_param (l : parameter_label) (s : List (job_parameter Job)) : type_of_label Job l :=
  get_param_function Job l (find_param Job l s)

theorem return_param_works1 (example_job_cost : Job → Time)
    (example_job_suspension : Job → Time → Duration) :
    return_param Job parameter_label.JOB_COST
      [param Job parameter_label.JOB_COST example_job_cost,
       param Job parameter_label.JOB_SUSPENSION example_job_suspension] =
    example_job_cost := by
  unfold return_param find_param get_param_function param List.findIdx List.getD
  simp only [List.findIdx.go, BEq.beq, default_val]
  rfl

theorem return_param_works2 (example_job_cost : Job → Time)
    (example_job_suspension : Job → Time → Duration) :
    return_param Job parameter_label.JOB_SUSPENSION
      [param Job parameter_label.JOB_COST example_job_cost,
       param Job parameter_label.JOB_SUSPENSION example_job_suspension] =
    example_job_suspension := by
  unfold return_param find_param get_param_function param List.findIdx List.getD
  simp only [List.findIdx.go, BEq.beq, default_val]
  rfl

end ParameterLookup

section Properties

def differ_only_by (variable_labels : List parameter_label)
    (s1 s2 : List (job_parameter Job)) : Prop :=
  ∀ (p p' : job_parameter Job),
    p ∈ s1 → p' ∈ s2 →
    p.p_label = p'.p_label →
    p.p_label ∉ variable_labels →
    p = p'

def labels_of (params : List (job_parameter Job)) : List parameter_label :=
  params.map (fun p => p.p_label)

def has_unique_labels (params : List (job_parameter Job)) : Prop :=
  (labels_of Job params).Nodup

def corresponding_labels (params : List (job_parameter Job))
    (labels : List parameter_label) : Prop :=
  ∀ l, l ∈ labels_of Job params ↔ l ∈ labels

theorem found_param_label :
    ∀ (params : List (job_parameter Job)) (p : job_parameter Job) (label : parameter_label),
      has_unique_labels Job params →
      p ∈ params →
      p.p_label = label →
      p = param Job label (return_param Job label params) := by
  intro params p label HUNIQ HIN HEQ
  subst HEQ
  induction params with
  | nil => exact absurd HIN (by simp)
  | cons p0 params' ih =>
    simp [has_unique_labels, labels_of] at HUNIQ
    obtain ⟨HNOTIN, HUNIQ'⟩ := HUNIQ
    cases HIN with
    | head =>
      -- p0 = p, and p.p_label = p.p_label
      unfold return_param find_param
      simp only [List.findIdx, List.findIdx.go]
      have hbeq_true : (p.p_label == p.p_label) = true := by
        cases p.p_label <;> rfl
      simp only [hbeq_true, cond_true]
      simp only [List.getD, List.getElem?_cons_zero, Option.getD_some]
      unfold get_param_function
      simp only [dite_true, param]
    | tail _ HIN' =>
      -- p ∈ params'
      have hne : p0.p_label ≠ p.p_label := by
        intro heq
        exact (HNOTIN p HIN') heq.symm
      -- Key: show return_param on (p0 :: params') = return_param on params' when p0.p_label ≠ p.p_label
      suffices h : return_param Job p.p_label (p0 :: params') = return_param Job p.p_label params' by
        rw [h]
        exact ih HUNIQ' HIN'
      -- Prove: return_param on cons = return_param on tail when head label differs
      -- Strategy: show find_param on cons = find_param on tail
      have findIdx_shift : ∀ (l : List (job_parameter Job)) (f : job_parameter Job → Bool) (n : Nat),
          List.findIdx.go f l (n + 1) = List.findIdx.go f l n + 1 := by
        intro l f n
        induction l generalizing n with
        | nil => simp [List.findIdx.go]
        | cons a l' ihl =>
          unfold List.findIdx.go
          cases f a
          · simp only [cond_false]; rw [show n + 1 + 1 = (n + 1) + 1 from rfl, ihl]
          · simp only [cond_true]
      have hbeq_false : (p0.p_label == p.p_label) = false := by
        cases hp0 : p0.p_label <;> cases hp : p.p_label <;>
          first | rfl | (exfalso; apply hne; rw [hp0, hp])
      -- Show find_param on cons = find_param on tail
      suffices hfp : find_param Job p.p_label (p0 :: params') = find_param Job p.p_label params' by
        simp only [return_param, hfp]
      simp only [find_param, List.findIdx, List.findIdx.go, hbeq_false, cond_false]
      rw [findIdx_shift]
      simp [List.getD, List.getElem?_cons_succ]

end Properties

end DefiningParameters

section SustainabilityPolicy

variable (all_labels : List parameter_label)

variable (is_schedulable :
    List (job_parameter Job) → schedule Job → Job → Bool)

variable (belongs_to_task_model :
    List (job_parameter Job) → arrival_sequence Job → schedule Job → Prop)

variable (sustainable_param : parameter_label)

variable (has_better_params : type_of_label Job sustainable_param →
    type_of_label Job sustainable_param → Prop)

def sustainable_param_becomes_better
    (params params' : List (job_parameter Job)) : Prop :=
  let P := return_param Job sustainable_param params
  let P' := return_param Job sustainable_param params'
  has_better_params P P'

section VaryingParameters

variable (variable_params : List parameter_label)

def sustainable_and_varying_params_in (params : List (job_parameter Job)) : Prop :=
  ∀ label,
    label ∈ (sustainable_param :: variable_params) →
    label ∈ labels_of Job params

def has_consistent_labels (params : List (job_parameter Job)) : Prop :=
  has_unique_labels Job params ∧
  corresponding_labels Job params all_labels ∧
  sustainable_and_varying_params_in Job sustainable_param variable_params params

def jobs_are_schedulable_with (params : List (job_parameter Job)) : Prop :=
  ∀ arr_seq sched j,
    belongs_to_task_model params arr_seq sched →
    is_schedulable params sched j = true

def jobs_are_V_schedulable_with (params : List (job_parameter Job)) : Prop :=
  ∀ (similar_params : List (job_parameter Job)),
    has_consistent_labels Job all_labels sustainable_param variable_params similar_params →
    differ_only_by Job variable_params params similar_params →
    jobs_are_schedulable_with Job is_schedulable belongs_to_task_model similar_params

def weakly_sustainable : Prop :=
  ∀ (params better_prms : List (job_parameter Job)),
    has_consistent_labels Job all_labels sustainable_param variable_params params →
    has_consistent_labels Job all_labels sustainable_param variable_params better_prms →
    differ_only_by Job [sustainable_param] params better_prms →
    sustainable_param_becomes_better Job sustainable_param has_better_params params better_prms →
    jobs_are_V_schedulable_with Job all_labels is_schedulable belongs_to_task_model
      sustainable_param variable_params params →
    jobs_are_schedulable_with Job is_schedulable belongs_to_task_model better_prms

section AlternativeDefinition

def sustainable_param_becomes_worse
    (params params' : List (job_parameter Job)) : Prop :=
  let P := return_param Job sustainable_param params
  let P' := return_param Job sustainable_param params'
  has_better_params P' P

def jobs_are_not_schedulable_with (params : List (job_parameter Job)) : Prop :=
  ∃ arr_seq sched j,
    belongs_to_task_model params arr_seq sched ∧
    is_schedulable params sched j = false

def weakly_sustainable_contrapositive : Prop :=
  ∀ (params params_worse : List (job_parameter Job)),
    has_consistent_labels Job all_labels sustainable_param variable_params params →
    has_consistent_labels Job all_labels sustainable_param variable_params params_worse →
    jobs_are_not_schedulable_with Job is_schedulable belongs_to_task_model params →
    differ_only_by Job [sustainable_param] params params_worse →
    sustainable_param_becomes_worse Job sustainable_param has_better_params params params_worse →
    ∃ params_worse',
      has_consistent_labels Job all_labels sustainable_param variable_params params_worse' ∧
      differ_only_by Job variable_params params_worse params_worse' ∧
      jobs_are_not_schedulable_with Job is_schedulable belongs_to_task_model params_worse'

theorem weak_sustainability_equivalence
    (H_classical_forall_exists :
      ∀ (T : Type _) (P : T → Prop), ¬ (∀ x, ¬ P x) → ∃ x, P x)
    (H_classical_and_or :
      ∀ (P Q : Prop), ¬ (P ∧ Q) → ¬ P ∨ ¬ Q) :
    weakly_sustainable Job all_labels is_schedulable belongs_to_task_model sustainable_param
      has_better_params variable_params ↔
    weakly_sustainable_contrapositive Job all_labels is_schedulable belongs_to_task_model
      sustainable_param has_better_params variable_params := by
  constructor
  · -- Forward: weakly_sustainable → weakly_sustainable_contrapositive
    intro WEAK params params_worse CONS CONSworse NOTSCHED DIFF WORSE
    -- Use classical reasoning: assume ¬∃ and derive contradiction
    by_contra hALL
    push_neg at hALL
    -- Apply WEAK with params_worse as "better" and params as base
    have hWEAK := WEAK params_worse params CONSworse CONS
    -- Build the differ_only_by for swapped direction
    have hDIFF : differ_only_by Job [sustainable_param] params_worse params := by
      intro p p' hIN hIN' hEQ hNOTIN
      exact (DIFF p' p hIN' hIN (Eq.symm hEQ) (hEQ ▸ hNOTIN)).symm
    have hWEAK2 := hWEAK hDIFF WORSE
    -- Build V-schedulability from ALL
    have hVSCHED : jobs_are_V_schedulable_with Job all_labels is_schedulable
        belongs_to_task_model sustainable_param variable_params params_worse := by
      intro params' CONS' DIFF' arr_seq sched j BELONGS
      by_contra NOTSCHED'
      have := hALL params' CONS' DIFF'
      apply this
      refine ⟨arr_seq, sched, j, BELONGS, ?_⟩
      revert NOTSCHED'; cases is_schedulable params' sched j <;> simp
    have hWEAK3 := hWEAK2 hVSCHED
    -- Contradiction with NOTSCHED
    obtain ⟨arr_seq, sched, j, BELONGS, hNOT⟩ := NOTSCHED
    have hSCHED := hWEAK3 arr_seq sched j BELONGS
    simp [hSCHED] at hNOT
  · -- Backward: weakly_sustainable_contrapositive → weakly_sustainable
    intro WEAK params better_params CONS CONSbetter DIFF BETTER VSCHED
    intro arr_seq sched j BELONGS
    by_contra NOTSCHED
    -- Apply WEAK with better_params and params
    have hWEAK := WEAK better_params params CONSbetter CONS
    have hNOTSCHED : jobs_are_not_schedulable_with Job is_schedulable belongs_to_task_model
        better_params := by
      refine ⟨arr_seq, sched, j, BELONGS, ?_⟩
      revert NOTSCHED; cases is_schedulable better_params sched j <;> simp
    have hWEAK2 := hWEAK hNOTSCHED
    have hDIFF : differ_only_by Job [sustainable_param] better_params params := by
      intro p p' hIN hIN' hEQ hNOTIN
      exact (DIFF p' p hIN' hIN (Eq.symm hEQ) (hEQ ▸ hNOTIN)).symm
    have hWEAK3 := hWEAK2 hDIFF BETTER
    obtain ⟨params_worse', CONS', DIFF', NOTSCHED'⟩ := hWEAK3
    -- Use V-schedulability
    have hVSCHED := VSCHED params_worse' CONS' DIFF'
    obtain ⟨arr_seq', sched', j', BELONGS', hNOT'⟩ := NOTSCHED'
    have hSCHED' := hVSCHED arr_seq' sched' j' BELONGS'
    simp [hSCHED'] at hNOT'

end AlternativeDefinition

end VaryingParameters

def strongly_sustainable : Prop :=
  weakly_sustainable Job all_labels is_schedulable belongs_to_task_model sustainable_param
    has_better_params []

end SustainabilityPolicy

end SustainabilityDefs

end Prosa.Classic.Model.Schedule.Uni.Sustainability
