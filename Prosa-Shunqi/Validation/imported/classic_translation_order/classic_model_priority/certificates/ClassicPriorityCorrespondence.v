From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From prosa Require Import classic.model.time classic.util.list classic.model.arrival.basic.arrival_sequence classic.model.priority.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedClassicPriority.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence ClassicPriorityBase ClassicPriorityList.

Module I := ImportedClassicPriority.
Local Open Scope nat_scope.

(** Certificates for [classic/model/priority.v] (ProsaBuddy classic, commit f692cb7).

    Inputs: the job and task types are [eqType]s, identified, with the Lean
    [DecidableEq] instances given by the eqTypes' decision procedures
    ([ct_decidable_eq]); [job_task] and jobs identified; times by [SubNatRel];
    job/task parameters [X -> time] pointwise through [SubNatRel] ([CpParRel]);
    Boolean relations (FP and JLFP policies, [rel T]) pointwise ([CpRelRel]);
    JLDP policies pointwise on related times ([CpJldpRel]); sequences
    elementwise; arrival sequences pointwise on related times ([CpArrRel], as for
    the accepted classic arrival_sequence certificate); all with two-way totals.
    MathComp's [reflexive]/[irreflexive]/[transitive] on Boolean relations are
    the Lean helpers [reflexiveB]/[irreflexiveB]/[transitiveB] (same binder
    order); all definitions compute to related values on related inputs.

    Statements: the source side is the exact elaborated type of the pinned lemma
    (via [type of]; the source proof is not used).  For
    [EDF_respects_sequential_jobs], whose Rocq and Lean binder lists put
    [task_deadline : Task -> time] before the job type, the job type is fixed as
    an [eqType] with its canonical Lean instance and [task_deadline] stays
    universally quantified on both sides. *)

Ltac type_of_term t := let T := type of t in exact T.
Notation cid := (fun z => z).

(* ------------------------------------------------------------------ *)
(** * Generic covers *)

Lemma cp_forall_cover (A B : Type) (Rel : A -> B -> SProp) (toB : A -> B) (toA : B -> A)
    (HB : forall a, Rel a (toB a)) (HA : forall b, Rel (toA b) b) (PR : A -> Prop) (PL : B -> SProp) :
  (forall a b, Rel a b -> PropSPropRel (PR a) (PL b)) -> PropSPropRel (forall a, PR a) (forall b, PL b).
Proof.
  intro H. apply prop_sprop_rel_intro.
  - intros HR b. exact (prop_to_sprop _ _ (H _ _ (HA b)) (HR _)).
  - intro HL. apply strictly_inhabits. intro a. exact (sprop_to_prop _ _ (H _ _ (HB a)) (HL _)).
Qed.

Lemma cp_mem (T : eqType) x s sL : ClListRel cid s sL ->
  PropSPropRel (x \in s) (I.Membership_mem T (I.List T) (I.List_instMembership T) sL x).
Proof. exact (cl_mem_rel_list T T cid cid (fun _ => Logic.eq_refl _) x s sL). Qed.

Definition CpParRel (T : Type) (pR : T -> nat) (pL : T -> Lean.Nat) : SProp := forall x, SubNatRel (pR x) (pL x).

Lemma cp_forall_par (T : Type) (PR : (T -> nat) -> Prop) (PL : (T -> Lean.Nat) -> SProp) :
  (forall pR pL, CpParRel T pR pL -> PropSPropRel (PR pR) (PL pL)) -> PropSPropRel (forall p, PR p) (forall p, PL p).
Proof.
  exact (cp_forall_cover _ _ (CpParRel T) (fun pR j => sub_nat_to_imported (pR j)) (fun pL j => sub_nat_to_rocq (pL j))
           (fun pR j => sub_nat_rel_canonical (pR j)) (fun pL j => sub_nat_rel_surjective (pL j)) PR PL).
Qed.

Definition CpRelRel (T : Type) (rR : T -> T -> bool) (rL : T -> T -> I.Bool) : SProp :=
  forall a b, CtBoolRel (rR a b) (rL a b).

Lemma cp_rel_canonical (T : Type) (rR : T -> T -> bool) : CpRelRel T rR (fun a b => ct_b2l (rR a b)).
Proof. intros a b. exact (ct_bool_canonical _). Qed.

Lemma cp_rel_surjective (T : Type) (rL : T -> T -> I.Bool) : CpRelRel T (fun a b => ct_l2b (rL a b)) rL.
Proof. intros a b. exact (ct_bool_surjective _). Qed.

Lemma cp_forall_rel (T : Type) (PR : (T -> T -> bool) -> Prop) (PL : (T -> T -> I.Bool) -> SProp) :
  (forall rR rL, CpRelRel T rR rL -> PropSPropRel (PR rR) (PL rL)) -> PropSPropRel (forall r, PR r) (forall r, PL r).
Proof.
  exact (cp_forall_cover _ _ (CpRelRel T) (fun rR a b => ct_b2l (rR a b)) (fun rL a b => ct_l2b (rL a b))
           (cp_rel_canonical T) (cp_rel_surjective T) PR PL).
Qed.

Definition CpJldpRel (T : Type) (rR : nat -> T -> T -> bool) (rL : Lean.Nat -> T -> T -> I.Bool) : SProp :=
  forall tR tL, SubNatRel tR tL -> CpRelRel T (rR tR) (rL tL).

Lemma cp_jldp_canonical (T : Type) (rR : nat -> T -> T -> bool) :
  CpJldpRel T rR (fun tL a b => ct_b2l (rR (sub_nat_to_rocq tL) a b)).
Proof.
  intros tR tL Ht a b. have E := cl_nat_logic _ _ Ht. subst tL. rewrite sub_nat_rocq_roundtrip.
  exact (ct_bool_canonical _).
Qed.

Lemma cp_jldp_surjective (T : Type) (rL : Lean.Nat -> T -> T -> I.Bool) :
  CpJldpRel T (fun tR a b => ct_l2b (rL (sub_nat_to_imported tR) a b)) rL.
Proof. intros tR tL Ht a b. have E := cl_nat_logic _ _ Ht. subst tL. exact (ct_bool_surjective _). Qed.

(* ------------------------------------------------------------------ *)
(** * Arrival sequences *)

Section Arr.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).
Notation LArr := (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrival_sequence Job dJ).

Definition CpArrRel (aR : ArrivalSequence.arrival_sequence Job) (aL : LArr) : SProp :=
  forall tR tL, SubNatRel tR tL -> ClListRel cid (aR tR) (aL tL).

Definition cp_arr_to_target (aR : ArrivalSequence.arrival_sequence Job) : LArr :=
  fun tL => cl_map cid (aR (sub_nat_to_rocq tL)).

Definition cp_arr_to_source (aL : LArr) : ArrivalSequence.arrival_sequence Job :=
  fun tR => cl_unmap cid (aL (sub_nat_to_imported tR)).

Lemma cp_arr_canonical aR : CpArrRel aR (cp_arr_to_target aR).
Proof.
  intros tR tL Ht. have E := cl_nat_logic _ _ Ht. subst tL.
  apply: coq_eq_to_imported_eq. rewrite /cp_arr_to_target sub_nat_rocq_roundtrip. reflexivity.
Qed.

Lemma cp_arr_surjective aL : CpArrRel (cp_arr_to_source aL) aL.
Proof.
  intros tR tL Ht. have E := cl_nat_logic _ _ Ht. subst tL.
  apply: coq_eq_to_imported_eq. exact (cl_map_unmap cid cid (fun _ => Logic.eq_refl _) _).
Qed.

Lemma cp_forall_arr (PR : ArrivalSequence.arrival_sequence Job -> Prop) (PL : LArr -> SProp) :
  (forall aR aL, CpArrRel aR aL -> PropSPropRel (PR aR) (PL aL)) -> PropSPropRel (forall a, PR a) (forall a, PL a).
Proof. exact (cp_forall_cover _ _ CpArrRel cp_arr_to_target cp_arr_to_source cp_arr_canonical cp_arr_surjective PR PL). Qed.

Lemma cp_arrives_in aR aL (Ha : CpArrRel aR aL) j :
  PropSPropRel (ArrivalSequence.arrives_in aR j)
    (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrives_in Job dJ aL j).
Proof. apply: ct_exists_nat => tR tL Ht. exact (cp_mem Job j _ _ (Ha tR tL Ht)). Qed.
End Arr.

(* ------------------------------------------------------------------ *)
(** * Definitions *)

Section Defs.
Variables (Task Job : eqType).
Notation dT := (ct_decidable_eq Task).
Notation dJ := (ct_decidable_eq Job).

Theorem Priority_FP_policy_correspondence :
  And (forall rR : Priority.FP_policy Task, CpRelRel Task rR (fun a b => ct_b2l (rR a b)))
      (forall rL : I.Prosa_Classic_Model_Priority_Priority_FP_policy Task dT, CpRelRel Task (fun a b => ct_l2b (rL a b)) rL).
Proof. exact (And_intro _ _ (cp_rel_canonical Task) (cp_rel_surjective Task)). Qed.

Theorem Priority_JLFP_policy_correspondence :
  And (forall rR : Priority.JLFP_policy Job, CpRelRel Job rR (fun a b => ct_b2l (rR a b)))
      (forall rL : I.Prosa_Classic_Model_Priority_Priority_JLFP_policy Job dJ, CpRelRel Job (fun a b => ct_l2b (rL a b)) rL).
Proof. exact (And_intro _ _ (cp_rel_canonical Job) (cp_rel_surjective Job)). Qed.

Theorem Priority_JLDP_policy_correspondence :
  And (forall rR : Priority.JLDP_policy Job, CpJldpRel Job rR (fun tL a b => ct_b2l (rR (sub_nat_to_rocq tL) a b)))
      (forall rL : I.Prosa_Classic_Model_Priority_Priority_JLDP_policy Job dJ,
         CpJldpRel Job (fun tR a b => ct_l2b (rL (sub_nat_to_imported tR) a b)) rL).
Proof. exact (And_intro _ _ (cp_jldp_canonical Job) (cp_jldp_surjective Job)). Qed.

Theorem Priority_FP_to_JLFP_correspondence (job_task : Job -> Task) rR rL (Hr : CpRelRel Task rR rL) :
  CpRelRel Job (Priority.FP_to_JLFP job_task rR)
    (I.Prosa_Classic_Model_Priority_Priority_FP_to_JLFP Task Job dT dJ job_task rL).
Proof. intros a b. exact (Hr (job_task a) (job_task b)). Qed.

Theorem Priority_FP_to_JLDP_correspondence (job_task : Job -> Task) rR rL (Hr : CpRelRel Task rR rL) :
  CpJldpRel Job (Priority.FP_to_JLDP job_task rR)
    (I.Prosa_Classic_Model_Priority_Priority_FP_to_JLDP Task Job dT dJ job_task rL).
Proof. intros tR tL _ a b. exact (Hr (job_task a) (job_task b)). Qed.

Theorem Priority_JLFP_to_JLDP_correspondence rR rL (Hr : CpRelRel Job rR rL) :
  CpJldpRel Job (Priority.JLFP_to_JLDP rR) (I.Prosa_Classic_Model_Priority_Priority_JLFP_to_JLDP Job dJ rL).
Proof. intros tR tL _. exact Hr. Qed.

Lemma cp_reflexive (T : Type) rR rL (Hr : CpRelRel T rR rL) :
  PropSPropRel (reflexive rR) (I.Prosa_Classic_Model_Priority_Priority_reflexiveB T rL).
Proof. apply: ct_forall_identity => x. exact (ct_bool_truth _ _ (Hr x x)). Qed.

Lemma cp_irreflexive (T : Type) rR rL (Hr : CpRelRel T rR rL) :
  PropSPropRel (irreflexive rR) (I.Prosa_Classic_Model_Priority_Priority_irreflexiveB T rL).
Proof. apply: ct_forall_identity => x. exact (ct_bool_false _ _ (Hr x x)). Qed.

Lemma cp_transitive (T : Type) rR rL (Hr : CpRelRel T rR rL) :
  PropSPropRel (transitive rR) (I.Prosa_Classic_Model_Priority_Priority_transitiveB T rL).
Proof.
  apply: ct_forall_identity => y. apply: ct_forall_identity => x. apply: ct_forall_identity => z.
  apply: ct_imp; first exact (ct_bool_truth _ _ (Hr x y)).
  apply: ct_imp; first exact (ct_bool_truth _ _ (Hr y z)).
  exact (ct_bool_truth _ _ (Hr x z)).
Qed.

Theorem Priority_FP_is_reflexive_correspondence rR rL (Hr : CpRelRel Task rR rL) :
  PropSPropRel (Priority.FP_is_reflexive rR) (I.Prosa_Classic_Model_Priority_Priority_FP_is_reflexive Task dT rL).
Proof. exact (cp_reflexive Task rR rL Hr). Qed.

Theorem Priority_FP_is_irreflexive_correspondence rR rL (Hr : CpRelRel Task rR rL) :
  PropSPropRel (Priority.FP_is_irreflexive rR) (I.Prosa_Classic_Model_Priority_Priority_FP_is_irreflexive Task dT rL).
Proof. exact (cp_irreflexive Task rR rL Hr). Qed.

Theorem Priority_FP_is_transitive_correspondence rR rL (Hr : CpRelRel Task rR rL) :
  PropSPropRel (Priority.FP_is_transitive rR) (I.Prosa_Classic_Model_Priority_Priority_FP_is_transitive Task dT rL).
Proof. exact (cp_transitive Task rR rL Hr). Qed.

Theorem Priority_FP_is_total_over_task_set_correspondence rR rL (Hr : CpRelRel Task rR rL) ts tsL (Hts : ClListRel cid ts tsL) :
  PropSPropRel (Priority.FP_is_total_over_task_set rR ts)
    (I.Prosa_Classic_Model_Priority_Priority_FP_is_total_over_task_set Task dT rL tsL).
Proof.
  apply: ct_forall_identity => x1. apply: ct_forall_identity => x2.
  apply: ct_imp; first exact (cp_mem Task x1 ts tsL Hts).
  apply: ct_imp; first exact (cp_mem Task x2 ts tsL Hts).
  exact (ct_or _ _ _ _ (ct_bool_truth _ _ (Hr x1 x2)) (ct_bool_truth _ _ (Hr x2 x1))).
Qed.

Theorem Priority_FP_is_antisymmetric_over_task_set_correspondence rR rL (Hr : CpRelRel Task rR rL) ts tsL (Hts : ClListRel cid ts tsL) :
  PropSPropRel (Priority.FP_is_antisymmetric_over_task_set rR ts)
    (I.Prosa_Classic_Model_Priority_Priority_FP_is_antisymmetric_over_task_set Task dT rL tsL).
Proof.
  apply: ct_forall_identity => x1. apply: ct_forall_identity => x2.
  apply: ct_imp; first exact (cp_mem Task x1 ts tsL Hts).
  apply: ct_imp; first exact (cp_mem Task x2 ts tsL Hts).
  apply: ct_imp; first exact (ct_bool_truth _ _ (Hr x1 x2)).
  apply: ct_imp; first exact (ct_bool_truth _ _ (Hr x2 x1)).
  exact (ct_eq_rel Task x1 x2).
Qed.

Theorem Priority_JLFP_is_reflexive_correspondence rR rL (Hr : CpRelRel Job rR rL) :
  PropSPropRel (Priority.JLFP_is_reflexive rR) (I.Prosa_Classic_Model_Priority_Priority_JLFP_is_reflexive Job dJ rL).
Proof. exact (cp_reflexive Job rR rL Hr). Qed.

Theorem Priority_JLFP_is_irreflexive_correspondence rR rL (Hr : CpRelRel Job rR rL) :
  PropSPropRel (Priority.JLFP_is_irreflexive rR) (I.Prosa_Classic_Model_Priority_Priority_JLFP_is_irreflexive Job dJ rL).
Proof. exact (cp_irreflexive Job rR rL Hr). Qed.

Theorem Priority_JLFP_is_transitive_correspondence rR rL (Hr : CpRelRel Job rR rL) :
  PropSPropRel (Priority.JLFP_is_transitive rR) (I.Prosa_Classic_Model_Priority_Priority_JLFP_is_transitive Job dJ rL).
Proof. exact (cp_transitive Job rR rL Hr). Qed.

Theorem Priority_JLFP_is_total_correspondence aR aL (Ha : CpArrRel Job aR aL) rR rL (Hr : CpRelRel Job rR rL) :
  PropSPropRel (Priority.JLFP_is_total aR rR) (I.Prosa_Classic_Model_Priority_Priority_JLFP_is_total Job dJ aL rL).
Proof.
  apply: ct_forall_identity => j1. apply: ct_forall_identity => j2.
  apply: ct_imp; first exact (cp_arrives_in Job aR aL Ha j1).
  apply: ct_imp; first exact (cp_arrives_in Job aR aL Ha j2).
  exact (ct_bool_truth _ _ (ct_bool_or _ _ _ _ (Hr j1 j2) (Hr j2 j1))).
Qed.

Theorem Priority_JLFP_respects_sequential_jobs_correspondence (job_task : Job -> Task) jaR jaL (Hja : CpParRel Job jaR jaL)
    rR rL (Hr : CpRelRel Job rR rL) :
  PropSPropRel (Priority.JLFP_respects_sequential_jobs job_task jaR rR)
    (I.Prosa_Classic_Model_Priority_Priority_JLFP_respects_sequential_jobs Task Job dT dJ job_task jaL rL).
Proof.
  apply: ct_forall_identity => j1. apply: ct_forall_identity => j2.
  apply: ct_imp; first exact (ct_bool_truth _ _ (ct_decide_eq Task (job_task j1) (job_task j2))).
  apply: ct_imp; first exact (sub_nat_le_correspondence _ _ _ _ (Hja j1) (Hja j2)).
  exact (ct_bool_truth _ _ (Hr j1 j2)).
Qed.

Theorem Priority_JLDP_is_reflexive_correspondence rR rL (Hr : CpJldpRel Job rR rL) :
  PropSPropRel (Priority.JLDP_is_reflexive rR) (I.Prosa_Classic_Model_Priority_Priority_JLDP_is_reflexive Job dJ rL).
Proof. apply: ct_forall_nat => tR tL Ht. exact (cp_reflexive Job _ _ (Hr tR tL Ht)). Qed.

Theorem Priority_JLDP_is_irreflexive_correspondence rR rL (Hr : CpJldpRel Job rR rL) :
  PropSPropRel (Priority.JLDP_is_irreflexive rR) (I.Prosa_Classic_Model_Priority_Priority_JLDP_is_irreflexive Job dJ rL).
Proof. apply: ct_forall_nat => tR tL Ht. exact (cp_irreflexive Job _ _ (Hr tR tL Ht)). Qed.

Theorem Priority_JLDP_is_transitive_correspondence rR rL (Hr : CpJldpRel Job rR rL) :
  PropSPropRel (Priority.JLDP_is_transitive rR) (I.Prosa_Classic_Model_Priority_Priority_JLDP_is_transitive Job dJ rL).
Proof. apply: ct_forall_nat => tR tL Ht. exact (cp_transitive Job _ _ (Hr tR tL Ht)). Qed.

Theorem Priority_JLDP_is_total_correspondence aR aL (Ha : CpArrRel Job aR aL) rR rL (Hr : CpJldpRel Job rR rL) :
  PropSPropRel (Priority.JLDP_is_total aR rR) (I.Prosa_Classic_Model_Priority_Priority_JLDP_is_total Job dJ aL rL).
Proof.
  apply: ct_forall_identity => j1. apply: ct_forall_identity => j2. apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (cp_arrives_in Job aR aL Ha j1).
  apply: ct_imp; first exact (cp_arrives_in Job aR aL Ha j2).
  exact (ct_bool_truth _ _ (ct_bool_or _ _ _ _ (Hr tR tL Ht j1 j2) (Hr tR tL Ht j2 j1))).
Qed.

Theorem Priority_RM_correspondence pR pL (Hp : CpParRel Task pR pL) :
  CpRelRel Task (Priority.RM pR) (I.Prosa_Classic_Model_Priority_Priority_RM Task dT pL).
Proof. intros a b. exact (ct_decide_le _ _ _ _ (Hp a) (Hp b)). Qed.

Theorem Priority_DM_correspondence dR dL (Hd : CpParRel Task dR dL) :
  CpRelRel Task (Priority.DM dR) (I.Prosa_Classic_Model_Priority_Priority_DM Task dT dL).
Proof. intros a b. exact (ct_decide_le _ _ _ _ (Hd a) (Hd b)). Qed.

Theorem Priority_EDF_correspondence jaR jaL (Hja : CpParRel Job jaR jaL) jdR jdL (Hjd : CpParRel Job jdR jdL) :
  CpRelRel Job (Priority.EDF jaR jdR) (I.Prosa_Classic_Model_Priority_Priority_EDF Job dJ jaL jdL).
Proof.
  intros a b. exact (ct_decide_le _ _ _ _ (sub_add_correspondence _ _ _ _ (Hja a) (Hjd a))
                                          (sub_add_correspondence _ _ _ _ (Hja b) (Hjd b))).
Qed.

Theorem Priority_job_relative_dealine_correspondence tdR tdL (Htd : CpParRel Task tdR tdL) (job_task : Job -> Task) :
  CpParRel Job (Priority.job_relative_dealine tdR job_task)
    (I.Prosa_Classic_Model_Priority_Priority_job_relative_dealine Task dT tdL Job dJ job_task).
Proof. intro j. exact (Htd (job_task j)). Qed.

Theorem Priority_higher_priority_task_correspondence rR rL (Hr : CpRelRel Task rR rL) tsk tsk_other :
  CtBoolRel (Priority.higher_priority_task rR tsk tsk_other)
    (I.Prosa_Classic_Model_Priority_Priority_higher_priority_task Task dT rL tsk tsk_other).
Proof. exact (ct_bool_and _ _ _ _ (Hr tsk_other tsk) (ct_bool_not _ _ (ct_decide_eq Task tsk_other tsk))). Qed.

Theorem Priority_different_task_correspondence tsk tsk_other :
  CtBoolRel (Priority.different_task tsk tsk_other)
    (I.Prosa_Classic_Model_Priority_Priority_different_task Task dT tsk tsk_other).
Proof. exact (ct_bool_not _ _ (ct_decide_eq Task tsk_other tsk)). Qed.
End Defs.

(* ------------------------------------------------------------------ *)
(** * Statements *)

Definition src_RM_is_reflexive (Task : eqType) : Prop := ltac:(type_of_term (@Priority.RM_is_reflexive Task)).
Definition tgt_RM_is_reflexive (Task : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Model_Priority_Priority_RM_is_reflexive Task (ct_decidable_eq Task))).
Theorem Priority_RM_is_reflexive_correspondence (Task : eqType) :
  PropSPropRel (src_RM_is_reflexive Task) (tgt_RM_is_reflexive Task).
Proof.
  unfold src_RM_is_reflexive, tgt_RM_is_reflexive. apply: cp_forall_par => pR pL Hp.
  exact (Priority_FP_is_reflexive_correspondence Task _ _ (Priority_RM_correspondence Task pR pL Hp)).
Qed.

Definition src_RM_is_transitive (Task : eqType) : Prop := ltac:(type_of_term (@Priority.RM_is_transitive Task)).
Definition tgt_RM_is_transitive (Task : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Model_Priority_Priority_RM_is_transitive Task (ct_decidable_eq Task))).
Theorem Priority_RM_is_transitive_correspondence (Task : eqType) :
  PropSPropRel (src_RM_is_transitive Task) (tgt_RM_is_transitive Task).
Proof.
  unfold src_RM_is_transitive, tgt_RM_is_transitive. apply: cp_forall_par => pR pL Hp.
  exact (Priority_FP_is_transitive_correspondence Task _ _ (Priority_RM_correspondence Task pR pL Hp)).
Qed.

Definition src_DM_is_reflexive (Task : eqType) : Prop := ltac:(type_of_term (@Priority.DM_is_reflexive Task)).
Definition tgt_DM_is_reflexive (Task : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Model_Priority_Priority_DM_is_reflexive Task (ct_decidable_eq Task))).
Theorem Priority_DM_is_reflexive_correspondence (Task : eqType) :
  PropSPropRel (src_DM_is_reflexive Task) (tgt_DM_is_reflexive Task).
Proof.
  unfold src_DM_is_reflexive, tgt_DM_is_reflexive. apply: cp_forall_par => dR dL Hd.
  exact (Priority_FP_is_reflexive_correspondence Task _ _ (Priority_DM_correspondence Task dR dL Hd)).
Qed.

Definition src_DM_is_transitive (Task : eqType) : Prop := ltac:(type_of_term (@Priority.DM_is_transitive Task)).
Definition tgt_DM_is_transitive (Task : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Model_Priority_Priority_DM_is_transitive Task (ct_decidable_eq Task))).
Theorem Priority_DM_is_transitive_correspondence (Task : eqType) :
  PropSPropRel (src_DM_is_transitive Task) (tgt_DM_is_transitive Task).
Proof.
  unfold src_DM_is_transitive, tgt_DM_is_transitive. apply: cp_forall_par => dR dL Hd.
  exact (Priority_FP_is_transitive_correspondence Task _ _ (Priority_DM_correspondence Task dR dL Hd)).
Qed.

Definition src_any_reflexive_FP_respects_sequential_jobs (Job Task : eqType) : Prop :=
  ltac:(type_of_term (@Priority.any_reflexive_FP_respects_sequential_jobs Job Task)).
Definition tgt_any_reflexive_FP_respects_sequential_jobs (Job Task : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Model_Priority_Priority_any_reflexive_FP_respects_sequential_jobs
                        Job Task (ct_decidable_eq Job) (ct_decidable_eq Task))).
Theorem Priority_any_reflexive_FP_respects_sequential_jobs_correspondence (Job Task : eqType) :
  PropSPropRel (src_any_reflexive_FP_respects_sequential_jobs Job Task) (tgt_any_reflexive_FP_respects_sequential_jobs Job Task).
Proof.
  unfold src_any_reflexive_FP_respects_sequential_jobs, tgt_any_reflexive_FP_respects_sequential_jobs.
  apply: cp_forall_par => jaR jaL Hja. apply: ct_forall_identity => job_task.
  apply: cp_forall_rel => rR rL Hr.
  apply: ct_imp; first exact (Priority_FP_is_reflexive_correspondence Task rR rL Hr).
  exact (Priority_JLFP_respects_sequential_jobs_correspondence Task Job job_task jaR jaL Hja _ _
           (Priority_FP_to_JLFP_correspondence Task Job job_task rR rL Hr)).
Qed.

Definition src_EDF_is_reflexive (Job : eqType) : Prop := ltac:(type_of_term (@Priority.EDF_is_reflexive Job)).
Definition tgt_EDF_is_reflexive (Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Model_Priority_Priority_EDF_is_reflexive Job (ct_decidable_eq Job))).
Theorem Priority_EDF_is_reflexive_correspondence (Job : eqType) :
  PropSPropRel (src_EDF_is_reflexive Job) (tgt_EDF_is_reflexive Job).
Proof.
  unfold src_EDF_is_reflexive, tgt_EDF_is_reflexive.
  apply: cp_forall_par => jaR jaL Hja. apply: cp_forall_par => jdR jdL Hjd.
  exact (Priority_JLFP_is_reflexive_correspondence Job _ _ (Priority_EDF_correspondence Job jaR jaL Hja jdR jdL Hjd)).
Qed.

Definition src_EDF_is_transitive (Job : eqType) : Prop := ltac:(type_of_term (@Priority.EDF_is_transitive Job)).
Definition tgt_EDF_is_transitive (Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Model_Priority_Priority_EDF_is_transitive Job (ct_decidable_eq Job))).
Theorem Priority_EDF_is_transitive_correspondence (Job : eqType) :
  PropSPropRel (src_EDF_is_transitive Job) (tgt_EDF_is_transitive Job).
Proof.
  unfold src_EDF_is_transitive, tgt_EDF_is_transitive.
  apply: cp_forall_par => jaR jaL Hja. apply: cp_forall_par => jdR jdL Hjd.
  exact (Priority_JLFP_is_transitive_correspondence Job _ _ (Priority_EDF_correspondence Job jaR jaL Hja jdR jdL Hjd)).
Qed.

Definition src_EDF_is_total (Job : eqType) : Prop := ltac:(type_of_term (@Priority.EDF_is_total Job)).
Definition tgt_EDF_is_total (Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Model_Priority_Priority_EDF_is_total Job (ct_decidable_eq Job))).
Theorem Priority_EDF_is_total_correspondence (Job : eqType) :
  PropSPropRel (src_EDF_is_total Job) (tgt_EDF_is_total Job).
Proof.
  unfold src_EDF_is_total, tgt_EDF_is_total.
  apply: cp_forall_par => jaR jaL Hja. apply: cp_forall_par => jdR jdL Hjd. apply: cp_forall_arr => aR aL Ha.
  exact (Priority_JLFP_is_total_correspondence Job aR aL Ha _ _ (Priority_EDF_correspondence Job jaR jaL Hja jdR jdL Hjd)).
Qed.

Definition src_EDF_respects_sequential_jobs (Task Job : eqType) : Prop :=
  forall task_deadline : Task -> Time.time,
    ltac:(type_of_term (@Priority.EDF_respects_sequential_jobs Task task_deadline Job)).
Definition tgt_EDF_respects_sequential_jobs (Task Job : eqType) : SProp :=
  forall task_deadline : Task -> Lean.Nat,
    ltac:(type_of_term (I.Prosa_Classic_Model_Priority_Priority_EDF_respects_sequential_jobs
                          Task (ct_decidable_eq Task) task_deadline Job (ct_decidable_eq Job))).
Theorem Priority_EDF_respects_sequential_jobs_correspondence (Task Job : eqType) :
  PropSPropRel (src_EDF_respects_sequential_jobs Task Job) (tgt_EDF_respects_sequential_jobs Task Job).
Proof.
  unfold src_EDF_respects_sequential_jobs, tgt_EDF_respects_sequential_jobs.
  apply: cp_forall_par => tdR tdL Htd. apply: cp_forall_par => jaR jaL Hja. apply: ct_forall_identity => job_task.
  exact (Priority_JLFP_respects_sequential_jobs_correspondence Task Job job_task jaR jaL Hja _ _
           (Priority_EDF_correspondence Job jaR jaL Hja _ _
              (Priority_job_relative_dealine_correspondence Task Job tdR tdL Htd job_task))).
Qed.
