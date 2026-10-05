From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat.
From mathcomp Require Import ssralg ssrnum ssrint.
From prosa Require Import model.priority.gel.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedPriorityGel.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence NatSubCorrespondence
  PcoBaseAdapter PcoStaticOrder PcoDynamicOrder PriorityCoercionCorrespondence.

Module I := ImportedPriorityGel.

(** Certificates for [model/priority/gel.v].

    [offset] (MathComp [int]) and Lean's [Int] are related constructor-wise
    ([Posz n] / [Negz n] against [Int.ofNat n] / [Int.negSucc n], through the
    certified Nat relation) with roundtrips in both directions; the
    [PriorityPoint] class is related pointwise with two-way totals.  The Int
    operations in the Lean bodies are related through kernel-checked Lean
    constructor equations exported with the artifact.  [GEL] is related as
    [PdJLFPRel]; its reflexive/transitive/total statements (source side: the
    exact elaborated type of the pinned source lemma via [type of], the source
    proof is not used) through the accepted [pd_*_priorities_certificate]s. *)

Ltac type_of_term t := let T := type of t in exact T.

Notation P_ofNat_ofNat := I.Prosa_Validation_PriorityGelInterface_production_int_add_ofNat_ofNat.
Notation P_ofNat_negSucc_lt := I.Prosa_Validation_PriorityGelInterface_production_int_add_ofNat_negSucc_lt.
Notation P_ofNat_negSucc_ge := I.Prosa_Validation_PriorityGelInterface_production_int_add_ofNat_negSucc_ge.
Notation P_le_pp := I.Prosa_Validation_PriorityGelInterface_production_int_le_ofNat_ofNat.
Notation P_le_nn := I.Prosa_Validation_PriorityGelInterface_production_int_le_negSucc_negSucc.
Notation P_le_pn := I.Prosa_Validation_PriorityGelInterface_production_int_le_ofNat_negSucc.
Notation P_le_np := I.Prosa_Validation_PriorityGelInterface_production_int_le_negSucc_ofNat.
Notation P_cast := I.Prosa_Validation_PriorityGelInterface_production_nat_cast_eq.

(** ** The integer carrier *)

Definition gel_int_to_imported (z : int) : I.Int :=
  match z with
  | Posz n => I.Int_ofNat (sub_nat_to_imported n)
  | Negz n => I.Int_negSucc (sub_nat_to_imported n)
  end.

Definition gel_int_to_rocq (z : I.Int) : int :=
  match z with
  | I.Int_ofNat n => Posz (sub_nat_to_rocq n)
  | I.Int_negSucc n => Negz (sub_nat_to_rocq n)
  end.

Definition GelIntRel (zR : int) (zL : I.Int) : SProp := Lean.eq (gel_int_to_imported zR) zL.

Lemma offset_rocq_roundtrip_certificate (z : prosa.model.priority.gel.offset) :
  Logic.eq (gel_int_to_rocq (gel_int_to_imported z)) z.
Proof. destruct z as [n|n]; cbn; by rewrite sub_nat_rocq_roundtrip. Qed.

Lemma offset_imported_roundtrip_certificate (z : I.Prosa_Model_Priority_Gel_offset) :
  Lean.eq (gel_int_to_imported (gel_int_to_rocq z)) z.
Proof.
  destruct z as [n|n]; cbn.
  - exact (sub_imported_eq_congr I.Int_ofNat _ _ (sub_nat_imported_roundtrip n)).
  - exact (sub_imported_eq_congr I.Int_negSucc _ _ (sub_nat_imported_roundtrip n)).
Qed.

Definition gel_coq_false_to_target (H : Logic.False) : I.False :=
  match H return I.False with end.

(** ** Integer order *)

Lemma gel_lez_pp (m n : nat) : ((Posz m) <= (Posz n))%R = (leq m n). Proof. by []. Qed.
Lemma gel_lez_nn (m n : nat) : ((Negz m) <= (Negz n))%R = (leq n m). Proof. by []. Qed.
Lemma gel_lez_pn (m n : nat) : ((Posz m) <= (Negz n))%R = false. Proof. by []. Qed.
Lemma gel_lez_np (m n : nat) : ((Negz m) <= (Posz n))%R = true. Proof. by []. Qed.

Definition gel_target_int_le (a b : I.Int) : I.Bool :=
  I.Decidable_decide (I.LE_le_inst1 I.Int I.Int_instLEInt a b) (I.Int_decLe a b).

Lemma gel_le_canonical (x y : int) :
  PdBoolRel (x <= y)%R (gel_target_int_le (gel_int_to_imported x) (gel_int_to_imported y)).
Proof.
  unfold PdBoolRel, gel_target_int_le.
  destruct x as [m|m], y as [n|n]; cbn [gel_int_to_imported].
  - rewrite gel_lez_pp.
    exact (sub_imported_eq_trans _ _ _
      (pd_decide_le_related _ _ _ _ (sub_nat_rel_canonical m) (sub_nat_rel_canonical n))
      (sub_imported_eq_sym _ _ (P_le_pp _ _))).
  - rewrite gel_lez_pn. exact (sub_imported_eq_sym _ _ (P_le_pn _ _)).
  - rewrite gel_lez_np. exact (sub_imported_eq_sym _ _ (P_le_np _ _)).
  - rewrite gel_lez_nn.
    exact (sub_imported_eq_trans _ _ _
      (pd_decide_le_related _ _ _ _ (sub_nat_rel_canonical n) (sub_nat_rel_canonical m))
      (sub_imported_eq_sym _ _ (P_le_nn _ _))).
Qed.

Lemma gel_le_related xR xL yR yL :
  GelIntRel xR xL -> GelIntRel yR yL -> PdBoolRel (xR <= yR)%R (gel_target_int_le xL yL).
Proof.
  intros Hx Hy. unfold PdBoolRel.
  exact (sub_imported_eq_trans _ _ _ (gel_le_canonical xR yR)
    (sub_imported_eq_congr2 gel_target_int_le _ _ _ _ Hx Hy)).
Qed.

(** ** Adding a natural number to an integer *)

Lemma gel_addz_pp (a p : nat) : ((Posz a) + (Posz p))%R = Posz (addn a p). Proof. by []. Qed.
Lemma gel_addz_pn (a p : nat) :
  ((Posz a) + (Negz p))%R = (if ltn p a then Posz (subn a p.+1) else Negz (subn p a)).
Proof. by []. Qed.

Definition gel_target_add (x : Lean.Nat) (z : I.Int) : I.Int :=
  I.HAdd_hAdd_inst7 I.Int I.Int I.Int (I.instHAdd_inst1 I.Int I.Int_instAdd)
    (I.Nat_cast_inst1 I.Int I.instNatCastInt x) z.

Definition gel_target_add_ofNat (x : Lean.Nat) (z : I.Int) : I.Int :=
  I.HAdd_hAdd_inst7 I.Int I.Int I.Int (I.instHAdd_inst1 I.Int I.Int_instAdd) (I.Int_ofNat x) z.

Lemma gel_target_add_cast (x : Lean.Nat) (z : I.Int) :
  Lean.eq (gel_target_add_ofNat x z) (gel_target_add x z).
Proof.
  exact (sub_imported_eq_congr (fun y => I.HAdd_hAdd_inst7 I.Int I.Int I.Int
    (I.instHAdd_inst1 I.Int I.Int_instAdd) y z) _ _ (sub_imported_eq_sym _ _ (P_cast x))).
Qed.

Lemma gel_succ_related (p : nat) :
  SubNatRel p.+1 (nat_target_add (sub_nat_to_imported p) (sub_nat_to_imported 1)).
Proof.
  have H := nat_target_add_correspondence p (sub_nat_to_imported p) 1 (sub_nat_to_imported 1)
    (sub_nat_rel_canonical p) (sub_nat_rel_canonical 1).
  rewrite addn1 in H. exact H.
Qed.

Lemma gel_add_canonical (a : nat) (z : int) :
  GelIntRel ((Posz a) + z)%R (gel_target_add_ofNat (sub_nat_to_imported a) (gel_int_to_imported z)).
Proof.
  unfold GelIntRel, gel_target_add_ofNat.
  destruct z as [p|p]; cbn [gel_int_to_imported].
  - rewrite gel_addz_pp. cbn [gel_int_to_imported].
    refine (sub_imported_eq_trans _ _ _ _ (sub_imported_eq_sym _ _ (P_ofNat_ofNat _ _))).
    exact (sub_imported_eq_congr I.Int_ofNat _ _
      (nat_target_add_correspondence _ _ _ _ (sub_nat_rel_canonical a) (sub_nat_rel_canonical p))).
  - rewrite gel_addz_pn.
    have Hlt := sub_nat_lt_correspondence p (sub_nat_to_imported p) a (sub_nat_to_imported a)
      (sub_nat_rel_canonical p) (sub_nat_rel_canonical a).
    destruct (ltn p a) eqn:E; cbn [gel_int_to_imported].
    + refine (sub_imported_eq_trans _ _ _ _ (sub_imported_eq_sym _ _
        (P_ofNat_negSucc_lt _ _ (prop_to_sprop _ _ Hlt isT)))).
      exact (sub_imported_eq_congr I.Int_ofNat _ _
        (nat_target_sub_correspondence _ _ _ _ (sub_nat_rel_canonical a) (gel_succ_related p))).
    + refine (sub_imported_eq_trans _ _ _ _ (sub_imported_eq_sym _ _
        (P_ofNat_negSucc_ge _ _ (fun H => gel_coq_false_to_target
          (Bool.diff_false_true (sprop_to_prop _ _ Hlt H)))))).
      exact (sub_imported_eq_congr I.Int_negSucc _ _
        (nat_target_sub_correspondence _ _ _ _ (sub_nat_rel_canonical p) (sub_nat_rel_canonical a))).
Qed.

Lemma gel_add_related (aR : nat) (aL : Lean.Nat) (zR : int) (zL : I.Int) :
  SubNatRel aR aL -> GelIntRel zR zL -> GelIntRel ((aR%:R : int) + zR)%R (gel_target_add aL zL).
Proof.
  intros Ha Hz. rewrite natz. unfold GelIntRel.
  refine (sub_imported_eq_trans _ _ _ (gel_add_canonical aR zR) _).
  refine (sub_imported_eq_trans _ _ _ (gel_target_add_cast _ _) _).
  exact (sub_imported_eq_congr2 gel_target_add _ _ _ _ Ha Hz).
Qed.

(** ** The [PriorityPoint] class (input relation with two-way totals) *)

Section Classes.
  Context (Task : eqType).
  Let dT := pd_decidable_eq Task.

  Definition GelPriorityPointRel (ppR : prosa.model.priority.gel.PriorityPoint Task)
      (ppL : I.Prosa_Model_Priority_Gel_PriorityPoint Task dT) : SProp :=
    forall tsk : Task, GelIntRel (@prosa.model.priority.gel.task_priority_point Task ppR tsk)
      (I.Prosa_Model_Priority_Gel_PriorityPoint_task_priority_point Task dT ppL tsk).

  Lemma PriorityPoint_source_total ppR :
    GelPriorityPointRel ppR (I.Prosa_Model_Priority_Gel_PriorityPoint_mk Task dT
      (fun tsk => gel_int_to_imported (@prosa.model.priority.gel.task_priority_point Task ppR tsk))).
  Proof. intro tsk. exact (@Lean.eq_refl _ _). Qed.

  Lemma PriorityPoint_target_total ppL :
    GelPriorityPointRel ((fun tsk => gel_int_to_rocq
      (I.Prosa_Model_Priority_Gel_PriorityPoint_task_priority_point Task dT ppL tsk))
      : prosa.model.priority.gel.PriorityPoint Task) ppL.
  Proof. intro tsk. exact (offset_imported_roundtrip_certificate _). Qed.
End Classes.

(** ** Priority point and policy *)

Section Policy.
  Context (Job Task : eqType).
  Let dJ := pd_decidable_eq Job.
  Let dT := pd_decidable_eq Task.
  Variable ppR : prosa.model.priority.gel.PriorityPoint Task.
  Variable ppL : I.Prosa_Model_Priority_Gel_PriorityPoint Task dT.
  Hypothesis Hpp : GelPriorityPointRel Task ppR ppL.
  Variable jaR : prosa.behavior.job.JobArrival Job.
  Variable jaL : I.Prosa_Behavior_Job_JobArrival Job dJ.
  Hypothesis Hja : forall j : Job,
    SubNatRel (@prosa.behavior.job.job_arrival Job jaR j)
      (I.Prosa_Behavior_Job_JobArrival_job_arrival Job dJ jaL j).
  Variable jtR : prosa.model.task.concept.JobTask Job Task.
  Variable jtL : I.Prosa_Model_Task_Concept_JobTask Job dJ Task dT.
  Hypothesis Hjt : forall j : Job,
    Lean.eq (@prosa.model.task.concept.job_task Job Task jtR j)
      (I.Prosa_Model_Task_Concept_JobTask_job_task Job dJ Task dT jtL j).

  Theorem job_priority_point_correspondence (j : Job) :
    GelIntRel (@prosa.model.priority.gel.job_priority_point Job Task jtR ppR jaR j)
      (I.Prosa_Model_Priority_Gel_job_priority_point Job dJ Task dT jtL ppL jaL j).
  Proof.
    unfold prosa.model.priority.gel.job_priority_point.
    cbn [I.Prosa_Model_Priority_Gel_job_priority_point].
    exact (gel_add_related _ _ _ _ (Hja j)
      (sub_imported_eq_trans _ _ _ (Hpp _)
        (sub_imported_eq_congr
          (I.Prosa_Model_Priority_Gel_PriorityPoint_task_priority_point Task dT ppL) _ _ (Hjt j)))).
  Qed.

  Theorem GEL_correspondence :
    PdJLFPRel Job (@prosa.model.priority.gel.GEL Job Task ppR jaR jtR)
      (I.Prosa_Model_Priority_Gel_GEL Job dJ Task dT ppL jaL jtL).
  Proof.
    intros x y.
    exact (gel_le_related _ _ _ _ (job_priority_point_correspondence x)
      (job_priority_point_correspondence y)).
  Qed.

  Definition src_GEL_is_reflexive : Prop :=
    ltac:(type_of_term (@prosa.model.priority.gel.GEL_is_reflexive Task ppR Job jaR jtR)).
  Definition tgt_GEL_is_reflexive : SProp :=
    ltac:(type_of_term (@I.Prosa_Model_Priority_Gel_GEL_is_reflexive Task dT ppL Job dJ jaL jtL)).
  Theorem GEL_is_reflexive_correspondence : PropSPropRel src_GEL_is_reflexive tgt_GEL_is_reflexive.
  Proof. exact (pd_reflexive_job_priorities_certificate Job _ _ GEL_correspondence). Qed.

  Definition src_GEL_is_transitive : Prop :=
    ltac:(type_of_term (@prosa.model.priority.gel.GEL_is_transitive Task ppR Job jaR jtR)).
  Definition tgt_GEL_is_transitive : SProp :=
    ltac:(type_of_term (@I.Prosa_Model_Priority_Gel_GEL_is_transitive Task dT ppL Job dJ jaL jtL)).
  Theorem GEL_is_transitive_correspondence : PropSPropRel src_GEL_is_transitive tgt_GEL_is_transitive.
  Proof. exact (pd_transitive_job_priorities_certificate Job _ _ GEL_correspondence). Qed.

  Definition src_GEL_is_total : Prop :=
    ltac:(type_of_term (@prosa.model.priority.gel.GEL_is_total Task ppR Job jaR jtR)).
  Definition tgt_GEL_is_total : SProp :=
    ltac:(type_of_term (@I.Prosa_Model_Priority_Gel_GEL_is_total Task dT ppL Job dJ jaL jtL)).
  Theorem GEL_is_total_correspondence : PropSPropRel src_GEL_is_total tgt_GEL_is_total.
  Proof. exact (pd_total_job_priorities_certificate Job _ _ GEL_correspondence). Qed.
End Policy.
