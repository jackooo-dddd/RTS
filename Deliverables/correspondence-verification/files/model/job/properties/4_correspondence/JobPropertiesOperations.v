From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From prosa Require Import model.job.properties.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedJobProperties ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation
  LogicalRelation SubadditivityNatCorrespondence JobPropertiesBaseAdapter.

(** Minimal artifact-local operations needed by both v0.6 job-property
    definitions.  The Bool/List adapter is generated from an accepted,
    kernel-checked template for this exact imported module. *)

Definition jp_target_false_elim (Q : SProp)
    (H : ImportedJobProperties.False) : Q := match H return Q with end.

Lemma jp_decide_bool_correspondence (b : bool) (Q : SProp)
    (d : ImportedJobProperties.Decidable Q) :
  PropSPropRel (is_true b) Q ->
  JpBoolRel b (ImportedJobProperties.Decidable_decide Q d).
Proof.
  intro Hrel. unfold JpBoolRel.
  destruct d as [Hfalse | Htrue]; destruct b; cbn.
  - exact (jp_target_false_elim _
      (Hfalse (prop_to_sprop _ _ Hrel (Logic.eq_refl true)))).
  - exact (@Lean.eq_refl _ _).
  - exact (@Lean.eq_refl _ _).
  - exact (jp_target_false_elim _ (jp_coq_false_to_target
      (match sprop_to_prop _ _ Hrel Htrue with end))).
Qed.

Definition jp_target_decide_mem (T : eqType) (x : T)
    (xs : ImportedJobProperties.List T) : ImportedJobProperties.Bool :=
  ImportedJobProperties.Decidable_decide (jp_target_mem x xs)
    (ImportedJobProperties.List_instDecidableMemOfLawfulBEq T
      (ImportedJobProperties.instBEqOfDecidableEq T (jp_decidable_eq T))
      (ImportedJobProperties.instLawfulBEq T (jp_decidable_eq T)) x xs).

Lemma jp_decide_mem_related (T : eqType) (x : T)
    (xsR : seq T) (xsL : ImportedJobProperties.List T) :
  JpListRel xsR xsL ->
  JpBoolRel (x \in xsR) (jp_target_decide_mem T x xsL).
Proof.
  intro Hxs. apply jp_decide_bool_correspondence.
  exact (jp_membership_correspondence T x xsR xsL Hxs).
Qed.

Definition JpArrivalSequenceRel (T : eqType)
    (arrR : prosa.behavior.arrival_sequence.arrival_sequence T)
    (arrL : ImportedJobProperties.Prosa_Behavior_Arrival_sequence_arrival_sequence
      T (jp_decidable_eq T)) : SProp :=
  forall tR tL, SubNatRel tR tL -> JpListRel (arrR tR) (arrL tL).

Lemma jp_arrives_at_related (T : eqType)
    (arrR : prosa.behavior.arrival_sequence.arrival_sequence T)
    (arrL : ImportedJobProperties.Prosa_Behavior_Arrival_sequence_arrival_sequence
      T (jp_decidable_eq T)) (j : T) :
  JpArrivalSequenceRel T arrR arrL ->
  forall tR tL, SubNatRel tR tL ->
  JpBoolRel (prosa.behavior.arrival_sequence.arrives_at arrR j tR)
    (ImportedJobProperties.Prosa_Behavior_Arrival_sequence_arrives_at T
      (jp_decidable_eq T) arrL j tL).
Proof.
  intros Harr tR tL Ht. cbn.
  apply jp_decide_mem_related.
  exact (Harr tR tL Ht).
Qed.

Lemma jp_exists_nat_correspondence
    (PR : nat -> Prop) (PL : Lean.Nat -> SProp) :
  (forall nR nL, SubNatRel nR nL ->
    PropSPropRel (PR nR) (PL nL)) ->
  PropSPropRel (exists nR, PR nR)
    (ImportedJobProperties.Exists Lean.Nat PL).
Proof.
  intro HP. apply prop_sprop_rel_intro.
  - intros [nR Hn].
    exact (ImportedJobProperties.Exists_intro Lean.Nat PL
      (sub_nat_to_imported nR)
      (prop_to_sprop _ _
        (HP nR (sub_nat_to_imported nR) (sub_nat_rel_canonical nR)) Hn)).
  - intros [nL Hn]. apply strictly_inhabits.
    exists (sub_nat_to_rocq nL).
    exact (sprop_to_prop _ _
      (HP (sub_nat_to_rocq nL) nL (sub_nat_rel_surjective nL)) Hn).
Qed.

Lemma jp_arrives_in_related (T : eqType)
    (arrR : prosa.behavior.arrival_sequence.arrival_sequence T)
    (arrL : ImportedJobProperties.Prosa_Behavior_Arrival_sequence_arrival_sequence
      T (jp_decidable_eq T)) (j : T) :
  JpArrivalSequenceRel T arrR arrL ->
  PropSPropRel (prosa.behavior.arrival_sequence.arrives_in arrR j)
    (ImportedJobProperties.Prosa_Behavior_Arrival_sequence_arrives_in T
      (jp_decidable_eq T) arrL j).
Proof.
  intro Harr. cbn. apply jp_exists_nat_correspondence.
  intros tR tL Ht. apply jp_bool_truth_correspondence.
  exact (jp_arrives_at_related T arrR arrL j Harr tR tL Ht).
Qed.

Definition JpJobCostRel (T : eqType)
    (costR : prosa.behavior.job.JobCost T)
    (costL : ImportedJobProperties.Prosa_Behavior_Job_JobCost T
      (jp_decidable_eq T)) : SProp :=
  forall j : T,
    SubNatRel (@prosa.behavior.job.job_cost T costR j)
      (ImportedJobProperties.Prosa_Behavior_Job_JobCost_job_cost T
        (jp_decidable_eq T) costL j).

Definition jp_target_lt (a b : Lean.Nat) : SProp :=
  ImportedJobProperties.LT_lt_inst1 Lean.Nat ImportedJobProperties.instLTNat a b.

Definition jp_target_decide_lt (a b : Lean.Nat) : ImportedJobProperties.Bool :=
  ImportedJobProperties.Decidable_decide (jp_target_lt a b)
    (ImportedJobProperties.Nat_decLt a b).

Lemma jp_decide_lt_related aR aL bR bL :
  SubNatRel aR aL -> SubNatRel bR bL ->
  JpBoolRel (ltn aR bR) (jp_target_decide_lt aL bL).
Proof.
  intros Ha Hb. apply jp_decide_bool_correspondence.
  exact (sub_nat_lt_correspondence aR aL bR bL Ha Hb).
Qed.

Lemma jp_imp_correspondence (P Q : Prop) (PL QL : SProp) :
  PropSPropRel P PL -> PropSPropRel Q QL ->
  PropSPropRel (P -> Q) (PL -> QL).
Proof.
  intros HP HQ. apply prop_sprop_rel_intro.
  - intros H p. apply (prop_to_sprop _ _ HQ).
    exact (H (sprop_to_prop _ _ HP p)).
  - intro H. apply strictly_inhabits. intro p.
    apply (sprop_to_prop _ _ HQ).
    exact (H (prop_to_sprop _ _ HP p)).
Qed.

Lemma jp_forall_identity_correspondence (T : Type)
    (PR : T -> Prop) (PL : T -> SProp) :
  (forall x, PropSPropRel (PR x) (PL x)) ->
  PropSPropRel (forall x, PR x) (forall x, PL x).
Proof.
  intro HP. apply prop_sprop_rel_intro.
  - intros HR x. exact (prop_to_sprop _ _ (HP x) (HR x)).
  - intro HL. apply strictly_inhabits. intro x.
    exact (sprop_to_prop _ _ (HP x) (HL x)).
Qed.

Print Assumptions jp_arrives_in_related.
Print Assumptions jp_decide_lt_related.
