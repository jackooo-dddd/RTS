From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedPoet.
From FoundationCertificates Require Import
  PropSPropFoundation LogicalRelation SubadditivityNatCorrespondence
  PoetCorrespondence.
From prosa Require Import GeneratedPoetSource.

Definition po_prop_to_sprop {T U : Type} (P : T -> U -> Prop)
    (x : T) (y : U) : SProp := StrictlyInhabited (P x y).

Lemma po_prop_embedding_correspondence (P : Prop) :
  PropSPropRel P (StrictlyInhabited P).
Proof.
  constructor.
  - exact strictly_inhabits.
  - exact (interpret_strict P).
Qed.

Lemma po_prop2_canonical {T U : Type} (P : T -> U -> Prop) :
  PoProp2Rel P (po_prop_to_sprop P).
Proof. intros x y. exact (po_prop_embedding_correspondence (P x y)). Qed.

Definition po_target_instance_statement
    (X Y : eqType)
    (PBool : ImportedPoet.Prod X Y -> ImportedPoet.Bool)
    (PProp : X -> Y -> SProp)
    (xs : ImportedPoet.List X) : SProp :=
  (forall x y,
    ImportedPoet.Iff
      (Lean.eq (PBool (ImportedPoet.Prod_mk X Y x y))
        ImportedPoet.Bool_true)
      (PProp x y)) ->
  ImportedPoet.Exists (ImportedPoet.List Y) (fun ys =>
    Lean.And
      (Lean.eq (po_target_length xs) (po_target_length ys))
      (Lean.eq
        (ImportedPoet.List_all (ImportedPoet.Prod X Y)
          (po_target_zip xs ys) PBool)
        ImportedPoet.Bool_true)) ->
  forall x, po_target_mem x xs ->
    ImportedPoet.Exists Y (fun y => PProp x y).

Definition po_source_instance_statement
    (X Y : eqType) (PBool : X * Y -> bool)
    (PProp : X -> Y -> Prop) (xs : seq X) : Prop :=
  (forall x y, PBool (x, y) <-> PProp x y) ->
  (exists ys : seq Y,
    size xs = size ys /\ all PBool (zip xs ys) == true) ->
  forall x, x \in xs -> exists y, PProp x y.

Lemma po_predicate_relation_correspondence
    (X Y : eqType)
    (PBoolR : X * Y -> bool)
    (PBoolL : ImportedPoet.Prod X Y -> ImportedPoet.Bool)
    (PPropR : X -> Y -> Prop) (PPropL : X -> Y -> SProp) :
  PoPairPredRel PBoolR PBoolL -> PoProp2Rel PPropR PPropL ->
  PropSPropRel
    (forall x y, PBoolR (x, y) <-> PPropR x y)
    (forall x y,
      ImportedPoet.Iff
        (Lean.eq (PBoolL (ImportedPoet.Prod_mk X Y x y))
          ImportedPoet.Bool_true)
        (PPropL x y)).
Proof.
  intros HPBool HPProp.
  apply po_forall_identity_correspondence. intro x.
  apply po_forall_identity_correspondence. intro y.
  apply po_iff_correspondence.
  - apply po_bool_truth_correspondence.
    exact (HPBool (x, y) (ImportedPoet.Prod_mk X Y x y)
      (@Lean.eq_refl _ _)).
  - exact (HPProp x y).
Qed.

Lemma po_zip_witness_body_correspondence
    (X Y : eqType)
    (PBoolR : X * Y -> bool)
    (PBoolL : ImportedPoet.Prod X Y -> ImportedPoet.Bool)
    (xsR : seq X) (xsL : ImportedPoet.List X)
    (ysR : seq Y) (ysL : ImportedPoet.List Y) :
  PoPairPredRel PBoolR PBoolL ->
  PoListRel xsR xsL -> PoListRel ysR ysL ->
  PropSPropRel
    (size xsR = size ysR /\ all PBoolR (zip xsR ysR) == true)
    (Lean.And
      (Lean.eq (po_target_length xsL) (po_target_length ysL))
      (Lean.eq
        (ImportedPoet.List_all (ImportedPoet.Prod X Y)
          (po_target_zip xsL ysL) PBoolL)
        ImportedPoet.Bool_true)).
Proof.
  intros HP Hxs Hys. apply po_and_correspondence.
  - exact (sub_nat_eq_correspondence _ _ _ _
      (po_length_related xsR xsL Hxs)
      (po_length_related ysR ysL Hys)).
  - have Hzip := po_zip_related X Y xsR xsL ysR ysL Hxs Hys.
    have Hall := po_all_related X Y PBoolR PBoolL
      (zip xsR ysR) (po_target_zip xsL ysL) HP Hzip.
    exact (po_bool_eqb_correspondence
      (all PBoolR (zip xsR ysR))
      (ImportedPoet.List_all (ImportedPoet.Prod X Y)
        (po_target_zip xsL ysL) PBoolL)
      true ImportedPoet.Bool_true Hall (@Lean.eq_refl _ _)).
Qed.

Lemma po_zip_witness_correspondence
    (X Y : eqType)
    (PBoolR : X * Y -> bool)
    (PBoolL : ImportedPoet.Prod X Y -> ImportedPoet.Bool)
    (xsR : seq X) (xsL : ImportedPoet.List X) :
  PoPairPredRel PBoolR PBoolL -> PoListRel xsR xsL ->
  PropSPropRel
    (exists ys : seq Y,
      size xsR = size ys /\ all PBoolR (zip xsR ys) == true)
    (ImportedPoet.Exists (ImportedPoet.List Y) (fun ys =>
      Lean.And
        (Lean.eq (po_target_length xsL) (po_target_length ys))
        (Lean.eq
          (ImportedPoet.List_all (ImportedPoet.Prod X Y)
            (po_target_zip xsL ys) PBoolL)
          ImportedPoet.Bool_true))).
Proof.
  intros HP Hxs. apply po_exists_list_correspondence.
  intros ysR ysL Hys.
  exact (po_zip_witness_body_correspondence
    X Y PBoolR PBoolL xsR xsL ysR ysL HP Hxs Hys).
Qed.

Lemma po_conclusion_correspondence
    (X Y : eqType) (PPropR : X -> Y -> Prop)
    (PPropL : X -> Y -> SProp)
    (xsR : seq X) (xsL : ImportedPoet.List X) :
  PoProp2Rel PPropR PPropL -> PoListRel xsR xsL ->
  PropSPropRel
    (forall x, x \in xsR -> exists y, PPropR x y)
    (forall x, po_target_mem x xsL ->
      ImportedPoet.Exists Y (fun y => PPropL x y)).
Proof.
  intros HP Hxs. apply po_forall_identity_correspondence. intro x.
  apply po_imp_correspondence.
  - exact (po_membership_correspondence X x xsR xsL Hxs).
  - apply po_exists_identity_correspondence. intro y.
    exact (HP x y).
Qed.

Lemma po_instance_statement_correspondence
    (X Y : eqType)
    (PBoolR : X * Y -> bool)
    (PBoolL : ImportedPoet.Prod X Y -> ImportedPoet.Bool)
    (PPropR : X -> Y -> Prop) (PPropL : X -> Y -> SProp)
    (xsR : seq X) (xsL : ImportedPoet.List X) :
  PoPairPredRel PBoolR PBoolL -> PoProp2Rel PPropR PPropL ->
  PoListRel xsR xsL ->
  PropSPropRel
    (po_source_instance_statement X Y PBoolR PPropR xsR)
    (po_target_instance_statement X Y PBoolL PPropL xsL).
Proof.
  intros HPBool HPProp Hxs.
  unfold po_source_instance_statement, po_target_instance_statement.
  apply po_imp_correspondence.
  - exact (po_predicate_relation_correspondence
      X Y PBoolR PBoolL PPropR PPropL HPBool HPProp).
  - apply po_imp_correspondence.
    + exact (po_zip_witness_correspondence
        X Y PBoolR PBoolL xsR xsL HPBool Hxs).
    + exact (po_conclusion_correspondence
        X Y PPropR PPropL xsR xsL HPProp Hxs).
Qed.

(** Canonically embedded target statement.  Its exact-type guard is an
    application of the actual imported theorem at the approved
    eqType/DecidableEq and Prop/SProp representation maps. *)
Definition po_encoded_target_statement : SProp :=
  forall (X Y : eqType) (PBool : X * Y -> bool)
    (PProp : X -> Y -> Prop) (xs : seq X),
  po_target_instance_statement X Y
    (po_pair_pred_to_imported PBool)
    (po_prop_to_sprop PProp)
    (po_list_to_imported xs).

Theorem forall_exists_implied_by_forall_in_zip_statement_certificate :
  PropSPropRel
    GeneratedPoetSource.statement_forall_exists_implied_by_forall_in_zip
    po_encoded_target_statement.
Proof.
  unfold GeneratedPoetSource.statement_forall_exists_implied_by_forall_in_zip,
    po_encoded_target_statement.
  apply prop_sprop_rel_intro.
  - intros Hsource X Y PBool PProp xs.
    exact (prop_to_sprop _ _
      (po_instance_statement_correspondence X Y
        PBool (po_pair_pred_to_imported PBool)
        PProp (po_prop_to_sprop PProp)
        xs (po_list_to_imported xs)
        (po_pair_pred_canonical PBool)
        (po_prop2_canonical PProp)
        (@Lean.eq_refl _ _))
      (Hsource X Y PBool PProp xs)).
  - intro Htarget. apply strictly_inhabits.
    intros X Y PBool PProp xs.
    exact (sprop_to_prop _ _
      (po_instance_statement_correspondence X Y
        PBool (po_pair_pred_to_imported PBool)
        PProp (po_prop_to_sprop PProp)
        xs (po_list_to_imported xs)
        (po_pair_pred_canonical PBool)
        (po_prop2_canonical PProp)
        (@Lean.eq_refl _ _))
      (Htarget X Y PBool PProp xs)).
Qed.

Print Assumptions forall_exists_implied_by_forall_in_zip_statement_certificate.
