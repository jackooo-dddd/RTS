From mathcomp Require Import ssreflect ssrbool ssrnat.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedSearchArg ImportedSubadditivity.
From FoundationCertificates Require Import
  PropSPropFoundation LogicalRelation SubadditivityNatCorrespondence
  SearchArgDefinitionCertificate.
Require Import GeneratedSearchArgSource.

(** Logical and representation adapters for theorem statements surrounding
    the already-certified recursive [search_arg] computation. *)

Definition sa_target_le (a b : Lean.Nat) : SProp :=
  ImportedSearchArg.LE_le_inst1 Lean.Nat ImportedSearchArg.instLENat a b.

Definition sa_target_ltL (a b : Lean.Nat) : SProp :=
  ImportedSearchArg.LT_lt_inst1 Lean.Nat ImportedSearchArg.instLTNat a b.

Lemma sa_le_correspondence aR aL bR bL :
  SubNatRel aR aL -> SubNatRel bR bL ->
  PropSPropRel (is_true (leq aR bR)) (sa_target_le aL bL).
Proof. exact (sub_nat_le_correspondence aR aL bR bL). Qed.

Lemma sa_lt_correspondence aR aL bR bL :
  SubNatRel aR aL -> SubNatRel bR bL ->
  PropSPropRel (is_true (ltn aR bR)) (sa_target_ltL aL bL).
Proof. exact (sub_nat_lt_correspondence aR aL bR bL). Qed.

Definition sa_bool_to_rocq (b : ImportedSearchArg.Bool) : bool :=
  match b with
  | ImportedSearchArg.Bool_true => true
  | ImportedSearchArg.Bool_false => false
  end.

Lemma sa_bool_rocq_roundtrip (b : bool) :
  Logic.eq (sa_bool_to_rocq (sa_bool_to_imported b)) b.
Proof. by case: b. Qed.

Lemma sa_bool_imported_roundtrip (b : ImportedSearchArg.Bool) :
  Lean.eq (sa_bool_to_imported (sa_bool_to_rocq b)) b.
Proof. destruct b; exact (@Lean.eq_refl ImportedSearchArg.Bool _). Qed.

Lemma sa_bool_true_correspondence (b : bool) :
  PropSPropRel (is_true b)
    (Lean.eq (sa_bool_to_imported b) ImportedSearchArg.Bool_true).
Proof.
  apply prop_sprop_rel_intro; destruct b; cbn.
  - intro H. discriminate H.
  - intro H. exact (@Lean.eq_refl ImportedSearchArg.Bool
      ImportedSearchArg.Bool_true).
  - intro H. apply strictly_inhabits.
    exact (match H in Lean.eq _ z return
      match z with
      | ImportedSearchArg.Bool_false => Logic.False
      | ImportedSearchArg.Bool_true => Logic.eq true true
      end
    with Lean.eq_refl => Logic.eq_refl true end).
  - intro _. exact (strictly_inhabits (Logic.eq_refl true)).
Qed.

Lemma sa_bool_false_correspondence (b : bool) :
  PropSPropRel (is_true (~~ b))
    (Lean.eq (sa_bool_to_imported b) ImportedSearchArg.Bool_false).
Proof.
  apply prop_sprop_rel_intro; destruct b; cbn.
  - intro H. exact (@Lean.eq_refl ImportedSearchArg.Bool
      ImportedSearchArg.Bool_false).
  - intro H. discriminate H.
  - intro _. exact (strictly_inhabits (Logic.eq_refl true)).
  - intro H. apply strictly_inhabits.
    exact (match H in Lean.eq _ z return
      match z with
      | ImportedSearchArg.Bool_true => Logic.False
      | ImportedSearchArg.Bool_false => Logic.eq true true
      end
    with Lean.eq_refl => Logic.eq_refl true end).
Qed.

Definition sa_option_to_rocq
    (o : ImportedSearchArg.Option_inst1 Lean.Nat) : option nat :=
  match o with
  | ImportedSearchArg.Option_none_inst1 _ => None
  | ImportedSearchArg.Option_some_inst1 _ n => Some (sub_nat_to_rocq n)
  end.

Lemma sa_option_rocq_roundtrip (o : option nat) :
  Logic.eq (sa_option_to_rocq (sa_option_to_imported o)) o.
Proof.
  destruct o as [n|]; cbn; last reflexivity.
  f_equal. exact (sub_nat_rocq_roundtrip n).
Qed.

Lemma sa_option_imported_roundtrip
    (o : ImportedSearchArg.Option_inst1 Lean.Nat) :
  Lean.eq (sa_option_to_imported (sa_option_to_rocq o)) o.
Proof.
  destruct o as [n|]; cbn.
  - exact (sub_imported_eq_congr
      (ImportedSearchArg.Option_some_inst1 Lean.Nat) _ _
      (sub_nat_imported_roundtrip n)).
  - exact (@Lean.eq_refl (ImportedSearchArg.Option_inst1 Lean.Nat)
      (ImportedSearchArg.Option_none_inst1 Lean.Nat)).
Qed.

Definition SaOptionRel (oR : option nat)
    (oL : ImportedSearchArg.Option_inst1 Lean.Nat) : SProp :=
  Lean.eq (sa_option_to_imported oR) oL.

Lemma sa_option_eq_correspondence o1R o1L o2R o2L :
  SaOptionRel o1R o1L -> SaOptionRel o2R o2L ->
  PropSPropRel (Logic.eq o1R o2R) (Lean.eq o1L o2L).
Proof.
  intros H1 H2. apply prop_sprop_rel_intro.
  - intro HR. exact (sub_imported_eq_trans _ _ _
      (sub_imported_eq_sym _ _ H1)
      (sub_imported_eq_trans _ _ _
        (coq_eq_to_imported_eq _ _ (f_equal sa_option_to_imported HR)) H2)).
  - intro HL. apply strictly_inhabits.
    have Hmaps : Lean.eq (sa_option_to_imported o1R)
        (sa_option_to_imported o2R) :=
      sub_imported_eq_trans _ _ _ H1
        (sub_imported_eq_trans _ _ _ HL
          (sub_imported_eq_sym _ _ H2)).
    have Hback := f_equal sa_option_to_rocq
      (imported_eq_to_coq_eq _ _ Hmaps).
    exact (eq_trans (eq_sym (sa_option_rocq_roundtrip o1R))
      (eq_trans Hback (sa_option_rocq_roundtrip o2R))).
Qed.

Lemma sa_and_correspondence (P Q : Prop) (PL QL : SProp) :
  PropSPropRel P PL -> PropSPropRel Q QL ->
  PropSPropRel (P /\ Q) (Lean.And PL QL).
Proof.
  intros HP HQ. apply prop_sprop_rel_intro.
  - intros [p q]. exact (Lean.And_intro _ _
      (prop_to_sprop _ _ HP p) (prop_to_sprop _ _ HQ q)).
  - intro H. destruct H as [p q]. apply strictly_inhabits. split.
    + exact (sprop_to_prop _ _ HP p).
    + exact (sprop_to_prop _ _ HQ q).
Qed.

Lemma sa_iff_correspondence (P Q : Prop) (PL QL : SProp) :
  PropSPropRel P PL -> PropSPropRel Q QL ->
  PropSPropRel (P <-> Q) (ImportedSearchArg.Iff PL QL).
Proof.
  intros HP HQ. apply prop_sprop_rel_intro.
  - intros [HPQ HQP]. exact (ImportedSearchArg.Iff_intro _ _
      (fun p => prop_to_sprop _ _ HQ (HPQ (sprop_to_prop _ _ HP p)))
      (fun q => prop_to_sprop _ _ HP (HQP (sprop_to_prop _ _ HQ q)))).
  - intro H. apply strictly_inhabits. split.
    + intro p. apply (sprop_to_prop _ _ HQ).
      exact (ImportedSearchArg.mp _ _ H (prop_to_sprop _ _ HP p)).
    + intro q. apply (sprop_to_prop _ _ HP).
      exact (ImportedSearchArg.mpr _ _ H (prop_to_sprop _ _ HQ q)).
Qed.

Lemma sa_forall_nat_correspondence
    (PR : nat -> Prop) (PL : Lean.Nat -> SProp) :
  (forall nR nL, SubNatRel nR nL -> PropSPropRel (PR nR) (PL nL)) ->
  PropSPropRel (forall nR, PR nR) (forall nL, PL nL).
Proof.
  intro HP. apply prop_sprop_rel_intro.
  - intros HR nL. set (nR := sub_nat_to_rocq nL).
    exact (prop_to_sprop _ _ (HP nR nL (sub_nat_rel_surjective nL)) (HR nR)).
  - intro HL. apply strictly_inhabits. intro nR.
    exact (sprop_to_prop _ _
      (HP nR (sub_nat_to_imported nR) (sub_nat_rel_canonical nR))
      (HL (sub_nat_to_imported nR))).
Qed.

Lemma sa_exists_nat_correspondence
    (PR : nat -> Prop) (PL : Lean.Nat -> SProp) :
  (forall nR nL, SubNatRel nR nL -> PropSPropRel (PR nR) (PL nL)) ->
  PropSPropRel (exists nR, PR nR) (ImportedSearchArg.Exists Lean.Nat PL).
Proof.
  intro HP. apply prop_sprop_rel_intro.
  - intros [nR Hn]. exact (ImportedSearchArg.Exists_intro Lean.Nat PL
      (sub_nat_to_imported nR)
      (prop_to_sprop _ _
        (HP nR (sub_nat_to_imported nR) (sub_nat_rel_canonical nR)) Hn)).
  - intro HL. destruct HL as [nL Hn]. apply strictly_inhabits.
    set (nR := sub_nat_to_rocq nL). exists nR.
    exact (sprop_to_prop _ _ (HP nR nL (sub_nat_rel_surjective nL)) Hn).
Qed.

Lemma sa_range_correspondence aR aL bR bL xR xL :
  SubNatRel aR aL -> SubNatRel bR bL -> SubNatRel xR xL ->
  PropSPropRel
    (is_true (leq aR xR) /\ is_true (ltn xR bR))
    (Lean.And (sa_target_le aL xL) (sa_target_ltL xL bL)).
Proof.
  intros Ha Hb Hx. apply sa_and_correspondence.
  - exact (sa_le_correspondence _ _ _ _ Ha Hx).
  - exact (sa_lt_correspondence _ _ _ _ Hx Hb).
Qed.

Definition sa_source_search {T : Type} (f : nat -> T)
    (P : T -> bool) (R : T -> T -> bool) :=
  GeneratedSearchArgSource.search_arg f P R.

Lemma search_arg_none_statement_certificate {T : Type}
    (f : nat -> T) (P : T -> bool) (R : T -> T -> bool)
    (aR bR : nat) (aL bL : Lean.Nat) :
  SubNatRel aR aL -> SubNatRel bR bL ->
  PropSPropRel
    (sa_source_search f P R aR bR = None <->
      forall xR, is_true (leq aR xR) /\ is_true (ltn xR bR) ->
        is_true (~~ P (f xR)))
    (ImportedSearchArg.Iff
      (Lean.eq (sa_target_search f P R aR bR)
        (ImportedSearchArg.Option_none_inst1 Lean.Nat))
      (forall xL,
        Lean.And (sa_target_le aL xL) (sa_target_ltL xL bL) ->
        Lean.eq (sa_target_P P (sa_target_f f xL))
          ImportedSearchArg.Bool_false)).
Proof.
  intros Ha Hb. apply sa_iff_correspondence.
  - apply sa_option_eq_correspondence.
    + exact (search_arg_definition_certificate f P R aR bR).
    + exact (@Lean.eq_refl (ImportedSearchArg.Option_inst1 Lean.Nat)
        (ImportedSearchArg.Option_none_inst1 Lean.Nat)).
  - apply sa_forall_nat_correspondence. intros xR xL Hx.
    apply prop_sprop_rel_intro.
    + intros HR HrangeL.
      have HrangeR := sprop_to_prop _ _
        (sa_range_correspondence _ _ _ _ _ _ Ha Hb Hx) HrangeL.
      unfold sa_target_P, sa_target_f. rewrite (sub_nat_rocq_roundtrip xR).
      exact (prop_to_sprop _ _ (sa_bool_false_correspondence _)
        (HR HrangeR)).
    + intro HL. apply strictly_inhabits. intro HrangeR.
      have HrangeL := prop_to_sprop _ _
        (sa_range_correspondence _ _ _ _ _ _ Ha Hb Hx) HrangeR.
      have HfalseL := HL HrangeL.
      unfold sa_target_P, sa_target_f in HfalseL.
      rewrite (sub_nat_rocq_roundtrip xR) in HfalseL.
      exact (sprop_to_prop _ _ (sa_bool_false_correspondence _) HfalseL).
Qed.

Lemma search_arg_pred_statement_certificate {T : Type}
    (f : nat -> T) (P : T -> bool) (R : T -> T -> bool)
    (aR bR xR : nat) (aL bL xL : Lean.Nat) :
  SubNatRel aR aL -> SubNatRel bR bL -> SubNatRel xR xL ->
  PropSPropRel
    (sa_source_search f P R aR bR = Some xR -> is_true (P (f xR)))
    (Lean.eq (sa_target_search f P R aR bR)
        (ImportedSearchArg.Option_some_inst1 Lean.Nat xL) ->
      Lean.eq (sa_target_P P (sa_target_f f xL))
        ImportedSearchArg.Bool_true).
Proof.
  intros Ha Hb Hx. apply prop_sprop_rel_intro.
  - intros HR HeqL.
    have HeqR := sprop_to_prop _ _
      (sa_option_eq_correspondence _ _ _ _
        (search_arg_definition_certificate f P R aR bR) Hx) HeqL.
    unfold sa_target_P, sa_target_f. unfold SubNatRel in Hx.
    have Hxback := f_equal sub_nat_to_rocq
      (imported_eq_to_coq_eq _ _ Hx).
    rewrite (sub_nat_rocq_roundtrip xR) in Hxback.
    rewrite <- Hxback.
    exact (prop_to_sprop _ _ (sa_bool_true_correspondence _) (HR HeqR)).
  - intro HL. apply strictly_inhabits. intro HeqR.
    have HeqL := prop_to_sprop _ _
      (sa_option_eq_correspondence _ _ _ _
        (search_arg_definition_certificate f P R aR bR) Hx) HeqR.
    have HtrueL := HL HeqL.
    unfold sa_target_P, sa_target_f in HtrueL.
    unfold SubNatRel in Hx.
    have Hxback := f_equal sub_nat_to_rocq
      (imported_eq_to_coq_eq _ _ Hx).
    rewrite (sub_nat_rocq_roundtrip xR) in Hxback.
    rewrite <- Hxback in HtrueL.
    exact (sprop_to_prop _ _ (sa_bool_true_correspondence _) HtrueL).
Qed.

Lemma search_arg_in_range_statement_certificate {T : Type}
    (f : nat -> T) (P : T -> bool) (R : T -> T -> bool)
    (aR bR xR : nat) (aL bL xL : Lean.Nat) :
  SubNatRel aR aL -> SubNatRel bR bL -> SubNatRel xR xL ->
  PropSPropRel
    (sa_source_search f P R aR bR = Some xR ->
      is_true (leq aR xR) /\ is_true (ltn xR bR))
    (Lean.eq (sa_target_search f P R aR bR)
        (ImportedSearchArg.Option_some_inst1 Lean.Nat xL) ->
      Lean.And (sa_target_le aL xL) (sa_target_ltL xL bL)).
Proof.
  intros Ha Hb Hx. apply prop_sprop_rel_intro.
  - intros HR HeqL. apply (prop_to_sprop _ _
      (sa_range_correspondence _ _ _ _ _ _ Ha Hb Hx)).
    apply HR. exact (sprop_to_prop _ _
      (sa_option_eq_correspondence _ _ _ _
        (search_arg_definition_certificate f P R aR bR) Hx) HeqL).
  - intro HL. apply strictly_inhabits. intro HeqR.
    apply (sprop_to_prop _ _
      (sa_range_correspondence _ _ _ _ _ _ Ha Hb Hx)).
    apply HL. exact (prop_to_sprop _ _
      (sa_option_eq_correspondence _ _ _ _
        (search_arg_definition_certificate f P R aR bR) Hx) HeqR).
Qed.

Lemma search_arg_not_none_statement_certificate {T : Type}
    (f : nat -> T) (P : T -> bool) (R : T -> T -> bool)
    (aR bR : nat) (aL bL : Lean.Nat) :
  SubNatRel aR aL -> SubNatRel bR bL ->
  PropSPropRel
    ((exists xR,
        (is_true (leq aR xR) /\ is_true (ltn xR bR)) /\
        is_true (P (f xR))) ->
      exists yR, sa_source_search f P R aR bR = Some yR)
    (ImportedSearchArg.Exists Lean.Nat (fun xL =>
        Lean.And (Lean.And (sa_target_le aL xL) (sa_target_ltL xL bL))
          (Lean.eq (sa_target_P P (sa_target_f f xL))
            ImportedSearchArg.Bool_true)) ->
      ImportedSearchArg.Exists Lean.Nat (fun yL =>
        Lean.eq (sa_target_search f P R aR bR)
          (ImportedSearchArg.Option_some_inst1 Lean.Nat yL))).
Proof.
  intros Ha Hb.
  have Hprem : PropSPropRel
      (exists xR,
        (is_true (leq aR xR) /\ is_true (ltn xR bR)) /\
        is_true (P (f xR)))
      (ImportedSearchArg.Exists Lean.Nat (fun xL =>
        Lean.And (Lean.And (sa_target_le aL xL) (sa_target_ltL xL bL))
          (Lean.eq (sa_target_P P (sa_target_f f xL))
            ImportedSearchArg.Bool_true))).
  { apply sa_exists_nat_correspondence. intros xR xL Hx.
    apply sa_and_correspondence.
    - exact (sa_range_correspondence _ _ _ _ _ _ Ha Hb Hx).
    - unfold sa_target_P, sa_target_f. unfold SubNatRel in Hx.
      have Hxback := f_equal sub_nat_to_rocq
        (imported_eq_to_coq_eq _ _ Hx).
      rewrite (sub_nat_rocq_roundtrip xR) in Hxback.
      rewrite <- Hxback.
      exact (sa_bool_true_correspondence _). }
  have Hconcl : PropSPropRel
      (exists yR, sa_source_search f P R aR bR = Some yR)
      (ImportedSearchArg.Exists Lean.Nat (fun yL =>
        Lean.eq (sa_target_search f P R aR bR)
          (ImportedSearchArg.Option_some_inst1 Lean.Nat yL))).
  { apply sa_exists_nat_correspondence. intros yR yL Hy.
    exact (sa_option_eq_correspondence _ _ _ _
      (search_arg_definition_certificate f P R aR bR) Hy). }
  apply prop_sprop_rel_intro.
  - intros HR HpremL. apply (prop_to_sprop _ _ Hconcl).
    apply HR. exact (sprop_to_prop _ _ Hprem HpremL).
  - intro HL. apply strictly_inhabits. intro HpremR.
    apply (sprop_to_prop _ _ Hconcl).
    apply HL. exact (prop_to_sprop _ _ Hprem HpremR).
Qed.

Print Assumptions search_arg_none_statement_certificate.
Print Assumptions search_arg_not_none_statement_certificate.
Print Assumptions search_arg_pred_statement_certificate.
Print Assumptions search_arg_in_range_statement_certificate.
