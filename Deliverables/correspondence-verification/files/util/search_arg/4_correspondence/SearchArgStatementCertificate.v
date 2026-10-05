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

Lemma sa_nat_back_of_rel (nR : nat) (nL : Lean.Nat) :
  SubNatRel nR nL -> Logic.eq (sub_nat_to_rocq nL) nR.
Proof.
  intro H. unfold SubNatRel in H.
  have Hback := f_equal sub_nat_to_rocq
    (imported_eq_to_coq_eq _ _ H).
  exact (eq_trans (eq_sym Hback) (sub_nat_rocq_roundtrip nR)).
Qed.

Lemma sa_bool_true_correspondence (b : bool) :
  PropSPropRel (is_true b)
    (Lean.eq (sa_bool_to_imported b) ImportedSearchArg.Bool_true).
Proof.
  apply prop_sprop_rel_intro; destruct b; cbn.
  - intro Hignored. exact (@Lean.eq_refl ImportedSearchArg.Bool
      ImportedSearchArg.Bool_true).
  - intro H. discriminate H.
  - intro Hignored. exact (strictly_inhabits (Logic.eq_refl true)).
  - intro H. exact (sa_imported_false_elim _
      (ImportedSearchArg.Bool_noConfusion_inst1 ImportedSearchArg.False
        ImportedSearchArg.Bool_false ImportedSearchArg.Bool_true H)).
Qed.

Lemma sa_bool_false_correspondence (b : bool) :
  PropSPropRel (is_true (~~ b))
    (Lean.eq (sa_bool_to_imported b) ImportedSearchArg.Bool_false).
Proof.
  apply prop_sprop_rel_intro; destruct b; cbn.
  - intro H. discriminate H.
  - intro Hignored. exact (@Lean.eq_refl ImportedSearchArg.Bool
      ImportedSearchArg.Bool_false).
  - intro H. exact (sa_imported_false_elim _
      (ImportedSearchArg.Bool_noConfusion_inst1 ImportedSearchArg.False
        ImportedSearchArg.Bool_true ImportedSearchArg.Bool_false H)).
  - intro Hignored. exact (strictly_inhabits (Logic.eq_refl true)).
Qed.

Definition sa_option_to_rocq
    (o : ImportedSearchArg.Option_inst1 Lean.Nat) : option nat :=
  match o with
  | ImportedSearchArg.Option_none_inst1 => None
  | ImportedSearchArg.Option_some_inst1 n => Some (sub_nat_to_rocq n)
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
  destruct o as [|n]; cbn.
  - exact (@Lean.eq_refl (ImportedSearchArg.Option_inst1 Lean.Nat)
      (ImportedSearchArg.Option_none_inst1 Lean.Nat)).
  - exact (sub_imported_eq_congr
      (ImportedSearchArg.Option_some_inst1 Lean.Nat) _ _
      (sub_nat_imported_roundtrip n)).
Qed.

Definition SaOptionRel (oR : option nat)
    (oL : ImportedSearchArg.Option_inst1 Lean.Nat) : SProp :=
  Lean.eq (sa_option_to_imported oR) oL.

Lemma sa_some_rel (nR : nat) (nL : Lean.Nat) :
  SubNatRel nR nL ->
  SaOptionRel (Some nR)
    (ImportedSearchArg.Option_some_inst1 Lean.Nat nL).
Proof.
  intro H. exact (sub_imported_eq_congr
    (ImportedSearchArg.Option_some_inst1 Lean.Nat) _ _ H).
Qed.

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

Lemma sa_or_correspondence (P Q : Prop) (PL QL : SProp) :
  PropSPropRel P PL -> PropSPropRel Q QL ->
  PropSPropRel (P \/ Q) (Lean.Or PL QL).
Proof.
  intros HP HQ. apply prop_sprop_rel_intro.
  - intros [p|q].
    + exact (Lean.Or_inl PL QL (prop_to_sprop _ _ HP p)).
    + exact (Lean.Or_inr PL QL (prop_to_sprop _ _ HQ q)).
  - intro H. destruct H as [p|q].
    + exact (strictly_inhabits (or_introl _ (sprop_to_prop _ _ HP p))).
    + exact (strictly_inhabits (or_intror _ (sprop_to_prop _ _ HQ q))).
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

Definition sa_target_nat_pred (P : nat -> bool)
    (nL : Lean.Nat) : ImportedSearchArg.Bool :=
  sa_bool_to_imported (P (sub_nat_to_rocq nL)).

Lemma sa_nat_pred_true_correspondence (P : nat -> bool)
    nR nL : SubNatRel nR nL ->
  PropSPropRel (is_true (P nR))
    (Lean.eq (sa_target_nat_pred P nL) ImportedSearchArg.Bool_true).
Proof.
  intro Hn. unfold sa_target_nat_pred.
  rw (sa_nat_back_of_rel nR nL Hn).
  exact (sa_bool_true_correspondence (P nR)).
Qed.

Lemma sa_nat_pred_false_correspondence (P : nat -> bool)
    nR nL : SubNatRel nR nL ->
  PropSPropRel (is_true (~~ P nR))
    (Lean.eq (sa_target_nat_pred P nL) ImportedSearchArg.Bool_false).
Proof.
  intro Hn. unfold sa_target_nat_pred.
  rw (sa_nat_back_of_rel nR nL Hn).
  exact (sa_bool_false_correspondence (P nR)).
Qed.

Lemma earliest_pred_element_exists_case_statement_certificate
    (P : nat -> bool) (t1R t2R : nat) (t1L t2L : Lean.Nat) :
  SubNatRel t1R t1L -> SubNatRel t2R t2L ->
  PropSPropRel
    ((forall tR,
        (is_true (leq t1R tR) /\ is_true (ltn tR t2R)) ->
        is_true (~~ P tR)) \/
      (exists tR,
        (is_true (leq t1R tR) /\ is_true (ltn tR t2R)) /\
        is_true (P tR) /\
        forall tR', is_true (leq t1R tR') ->
          is_true (P tR') -> is_true (leq tR tR')))
    (Lean.Or
      (forall tL,
        Lean.And (sa_target_le t1L tL) (sa_target_ltL tL t2L) ->
        Lean.eq (sa_target_nat_pred P tL) ImportedSearchArg.Bool_false)
      (ImportedSearchArg.Exists Lean.Nat (fun tL =>
        Lean.And
          (Lean.And (sa_target_le t1L tL) (sa_target_ltL tL t2L))
          (Lean.And
            (Lean.eq (sa_target_nat_pred P tL)
              ImportedSearchArg.Bool_true)
            (forall tL', sa_target_le t1L tL' ->
              Lean.eq (sa_target_nat_pred P tL')
                ImportedSearchArg.Bool_true ->
              sa_target_le tL tL'))))).
Proof.
  intros Ht1 Ht2.
  apply sa_or_correspondence.
  - apply sa_forall_nat_correspondence. intros tR tL Ht.
    apply prop_sprop_rel_intro.
    + intros HR HrangeL. apply (prop_to_sprop _ _
        (sa_nat_pred_false_correspondence P tR tL Ht)).
      apply HR. exact (sprop_to_prop _ _
        (sa_range_correspondence _ _ _ _ _ _ Ht1 Ht2 Ht) HrangeL).
    + intro HL. apply strictly_inhabits. intro HrangeR.
      apply (sprop_to_prop _ _
        (sa_nat_pred_false_correspondence P tR tL Ht)).
      apply HL. exact (prop_to_sprop _ _
        (sa_range_correspondence _ _ _ _ _ _ Ht1 Ht2 Ht) HrangeR).
  - apply sa_exists_nat_correspondence. intros tR tL Ht.
    apply sa_and_correspondence.
    + exact (sa_range_correspondence _ _ _ _ _ _ Ht1 Ht2 Ht).
    + apply sa_and_correspondence.
      * exact (sa_nat_pred_true_correspondence P tR tL Ht).
      * apply sa_forall_nat_correspondence. intros uR uL Hu.
        apply prop_sprop_rel_intro.
        -- intros HR HloL HPuL.
           apply (prop_to_sprop _ _
             (sa_le_correspondence _ _ _ _ Ht Hu)).
           apply HR.
           ++ exact (sprop_to_prop _ _
                (sa_le_correspondence _ _ _ _ Ht1 Hu) HloL).
           ++ exact (sprop_to_prop _ _
                (sa_nat_pred_true_correspondence P uR uL Hu) HPuL).
        -- intro HL. apply strictly_inhabits. intros HloR HPuR.
           apply (sprop_to_prop _ _
             (sa_le_correspondence _ _ _ _ Ht Hu)).
           apply HL.
           ++ exact (prop_to_sprop _ _
                (sa_le_correspondence _ _ _ _ Ht1 Hu) HloR).
           ++ exact (prop_to_sprop _ _
                (sa_nat_pred_true_correspondence P uR uL Hu) HPuR).
Qed.

Definition sa_source_search {T : Type} (f : nat -> T)
    (P : T -> bool) (R : T -> T -> bool) :=
  GeneratedSearchArgSource.search_arg f P R.

Lemma search_arg_none_statement_certificate {T : Type}
    (f : nat -> T) (P : T -> bool) (R : T -> T -> bool)
    (aR bR : nat) (aL bL : Lean.Nat) :
  SubNatRel aR aL -> SubNatRel bR bL ->
  PropSPropRel
    (Logic.eq (sa_source_search f P R aR bR) None <->
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
    + exact (sub_imported_eq_sym _ _
        (search_arg_definition_certificate f P R aR bR)).
    + exact (@Lean.eq_refl (ImportedSearchArg.Option_inst1 Lean.Nat)
        (ImportedSearchArg.Option_none_inst1 Lean.Nat)).
  - apply sa_forall_nat_correspondence. intros xR xL Hx.
    apply prop_sprop_rel_intro.
    + intros HR HrangeL.
      have HrangeR := sprop_to_prop _ _
        (sa_range_correspondence _ _ _ _ _ _ Ha Hb Hx) HrangeL.
      unfold sa_target_P, sa_target_f. rw (sa_nat_back_of_rel xR xL Hx).
      exact (prop_to_sprop _ _ (sa_bool_false_correspondence _)
        (HR HrangeR)).
    + intro HL. apply strictly_inhabits. intro HrangeR.
      have HrangeL := prop_to_sprop _ _
        (sa_range_correspondence _ _ _ _ _ _ Ha Hb Hx) HrangeR.
      have HfalseL := HL HrangeL.
      unfold sa_target_P, sa_target_f in HfalseL.
      rw (sa_nat_back_of_rel xR xL Hx) in HfalseL.
      exact (sprop_to_prop _ _ (sa_bool_false_correspondence _) HfalseL).
Qed.

Lemma search_arg_pred_statement_certificate {T : Type}
    (f : nat -> T) (P : T -> bool) (R : T -> T -> bool)
    (aR bR xR : nat) (aL bL xL : Lean.Nat) :
  SubNatRel aR aL -> SubNatRel bR bL -> SubNatRel xR xL ->
  PropSPropRel
    (Logic.eq (sa_source_search f P R aR bR) (Some xR) ->
      is_true (P (f xR)))
    (Lean.eq (sa_target_search f P R aR bR)
        (ImportedSearchArg.Option_some_inst1 Lean.Nat xL) ->
      Lean.eq (sa_target_P P (sa_target_f f xL))
        ImportedSearchArg.Bool_true).
Proof.
  intros Ha Hb Hx. apply prop_sprop_rel_intro.
  - intros HR HeqL.
    have HeqR := sprop_to_prop _ _
      (sa_option_eq_correspondence _ _ _ _
        (sub_imported_eq_sym _ _
          (search_arg_definition_certificate f P R aR bR))
        (sa_some_rel xR xL Hx)) HeqL.
    unfold sa_target_P, sa_target_f. unfold SubNatRel in Hx.
    have Hxback := f_equal sub_nat_to_rocq
      (imported_eq_to_coq_eq _ _ Hx).
    rewrite (sub_nat_rocq_roundtrip xR) in Hxback.
    rewrite <- Hxback.
    exact (prop_to_sprop _ _ (sa_bool_true_correspondence _) (HR HeqR)).
  - intro HL. apply strictly_inhabits. intro HeqR.
    have HeqL := prop_to_sprop _ _
      (sa_option_eq_correspondence _ _ _ _
        (sub_imported_eq_sym _ _
          (search_arg_definition_certificate f P R aR bR))
        (sa_some_rel xR xL Hx)) HeqR.
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
    (Logic.eq (sa_source_search f P R aR bR) (Some xR) ->
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
        (sub_imported_eq_sym _ _
          (search_arg_definition_certificate f P R aR bR))
        (sa_some_rel xR xL Hx)) HeqL).
  - intro HL. apply strictly_inhabits. intro HeqR.
    apply (sprop_to_prop _ _
      (sa_range_correspondence _ _ _ _ _ _ Ha Hb Hx)).
    apply HL. exact (prop_to_sprop _ _
      (sa_option_eq_correspondence _ _ _ _
        (sub_imported_eq_sym _ _
          (search_arg_definition_certificate f P R aR bR))
        (sa_some_rel xR xL Hx)) HeqR).
Qed.

Lemma search_arg_not_none_statement_certificate {T : Type}
    (f : nat -> T) (P : T -> bool) (R : T -> T -> bool)
    (aR bR : nat) (aL bL : Lean.Nat) :
  SubNatRel aR aL -> SubNatRel bR bL ->
  PropSPropRel
    ((exists xR,
        (is_true (leq aR xR) /\ is_true (ltn xR bR)) /\
        is_true (P (f xR))) ->
      exists yR, Logic.eq (sa_source_search f P R aR bR) (Some yR))
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
      (exists yR, Logic.eq (sa_source_search f P R aR bR) (Some yR))
      (ImportedSearchArg.Exists Lean.Nat (fun yL =>
        Lean.eq (sa_target_search f P R aR bR)
          (ImportedSearchArg.Option_some_inst1 Lean.Nat yL))).
  { apply sa_exists_nat_correspondence. intros yR yL Hy.
    exact (sa_option_eq_correspondence _ _ _ _
      (sub_imported_eq_sym _ _
        (search_arg_definition_certificate f P R aR bR))
      (sa_some_rel yR yL Hy)). }
  apply prop_sprop_rel_intro.
  - intros HR HpremL. apply (prop_to_sprop _ _ Hconcl).
    apply HR. exact (sprop_to_prop _ _ Hprem HpremL).
  - intro HL. apply strictly_inhabits. intro HpremR.
    apply (sprop_to_prop _ _ Hconcl).
    apply HL. exact (prop_to_sprop _ _ Hprem HpremR).
Qed.

Lemma sa_Pf_true_correspondence {T : Type}
    (f : nat -> T) (P : T -> bool) nR nL :
  SubNatRel nR nL ->
  PropSPropRel (is_true (P (f nR)))
    (Lean.eq (sa_target_P P (sa_target_f f nL))
      ImportedSearchArg.Bool_true).
Proof.
  intro Hn. unfold sa_target_P, sa_target_f.
  rw (sa_nat_back_of_rel nR nL Hn).
  exact (sa_bool_true_correspondence (P (f nR))).
Qed.

Lemma sa_Rff_true_correspondence {T : Type}
    (f : nat -> T) (R : T -> T -> bool)
    nR nL mR mL :
  SubNatRel nR nL -> SubNatRel mR mL ->
  PropSPropRel (is_true (R (f nR) (f mR)))
    (Lean.eq
      (sa_target_R R (sa_target_f f nL) (sa_target_f f mL))
      ImportedSearchArg.Bool_true).
Proof.
  intros Hn Hm. unfold sa_target_R, sa_target_f.
  rw (sa_nat_back_of_rel nR nL Hn).
  rw (sa_nat_back_of_rel mR mL Hm).
  exact (sa_bool_true_correspondence (R (f nR) (f mR))).
Qed.

Lemma sa_R_true_correspondence {T : Type}
    (R : T -> T -> bool) (x y : T) :
  PropSPropRel (is_true (R x y))
    (Lean.eq (sa_target_R R x y) ImportedSearchArg.Bool_true).
Proof.
  unfold sa_target_R. exact (sa_bool_true_correspondence (R x y)).
Qed.

Definition sa_source_reflexive {T : Type} (R : T -> T -> bool) : Prop :=
  forall x, is_true (R x x).

Definition sa_target_reflexive {T : Type} (R : T -> T -> bool) : SProp :=
  forall x, Lean.eq (sa_target_R R x x) ImportedSearchArg.Bool_true.

Lemma sa_reflexive_correspondence {T : Type} (R : T -> T -> bool) :
  PropSPropRel (sa_source_reflexive R) (sa_target_reflexive R).
Proof.
  apply prop_sprop_rel_intro.
  - intros HR x. exact (prop_to_sprop _ _
      (sa_R_true_correspondence R x x) (HR x)).
  - intro HL. apply strictly_inhabits. intro x.
    exact (sprop_to_prop _ _ (sa_R_true_correspondence R x x) (HL x)).
Qed.

Definition sa_source_transitive {T : Type} (R : T -> T -> bool) : Prop :=
  forall x y z, is_true (R x y) -> is_true (R y z) -> is_true (R x z).

Definition sa_target_transitive {T : Type} (R : T -> T -> bool) : SProp :=
  forall x y z,
    Lean.eq (sa_target_R R x y) ImportedSearchArg.Bool_true ->
    Lean.eq (sa_target_R R y z) ImportedSearchArg.Bool_true ->
    Lean.eq (sa_target_R R x z) ImportedSearchArg.Bool_true.

Lemma sa_transitive_correspondence {T : Type} (R : T -> T -> bool) :
  PropSPropRel (sa_source_transitive R) (sa_target_transitive R).
Proof.
  apply prop_sprop_rel_intro.
  - intros HR x y z HxyL HyzL. unfold sa_source_transitive in HR.
    have HxyR := sprop_to_prop _ _
      (sa_R_true_correspondence R x y) HxyL.
    have HyzR := sprop_to_prop _ _
      (sa_R_true_correspondence R y z) HyzL.
    exact (prop_to_sprop _ _ (sa_R_true_correspondence R x z)
      (HR x y z HxyR HyzR)).
  - intro HL. unfold sa_target_transitive in HL.
    apply strictly_inhabits. intros x y z HxyR HyzR.
    have HxyL := prop_to_sprop _ _
      (sa_R_true_correspondence R x y) HxyR.
    have HyzL := prop_to_sprop _ _
      (sa_R_true_correspondence R y z) HyzR.
    exact (sprop_to_prop _ _ (sa_R_true_correspondence R x z)
      (HL x y z HxyL HyzL)).
Qed.

Definition sa_source_total {T : Type} (R : T -> T -> bool) : Prop :=
  forall x y, is_true (R x y || R y x).

Definition sa_target_total {T : Type} (R : T -> T -> bool) : SProp :=
  forall x y,
    Lean.Or
      (Lean.eq (sa_target_R R x y) ImportedSearchArg.Bool_true)
      (Lean.eq (sa_target_R R y x) ImportedSearchArg.Bool_true).

Lemma sa_total_pair_correspondence {T : Type}
    (R : T -> T -> bool) (x y : T) :
  PropSPropRel (is_true (R x y || R y x))
    (Lean.Or
      (Lean.eq (sa_target_R R x y) ImportedSearchArg.Bool_true)
      (Lean.eq (sa_target_R R y x) ImportedSearchArg.Bool_true)).
Proof.
  apply prop_sprop_rel_intro.
  - intro HR. destruct (R x y) eqn:Hxy, (R y x) eqn:Hyx; cbn in HR.
    + exact (Lean.Or_inl _ _ (prop_to_sprop _ _
        (sa_R_true_correspondence R x y) Hxy)).
    + exact (Lean.Or_inl _ _ (prop_to_sprop _ _
        (sa_R_true_correspondence R x y) Hxy)).
    + exact (Lean.Or_inr _ _ (prop_to_sprop _ _
        (sa_R_true_correspondence R y x) Hyx)).
    + discriminate HR.
  - intro HL. destruct HL as [HxyL|HyxL]; apply strictly_inhabits.
    + have HxyR := sprop_to_prop _ _
        (sa_R_true_correspondence R x y) HxyL.
      apply/orP. left. exact HxyR.
    + have HyxR := sprop_to_prop _ _
        (sa_R_true_correspondence R y x) HyxL.
      apply/orP. right. exact HyxR.
Qed.

Lemma sa_total_correspondence {T : Type} (R : T -> T -> bool) :
  PropSPropRel (sa_source_total R) (sa_target_total R).
Proof.
  apply prop_sprop_rel_intro.
  - intros HR x y. exact (prop_to_sprop _ _
      (sa_total_pair_correspondence R x y) (HR x y)).
  - intro HL. apply strictly_inhabits. intros x y.
    exact (sprop_to_prop _ _
      (sa_total_pair_correspondence R x y) (HL x y)).
Qed.

Lemma sa_extremum_result_correspondence {T : Type}
    (f : nat -> T) (P : T -> bool) (R : T -> T -> bool)
    (aR bR xR : nat) (aL bL xL : Lean.Nat) :
  SubNatRel aR aL -> SubNatRel bR bL -> SubNatRel xR xL ->
  PropSPropRel
    (Logic.eq (sa_source_search f P R aR bR) (Some xR) ->
      forall yR,
        (is_true (leq aR yR) /\ is_true (ltn yR bR)) ->
        is_true (P (f yR)) -> is_true (R (f xR) (f yR)))
    (Lean.eq (sa_target_search f P R aR bR)
        (ImportedSearchArg.Option_some_inst1 Lean.Nat xL) ->
      forall yL,
        Lean.And (sa_target_le aL yL) (sa_target_ltL yL bL) ->
        Lean.eq (sa_target_P P (sa_target_f f yL))
          ImportedSearchArg.Bool_true ->
        Lean.eq
          (sa_target_R R (sa_target_f f xL) (sa_target_f f yL))
          ImportedSearchArg.Bool_true).
Proof.
  intros Ha Hb Hx.
  have Heq : PropSPropRel
      (Logic.eq (sa_source_search f P R aR bR) (Some xR))
      (Lean.eq (sa_target_search f P R aR bR)
        (ImportedSearchArg.Option_some_inst1 Lean.Nat xL)) :=
    sa_option_eq_correspondence _ _ _ _
      (sub_imported_eq_sym _ _
        (search_arg_definition_certificate f P R aR bR))
      (sa_some_rel xR xL Hx).
  have Hall : PropSPropRel
      (forall yR,
        (is_true (leq aR yR) /\ is_true (ltn yR bR)) ->
        is_true (P (f yR)) -> is_true (R (f xR) (f yR)))
      (forall yL,
        Lean.And (sa_target_le aL yL) (sa_target_ltL yL bL) ->
        Lean.eq (sa_target_P P (sa_target_f f yL))
          ImportedSearchArg.Bool_true ->
        Lean.eq
          (sa_target_R R (sa_target_f f xL) (sa_target_f f yL))
          ImportedSearchArg.Bool_true).
  { apply sa_forall_nat_correspondence. intros yR yL Hy.
    apply prop_sprop_rel_intro.
    - intros HR HrangeL HPyL.
      apply (prop_to_sprop _ _
        (sa_Rff_true_correspondence f R xR xL yR yL Hx Hy)).
      apply HR.
      + exact (sprop_to_prop _ _
          (sa_range_correspondence _ _ _ _ _ _ Ha Hb Hy) HrangeL).
      + exact (sprop_to_prop _ _
          (sa_Pf_true_correspondence f P yR yL Hy) HPyL).
    - intro HL. apply strictly_inhabits. intros HrangeR HPyR.
      apply (sprop_to_prop _ _
        (sa_Rff_true_correspondence f R xR xL yR yL Hx Hy)).
      apply HL.
      + exact (prop_to_sprop _ _
          (sa_range_correspondence _ _ _ _ _ _ Ha Hb Hy) HrangeR).
      + exact (prop_to_sprop _ _
          (sa_Pf_true_correspondence f P yR yL Hy) HPyR). }
  apply prop_sprop_rel_intro.
  - intros HR HeqL. apply (prop_to_sprop _ _ Hall).
    apply HR. exact (sprop_to_prop _ _ Heq HeqL).
  - intro HL. apply strictly_inhabits. intro HeqR.
    apply (sprop_to_prop _ _ Hall).
    apply HL. exact (prop_to_sprop _ _ Heq HeqR).
Qed.

Lemma search_arg_extremum_statement_certificate {T : Type}
    (f : nat -> T) (P : T -> bool) (R : T -> T -> bool)
    (aR bR xR : nat) (aL bL xL : Lean.Nat) :
  SubNatRel aR aL -> SubNatRel bR bL -> SubNatRel xR xL ->
  PropSPropRel
    (sa_source_reflexive R -> sa_source_transitive R ->
      sa_source_total R ->
      Logic.eq (sa_source_search f P R aR bR) (Some xR) ->
      forall yR,
        (is_true (leq aR yR) /\ is_true (ltn yR bR)) ->
        is_true (P (f yR)) -> is_true (R (f xR) (f yR)))
    (sa_target_reflexive R -> sa_target_transitive R ->
      sa_target_total R ->
      Lean.eq (sa_target_search f P R aR bR)
        (ImportedSearchArg.Option_some_inst1 Lean.Nat xL) ->
      forall yL,
        Lean.And (sa_target_le aL yL) (sa_target_ltL yL bL) ->
        Lean.eq (sa_target_P P (sa_target_f f yL))
          ImportedSearchArg.Bool_true ->
        Lean.eq
          (sa_target_R R (sa_target_f f xL) (sa_target_f f yL))
          ImportedSearchArg.Bool_true).
Proof.
  intros Ha Hb Hx.
  have Hresult := sa_extremum_result_correspondence
    f P R aR bR xR aL bL xL Ha Hb Hx.
  apply prop_sprop_rel_intro.
  - intros HR HreflL HtransL HtotalL. apply (prop_to_sprop _ _ Hresult).
    apply HR.
    + exact (sprop_to_prop _ _ (sa_reflexive_correspondence R) HreflL).
    + exact (sprop_to_prop _ _ (sa_transitive_correspondence R) HtransL).
    + exact (sprop_to_prop _ _ (sa_total_correspondence R) HtotalL).
  - intro HL. apply strictly_inhabits. intros HreflR HtransR HtotalR.
    apply (sprop_to_prop _ _ Hresult).
    apply HL.
    + exact (prop_to_sprop _ _ (sa_reflexive_correspondence R) HreflR).
    + exact (prop_to_sprop _ _ (sa_transitive_correspondence R) HtransR).
    + exact (prop_to_sprop _ _ (sa_total_correspondence R) HtotalR).
Qed.

(** The final declaration is proof-dependent: both source and target carry an
    existence proof into their least-witness computation.  The following
    bridge derives the target least-witness laws from the actual imported
    [Nat.find] body and its [Subtype.property], rather than assuming a
    source/target find equality. *)

Definition sa_target_find_pred (pred : nat -> bool)
    (nL : Lean.Nat) : SProp :=
  Lean.eq (sa_target_nat_pred pred nL) ImportedSearchArg.Bool_true.

Definition sa_target_find_exists (pred : nat -> bool)
    (exR : exists n : nat, pred n) :
    ImportedSearchArg.Exists Lean.Nat (sa_target_find_pred pred).
Proof.
  destruct exR as [nR Hn].
  exact (ImportedSearchArg.Exists_intro Lean.Nat
    (sa_target_find_pred pred) (sub_nat_to_imported nR)
    (prop_to_sprop _ _
      (sa_nat_pred_true_correspondence pred nR
        (sub_nat_to_imported nR) (sub_nat_rel_canonical nR)) Hn)).
Defined.

Definition sa_target_find (pred : nat -> bool)
    (exR : exists n : nat, pred n) : Lean.Nat :=
  ImportedSearchArg.Nat_find (sa_target_find_pred pred)
    (fun nL => ImportedSearchArg.instDecidableEqBool
      (sa_target_nat_pred pred nL) ImportedSearchArg.Bool_true)
    (sa_target_find_exists pred exR).

Lemma sa_target_find_property (pred : nat -> bool)
    (exR : exists n : nat, pred n) :
  Lean.And
    (sa_target_find_pred pred (sa_target_find pred exR))
    (forall mL,
      sa_target_ltL mL (sa_target_find pred exR) ->
      ImportedSearchArg.Not (sa_target_find_pred pred mL)).
Proof.
  unfold sa_target_find, ImportedSearchArg.Nat_find.
  exact (ImportedSearchArg.property Lean.Nat
    (fun nL => Lean.And (sa_target_find_pred pred nL)
      (forall mL,
        sa_target_ltL mL nL ->
        ImportedSearchArg.Not (sa_target_find_pred pred mL)))
    (ImportedSearchArg.Nat_findX (sa_target_find_pred pred)
      (fun nL => ImportedSearchArg.instDecidableEqBool
        (sa_target_nat_pred pred nL) ImportedSearchArg.Bool_true)
      (sa_target_find_exists pred exR))).
Qed.

Lemma sa_ex_minn_pred (pred : nat -> bool)
    (exR : exists n : nat, pred n) :
  is_true (pred (ex_minn exR)).
Proof. case: (ex_minnP exR) => m Hpred Hmin. exact Hpred. Qed.

Lemma sa_ex_minn_min (pred : nat -> bool)
    (exR : exists n : nat, pred n) (n : nat) :
  is_true (pred n) -> is_true (leq (ex_minn exR) n).
Proof. case: (ex_minnP exR) => m Hpred Hmin. exact (Hmin n). Qed.

Lemma sa_find_correspondence (pred : nat -> bool)
    (exR : exists n : nat, pred n) :
  SubNatRel (ex_minn exR) (sa_target_find pred exR).
Proof.
  have Hproperty := sa_target_find_property pred exR.
  destruct Hproperty as [HfindPred HfindMin].
  have HfindPredR := sprop_to_prop _ _
    (sa_nat_pred_true_correspondence pred
      (sub_nat_to_rocq (sa_target_find pred exR))
      (sa_target_find pred exR)
      (sub_nat_rel_surjective (sa_target_find pred exR))) HfindPred.
  have Hleft : sa_target_le (sub_nat_to_imported (ex_minn exR))
      (sa_target_find pred exR) :=
    prop_to_sprop _ _
      (sa_le_correspondence _ _ _ _
        (sub_nat_rel_canonical (ex_minn exR))
        (sub_nat_rel_surjective (sa_target_find pred exR)))
      (sa_ex_minn_min pred exR _ HfindPredR).
  have HsourcePred := sa_ex_minn_pred pred exR.
  have HtargetPred :
      sa_target_find_pred pred (sub_nat_to_imported (ex_minn exR)) :=
    prop_to_sprop _ _
      (sa_nat_pred_true_correspondence pred (ex_minn exR)
        (sub_nat_to_imported (ex_minn exR))
        (sub_nat_rel_canonical (ex_minn exR))) HsourcePred.
  have Hright : sa_target_le (sa_target_find pred exR)
      (sub_nat_to_imported (ex_minn exR)) :=
    ImportedSearchArg.Or_elim _ _ _
      (ImportedSearchArg.Nat_lt_or_ge
        (sub_nat_to_imported (ex_minn exR))
        (sa_target_find pred exR))
      (fun Hlt => sa_imported_false_elim _
        (HfindMin (sub_nat_to_imported (ex_minn exR)) Hlt HtargetPred))
      (fun Hge => Hge).
  unfold SubNatRel.
  exact (ImportedSearchArg.Nat_le_antisymm
    (sub_nat_to_imported (ex_minn exR)) (sa_target_find pred exR)
    Hleft Hright).
Qed.

Definition sa_target_prop (P : nat -> Prop) (nL : Lean.Nat) : SProp :=
  StrictlyInhabited (P (sub_nat_to_rocq nL)).

Lemma sa_prop_at_correspondence (P : nat -> Prop) nR nL :
  SubNatRel nR nL -> PropSPropRel (P nR) (sa_target_prop P nL).
Proof.
  intro Hn. apply prop_sprop_rel_intro.
  - intro HP. unfold sa_target_prop.
    rw (sa_nat_back_of_rel nR nL Hn). exact (strictly_inhabits HP).
  - intro HL. apply strictly_inhabits. unfold sa_target_prop in HL.
    have HP := interpret_strict _ HL.
    rw (sa_nat_back_of_rel nR nL Hn) in HP. exact HP.
Qed.

Lemma sa_minimal_correspondence (pred : nat -> bool) nR nL :
  SubNatRel nR nL ->
  PropSPropRel
    (forall mR, is_true (pred mR) -> is_true (leq nR mR))
    (forall mL,
      sa_target_find_pred pred mL -> sa_target_le nL mL).
Proof.
  intro Hn. apply sa_forall_nat_correspondence. intros mR mL Hm.
  apply prop_sprop_rel_intro.
  - intros HR HpredL. apply (prop_to_sprop _ _
      (sa_le_correspondence _ _ _ _ Hn Hm)).
    apply HR. exact (sprop_to_prop _ _
      (sa_nat_pred_true_correspondence pred mR mL Hm) HpredL).
  - intro HL. apply strictly_inhabits. intro HpredR.
    apply (sprop_to_prop _ _ (sa_le_correspondence _ _ _ _ Hn Hm)).
    apply HL. exact (prop_to_sprop _ _
      (sa_nat_pred_true_correspondence pred mR mL Hm) HpredR).
Qed.

Lemma sa_prop_on_ex_minn_result_correspondence
    (P : nat -> Prop) (pred : nat -> bool) :
  PropSPropRel
    (exists nR,
      P nR /\ is_true (pred nR) /\
      forall mR, is_true (pred mR) -> is_true (leq nR mR))
    (ImportedSearchArg.Exists Lean.Nat (fun nL =>
      Lean.And (sa_target_prop P nL)
        (Lean.And (sa_target_find_pred pred nL)
          (forall mL,
            sa_target_find_pred pred mL -> sa_target_le nL mL)))).
Proof.
  apply sa_exists_nat_correspondence. intros nR nL Hn.
  apply sa_and_correspondence.
  - exact (sa_prop_at_correspondence P nR nL Hn).
  - apply sa_and_correspondence.
    + exact (sa_nat_pred_true_correspondence pred nR nL Hn).
    + exact (sa_minimal_correspondence pred nR nL Hn).
Qed.

Lemma prop_on_ex_minn_statement_certificate
    (P : nat -> Prop) (pred : nat -> bool)
    (exR : exists n : nat, pred n) :
  PropSPropRel
    (P (ex_minn exR) ->
      exists nR,
        P nR /\ is_true (pred nR) /\
        forall mR, is_true (pred mR) -> is_true (leq nR mR))
    (sa_target_prop P (sa_target_find pred exR) ->
      ImportedSearchArg.Exists Lean.Nat (fun nL =>
        Lean.And (sa_target_prop P nL)
          (Lean.And (sa_target_find_pred pred nL)
            (forall mL,
              sa_target_find_pred pred mL -> sa_target_le nL mL)))).
Proof.
  have Hfind := sa_find_correspondence pred exR.
  have Hprem := sa_prop_at_correspondence P
    (ex_minn exR) (sa_target_find pred exR) Hfind.
  have Hresult := sa_prop_on_ex_minn_result_correspondence P pred.
  apply prop_sprop_rel_intro.
  - intros HR HpremL. apply (prop_to_sprop _ _ Hresult).
    apply HR. exact (sprop_to_prop _ _ Hprem HpremL).
  - intro HL. apply strictly_inhabits. intro HpremR.
    apply (sprop_to_prop _ _ Hresult).
    apply HL. exact (prop_to_sprop _ _ Hprem HpremR).
Qed.

Print Assumptions search_arg_none_statement_certificate.
Print Assumptions search_arg_not_none_statement_certificate.
Print Assumptions search_arg_pred_statement_certificate.
Print Assumptions search_arg_in_range_statement_certificate.
Print Assumptions earliest_pred_element_exists_case_statement_certificate.
Print Assumptions search_arg_extremum_statement_certificate.
Print Assumptions sa_find_correspondence.
Print Assumptions prop_on_ex_minn_statement_certificate.
