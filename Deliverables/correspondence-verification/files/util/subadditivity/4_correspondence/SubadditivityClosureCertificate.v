From mathcomp Require Import ssreflect ssrbool ssrnat.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedSubadditivity.
From FoundationCertificates Require Import
  PropSPropFoundation LogicalRelation SubadditivityNatCorrespondence.
From prosa Require Import util.subadditivity.

(** Logical relation for the pointwise subadditivity definition.  The Lean
    side is the actual body imported from the compiled production artifact. *)
Lemma subadditive_at_correspondence_certificate :
  forall (fR : nat -> nat) (fL : Lean.Nat -> Lean.Nat),
    SubNatFunRel fR fL ->
    forall hR hL, SubNatRel hR hL ->
    PropSPropRel
      (prosa.util.subadditivity.subadditive_at fR hR)
      (Prosa_Util_Subadditivity_subadditive_at fL hL).
Proof.
  intros fR fL Hf hR hL Hh. apply prop_sprop_rel_intro.
  - intros Hsource aL bL HsumL.
    set (aR := sub_nat_to_rocq aL).
    set (bR := sub_nat_to_rocq bL).
    have Ha : SubNatRel aR aL := sub_nat_rel_surjective aL.
    have Hb : SubNatRel bR bL := sub_nat_rel_surjective bL.
    have HsumRel := sub_add_correspondence aR aL bR bL Ha Hb.
    have HsumR := sprop_to_prop _ _
      (sub_nat_eq_correspondence _ _ _ _ HsumRel Hh) HsumL.
    have HleR := Hsource aR bR HsumR.
    have Hfh := Hf hR hL Hh.
    have Hfa := Hf aR aL Ha.
    have Hfb := Hf bR bL Hb.
    have HaddF := sub_add_correspondence _ _ _ _ Hfa Hfb.
    exact (prop_to_sprop _ _
      (sub_nat_le_correspondence _ _ _ _ Hfh HaddF) HleR).
  - intro Htarget. apply strictly_inhabits.
    intros aR bR HsumR.
    have Ha := sub_nat_rel_canonical aR.
    have Hb := sub_nat_rel_canonical bR.
    have HsumRel := sub_add_correspondence _ _ _ _ Ha Hb.
    have HsumL := prop_to_sprop _ _
      (sub_nat_eq_correspondence _ _ _ _ HsumRel Hh) HsumR.
    have HleL := Htarget _ _ HsumL.
    have Hfh := Hf hR hL Hh.
    have Hfa := Hf _ _ Ha.
    have Hfb := Hf _ _ Hb.
    have HaddF := sub_add_correspondence _ _ _ _ Hfa Hfb.
    exact (sprop_to_prop _ _
      (sub_nat_le_correspondence _ _ _ _ Hfh HaddF) HleL).
Qed.

Lemma subadditive_until_correspondence_certificate :
  forall (fR : nat -> nat) (fL : Lean.Nat -> Lean.Nat),
    SubNatFunRel fR fL ->
    forall hR hL, SubNatRel hR hL ->
    PropSPropRel
      (prosa.util.subadditivity.subadditive_until fR hR)
      (Prosa_Util_Subadditivity_subadditive_until fL hL).
Proof.
  intros fR fL Hf hR hL Hh. apply prop_sprop_rel_intro.
  - intros Hsource xL HltL.
    set (xR := sub_nat_to_rocq xL).
    have Hx : SubNatRel xR xL := sub_nat_rel_surjective xL.
    have HltR := sprop_to_prop _ _
      (sub_nat_lt_correspondence _ _ _ _ Hx Hh) HltL.
    exact (prop_to_sprop _ _
      (subadditive_at_correspondence_certificate fR fL Hf xR xL Hx)
      (Hsource xR HltR)).
  - intro Htarget. apply strictly_inhabits.
    intros xR HltR.
    have Hx := sub_nat_rel_canonical xR.
    have HltL := prop_to_sprop _ _
      (sub_nat_lt_correspondence _ _ _ _ Hx Hh) HltR.
    exact (sprop_to_prop _ _
      (subadditive_at_correspondence_certificate fR fL Hf _ _ Hx)
      (Htarget _ HltL)).
Qed.

Lemma subadditive_correspondence_certificate :
  forall (fR : nat -> nat) (fL : Lean.Nat -> Lean.Nat),
    SubNatFunRel fR fL ->
    PropSPropRel
      (prosa.util.subadditivity.subadditive fR)
      (Prosa_Util_Subadditivity_subadditive fL).
Proof.
  intros fR fL Hf. apply prop_sprop_rel_intro.
  - intros Hsource hL.
    set (hR := sub_nat_to_rocq hL).
    have Hh : SubNatRel hR hL := sub_nat_rel_surjective hL.
    exact (prop_to_sprop _ _
      (subadditive_at_correspondence_certificate fR fL Hf hR hL Hh)
      (Hsource hR)).
  - intro Htarget. apply strictly_inhabits.
    intro hR. have Hh := sub_nat_rel_canonical hR.
    exact (sprop_to_prop _ _
      (subadditive_at_correspondence_certificate fR fL Hf _ _ Hh)
      (Htarget _)).
Qed.

Lemma subadditive_standard_correspondence_certificate :
  forall (fR : nat -> nat) (fL : Lean.Nat -> Lean.Nat),
    SubNatFunRel fR fL ->
    PropSPropRel
      (prosa.util.subadditivity.subadditive_standard fR)
      (Prosa_Util_Subadditivity_subadditive_standard fL).
Proof.
  intros fR fL Hf. apply prop_sprop_rel_intro.
  - intros Hsource aL bL.
    set (aR := sub_nat_to_rocq aL).
    set (bR := sub_nat_to_rocq bL).
    have Ha : SubNatRel aR aL := sub_nat_rel_surjective aL.
    have Hb : SubNatRel bR bL := sub_nat_rel_surjective bL.
    have Hab := sub_add_correspondence _ _ _ _ Ha Hb.
    have Hfab := Hf _ _ Hab.
    have Hfa := Hf _ _ Ha.
    have Hfb := Hf _ _ Hb.
    have HaddF := sub_add_correspondence _ _ _ _ Hfa Hfb.
    exact (prop_to_sprop _ _
      (sub_nat_le_correspondence _ _ _ _ Hfab HaddF)
      (Hsource aR bR)).
  - intro Htarget. apply strictly_inhabits.
    intros aR bR.
    have Ha := sub_nat_rel_canonical aR.
    have Hb := sub_nat_rel_canonical bR.
    have Hab := sub_add_correspondence _ _ _ _ Ha Hb.
    have Hfab := Hf _ _ Hab.
    have Hfa := Hf _ _ Ha.
    have Hfb := Hf _ _ Hb.
    have HaddF := sub_add_correspondence _ _ _ _ Hfa Hfb.
    exact (sprop_to_prop _ _
      (sub_nat_le_correspondence _ _ _ _ Hfab HaddF)
      (Htarget _ _)).
Qed.

Lemma sub_imported_iff_correspondence (P Q : Prop) (PL QL : SProp) :
  PropSPropRel P PL -> PropSPropRel Q QL ->
  PropSPropRel (P <-> Q) (ImportedSubadditivity.Iff PL QL).
Proof.
  intros HP HQ. apply prop_sprop_rel_intro.
  - intro H. apply ImportedSubadditivity.Iff_intro.
    + intro pL. apply (prop_to_sprop _ _ HQ).
      apply H. exact (sprop_to_prop _ _ HP pL).
    + intro qL. apply (prop_to_sprop _ _ HP).
      apply H. exact (sprop_to_prop _ _ HQ qL).
  - intro H. apply strictly_inhabits. split.
    + intro p. apply (sprop_to_prop _ _ HQ).
      exact (ImportedSubadditivity.mp _ _ H (prop_to_sprop _ _ HP p)).
    + intro q. apply (sprop_to_prop _ _ HP).
      exact (ImportedSubadditivity.mpr _ _ H (prop_to_sprop _ _ HQ q)).
Qed.

(** Exact-type provenance guards.  The semantic certificate below does not
    reference either guard or either theorem proof constant. *)
Definition rocq_subadditive_standard_equivalence_type_guard :
    forall f : nat -> nat,
      prosa.util.subadditivity.subadditive f <->
      prosa.util.subadditivity.subadditive_standard f :=
  prosa.util.subadditivity.subadditive_standard_equivalence.

Definition imported_subadditive_standard_equivalence_type_guard :
    forall f : Lean.Nat -> Lean.Nat,
      ImportedSubadditivity.Iff
        (Prosa_Util_Subadditivity_subadditive f)
        (Prosa_Util_Subadditivity_subadditive_standard f) :=
  Prosa_Util_Subadditivity_subadditive_standard_equivalence.

Lemma subadditive_standard_equivalence_statement_certificate :
  forall (fR : nat -> nat) (fL : Lean.Nat -> Lean.Nat),
    SubNatFunRel fR fL ->
    PropSPropRel
      (prosa.util.subadditivity.subadditive fR <->
       prosa.util.subadditivity.subadditive_standard fR)
      (ImportedSubadditivity.Iff
        (Prosa_Util_Subadditivity_subadditive fL)
        (Prosa_Util_Subadditivity_subadditive_standard fL)).
Proof.
  intros fR fL Hf. apply sub_imported_iff_correspondence.
  - exact (subadditive_correspondence_certificate fR fL Hf).
  - exact (subadditive_standard_correspondence_certificate fR fL Hf).
Qed.

Definition rocq_subadditive_leq_mul_type_guard :
  forall (f : nat -> nat),
    prosa.util.subadditivity.subadditive f ->
    forall n m : nat, is_true (ltn O m) ->
      is_true (leq (f (m * n)) (m * f n)) :=
  prosa.util.subadditivity.subadditive_leq_mul.

Definition imported_subadditive_leq_mul_type_guard :
  forall f : Lean.Nat -> Lean.Nat,
    Prosa_Util_Subadditivity_subadditive f ->
    forall n m : Lean.Nat,
      sub_imported_lt sub_imported_zero m ->
      sub_imported_le (f (sub_imported_mul m n))
        (sub_imported_mul m (f n)) :=
  Prosa_Util_Subadditivity_subadditive_leq_mul.

Lemma subadditive_leq_mul_statement_certificate :
  forall (fR : nat -> nat) (fL : Lean.Nat -> Lean.Nat),
    SubNatFunRel fR fL ->
    PropSPropRel
      (prosa.util.subadditivity.subadditive fR ->
       forall n m : nat, is_true (ltn O m) ->
         is_true (leq (fR (m * n)) (m * fR n)))
      (Prosa_Util_Subadditivity_subadditive fL ->
       forall n m : Lean.Nat,
         sub_imported_lt sub_imported_zero m ->
         sub_imported_le (fL (sub_imported_mul m n))
           (sub_imported_mul m (fL n))).
Proof.
  intros fR fL Hf. apply prop_sprop_rel_intro.
  - intros Hsource HsubL nL mL HpositiveL.
    set (nR := sub_nat_to_rocq nL).
    set (mR := sub_nat_to_rocq mL).
    have Hn : SubNatRel nR nL := sub_nat_rel_surjective nL.
    have Hm : SubNatRel mR mL := sub_nat_rel_surjective mL.
    have Hz : SubNatRel O sub_imported_zero :=
      @Lean.eq_refl Lean.Nat Lean.Nat_zero.
    have HpositiveR := sprop_to_prop _ _
      (sub_nat_lt_correspondence _ _ _ _ Hz Hm) HpositiveL.
    have HsubR := sprop_to_prop _ _
      (subadditive_correspondence_certificate fR fL Hf) HsubL.
    have HresultR := Hsource HsubR nR mR HpositiveR.
    have Hmn := sub_mul_correspondence _ _ _ _ Hm Hn.
    have Hfmn := Hf _ _ Hmn.
    have Hfn := Hf _ _ Hn.
    have Hmfn := sub_mul_correspondence _ _ _ _ Hm Hfn.
    exact (prop_to_sprop _ _
      (sub_nat_le_correspondence _ _ _ _ Hfmn Hmfn) HresultR).
  - intro Htarget. apply strictly_inhabits.
    intros HsubR nR mR HpositiveR.
    have Hn := sub_nat_rel_canonical nR.
    have Hm := sub_nat_rel_canonical mR.
    have Hz : SubNatRel O sub_imported_zero :=
      @Lean.eq_refl Lean.Nat Lean.Nat_zero.
    have HsubL := prop_to_sprop _ _
      (subadditive_correspondence_certificate fR fL Hf) HsubR.
    have HpositiveL := prop_to_sprop _ _
      (sub_nat_lt_correspondence _ _ _ _ Hz Hm) HpositiveR.
    have HresultL := Htarget HsubL
      (sub_nat_to_imported nR) (sub_nat_to_imported mR) HpositiveL.
    have Hmn := sub_mul_correspondence _ _ _ _ Hm Hn.
    have Hfmn := Hf _ _ Hmn.
    have Hfn := Hf _ _ Hn.
    have Hmfn := sub_mul_correspondence _ _ _ _ Hm Hfn.
    exact (sprop_to_prop _ _
      (sub_nat_le_correspondence _ _ _ _ Hfmn Hmfn) HresultL).
Qed.

Print Assumptions subadditive_at_correspondence_certificate.
Print Assumptions subadditive_until_correspondence_certificate.
Print Assumptions subadditive_correspondence_certificate.
Print Assumptions subadditive_standard_correspondence_certificate.
Print Assumptions subadditive_standard_equivalence_statement_certificate.
Print Assumptions subadditive_leq_mul_statement_certificate.
