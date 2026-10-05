From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedSuperadditivity ImportedNat.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence NatSubCorrespondence
  SuperadditivityBaseCorrespondence SuperadditivityMonotoneCertificate.
Require Import OfficialListMax0 OfficialSuperadditivityExtension.

Fixpoint sa_list_to_imported (xs : seq nat) :
    ImportedSuperadditivity.List_inst1 Lean.Nat :=
  match xs with
  | [::] => ImportedSuperadditivity.List_nil_inst1 Lean.Nat
  | x :: tail => ImportedSuperadditivity.List_cons_inst1 Lean.Nat
      (sub_nat_to_imported x) (sa_list_to_imported tail)
  end.

Fixpoint sa_list_to_rocq
    (xs : ImportedSuperadditivity.List_inst1 Lean.Nat) : seq nat :=
  match xs with
  | ImportedSuperadditivity.List_nil_inst1 => [::]
  | ImportedSuperadditivity.List_cons_inst1 x tail =>
      sub_nat_to_rocq x :: sa_list_to_rocq tail
  end.

Definition SaListRel (xsR : seq nat)
    (xsL : ImportedSuperadditivity.List_inst1 Lean.Nat) : SProp :=
  Lean.eq (sa_list_to_imported xsR) xsL.

Lemma sa_list_target_roundtrip xsL :
  SaListRel (sa_list_to_rocq xsL) xsL.
Proof.
  induction xsL as [|x xs IH]; cbn.
  - exact (@Lean.eq_refl _ _).
  - exact (sub_imported_eq_congr2
      (ImportedSuperadditivity.List_cons_inst1 Lean.Nat) _ _ _ _
      (sub_nat_rel_surjective x) IH).
Qed.

Definition sa_target_one : Lean.Nat :=
  ImportedSuperadditivity.OfNat_ofNat_inst1 Lean.Nat (Lean.Nat_succ Lean.Nat_zero)
    (ImportedSuperadditivity.instOfNatNat (Lean.Nat_succ Lean.Nat_zero)).

Definition sa_target_range (m n : Lean.Nat) :
    ImportedSuperadditivity.List_inst1 Lean.Nat :=
  ImportedSuperadditivity.List_range' m n sa_target_one.

Definition sa_target_index_iota (a b : Lean.Nat) :
    ImportedSuperadditivity.List_inst1 Lean.Nat :=
  ImportedSuperadditivity.Prosa_Util_List_index_iota a b.

Definition sa_target_sub (a b : Lean.Nat) : Lean.Nat :=
  ImportedSuperadditivity.HSub_hSub_inst7 Lean.Nat Lean.Nat Lean.Nat
    (ImportedSuperadditivity.instHSub_inst1 Lean.Nat
      ImportedSuperadditivity.instSubNat) a b.

Lemma sa_sub_zero (a : Lean.Nat) :
  Lean.eq (sa_target_sub a Lean.Nat_zero) a.
Proof. exact (@Lean.eq_refl Lean.Nat a). Qed.

Lemma sa_sub_succ (a b : Lean.Nat) :
  Lean.eq (sa_target_sub a (Lean.Nat_succ b))
    (ImportedSuperadditivity.Nat_pred (sa_target_sub a b)).
Proof.
  exact (@Lean.eq_refl Lean.Nat
    (ImportedSuperadditivity.Nat_pred (sa_target_sub a b))).
Qed.

Definition sa_pred_canonical (n : nat) :
  Lean.eq (ImportedSuperadditivity.Nat_pred (sub_nat_to_imported n))
    (sub_nat_to_imported (Nat.pred n)) :=
  match n return Lean.eq
      (ImportedSuperadditivity.Nat_pred (sub_nat_to_imported n))
      (sub_nat_to_imported (Nat.pred n)) with
  | O => @Lean.eq_refl Lean.Nat Lean.Nat_zero
  | S n' => @Lean.eq_refl Lean.Nat (sub_nat_to_imported n')
  end.

Lemma sa_sub_iterated_pred (a b : nat) :
  Lean.eq (sa_target_sub (sub_nat_to_imported a) (sub_nat_to_imported b))
    (sub_nat_to_imported (rocq_iterated_pred a b)).
Proof.
  induction b as [|b IH].
  - exact (sa_sub_zero (sub_nat_to_imported a)).
  - exact (sub_imported_eq_trans _ _ _ (sa_sub_succ _ _)
      (sub_imported_eq_trans _ _ _
        (sub_imported_eq_congr ImportedSuperadditivity.Nat_pred _ _ IH)
        (sa_pred_canonical (rocq_iterated_pred a b)))).
Qed.

Lemma sa_sub_canonical (a b : nat) :
  Lean.eq (sa_target_sub (sub_nat_to_imported a) (sub_nat_to_imported b))
    (sub_nat_to_imported (a - b)).
Proof.
  exact (sub_imported_eq_trans _ _ _ (sa_sub_iterated_pred a b)
    (coq_eq_to_imported_eq _ _
      (f_equal sub_nat_to_imported (rocq_iterated_pred_is_subn a b)))).
Qed.

Lemma sa_sub_related aR aL bR bL :
  SubNatRel aR aL -> SubNatRel bR bL ->
  SubNatRel (aR - bR) (sa_target_sub aL bL).
Proof.
  intros Ha Hb. unfold SubNatRel.
  exact (sub_imported_eq_trans _ _ _
    (sub_imported_eq_sym _ _ (sa_sub_canonical aR bR))
    (sub_imported_eq_congr2 sa_target_sub _ _ _ _ Ha Hb)).
Qed.

Lemma sa_iota_canonical (m n : nat) :
  SaListRel (iota m n)
    (sa_target_range (sub_nat_to_imported m) (sub_nat_to_imported n)).
Proof.
  revert m. induction n as [|n IH]; intro m.
  - cbn [iota sa_list_to_imported].
    exact (sub_imported_eq_sym _ _
      (ImportedSuperadditivity.Prosa_Validation_SuperadditivityInterface_rangeZero
        (sub_nat_to_imported m))).
  - cbn [iota sa_list_to_imported].
    refine (sub_imported_eq_trans _ _ _
      (sub_imported_eq_congr
        (ImportedSuperadditivity.List_cons_inst1 Lean.Nat
          (sub_nat_to_imported m)) _ _ (IH m.+1)) _).
    exact (sub_imported_eq_sym _ _
      (ImportedSuperadditivity.Prosa_Validation_SuperadditivityInterface_rangeSucc
        (sub_nat_to_imported m) (sub_nat_to_imported n))).
Qed.

Lemma sa_index_iota_related aR aL bR bL :
  SubNatRel aR aL -> SubNatRel bR bL ->
  SaListRel (index_iota aR bR) (sa_target_index_iota aL bL).
Proof.
  intros Ha Hb. rewrite /index_iota.
  have Hsub := sa_sub_related bR bL aR aL Hb Ha.
  have Hiota := sa_iota_canonical aR (bR - aR).
  unfold SaListRel in Hiota |- *.
  have Hiota' := sub_imported_eq_trans _ _ _ Hiota
    (sub_imported_eq_congr2 sa_target_range _ _ _ _ Ha Hsub).
  exact (sub_imported_eq_trans _ _ _ Hiota'
    (sub_imported_eq_sym _ _
      (ImportedSuperadditivity.Prosa_Validation_SuperadditivityInterface_productionIndexIota
        aL bL))).
Qed.

Definition sa_false_to_strict (H : ImportedSuperadditivity.False) :
    StrictlyInhabited Logic.False := match H with end.

Lemma sa_max_canonical (a b : nat) :
  Lean.eq
    (ImportedSuperadditivity.Nat_max
      (sub_nat_to_imported a) (sub_nat_to_imported b))
    (sub_nat_to_imported (maxn a b)).
Proof.
  unfold ImportedSuperadditivity.Nat_max,
    ImportedSuperadditivity.Max_max_inst1,
    ImportedSuperadditivity.Nat_instMax,
    ImportedSuperadditivity.maxOfLe_inst1.
  cbn.
  destruct (ImportedSuperadditivity.Nat_decLe
    (sub_nat_to_imported a) (sub_nat_to_imported b)) as [Hnle|Hle].
  - have Hrel := sub_nat_le_correspondence a (sub_nat_to_imported a)
      b (sub_nat_to_imported b) (sub_nat_rel_canonical a)
      (sub_nat_rel_canonical b).
    have Hnot : ~ is_true (leq a b).
    { intro Hab.
      exact (interpret_strict Logic.False
        (sa_false_to_strict
          (Hnle (prop_to_sprop _ _ Hrel Hab)))). }
    have Hba : is_true (leq b a).
    { move: (leq_total a b) => /orP [Hab|Hba]; last exact Hba.
      exfalso. exact (Hnot Hab). }
    have Hmax : maxn a b = a := (elimT maxn_idPl Hba).
    rewrite Hmax. exact (@Lean.eq_refl Lean.Nat (sub_nat_to_imported a)).
  - have Hab : is_true (leq a b).
    { have Hrel := sub_nat_le_correspondence a (sub_nat_to_imported a)
        b (sub_nat_to_imported b) (sub_nat_rel_canonical a)
        (sub_nat_rel_canonical b).
      exact (sprop_to_prop _ _ Hrel Hle). }
    have Hmax : maxn a b = b := (elimT maxn_idPr Hab).
    rewrite Hmax. exact (@Lean.eq_refl Lean.Nat (sub_nat_to_imported b)).
Qed.

Lemma sa_foldl_max_canonical (z : nat) (xs : seq nat) :
  Lean.eq
    (ImportedSuperadditivity.List_foldl_inst3 Lean.Nat Lean.Nat
      ImportedSuperadditivity.Nat_max (sub_nat_to_imported z)
      (sa_list_to_imported xs))
    (sub_nat_to_imported (foldl maxn z xs)).
Proof.
  revert z. induction xs as [|x xs IH]; intro z.
  - exact (@Lean.eq_refl Lean.Nat (sub_nat_to_imported z)).
  - cbn [sa_list_to_imported ImportedSuperadditivity.List_foldl_inst3 foldl].
    refine (sub_imported_eq_trans _ _ _
      (sub_imported_eq_congr
        (fun init => ImportedSuperadditivity.List_foldl_inst3
          Lean.Nat Lean.Nat ImportedSuperadditivity.Nat_max init
          (sa_list_to_imported xs)) _ _
        (sa_max_canonical z x)) _).
    exact (IH (maxn z x)).
Qed.

Lemma sa_max0_related xsR xsL :
  SaListRel xsR xsL ->
  SubNatRel (OfficialListMax0.max0 xsR)
    (ImportedSuperadditivity.Prosa_Util_List_max0 xsL).
Proof.
  intro Hxs. unfold OfficialListMax0.max0, SubNatRel.
  exact (sub_imported_eq_trans _ _ _
    (sub_imported_eq_sym _ _ (sa_foldl_max_canonical O xsR))
    (sub_imported_eq_congr
      ImportedSuperadditivity.Prosa_Util_List_max0 _ _ Hxs)).
Qed.

Definition sa_target_add (a b : Lean.Nat) : Lean.Nat :=
  ImportedSuperadditivity.HAdd_hAdd_inst7 Lean.Nat Lean.Nat Lean.Nat
    (ImportedSuperadditivity.instHAdd_inst1 Lean.Nat
      ImportedSuperadditivity.instAddNat) a b.

Lemma sa_add_canonical (a b : nat) :
  Lean.eq (sa_target_add (sub_nat_to_imported a) (sub_nat_to_imported b))
    (sub_nat_to_imported (a + b)).
Proof.
  induction b as [|b IH].
  - rewrite addn0. exact (@Lean.eq_refl Lean.Nat (sub_nat_to_imported a)).
  - rewrite addnS. cbn [sub_nat_to_imported sa_target_add].
    exact (sub_imported_eq_congr Lean.Nat_succ _ _ IH).
Qed.

Lemma sa_add_related aR aL bR bL :
  SubNatRel aR aL -> SubNatRel bR bL ->
  SubNatRel (aR + bR) (sa_target_add aL bL).
Proof.
  intros Ha Hb. unfold SubNatRel.
  exact (sub_imported_eq_trans _ _ _
    (sub_imported_eq_sym _ _ (sa_add_canonical aR bR))
    (sub_imported_eq_congr2 sa_target_add _ _ _ _ Ha Hb)).
Qed.

Definition sa_target_map (g : Lean.Nat -> Lean.Nat)
    (xs : ImportedSuperadditivity.List_inst1 Lean.Nat) :
    ImportedSuperadditivity.List_inst1 Lean.Nat :=
  ImportedSuperadditivity.List_map_inst3 Lean.Nat Lean.Nat g xs.

Lemma sa_map_canonical (gR : nat -> nat) (gL : Lean.Nat -> Lean.Nat) :
  SubNatFunRel gR gL -> forall xsR,
  SaListRel (map gR xsR) (sa_target_map gL (sa_list_to_imported xsR)).
Proof.
  intro Hg. induction xsR as [|x xs IH].
  - exact (@Lean.eq_refl _ _).
  - cbn [map sa_list_to_imported sa_target_map].
    exact (sub_imported_eq_congr2
      (ImportedSuperadditivity.List_cons_inst1 Lean.Nat) _ _ _ _
      (Hg x (sub_nat_to_imported x) (sub_nat_rel_canonical x)) IH).
Qed.

Lemma sa_map_related (gR : nat -> nat) (gL : Lean.Nat -> Lean.Nat) :
  SubNatFunRel gR gL -> forall xsR xsL,
  SaListRel xsR xsL -> SaListRel (map gR xsR) (sa_target_map gL xsL).
Proof.
  intros Hg xsR xsL Hxs. unfold SaListRel.
  exact (sub_imported_eq_trans _ _ _ (sa_map_canonical gR gL Hg xsR)
    (sub_imported_eq_congr (sa_target_map gL) _ _ Hxs)).
Qed.

Definition sa_source_summand (fR : nat -> nat) (hR aR : nat) : nat :=
  fR aR + fR (hR - aR).

Definition sa_target_summand (fL : Lean.Nat -> Lean.Nat)
    (hL aL : Lean.Nat) : Lean.Nat :=
  sa_target_add (fL aL) (fL (sa_target_sub hL aL)).

Lemma sa_summand_related fR fL hR hL :
  SubNatFunRel fR fL -> SubNatRel hR hL ->
  SubNatFunRel (sa_source_summand fR hR)
    (sa_target_summand fL hL).
Proof.
  intros Hf Hh aR aL Ha.
  apply sa_add_related.
  - exact (Hf aR aL Ha).
  - exact (Hf _ _ (sa_sub_related hR hL aR aL Hh Ha)).
Qed.

Lemma sa_minimal_extension_related fR fL hR hL :
  SubNatFunRel fR fL -> SubNatRel hR hL ->
  SubNatRel
    (OfficialSuperadditivityExtension.minimal_superadditive_extension fR hR)
    (ImportedSuperadditivity.Prosa_Util_Superadditivity_minimal_superadditive_extension
      fL hL).
Proof.
  intros Hf Hh.
  have Hone : SubNatRel 1 sa_target_one := sub_nat_rel_canonical 1.
  have Hidx := sa_index_iota_related 1 sa_target_one hR hL Hone Hh.
  have Hg := sa_summand_related fR fL hR hL Hf Hh.
  have Hmap := sa_map_related _ _ Hg _ _ Hidx.
  have Hmax := sa_max0_related _ _ Hmap.
  unfold OfficialSuperadditivityExtension.minimal_superadditive_extension.
  exact (sub_imported_eq_trans _ _ _ Hmax
    (sub_imported_eq_sym _ _
      (ImportedSuperadditivity.Prosa_Validation_SuperadditivityInterface_productionMinimal
        fL hL))).
Qed.

Definition sa_target_update (fL : Lean.Nat -> Lean.Nat)
    (hL tL : Lean.Nat) : Lean.Nat :=
  ImportedSuperadditivity.Prosa_Validation_SuperadditivityInterface_updateValue
    fL hL tL.

Definition sa_coq_false_to_target (H : Logic.False) :
    ImportedSuperadditivity.False := match H with end.

Lemma sa_update_related fR fL hR hL tR tL :
  SubNatFunRel fR fL -> SubNatRel hR hL -> SubNatRel tR tL ->
  SubNatRel
    (if tR == hR then
      OfficialSuperadditivityExtension.minimal_superadditive_extension fR hR
     else fR tR)
    (sa_target_update fL hL tL).
Proof.
  intros Hf Hh Ht. destruct (tR == hR) eqn:Heq.
  - have Hteq : Logic.eq tR hR := (elimT eqP Heq).
    have HteqL := prop_to_sprop _ _
      (sub_nat_eq_correspondence _ _ _ _ Ht Hh) Hteq.
    destruct HteqL.
    simpl.
    exact (sub_imported_eq_trans _ _ _
      (sa_minimal_extension_related fR fL hR tL Hf Hh)
      (sub_imported_eq_sym _ _
        (ImportedSuperadditivity.Prosa_Validation_SuperadditivityInterface_updateValueEq
          fL tL))).
  - assert (HneL : ImportedSuperadditivity.Ne Lean.Nat tL hL).
    { intro HteqL.
      have HteqR := sprop_to_prop _ _
        (sub_nat_eq_correspondence _ _ _ _ Ht Hh) HteqL.
      have HteqB : tR == hR := (introT eqP HteqR).
      rewrite HteqB in Heq.
      discriminate Heq. }
    simpl.
    exact (sub_imported_eq_trans _ _ _ (Hf tR tL Ht)
      (sub_imported_eq_sym _ _
        (ImportedSuperadditivity.Prosa_Validation_SuperadditivityInterface_updateValueNe
          fL hL tL HneL))).
Qed.

Print Assumptions sa_index_iota_related.
Print Assumptions sa_max0_related.
Print Assumptions sa_minimal_extension_related.
Print Assumptions sa_update_related.
