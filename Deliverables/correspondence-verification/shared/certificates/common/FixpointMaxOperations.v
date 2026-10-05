From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq bigop.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedFixpoint.
From FoundationCertificates Require Import
  PropSPropFoundation LogicalRelation SubadditivityNatCorrespondence
  FixpointBaseCorrespondence FixpointMonotoneCorrespondence.
Require Import GeneratedFixpointSourceAll.

(** Operation-level correspondence for the actual Fixpoint artifact.  This
    module deliberately does not use any of the four business max theorems. *)

Definition fixpoint_max_target (a b : Lean.Nat) : Lean.Nat :=
  ImportedFixpoint.Nat_max a b.

Lemma fixpoint_max_canonical (a b : nat) :
  Lean.eq (fixpoint_max_target (sub_nat_to_imported a)
    (sub_nat_to_imported b)) (sub_nat_to_imported (maxn a b)).
Proof.
  revert b. induction a as [|a IHa]; intro b; destruct b as [|b].
  - exact (ImportedFixpoint.Prosa_Validation_FixpointInterface_natMaxZeroLeft
      Lean.Nat_zero).
  - rewrite max0n.
    exact (ImportedFixpoint.Prosa_Validation_FixpointInterface_natMaxZeroLeft
      (sub_nat_to_imported b.+1)).
  - rewrite maxn0.
    exact (ImportedFixpoint.Prosa_Validation_FixpointInterface_natMaxZeroRight
      (sub_nat_to_imported a.+1)).
  - rewrite maxnSS. cbn [sub_nat_to_imported].
    exact (sub_imported_eq_trans _ _ _
      (ImportedFixpoint.Prosa_Validation_FixpointInterface_natMaxSuccSucc
        (sub_nat_to_imported a) (sub_nat_to_imported b))
      (sub_imported_eq_congr Lean.Nat_succ _ _ (IHa b))).
Qed.

Lemma fixpoint_max_related aR aL bR bL :
  SubNatRel aR aL -> SubNatRel bR bL ->
  SubNatRel (maxn aR bR) (fixpoint_max_target aL bL).
Proof.
  intros Ha Hb. unfold SubNatRel.
  exact (sub_imported_eq_trans _ _ _
    (sub_imported_eq_sym _ _ (fixpoint_max_canonical aR bR))
    (sub_imported_eq_congr2 fixpoint_max_target _ _ _ _ Ha Hb)).
Qed.

Print Assumptions fixpoint_max_related.

Fixpoint fixpoint_list_to_imported {A B : Type}
    (encode : A -> B) (xs : seq A) : ImportedFixpoint.List_inst1 B :=
  match xs with
  | [::] => ImportedFixpoint.List_nil_inst1 B
  | x :: tail => ImportedFixpoint.List_cons_inst1 B (encode x)
      (fixpoint_list_to_imported encode tail)
  end.

Definition fixpoint_options_to_imported (xs : seq (option nat)) :=
  fixpoint_list_to_imported fixpoint_option_to_imported xs.

Definition fixpoint_target_isSome
    (o : ImportedFixpoint.Option_inst1 Lean.Nat) : ImportedFixpoint.Bool :=
  ImportedFixpoint.Option_isSome_inst1 Lean.Nat o.

Definition fixpoint_target_getD
    (o : ImportedFixpoint.Option_inst1 Lean.Nat) : Lean.Nat :=
  ImportedFixpoint.Option_getD_inst1 Lean.Nat o Lean.Nat_zero.

Lemma fixpoint_isSome_canonical (o : option nat) :
  FixpointBoolRel (o != None)
    (fixpoint_target_isSome (fixpoint_option_to_imported o)).
Proof.
  destruct o as [n|]; cbn [FixpointBoolRel fixpoint_option_to_imported].
  - exact (ImportedFixpoint.Prosa_Validation_FixpointInterface_optionIsSomeSome
      Lean.Nat (sub_nat_to_imported n)).
  - exact (ImportedFixpoint.Prosa_Validation_FixpointInterface_optionIsSomeNone
      Lean.Nat).
Qed.

Lemma fixpoint_getD_canonical (o : option nat) :
  SubNatRel (@odflt nat O o)
    (fixpoint_target_getD (fixpoint_option_to_imported o)).
Proof.
  destruct o as [n|]; cbn [fixpoint_option_to_imported].
  - exact (sub_imported_eq_sym _ _
      (ImportedFixpoint.Prosa_Validation_FixpointInterface_optionGetDSome
        Lean.Nat (sub_nat_to_imported n) Lean.Nat_zero)).
  - exact (sub_imported_eq_sym _ _
      (ImportedFixpoint.Prosa_Validation_FixpointInterface_optionGetDNone
        Lean.Nat Lean.Nat_zero)).
Qed.

Print Assumptions fixpoint_isSome_canonical.
Print Assumptions fixpoint_getD_canonical.

Definition fixpoint_target_bigMaxOptions
    (xs : ImportedFixpoint.List_inst1
      (ImportedFixpoint.Option_inst1 Lean.Nat)) : Lean.Nat :=
  ImportedFixpoint.Prosa_Util_Minmax_bigMaxListCond_inst1
    (ImportedFixpoint.Option_inst1 Lean.Nat) xs
    fixpoint_target_isSome fixpoint_target_getD.

Lemma fixpoint_bigMaxOptions_nil :
  SubNatRel O (fixpoint_target_bigMaxOptions
    (fixpoint_options_to_imported [::])).
Proof.
  unfold SubNatRel, fixpoint_target_bigMaxOptions,
    fixpoint_options_to_imported; cbn [fixpoint_list_to_imported].
  exact (sub_imported_eq_sym _ _
    (ImportedFixpoint.Prosa_Validation_FixpointInterface_bigMaxNil
      (ImportedFixpoint.Option_inst1 Lean.Nat)
      fixpoint_target_isSome fixpoint_target_getD)).
Qed.

Print Assumptions fixpoint_bigMaxOptions_nil.

Definition fixpoint_source_bigMaxOptions (xs : seq (option nat)) : nat :=
  \max_(o <- xs | o != None) (@odflt nat O o).

Lemma fixpoint_bigMaxOptions_cons (o : option nat)
    (xs : seq (option nat)) :
  SubNatRel (fixpoint_source_bigMaxOptions xs)
    (fixpoint_target_bigMaxOptions (fixpoint_options_to_imported xs)) ->
  SubNatRel (fixpoint_source_bigMaxOptions (o :: xs))
    (fixpoint_target_bigMaxOptions
      (fixpoint_options_to_imported (o :: xs))).
Proof.
  intro IH.
  unfold fixpoint_source_bigMaxOptions in IH |- *.
  rewrite big_cons.
  destruct o as [n|].
  - cbn [fixpoint_options_to_imported fixpoint_list_to_imported].
    unfold SubNatRel, fixpoint_target_bigMaxOptions in IH |- *.
    exact (sub_imported_eq_trans _ _ _
      (sub_imported_eq_sym _ _
        (fixpoint_max_canonical n
          (\max_(i <- xs | i != None) (@odflt nat O i))))
      (sub_imported_eq_trans _ _ _
        (sub_imported_eq_congr
          (fixpoint_max_target (sub_nat_to_imported n)) _ _ IH)
        (sub_imported_eq_sym _ _
          (ImportedFixpoint.Prosa_Validation_FixpointInterface_bigMaxCons
            (ImportedFixpoint.Option_inst1 Lean.Nat)
            fixpoint_target_isSome fixpoint_target_getD
            (fixpoint_option_to_imported (Some n))
            (fixpoint_options_to_imported xs))))).
  - cbn [fixpoint_options_to_imported fixpoint_list_to_imported].
    unfold SubNatRel, fixpoint_target_bigMaxOptions in IH |- *.
    exact IH.
Qed.

Lemma fixpoint_bigMaxOptions_canonical (xs : seq (option nat)) :
  SubNatRel (fixpoint_source_bigMaxOptions xs)
    (fixpoint_target_bigMaxOptions (fixpoint_options_to_imported xs)).
Proof.
  induction xs as [|o xs IH].
  - unfold fixpoint_source_bigMaxOptions. rewrite big_nil.
    exact fixpoint_bigMaxOptions_nil.
  - exact (fixpoint_bigMaxOptions_cons o xs IH).
Qed.

Print Assumptions fixpoint_bigMaxOptions_canonical.

Definition fixpoint_nat_list_to_imported (xs : seq nat) :=
  fixpoint_list_to_imported sub_nat_to_imported xs.

Definition FixpointBinaryFunRel (fR : nat -> nat -> nat)
    (fL : Lean.Nat -> Lean.Nat -> Lean.Nat) : SProp :=
  forall sR sL, SubNatRel sR sL -> SubNatFunRel (fR sR) (fL sL).

Definition fixpoint_target_map_results
    (fL : Lean.Nat -> Lean.Nat -> Lean.Nat)
    (spL : ImportedFixpoint.List_inst1 Lean.Nat) (hL : Lean.Nat) :=
  ImportedFixpoint.List_map_inst3 Lean.Nat
    (ImportedFixpoint.Option_inst1 Lean.Nat)
    (fun s => ImportedFixpoint.Prosa_Util_Fixpoint_find_fixpoint
      (fL s) hL) spL.

Lemma fixpoint_map_results_canonical
    (fR : nat -> nat -> nat) (fL : Lean.Nat -> Lean.Nat -> Lean.Nat)
    (spR : seq nat) (hR : nat) (hL : Lean.Nat) :
  FixpointBinaryFunRel fR fL -> SubNatRel hR hL ->
  Lean.eq
    (fixpoint_options_to_imported
      [seq GeneratedFixpointSourceAll.GeneratedFixpointSourceAll.find_fixpoint
        (fR s) hR | s <- spR])
    (fixpoint_target_map_results fL
      (fixpoint_nat_list_to_imported spR) hL).
Proof.
  intros Hf Hh. induction spR as [|s sp IH].
  - unfold fixpoint_target_map_results, fixpoint_nat_list_to_imported,
      fixpoint_options_to_imported.
    cbn [fixpoint_list_to_imported map].
    exact (sub_imported_eq_sym _ _
      (ImportedFixpoint.Prosa_Validation_FixpointInterface_listMapNil
        Lean.Nat (ImportedFixpoint.Option_inst1 Lean.Nat)
        (fun s => ImportedFixpoint.Prosa_Util_Fixpoint_find_fixpoint
          (fL s) hL))).
  - unfold fixpoint_target_map_results in IH |- *.
    cbn [map fixpoint_nat_list_to_imported fixpoint_options_to_imported
      fixpoint_list_to_imported].
    have Hs := sub_nat_rel_canonical s.
    have Hhead := fixpoint_correspondence (fR s)
      (fL (sub_nat_to_imported s)) hR hL (Hf s _ Hs) Hh.
    have HheadEq := fixpoint_option_rel_eq _ _ Hhead.
    exact (sub_imported_eq_trans _ _ _
      (sub_imported_eq_congr2
        (ImportedFixpoint.List_cons_inst1
          (ImportedFixpoint.Option_inst1 Lean.Nat)) _ _ _ _
        HheadEq IH)
      (sub_imported_eq_sym _ _
        (ImportedFixpoint.Prosa_Validation_FixpointInterface_listMapCons
          Lean.Nat (ImportedFixpoint.Option_inst1 Lean.Nat)
          (fun s => ImportedFixpoint.Prosa_Util_Fixpoint_find_fixpoint
            (fL s) hL)
          (sub_nat_to_imported s)
          (fixpoint_nat_list_to_imported sp)))).
Qed.

Print Assumptions fixpoint_map_results_canonical.

Definition fixpoint_target_allSome
    (xs : ImportedFixpoint.List_inst1
      (ImportedFixpoint.Option_inst1 Lean.Nat)) : ImportedFixpoint.Bool :=
  ImportedFixpoint.List_all_inst1
    (ImportedFixpoint.Option_inst1 Lean.Nat) xs fixpoint_target_isSome.

Lemma fixpoint_allSome_canonical (xs : seq (option nat)) :
  FixpointBoolRel (all (fun o => o != None) xs)
    (fixpoint_target_allSome (fixpoint_options_to_imported xs)).
Proof.
  induction xs as [|o xs IH].
  - exact (ImportedFixpoint.Prosa_Validation_FixpointInterface_listAllNil
      (ImportedFixpoint.Option_inst1 Lean.Nat) fixpoint_target_isSome).
  - cbn [all]. destruct o as [n|].
    + unfold fixpoint_target_allSome in IH |- *.
      cbn [fixpoint_options_to_imported fixpoint_list_to_imported].
      have Hcons := imported_eq_to_coq_eq _ _
        (ImportedFixpoint.Prosa_Validation_FixpointInterface_listAllCons
          (ImportedFixpoint.Option_inst1 Lean.Nat) fixpoint_target_isSome
          (fixpoint_option_to_imported (Some n))
          (fixpoint_options_to_imported xs)).
      have Hhead := imported_eq_to_coq_eq _ _
        (fixpoint_isSome_canonical (Some n)).
      destruct (all (fun o => o != None) xs) eqn:Htail;
        cbn [FixpointBoolRel] in IH |- *;
        have IH' := imported_eq_to_coq_eq _ _ IH;
        rewrite Hcons Hhead IH'; cbn;
        exact (@Lean.eq_refl _ _).
    + unfold fixpoint_target_allSome in IH |- *.
      cbn [fixpoint_options_to_imported fixpoint_list_to_imported].
      have Hcons := imported_eq_to_coq_eq _ _
        (ImportedFixpoint.Prosa_Validation_FixpointInterface_listAllCons
          (ImportedFixpoint.Option_inst1 Lean.Nat) fixpoint_target_isSome
          (fixpoint_option_to_imported None)
          (fixpoint_options_to_imported xs)).
      have Hhead := imported_eq_to_coq_eq _ _
        (fixpoint_isSome_canonical None).
      destruct (all (fun o => o != None) xs) eqn:Htail;
        cbn [FixpointBoolRel] in IH |- *;
        have IH' := imported_eq_to_coq_eq _ _ IH;
        rewrite Hcons Hhead IH'; cbn;
        exact (@Lean.eq_refl _ _).
Qed.

Print Assumptions fixpoint_allSome_canonical.

Lemma fixpoint_option_rel_of_eq (oR : option nat)
    (oL : ImportedFixpoint.Option_inst1 Lean.Nat) :
  Lean.eq (fixpoint_option_to_imported oR) oL ->
  FixpointOptionRel oR oL.
Proof.
  destruct oR; cbn [FixpointOptionRel fixpoint_option_to_imported];
    exact (fun H => sub_imported_eq_sym _ _ H).
Qed.

Lemma fixpoint_max_of_seq_canonical
    (fR : nat -> nat -> nat) (fL : Lean.Nat -> Lean.Nat -> Lean.Nat)
    (spR : seq nat) (hR : nat) (hL : Lean.Nat) :
  FixpointBinaryFunRel fR fL -> SubNatRel hR hL ->
  FixpointOptionRel
    (GeneratedFixpointSourceAll.GeneratedFixpointSourceAll.find_max_fixpoint_of_seq
      fR spR hR)
    (ImportedFixpoint.Prosa_Util_Fixpoint_find_max_fixpoint_of_seq
      fL (fixpoint_nat_list_to_imported spR) hL).
Proof.
  intros Hf Hh.
  set (fpsR := [seq GeneratedFixpointSourceAll.GeneratedFixpointSourceAll.find_fixpoint
    (fR s) hR | s <- spR]).
  set (fpsL := fixpoint_target_map_results fL
    (fixpoint_nat_list_to_imported spR) hL).
  have Hmap := fixpoint_map_results_canonical fR fL spR hR hL Hf Hh.
  have HmapP := imported_eq_to_coq_eq _ _ Hmap.
  have Hall := fixpoint_allSome_canonical fpsR.
  have Hmax := fixpoint_bigMaxOptions_canonical fpsR.
  unfold GeneratedFixpointSourceAll.GeneratedFixpointSourceAll.find_max_fixpoint_of_seq.
  change (FixpointOptionRel
    (if all (fun o => o != None) fpsR then
      Some (fixpoint_source_bigMaxOptions fpsR) else None)
    (ImportedFixpoint.Prosa_Util_Fixpoint_find_max_fixpoint_of_seq
      fL (fixpoint_nat_list_to_imported spR) hL)).
  destruct (all (fun o => o != None) fpsR) eqn:Hcase.
  - cbn [FixpointOptionRel].
    have HallP := imported_eq_to_coq_eq _ _ Hall.
    have Hproj := imported_eq_to_coq_eq _ _
      (ImportedFixpoint.Prosa_Validation_FixpointInterface_findMaxFixpointOfSeqProjection
        fL (fixpoint_nat_list_to_imported spR) hL).
    rewrite Hproj.
    unfold fpsL, fixpoint_target_map_results in HmapP |- *.
    rewrite <- HmapP.
    unfold fixpoint_target_allSome in HallP.
    rewrite HallP.
    exact (sub_imported_eq_sym _ _
      (sub_imported_eq_congr
        (ImportedFixpoint.Option_some_inst1 Lean.Nat) _ _ Hmax)).
  - cbn [FixpointOptionRel].
    have HallP := imported_eq_to_coq_eq _ _ Hall.
    have Hproj := imported_eq_to_coq_eq _ _
      (ImportedFixpoint.Prosa_Validation_FixpointInterface_findMaxFixpointOfSeqProjection
        fL (fixpoint_nat_list_to_imported spR) hL).
    rewrite Hproj.
    unfold fpsL, fixpoint_target_map_results in HmapP |- *.
    rewrite <- HmapP.
    unfold fixpoint_target_allSome in HallP.
    rewrite HallP.
    exact (@Lean.eq_refl _ _).
Qed.

Print Assumptions fixpoint_max_of_seq_canonical.

Definition FixpointNatListRel (spR : seq nat)
    (spL : ImportedFixpoint.List_inst1 Lean.Nat) : SProp :=
  Lean.eq (fixpoint_nat_list_to_imported spR) spL.

Lemma fixpoint_max_of_seq_correspondence
    (fR : nat -> nat -> nat) (fL : Lean.Nat -> Lean.Nat -> Lean.Nat)
    (spR : seq nat) (spL : ImportedFixpoint.List_inst1 Lean.Nat)
    (hR : nat) (hL : Lean.Nat) :
  FixpointBinaryFunRel fR fL -> FixpointNatListRel spR spL ->
  SubNatRel hR hL ->
  FixpointOptionRel
    (GeneratedFixpointSourceAll.GeneratedFixpointSourceAll.find_max_fixpoint_of_seq
      fR spR hR)
    (ImportedFixpoint.Prosa_Util_Fixpoint_find_max_fixpoint_of_seq
      fL spL hL).
Proof.
  intros Hf Hsp Hh.
  have HspP := imported_eq_to_coq_eq _ _ Hsp.
  destruct HspP.
  exact (fixpoint_max_of_seq_canonical fR fL spR hR hL Hf Hh).
Qed.

Print Assumptions fixpoint_max_of_seq_correspondence.

Lemma fixpoint_source_iota_succ (n : nat) :
  Logic.eq (iota O (S n)) (iota O n ++ [:: n]).
Proof.
  rewrite -addn1 iotaD add0n.
  reflexivity.
Qed.

Definition fixpoint_target_append {A : Type}
    (xs ys : ImportedFixpoint.List_inst1 A) :=
  ImportedFixpoint.List_append_inst1 A xs ys.

Lemma fixpoint_nat_list_append_canonical (xs ys : seq nat) :
  Lean.eq (fixpoint_nat_list_to_imported (xs ++ ys))
    (fixpoint_target_append
      (fixpoint_nat_list_to_imported xs)
      (fixpoint_nat_list_to_imported ys)).
Proof.
  induction xs as [|x xs IH].
  - exact (sub_imported_eq_sym _ _
      (ImportedFixpoint.Prosa_Validation_FixpointInterface_listAppendNil
        Lean.Nat (fixpoint_nat_list_to_imported ys))).
  - cbn [cat fixpoint_nat_list_to_imported fixpoint_list_to_imported].
    exact (sub_imported_eq_trans _ _ _
      (sub_imported_eq_congr
        (ImportedFixpoint.List_cons_inst1 Lean.Nat
          (sub_nat_to_imported x)) _ _ IH)
      (sub_imported_eq_sym _ _
        (ImportedFixpoint.Prosa_Validation_FixpointInterface_listAppendCons
          Lean.Nat (sub_nat_to_imported x)
          (fixpoint_nat_list_to_imported xs)
          (fixpoint_nat_list_to_imported ys)))).
Qed.

Print Assumptions fixpoint_nat_list_append_canonical.

Lemma fixpoint_range_canonical (n : nat) :
  Lean.eq (fixpoint_nat_list_to_imported (iota O n))
    (ImportedFixpoint.List_range (sub_nat_to_imported n)).
Proof.
  induction n as [|n IH].
  - exact (sub_imported_eq_sym _ _
      ImportedFixpoint.Prosa_Validation_FixpointInterface_listRangeZero).
  - rewrite (fixpoint_source_iota_succ n).
    exact (sub_imported_eq_trans _ _ _
      (fixpoint_nat_list_append_canonical (iota O n) [:: n])
      (sub_imported_eq_trans _ _ _
        (sub_imported_eq_congr2 fixpoint_target_append _ _ _ _
          IH (@Lean.eq_refl _ _))
        (sub_imported_eq_sym _ _
          (ImportedFixpoint.Prosa_Validation_FixpointInterface_listRangeSucc
            (sub_nat_to_imported n))))).
Qed.

Print Assumptions fixpoint_range_canonical.

Definition FixpointNatPredRel (pR : nat -> bool)
    (pL : Lean.Nat -> ImportedFixpoint.Bool) : SProp :=
  forall xR xL, SubNatRel xR xL -> FixpointBoolRel (pR xR) (pL xL).

Definition fixpoint_target_filter (pL : Lean.Nat -> ImportedFixpoint.Bool)
    (xs : ImportedFixpoint.List_inst1 Lean.Nat) :=
  ImportedFixpoint.List_filter_inst1 Lean.Nat pL xs.

Lemma fixpoint_filter_canonical (pR : nat -> bool)
    (pL : Lean.Nat -> ImportedFixpoint.Bool) (xs : seq nat) :
  FixpointNatPredRel pR pL ->
  Lean.eq (fixpoint_nat_list_to_imported (filter pR xs))
    (fixpoint_target_filter pL (fixpoint_nat_list_to_imported xs)).
Proof.
  intro Hp. induction xs as [|x xs IH].
  - exact (sub_imported_eq_sym _ _
      (ImportedFixpoint.Prosa_Validation_FixpointInterface_listFilterNil
        Lean.Nat pL)).
  - have Hx := Hp x (sub_nat_to_imported x)
      (sub_nat_rel_canonical x).
    destruct (pR x) eqn:Hpx;
      cbn [FixpointBoolRel] in Hx;
      have HxP := imported_eq_to_coq_eq _ _ Hx;
      have Hstep := imported_eq_to_coq_eq _ _
        (ImportedFixpoint.Prosa_Validation_FixpointInterface_listFilterCons
          Lean.Nat pL (sub_nat_to_imported x)
          (fixpoint_nat_list_to_imported xs));
      unfold fixpoint_target_filter in IH |- *;
      cbn [filter fixpoint_nat_list_to_imported fixpoint_list_to_imported];
      rewrite Hpx Hstep HxP.
    + exact (sub_imported_eq_congr
        (ImportedFixpoint.List_cons_inst1 Lean.Nat
          (sub_nat_to_imported x)) _ _ IH).
    + exact IH.
Qed.

Print Assumptions fixpoint_filter_canonical.

Definition fixpoint_target_any (pL : Lean.Nat -> ImportedFixpoint.Bool)
    (xs : ImportedFixpoint.List_inst1 Lean.Nat) :=
  ImportedFixpoint.List_any_inst1 Lean.Nat xs pL.

Lemma fixpoint_any_canonical (pR : nat -> bool)
    (pL : Lean.Nat -> ImportedFixpoint.Bool) (xs : seq nat) :
  FixpointNatPredRel pR pL ->
  FixpointBoolRel (has pR xs)
    (fixpoint_target_any pL (fixpoint_nat_list_to_imported xs)).
Proof.
  intro Hp. induction xs as [|x xs IH].
  - exact (ImportedFixpoint.Prosa_Validation_FixpointInterface_listAnyNil
      Lean.Nat pL).
  - have Hx := Hp x (sub_nat_to_imported x)
      (sub_nat_rel_canonical x).
    destruct (pR x) eqn:Hpx;
      cbn [FixpointBoolRel] in Hx;
      have HxP := imported_eq_to_coq_eq _ _ Hx;
      have Hstep := imported_eq_to_coq_eq _ _
        (ImportedFixpoint.Prosa_Validation_FixpointInterface_listAnyCons
          Lean.Nat pL (sub_nat_to_imported x)
          (fixpoint_nat_list_to_imported xs));
      unfold fixpoint_target_any in IH |- *;
      cbn [fixpoint_nat_list_to_imported fixpoint_list_to_imported];
      cbn [has]; rewrite Hpx Hstep HxP; cbn.
    + exact (@Lean.eq_refl _ _).
    + destruct (has pR xs) eqn:Htail;
        cbn [FixpointBoolRel] in IH |- *;
        have IH' := imported_eq_to_coq_eq _ _ IH;
        rewrite IH';
        exact (@Lean.eq_refl _ _).
Qed.

Print Assumptions fixpoint_any_canonical.

Lemma fixpoint_max_wrapper_canonical
    (L : nat) (pR : nat -> bool)
    (pL : Lean.Nat -> ImportedFixpoint.Bool)
    (fR : nat -> nat -> nat) (fL : Lean.Nat -> Lean.Nat -> Lean.Nat)
    (hR : nat) (hL : Lean.Nat) :
  FixpointNatPredRel pR pL -> FixpointBinaryFunRel fR fL ->
  SubNatRel hR hL ->
  FixpointOptionRel
    (GeneratedFixpointSourceAll.GeneratedFixpointSourceAll.find_max_fixpoint
      L pR fR hR)
    (ImportedFixpoint.Prosa_Util_Fixpoint_find_max_fixpoint
      (sub_nat_to_imported L) pL fL hL).
Proof.
  intros Hp Hf Hh.
  set (rangeR := iota O L).
  set (spR := filter pR rangeR).
  have Hrange := fixpoint_range_canonical L.
  have Hfilter := fixpoint_filter_canonical pR pL rangeR Hp.
  have Hsp := sub_imported_eq_trans _ _ _ Hfilter
    (sub_imported_eq_congr (fixpoint_target_filter pL) _ _ Hrange).
  have Hany := fixpoint_any_canonical pR pL rangeR Hp.
  have Hmax := fixpoint_max_of_seq_correspondence
    fR fL spR
    (fixpoint_target_filter pL
      (ImportedFixpoint.List_range (sub_nat_to_imported L)))
    hR hL Hf Hsp Hh.
  unfold GeneratedFixpointSourceAll.GeneratedFixpointSourceAll.find_max_fixpoint.
  change (FixpointOptionRel
    (if has pR rangeR then
      GeneratedFixpointSourceAll.GeneratedFixpointSourceAll.find_max_fixpoint_of_seq
        fR spR hR else None)
    (ImportedFixpoint.Prosa_Util_Fixpoint_find_max_fixpoint
      (sub_nat_to_imported L) pL fL hL)).
  destruct (has pR rangeR) eqn:Hcase.
  - cbn [FixpointBoolRel] in Hany.
    have HanyP := imported_eq_to_coq_eq _ _ Hany.
    have HrangeP := imported_eq_to_coq_eq _ _ Hrange.
    have Hproj := imported_eq_to_coq_eq _ _
      (ImportedFixpoint.Prosa_Validation_FixpointInterface_findMaxFixpointProjection
        (sub_nat_to_imported L) pL fL hL).
    rewrite Hproj.
    unfold fixpoint_target_any in HanyP.
    rewrite HrangeP in HanyP.
    rewrite HanyP.
    exact Hmax.
  - cbn [FixpointBoolRel] in Hany.
    have HanyP := imported_eq_to_coq_eq _ _ Hany.
    have HrangeP := imported_eq_to_coq_eq _ _ Hrange.
    have Hproj := imported_eq_to_coq_eq _ _
      (ImportedFixpoint.Prosa_Validation_FixpointInterface_findMaxFixpointProjection
        (sub_nat_to_imported L) pL fL hL).
    rewrite Hproj.
    unfold fixpoint_target_any in HanyP.
    rewrite HrangeP in HanyP.
    rewrite HanyP.
    exact (@Lean.eq_refl _ _).
Qed.

Print Assumptions fixpoint_max_wrapper_canonical.

Lemma fixpoint_max_wrapper_correspondence
    (LR : nat) (LL : Lean.Nat)
    (pR : nat -> bool) (pL : Lean.Nat -> ImportedFixpoint.Bool)
    (fR : nat -> nat -> nat) (fL : Lean.Nat -> Lean.Nat -> Lean.Nat)
    (hR : nat) (hL : Lean.Nat) :
  SubNatRel LR LL -> FixpointNatPredRel pR pL ->
  FixpointBinaryFunRel fR fL -> SubNatRel hR hL ->
  FixpointOptionRel
    (GeneratedFixpointSourceAll.GeneratedFixpointSourceAll.find_max_fixpoint
      LR pR fR hR)
    (ImportedFixpoint.Prosa_Util_Fixpoint_find_max_fixpoint
      LL pL fL hL).
Proof.
  intros HL Hp Hf Hh.
  have HLP := imported_eq_to_coq_eq _ _ HL.
  destruct HLP.
  exact (fixpoint_max_wrapper_canonical LR pR pL fR fL hR hL
    Hp Hf Hh).
Qed.

Print Assumptions fixpoint_max_wrapper_correspondence.

Fixpoint fixpoint_nat_list_to_rocq
    (xs : ImportedFixpoint.List_inst1 Lean.Nat) : seq nat :=
  match xs with
  | ImportedFixpoint.List_nil_inst1 => [::]
  | ImportedFixpoint.List_cons_inst1 x tail =>
      sub_nat_to_rocq x :: fixpoint_nat_list_to_rocq tail
  end.

Lemma fixpoint_nat_list_source_roundtrip (xs : seq nat) :
  Logic.eq (fixpoint_nat_list_to_rocq
    (fixpoint_nat_list_to_imported xs)) xs.
Proof.
  induction xs as [|x xs IH]; cbn; first reflexivity.
  rewrite (sub_nat_rocq_roundtrip x) IH. reflexivity.
Qed.

Lemma fixpoint_nat_list_target_roundtrip
    (xs : ImportedFixpoint.List_inst1 Lean.Nat) :
  Lean.eq (fixpoint_nat_list_to_imported
    (fixpoint_nat_list_to_rocq xs)) xs.
Proof.
  induction xs as [|x xs IH]; cbn.
  - exact (@Lean.eq_refl _ _).
  - exact (sub_imported_eq_congr2
      (ImportedFixpoint.List_cons_inst1 Lean.Nat) _ _ _ _
      (sub_nat_imported_roundtrip x) IH).
Qed.

Definition fixpoint_target_mem (x : Lean.Nat)
    (xs : ImportedFixpoint.List_inst1 Lean.Nat) : SProp :=
  ImportedFixpoint.List_Mem_inst1 Lean.Nat x xs.

Definition fixpoint_mem_head_truth (a b : bool) :
  SubNatTruth a -> SubNatTruth (a || b) :=
  match a, b return SubNatTruth a -> SubNatTruth (a || b) with
  | true, _ => fun _ => sub_nat_truth_intro
  | false, _ => sub_nat_false_elim _
  end.

Definition fixpoint_eq_refl_truth (x : nat) : SubNatTruth (x == x).
Proof. rewrite eqxx. exact sub_nat_truth_intro. Defined.

Definition fixpoint_mem_tail_truth (a b : bool) :
  SubNatTruth b -> SubNatTruth (a || b) :=
  match a, b return SubNatTruth b -> SubNatTruth (a || b) with
  | true, _ => fun _ => sub_nat_truth_intro
  | false, true => fun _ => sub_nat_truth_intro
  | false, false => fun H => H
  end.

Definition fixpoint_mem_head_of_source_eq (x y : nat)
    (xs : ImportedFixpoint.List_inst1 Lean.Nat) :
  Logic.eq x y ->
  fixpoint_target_mem (sub_nat_to_imported x)
    (ImportedFixpoint.List_cons_inst1 Lean.Nat
      (sub_nat_to_imported y) xs) :=
  fun H => match H in Logic.eq _ z return
      fixpoint_target_mem (sub_nat_to_imported x)
        (ImportedFixpoint.List_cons_inst1 Lean.Nat
          (sub_nat_to_imported z) xs)
    with
    | Logic.eq_refl =>
      ImportedFixpoint.List_Mem_head_inst1 Lean.Nat
        (sub_nat_to_imported x) xs
    end.

Fixpoint fixpoint_seq_mem_forward (x : nat) (xs : seq nat) :
  SubNatTruth (x \in xs) ->
  fixpoint_target_mem (sub_nat_to_imported x)
    (fixpoint_nat_list_to_imported xs) :=
  match xs as zs return SubNatTruth (x \in zs) ->
      fixpoint_target_mem (sub_nat_to_imported x)
        (fixpoint_nat_list_to_imported zs) with
  | [::] => sub_nat_false_elim _
  | y :: ys =>
      match @eqP _ x y as r in reflect _ b return
        SubNatTruth (b || (x \in ys)) ->
        fixpoint_target_mem (sub_nat_to_imported x)
          (ImportedFixpoint.List_cons_inst1 Lean.Nat
            (sub_nat_to_imported y) (fixpoint_nat_list_to_imported ys)) with
      | ReflectT Hxy => fun _ =>
          fixpoint_mem_head_of_source_eq x y _ Hxy
      | ReflectF _ => fun H =>
          ImportedFixpoint.List_Mem_tail_inst1 Lean.Nat
            (sub_nat_to_imported x) (sub_nat_to_imported y) _
            (fixpoint_seq_mem_forward x ys H)
      end
  end.

Fixpoint fixpoint_imported_mem_decoded (x : Lean.Nat)
    (xs : ImportedFixpoint.List_inst1 Lean.Nat)
    (H : fixpoint_target_mem x xs) :
    SubNatTruth (sub_nat_to_rocq x \in fixpoint_nat_list_to_rocq xs) :=
  match H with
  | ImportedFixpoint.List_Mem_head_inst1 ys =>
      fixpoint_mem_head_truth _ _
        (fixpoint_eq_refl_truth (sub_nat_to_rocq x))
  | ImportedFixpoint.List_Mem_tail_inst1 y ys Htail =>
      fixpoint_mem_tail_truth _ _
        (fixpoint_imported_mem_decoded x ys Htail)
  end.

Lemma fixpoint_membership_canonical (x : nat) (xs : seq nat) :
  PropSPropRel (is_true (x \in xs))
    (fixpoint_target_mem (sub_nat_to_imported x)
      (fixpoint_nat_list_to_imported xs)).
Proof.
  apply prop_sprop_rel_intro.
  - intro Hmem.
    exact (fixpoint_seq_mem_forward x xs
      (sub_nat_prop_to_truth _ Hmem)).
  - intro Hmem. apply sub_nat_truth_to_strict_prop.
    have Hdecoded := fixpoint_imported_mem_decoded
      (sub_nat_to_imported x) (fixpoint_nat_list_to_imported xs) Hmem.
    rewrite (sub_nat_rocq_roundtrip x)
      (fixpoint_nat_list_source_roundtrip xs) in Hdecoded.
    exact Hdecoded.
Qed.

Lemma fixpoint_membership_correspondence
    (xR : nat) (xL : Lean.Nat) (xsR : seq nat)
    (xsL : ImportedFixpoint.List_inst1 Lean.Nat) :
  SubNatRel xR xL -> FixpointNatListRel xsR xsL ->
  PropSPropRel (is_true (xR \in xsR))
    (fixpoint_target_mem xL xsL).
Proof.
  intros Hx Hxs.
  have HxP := imported_eq_to_coq_eq _ _ Hx.
  have HxsP := imported_eq_to_coq_eq _ _ Hxs.
  destruct HxP, HxsP.
  exact (fixpoint_membership_canonical xR xsR).
Qed.

Print Assumptions fixpoint_membership_correspondence.

Inductive FixpointListTrue : SProp := fixpoint_list_true_intro.

Definition fixpoint_list_cons_ne_nil (x : Lean.Nat)
    (xs : ImportedFixpoint.List_inst1 Lean.Nat) :
  ImportedFixpoint.Ne (ImportedFixpoint.List_inst1 Lean.Nat)
    (ImportedFixpoint.List_cons_inst1 Lean.Nat x xs)
    (ImportedFixpoint.List_nil_inst1 Lean.Nat) :=
  fun H => match H in Lean.eq _ z return
      match z with
      | ImportedFixpoint.List_nil_inst1 => ImportedFixpoint.False
      | ImportedFixpoint.List_cons_inst1 _ _ => FixpointListTrue
      end
    with Lean.eq_refl => fixpoint_list_true_intro end.

Lemma fixpoint_nonnil_correspondence (xsR : seq nat)
    (xsL : ImportedFixpoint.List_inst1 Lean.Nat) :
  FixpointNatListRel xsR xsL ->
  PropSPropRel (is_true (~~ nilp xsR))
    (ImportedFixpoint.Ne (ImportedFixpoint.List_inst1 Lean.Nat)
      xsL (ImportedFixpoint.List_nil_inst1 Lean.Nat)).
Proof.
  intro Hxs.
  have HxsP := imported_eq_to_coq_eq _ _ Hxs.
  destruct HxsP.
  destruct xsR as [|x xs].
  - apply prop_sprop_rel_intro.
    + intro H. discriminate H.
    + intro Hne. exact (fixpoint_false_elim _
        (Hne (@Lean.eq_refl _ _))).
  - apply prop_sprop_rel_intro.
    + intro Hnonempty. exact (fixpoint_list_cons_ne_nil _ _).
    + intro Hne. exact (strictly_inhabits (Logic.eq_refl true)).
Qed.

Print Assumptions fixpoint_nonnil_correspondence.

Definition fixpoint_binary_fun_to_imported
    (fR : nat -> nat -> nat) : Lean.Nat -> Lean.Nat -> Lean.Nat :=
  fun s x => sub_nat_to_imported
    (fR (sub_nat_to_rocq s) (sub_nat_to_rocq x)).

Definition fixpoint_binary_fun_to_rocq
    (fL : Lean.Nat -> Lean.Nat -> Lean.Nat) : nat -> nat -> nat :=
  fun s x => sub_nat_to_rocq
    (fL (sub_nat_to_imported s) (sub_nat_to_imported x)).

Lemma fixpoint_binary_fun_to_imported_rel (fR : nat -> nat -> nat) :
  FixpointBinaryFunRel fR (fixpoint_binary_fun_to_imported fR).
Proof.
  intros sR sL Hs xR xL Hx.
  have HsP := imported_eq_to_coq_eq _ _ Hs.
  have HxP := imported_eq_to_coq_eq _ _ Hx.
  destruct HsP, HxP.
  unfold fixpoint_binary_fun_to_imported.
  rewrite (sub_nat_rocq_roundtrip sR)
    (sub_nat_rocq_roundtrip xR).
  exact (sub_nat_rel_canonical (fR sR xR)).
Qed.

Lemma fixpoint_binary_fun_to_rocq_rel
    (fL : Lean.Nat -> Lean.Nat -> Lean.Nat) :
  FixpointBinaryFunRel (fixpoint_binary_fun_to_rocq fL) fL.
Proof.
  intros sR sL Hs xR xL Hx.
  have HsP := imported_eq_to_coq_eq _ _ Hs.
  have HxP := imported_eq_to_coq_eq _ _ Hx.
  destruct HsP, HxP.
  exact (sub_nat_rel_surjective
    (fL (sub_nat_to_imported sR) (sub_nat_to_imported xR))).
Qed.

Definition fixpoint_bool_to_imported (b : bool) : ImportedFixpoint.Bool :=
  if b then ImportedFixpoint.Bool_true else ImportedFixpoint.Bool_false.

Definition fixpoint_bool_to_rocq (b : ImportedFixpoint.Bool) : bool :=
  match b with
  | ImportedFixpoint.Bool_true => true
  | ImportedFixpoint.Bool_false => false
  end.

Lemma fixpoint_bool_target_roundtrip (b : ImportedFixpoint.Bool) :
  Lean.eq (fixpoint_bool_to_imported (fixpoint_bool_to_rocq b)) b.
Proof. destruct b; exact (@Lean.eq_refl _ _). Qed.

Definition fixpoint_pred_to_imported (pR : nat -> bool) :
    Lean.Nat -> ImportedFixpoint.Bool :=
  fun x => fixpoint_bool_to_imported (pR (sub_nat_to_rocq x)).

Definition fixpoint_pred_to_rocq
    (pL : Lean.Nat -> ImportedFixpoint.Bool) : nat -> bool :=
  fun x => fixpoint_bool_to_rocq (pL (sub_nat_to_imported x)).

Lemma fixpoint_pred_to_imported_rel (pR : nat -> bool) :
  FixpointNatPredRel pR (fixpoint_pred_to_imported pR).
Proof.
  intros xR xL Hx.
  have HxP := imported_eq_to_coq_eq _ _ Hx.
  destruct HxP.
  unfold fixpoint_pred_to_imported.
  rewrite (sub_nat_rocq_roundtrip xR).
  destruct (pR xR); exact (@Lean.eq_refl _ _).
Qed.

Lemma fixpoint_pred_to_rocq_rel
    (pL : Lean.Nat -> ImportedFixpoint.Bool) :
  FixpointNatPredRel (fixpoint_pred_to_rocq pL) pL.
Proof.
  intros xR xL Hx.
  have HxP := imported_eq_to_coq_eq _ _ Hx.
  destruct HxP.
  unfold fixpoint_pred_to_rocq.
  destruct (pL (sub_nat_to_imported xR));
    exact (@Lean.eq_refl _ _).
Qed.

Print Assumptions fixpoint_binary_fun_to_imported_rel.
Print Assumptions fixpoint_pred_to_rocq_rel.

Lemma fixpoint_bool_truth_correspondence (bR : bool)
    (bL : ImportedFixpoint.Bool) :
  FixpointBoolRel bR bL ->
  PropSPropRel (is_true bR)
    (Lean.eq bL ImportedFixpoint.Bool_true).
Proof.
  intro Hb. apply prop_sprop_rel_intro.
  - intro Htrue. destruct bR; cbn in Htrue.
    + exact Hb.
    + discriminate Htrue.
  - intro Htrue. destruct bR.
    + exact (strictly_inhabits (Logic.eq_refl true)).
    + exact (fixpoint_false_elim _
        (fixpoint_bool_false_ne_true
          (sub_imported_eq_trans _ _ _
            (sub_imported_eq_sym _ _ Hb) Htrue))).
Qed.

Lemma fixpoint_max_of_seq_some_eq_correspondence
    (fR : nat -> nat -> nat) (fL : Lean.Nat -> Lean.Nat -> Lean.Nat)
    (spR : seq nat) (spL : ImportedFixpoint.List_inst1 Lean.Nat)
    (hR xR : nat) (hL xL : Lean.Nat) :
  FixpointBinaryFunRel fR fL -> FixpointNatListRel spR spL ->
  SubNatRel hR hL -> SubNatRel xR xL ->
  PropSPropRel
    (Logic.eq
      (GeneratedFixpointSourceAll.GeneratedFixpointSourceAll.find_max_fixpoint_of_seq
        fR spR hR) (Some xR))
    (Lean.eq
      (ImportedFixpoint.Prosa_Util_Fixpoint_find_max_fixpoint_of_seq
        fL spL hL)
      (ImportedFixpoint.Option_some_inst1 Lean.Nat xL)).
Proof.
  intros Hf Hsp Hh Hx.
  exact (fixpoint_option_eq_correspondence _ _ _ _
    (fixpoint_max_of_seq_correspondence
      fR fL spR spL hR hL Hf Hsp Hh)
    (fixpoint_some_rel xR xL Hx)).
Qed.

Lemma fixpoint_max_wrapper_some_eq_correspondence
    (LR : nat) (LL : Lean.Nat)
    (pR : nat -> bool) (pL : Lean.Nat -> ImportedFixpoint.Bool)
    (fR : nat -> nat -> nat) (fL : Lean.Nat -> Lean.Nat -> Lean.Nat)
    (hR xR : nat) (hL xL : Lean.Nat) :
  SubNatRel LR LL -> FixpointNatPredRel pR pL ->
  FixpointBinaryFunRel fR fL -> SubNatRel hR hL ->
  SubNatRel xR xL ->
  PropSPropRel
    (Logic.eq
      (GeneratedFixpointSourceAll.GeneratedFixpointSourceAll.find_max_fixpoint
        LR pR fR hR) (Some xR))
    (Lean.eq
      (ImportedFixpoint.Prosa_Util_Fixpoint_find_max_fixpoint
        LL pL fL hL)
      (ImportedFixpoint.Option_some_inst1 Lean.Nat xL)).
Proof.
  intros HL Hp Hf Hh Hx.
  exact (fixpoint_option_eq_correspondence _ _ _ _
    (fixpoint_max_wrapper_correspondence
      LR LL pR pL fR fL hR hL HL Hp Hf Hh)
    (fixpoint_some_rel xR xL Hx)).
Qed.

Lemma fixpoint_max_of_seq_some_eq_reverse_correspondence
    (fR : nat -> nat -> nat) (fL : Lean.Nat -> Lean.Nat -> Lean.Nat)
    (spR : seq nat) (spL : ImportedFixpoint.List_inst1 Lean.Nat)
    (hR xR : nat) (hL xL : Lean.Nat) :
  FixpointBinaryFunRel fR fL -> FixpointNatListRel spR spL ->
  SubNatRel hR hL -> SubNatRel xR xL ->
  PropSPropRel
    (Logic.eq (Some xR)
      (GeneratedFixpointSourceAll.GeneratedFixpointSourceAll.find_max_fixpoint_of_seq
        fR spR hR))
    (Lean.eq (ImportedFixpoint.Option_some_inst1 Lean.Nat xL)
      (ImportedFixpoint.Prosa_Util_Fixpoint_find_max_fixpoint_of_seq
        fL spL hL)).
Proof.
  intros Hf Hsp Hh Hx.
  exact (fixpoint_option_eq_correspondence _ _ _ _
    (fixpoint_some_rel xR xL Hx)
    (fixpoint_max_of_seq_correspondence
      fR fL spR spL hR hL Hf Hsp Hh)).
Qed.

Lemma fixpoint_max_wrapper_some_eq_reverse_correspondence
    (LR : nat) (LL : Lean.Nat)
    (pR : nat -> bool) (pL : Lean.Nat -> ImportedFixpoint.Bool)
    (fR : nat -> nat -> nat) (fL : Lean.Nat -> Lean.Nat -> Lean.Nat)
    (hR xR : nat) (hL xL : Lean.Nat) :
  SubNatRel LR LL -> FixpointNatPredRel pR pL ->
  FixpointBinaryFunRel fR fL -> SubNatRel hR hL ->
  SubNatRel xR xL ->
  PropSPropRel
    (Logic.eq (Some xR)
      (GeneratedFixpointSourceAll.GeneratedFixpointSourceAll.find_max_fixpoint
        LR pR fR hR))
    (Lean.eq (ImportedFixpoint.Option_some_inst1 Lean.Nat xL)
      (ImportedFixpoint.Prosa_Util_Fixpoint_find_max_fixpoint
        LL pL fL hL)).
Proof.
  intros HL Hp Hf Hh Hx.
  exact (fixpoint_option_eq_correspondence _ _ _ _
    (fixpoint_some_rel xR xL Hx)
    (fixpoint_max_wrapper_correspondence
      LR LL pR pL fR fL hR hL HL Hp Hf Hh)).
Qed.

Print Assumptions fixpoint_bool_truth_correspondence.
Print Assumptions fixpoint_max_wrapper_some_eq_correspondence.
Print Assumptions fixpoint_max_wrapper_some_eq_reverse_correspondence.
