From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq path.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedListLast.
From FoundationCertificates Require Import
  PropSPropFoundation LogicalRelation SubadditivityNatCorrespondence
  ListLastCertificate ListRemCertificate ListBatch2Certificate
  ListBatch3Operations.
From prosa Require Import GeneratedListLastSource.

(** Exact structural target propositions, specialized at the approved
    [eqType -> Type + DecidableEq] boundary.  Separate type guards bind these
    propositions to the freshly imported theorem constants. *)

Definition l3_target_subseq_leq_size_statement : SProp :=
  forall (T : eqType) (xs ys : ImportedListLast.List T),
    ImportedListLast.List_Nodup T xs ->
    (forall x : T, lr_target_mem x xs -> lr_target_mem x ys) ->
    ll_target_le (lr_target_length xs) (lr_target_length ys).

Definition l3_target_in_zip_statement : SProp :=
  forall (T U : eqType)
    (xs : ImportedListLast.List T) (ys : ImportedListLast.List U)
    (x xDefault : T) (y yDefault : U),
    Lean.eq (lr_target_length xs) (lr_target_length ys) ->
    ImportedListLast.Exists Lean.Nat (fun idx =>
      Lean.And (ll_target_lt idx (lr_target_length xs))
        (Lean.And
          (Lean.eq (l3_target_getD xs idx xDefault) x)
          (Lean.eq (l3_target_getD ys idx yDefault) y))) ->
    l3_pair_target_mem (ImportedListLast.Prod_mk T U x y)
      (l3_target_zip xs ys).

Definition l3_target_eq_ind_in_seq_statement : SProp :=
  forall (T : eqType) (a b : T) (xs : ImportedListLast.List T),
    Lean.eq (l3_target_idxOf T a xs) (l3_target_idxOf T b xs) ->
    lr_target_mem a xs -> lr_target_mem b xs -> Lean.eq a b.

Definition l3_target_default_or_in_statement : SProp :=
  forall (T : eqType) (n : Lean.Nat) (d : T)
    (xs : ImportedListLast.List T),
    Lean.Or (Lean.eq (l3_target_getD xs n d) d)
      (lr_target_mem (l3_target_getD xs n d) xs).

Definition l3_target_exists_two_statement : SProp :=
  forall (T : eqType) (xs : ImportedListLast.List T),
    ll_target_lt ll_target_one (lr_target_length xs) ->
    ImportedListLast.List_Nodup T xs ->
    ImportedListLast.Exists T (fun a =>
      ImportedListLast.Exists T (fun b =>
        Lean.And (lr_target_ne a b)
          (Lean.And (lr_target_mem a xs) (lr_target_mem b xs)))).

Definition l3_target_has_all_nilp_statement : SProp :=
  forall (T : eqType) (xs : ImportedListLast.List T)
    (P : T -> ImportedListLast.Bool),
    Lean.eq (l3_target_all xs P) ImportedListLast.Bool_true ->
    Lean.eq (l3_target_isEmpty xs) ImportedListLast.Bool_false ->
    Lean.eq (l3_target_any xs P) ImportedListLast.Bool_true.

Definition l3_target_sorted_split_statement : SProp :=
  forall (T : eqType) (xs : ImportedListLast.List T)
    (P : T -> ImportedListLast.Bool) (f : T -> Lean.Nat) (t : Lean.Nat),
    l3_target_sorted
      (fun x y => l3_target_decide_le (f x) (f y)) xs ->
    Lean.eq (lr_target_filter P xs)
      (lr_target_append
        (lr_target_filter
          (fun x => ImportedListLast.Bool_and (P x)
            (l3_target_decide_le (f x) t)) xs)
        (lr_target_filter
          (fun x => ImportedListLast.Bool_and (P x)
            (l3_target_decide_lt t (f x))) xs)).

Definition l3_target_sorted_cat_statement : SProp :=
  forall (T : eqType) (R : T -> T -> ImportedListLast.Bool)
    (xs ys : ImportedListLast.List T),
    (forall x y z : T,
      Lean.eq (R x y) ImportedListLast.Bool_true ->
      Lean.eq (R y z) ImportedListLast.Bool_true ->
      Lean.eq (R x z) ImportedListLast.Bool_true) ->
    l3_target_sorted R (lr_target_append xs ys) ->
    Lean.And (l3_target_sorted R xs) (l3_target_sorted R ys).

Definition l3_target_nonnil_last_statement : SProp :=
  forall (T : eqType) (xs : ImportedListLast.List T) (d1 d2 : T),
    l3_target_nonempty xs ->
    Lean.eq (l3_target_last xs d1) (l3_target_last xs d2).

(** Reusable conclusion relations. *)

Lemma l3_exists_two_conclusion_correspondence (T : eqType)
    (xsR : seq T) (xsL : ImportedListLast.List T) :
  LrListRel xsR xsL ->
  PropSPropRel
    (exists a b : T, a <> b /\ a \in xsR /\ b \in xsR)
    (ImportedListLast.Exists T (fun a =>
      ImportedListLast.Exists T (fun b =>
        Lean.And (lr_target_ne a b)
          (Lean.And (lr_target_mem a xsL) (lr_target_mem b xsL))))).
Proof.
  intro Hxs. apply lr_exists_identity_correspondence. intro a.
  apply lr_exists_identity_correspondence. intro b.
  apply lr_and_correspondence.
  - exact (lb_not_correspondence (Logic.eq a b) (Lean.eq a b)
      (l3_identity_eq_correspondence a b)).
  - apply lr_and_correspondence.
    + exact (lr_membership_correspondence T a xsR xsL Hxs).
    + exact (lr_membership_correspondence T b xsR xsL Hxs).
Qed.

Lemma l3_zip_lookup_correspondence (T U : eqType)
    (xsR : seq T) (xsL : ImportedListLast.List T)
    (ysR : seq U) (ysL : ImportedListLast.List U)
    (x xDefault : T) (y yDefault : U) :
  LrListRel xsR xsL -> LrListRel ysR ysL ->
  PropSPropRel
    (exists idx : nat,
      ltn idx (size xsR) /\ nth xDefault xsR idx = x /\
      nth yDefault ysR idx = y)
    (ImportedListLast.Exists Lean.Nat (fun idx =>
      Lean.And (ll_target_lt idx (lr_target_length xsL))
        (Lean.And
          (Lean.eq (l3_target_getD xsL idx xDefault) x)
          (Lean.eq (l3_target_getD ysL idx yDefault) y)))).
Proof.
  intros Hxs Hys. apply l3_exists_nat_correspondence.
  intros nR nL Hn. apply lr_and_correspondence.
  - exact (sub_nat_lt_correspondence nR nL
      (size xsR) (lr_target_length xsL) Hn
      (lr_length_related T xsR xsL Hxs)).
  - apply lr_and_correspondence.
    + exact (l3_element_eq_correspondence
        (nth xDefault xsR nR) (l3_target_getD xsL nL xDefault)
        x x (l3_getD_related xDefault xsR xsL nR nL Hxs Hn)
        (@Lean.eq_refl T x)).
    + exact (l3_element_eq_correspondence
        (nth yDefault ysR nR) (l3_target_getD ysL nL yDefault)
        y y (l3_getD_related yDefault ysR ysL nR nL Hys Hn)
        (@Lean.eq_refl U y)).
Qed.

Lemma l3_transitive_correspondence (T : Type)
    (RR : T -> T -> bool) (RL : T -> T -> ImportedListLast.Bool) :
  L3BinaryPredRel RR RL ->
  PropSPropRel (@transitive T RR)
    (forall x y z : T,
      Lean.eq (RL x y) ImportedListLast.Bool_true ->
      Lean.eq (RL y z) ImportedListLast.Bool_true ->
      Lean.eq (RL x z) ImportedListLast.Bool_true).
Proof.
  intro HR. apply prop_sprop_rel_intro.
  - intros Htrans x y z HxyL HyzL.
    apply (prop_to_sprop _ _
      (ll_bool_true_correspondence (RR x z) (RL x z) (HR x z))).
    apply (Htrans y x z).
    + exact (sprop_to_prop _ _
        (ll_bool_true_correspondence (RR x y) (RL x y) (HR x y)) HxyL).
    + exact (sprop_to_prop _ _
        (ll_bool_true_correspondence (RR y z) (RL y z) (HR y z)) HyzL).
  - intro Htrans. apply strictly_inhabits.
    intros y x z HxyR HyzR.
    exact (sprop_to_prop _ _
      (ll_bool_true_correspondence (RR x z) (RL x z) (HR x z))
      (Htrans x y z
        (prop_to_sprop _ _
          (ll_bool_true_correspondence (RR x y) (RL x y) (HR x y)) HxyR)
        (prop_to_sprop _ _
          (ll_bool_true_correspondence (RR y z) (RL y z) (HR y z)) HyzR))).
Qed.

Lemma l3_subset_correspondence (T : eqType)
    (xsR ysR : seq T)
    (xsL ysL : ImportedListLast.List T) :
  LrListRel xsR xsL -> LrListRel ysR ysL ->
  PropSPropRel
    (forall x : T, x \in xsR -> x \in ysR)
    (forall x : T, lr_target_mem x xsL -> lr_target_mem x ysL).
Proof.
  intros Hxs Hys. apply prop_sprop_rel_intro.
  - intros Hsub x HmemL.
    exact (prop_to_sprop _ _
      (lr_membership_correspondence T x ysR ysL Hys)
      (Hsub x (sprop_to_prop _ _
        (lr_membership_correspondence T x xsR xsL Hxs) HmemL))).
  - intro Hsub. apply strictly_inhabits. intros x HmemR.
    exact (sprop_to_prop _ _
      (lr_membership_correspondence T x ysR ysL Hys)
      (Hsub x (prop_to_sprop _ _
        (lr_membership_correspondence T x xsR xsL Hxs) HmemR))).
Qed.

(** 1. [subseq_leq_size] *)
Theorem subseq_leq_size_statement_certificate :
  PropSPropRel GeneratedListLastSource.statement_subseq_leq_size
    l3_target_subseq_leq_size_statement.
Proof.
  unfold GeneratedListLastSource.statement_subseq_leq_size,
    l3_target_subseq_leq_size_statement.
  apply prop_sprop_rel_intro.
  - intros Hsource T xsL ysL HuniqL HsubL.
    pose xsR := lr_to_rocq xsL. pose ysR := lr_to_rocq ysL.
    have Hxs : LrListRel xsR xsL := lr_target_roundtrip xsL.
    have Hys : LrListRel ysR ysL := lr_target_roundtrip ysL.
    have HuniqR := sprop_to_prop _ _
      (l3_uniq_correspondence T xsR xsL Hxs) HuniqL.
    have HsubR := sprop_to_prop _ _
      (l3_subset_correspondence T xsR ysR xsL ysL Hxs Hys) HsubL.
    exact (prop_to_sprop _ _
      (sub_nat_le_correspondence _ _ _ _
        (lr_length_related T xsR xsL Hxs)
        (lr_length_related T ysR ysL Hys))
      (Hsource T xsR ysR HuniqR HsubR)).
  - intro Htarget. apply strictly_inhabits.
    intros T xsR ysR HuniqR HsubR.
    have Hxs : LrListRel xsR (lr_to_imported xsR) := @Lean.eq_refl _ _.
    have Hys : LrListRel ysR (lr_to_imported ysR) := @Lean.eq_refl _ _.
    have HuniqL := prop_to_sprop _ _
      (l3_uniq_correspondence T xsR _ Hxs) HuniqR.
    exact (sprop_to_prop _ _
      (sub_nat_le_correspondence _ _ _ _
        (lr_length_related T xsR _ Hxs)
        (lr_length_related T ysR _ Hys))
      (Htarget T (lr_to_imported xsR) (lr_to_imported ysR)
        HuniqL (prop_to_sprop _ _
          (l3_subset_correspondence T xsR ysR _ _ Hxs Hys) HsubR))).
Qed.

(** 2. [in_zip] *)
Theorem in_zip_statement_certificate :
  PropSPropRel GeneratedListLastSource.statement_in_zip
    l3_target_in_zip_statement.
Proof.
  unfold GeneratedListLastSource.statement_in_zip,
    l3_target_in_zip_statement.
  apply prop_sprop_rel_intro.
  - intros Hsource T U xsL ysL x xDefault y yDefault HlenL HlookupL.
    pose xsR := lr_to_rocq xsL. pose ysR := lr_to_rocq ysL.
    have Hxs : LrListRel xsR xsL := lr_target_roundtrip xsL.
    have Hys : LrListRel ysR ysL := lr_target_roundtrip ysL.
    have HlenR := sprop_to_prop _ _
      (sub_nat_eq_correspondence _ _ _ _
        (lr_length_related T xsR xsL Hxs)
        (lr_length_related U ysR ysL Hys)) HlenL.
    have HlookupR := sprop_to_prop _ _
      (l3_zip_lookup_correspondence T U xsR xsL ysR ysL
        x xDefault y yDefault Hxs Hys) HlookupL.
    have Hzip := l3_zip_related T U xsR xsL ysR ysL Hxs Hys.
    exact (prop_to_sprop _ _
      (l3_pair_membership_correspondence T U (x, y)
        (zip xsR ysR) (l3_target_zip xsL ysL) Hzip)
      (Hsource T U xsR ysR x xDefault y yDefault HlenR HlookupR)).
  - intro Htarget. apply strictly_inhabits.
    intros T U xsR ysR x xDefault y yDefault HlenR HlookupR.
    have Hxs : LrListRel xsR (lr_to_imported xsR) := @Lean.eq_refl _ _.
    have Hys : LrListRel ysR (lr_to_imported ysR) := @Lean.eq_refl _ _.
    have HlenL := prop_to_sprop _ _
      (sub_nat_eq_correspondence _ _ _ _
        (lr_length_related T xsR _ Hxs)
        (lr_length_related U ysR _ Hys)) HlenR.
    have HlookupL := prop_to_sprop _ _
      (l3_zip_lookup_correspondence T U xsR _ ysR _
        x xDefault y yDefault Hxs Hys) HlookupR.
    have Hzip := l3_zip_related T U xsR _ ysR _ Hxs Hys.
    exact (sprop_to_prop _ _
      (l3_pair_membership_correspondence T U (x, y)
        (zip xsR ysR)
        (l3_target_zip (lr_to_imported xsR) (lr_to_imported ysR)) Hzip)
      (Htarget T U (lr_to_imported xsR) (lr_to_imported ysR)
        x xDefault y yDefault HlenL HlookupL)).
Qed.

(** 3. [eq_ind_in_seq] *)
Theorem eq_ind_in_seq_statement_certificate :
  PropSPropRel GeneratedListLastSource.statement_eq_ind_in_seq
    l3_target_eq_ind_in_seq_statement.
Proof.
  unfold GeneratedListLastSource.statement_eq_ind_in_seq,
    l3_target_eq_ind_in_seq_statement.
  apply prop_sprop_rel_intro.
  - intros Hsource T a b xsL HidxL HaL HbL.
    pose xsR := lr_to_rocq xsL.
    have Hxs : LrListRel xsR xsL := lr_target_roundtrip xsL.
    have HidxR := sprop_to_prop _ _
      (sub_nat_eq_correspondence _ _ _ _
        (l3_idxOf_related T a xsR xsL Hxs)
        (l3_idxOf_related T b xsR xsL Hxs)) HidxL.
    have HaR := sprop_to_prop _ _
      (lr_membership_correspondence T a xsR xsL Hxs) HaL.
    have HbR := sprop_to_prop _ _
      (lr_membership_correspondence T b xsR xsL Hxs) HbL.
    exact (coq_eq_to_imported_eq _ _ (Hsource T a b xsR HidxR HaR HbR)).
  - intro Htarget. apply strictly_inhabits.
    intros T a b xsR HidxR HaR HbR.
    have Hxs : LrListRel xsR (lr_to_imported xsR) := @Lean.eq_refl _ _.
    have HidxL := prop_to_sprop _ _
      (sub_nat_eq_correspondence _ _ _ _
        (l3_idxOf_related T a xsR _ Hxs)
        (l3_idxOf_related T b xsR _ Hxs)) HidxR.
    have HaL := prop_to_sprop _ _
      (lr_membership_correspondence T a xsR _ Hxs) HaR.
    have HbL := prop_to_sprop _ _
      (lr_membership_correspondence T b xsR _ Hxs) HbR.
    exact (imported_eq_to_coq_eq _ _
      (Htarget T a b (lr_to_imported xsR) HidxL HaL HbL)).
Qed.

(** 4. [default_or_in] *)
Theorem default_or_in_statement_certificate :
  PropSPropRel GeneratedListLastSource.statement_default_or_in
    l3_target_default_or_in_statement.
Proof.
  unfold GeneratedListLastSource.statement_default_or_in,
    l3_target_default_or_in_statement.
  apply prop_sprop_rel_intro.
  - intros Hsource T nL d xsL.
    pose nR := sub_nat_to_rocq nL. pose xsR := lr_to_rocq xsL.
    have Hn : SubNatRel nR nL := sub_nat_rel_surjective nL.
    have Hxs : LrListRel xsR xsL := lr_target_roundtrip xsL.
    have Hget := l3_getD_related d xsR xsL nR nL Hxs Hn.
    exact (prop_to_sprop _ _
      (l3_or_correspondence _ _ _ _
        (l3_element_eq_correspondence
          (nth d xsR nR) (l3_target_getD xsL nL d)
          d d Hget (@Lean.eq_refl T d))
        (l3_membership_related T
          (nth d xsR nR) (l3_target_getD xsL nL d)
          xsR xsL Hget Hxs))
      (Hsource T nR d xsR)).
  - intro Htarget. apply strictly_inhabits.
    intros T nR d xsR.
    have Hn : SubNatRel nR (sub_nat_to_imported nR) :=
      sub_nat_rel_canonical nR.
    have Hxs : LrListRel xsR (lr_to_imported xsR) := @Lean.eq_refl _ _.
    have Hget := l3_getD_related d xsR _ nR _ Hxs Hn.
    exact (sprop_to_prop _ _
      (l3_or_correspondence _ _ _ _
        (l3_element_eq_correspondence
          (nth d xsR nR)
          (l3_target_getD (lr_to_imported xsR) (sub_nat_to_imported nR) d)
          d d Hget (@Lean.eq_refl T d))
        (l3_membership_related T
          (nth d xsR nR)
          (l3_target_getD (lr_to_imported xsR) (sub_nat_to_imported nR) d)
          xsR (lr_to_imported xsR) Hget Hxs))
      (Htarget T (sub_nat_to_imported nR) d (lr_to_imported xsR))).
Qed.

(** 5. [exists_two] *)
Theorem exists_two_statement_certificate :
  PropSPropRel GeneratedListLastSource.statement_exists_two
    l3_target_exists_two_statement.
Proof.
  unfold GeneratedListLastSource.statement_exists_two,
    l3_target_exists_two_statement.
  apply prop_sprop_rel_intro.
  - intros Hsource T xsL HlenL HuniqL.
    pose xsR := lr_to_rocq xsL.
    have Hxs : LrListRel xsR xsL := lr_target_roundtrip xsL.
    have HlenR := sprop_to_prop _ _
      (sub_nat_lt_correspondence 1 ll_target_one
        (size xsR) (lr_target_length xsL) lr_one_related
        (lr_length_related T xsR xsL Hxs)) HlenL.
    have HuniqR := sprop_to_prop _ _
      (l3_uniq_correspondence T xsR xsL Hxs) HuniqL.
    exact (prop_to_sprop _ _
      (l3_exists_two_conclusion_correspondence T xsR xsL Hxs)
      (Hsource T xsR HlenR HuniqR)).
  - intro Htarget. apply strictly_inhabits.
    intros T xsR HlenR HuniqR.
    have Hxs : LrListRel xsR (lr_to_imported xsR) := @Lean.eq_refl _ _.
    have HlenL := prop_to_sprop _ _
      (sub_nat_lt_correspondence 1 ll_target_one
        (size xsR) (lr_target_length (lr_to_imported xsR)) lr_one_related
        (lr_length_related T xsR _ Hxs)) HlenR.
    have HuniqL := prop_to_sprop _ _
      (l3_uniq_correspondence T xsR _ Hxs) HuniqR.
    exact (sprop_to_prop _ _
      (l3_exists_two_conclusion_correspondence T xsR _ Hxs)
      (Htarget T (lr_to_imported xsR) HlenL HuniqL)).
Qed.

(** 6. [has_all_nilp] *)
Theorem has_all_nilp_statement_certificate :
  PropSPropRel GeneratedListLastSource.statement_has_all_nilp
    l3_target_has_all_nilp_statement.
Proof.
  unfold GeneratedListLastSource.statement_has_all_nilp,
    l3_target_has_all_nilp_statement.
  apply prop_sprop_rel_intro.
  - intros Hsource T xsL PL HallL HnilL.
    pose xsR := lr_to_rocq xsL. pose PR := lr_pred_to_rocq PL.
    have Hxs : LrListRel xsR xsL := lr_target_roundtrip xsL.
    have HP : LrPredRel PR PL := lr_pred_surjective PL.
    have HallR := sprop_to_prop _ _
      (ll_bool_true_correspondence _ _
        (l3_all_related T PR PL xsR xsL HP Hxs)) HallL.
    have HnilR := sprop_to_prop _ _
      (lb_bool_false_correspondence _ _
        (l3_isEmpty_related T xsR xsL Hxs)) HnilL.
    exact (prop_to_sprop _ _
      (ll_bool_true_correspondence _ _
        (l3_any_related T PR PL xsR xsL HP Hxs))
      (Hsource T xsR PR HallR HnilR)).
  - intro Htarget. apply strictly_inhabits.
    intros T xsR PR HallR HnilR.
    have Hxs : LrListRel xsR (lr_to_imported xsR) := @Lean.eq_refl _ _.
    have HP : LrPredRel PR (lr_pred_to_imported PR) := lr_pred_canonical PR.
    have HallL := prop_to_sprop _ _
      (ll_bool_true_correspondence _ _
        (l3_all_related T PR _ xsR _ HP Hxs)) HallR.
    have HnilL := prop_to_sprop _ _
      (lb_bool_false_correspondence _ _
        (l3_isEmpty_related T xsR _ Hxs)) HnilR.
    exact (sprop_to_prop _ _
      (ll_bool_true_correspondence _ _
        (l3_any_related T PR _ xsR _ HP Hxs))
      (Htarget T (lr_to_imported xsR) (lr_pred_to_imported PR)
        HallL HnilL)).
Qed.

(** Relations needed only by [sorted_split]. *)
Lemma l3_order_binary_related {T : Type}
    (fR : T -> nat) (fL : T -> Lean.Nat) :
  L3NatFunRel fR fL ->
  L3BinaryPredRel (fun x y => leq (fR x) (fR y))
    (fun x y => l3_target_decide_le (fL x) (fL y)).
Proof.
  intros Hf x y. exact (l3_decide_le_related _ _ _ _ (Hf x) (Hf y)).
Qed.

Lemma l3_low_pred_related {T : Type}
    (PR : T -> bool) (PL : T -> ImportedListLast.Bool)
    (fR : T -> nat) (fL : T -> Lean.Nat) (tR : nat) (tL : Lean.Nat) :
  LrPredRel PR PL -> L3NatFunRel fR fL -> SubNatRel tR tL ->
  LrPredRel (fun x => PR x && leq (fR x) tR)
    (fun x => ImportedListLast.Bool_and (PL x)
      (l3_target_decide_le (fL x) tL)).
Proof.
  intros HP Hf Ht x.
  exact (l3_bool_and_related _ _ _ _ (HP x)
    (l3_decide_le_related _ _ _ _ (Hf x) Ht)).
Qed.

Lemma l3_high_pred_related {T : Type}
    (PR : T -> bool) (PL : T -> ImportedListLast.Bool)
    (fR : T -> nat) (fL : T -> Lean.Nat) (tR : nat) (tL : Lean.Nat) :
  LrPredRel PR PL -> L3NatFunRel fR fL -> SubNatRel tR tL ->
  LrPredRel (fun x => PR x && ltn tR (fR x))
    (fun x => ImportedListLast.Bool_and (PL x)
      (l3_target_decide_lt tL (fL x))).
Proof.
  intros HP Hf Ht x.
  exact (l3_bool_and_related _ _ _ _ (HP x)
    (l3_decide_lt_related _ _ _ _ Ht (Hf x))).
Qed.

Lemma l3_sorted_split_conclusion_correspondence (T : Type)
    (xsR : seq T) (xsL : ImportedListLast.List T)
    (PR : T -> bool) (PL : T -> ImportedListLast.Bool)
    (fR : T -> nat) (fL : T -> Lean.Nat) (tR : nat) (tL : Lean.Nat) :
  LrListRel xsR xsL -> LrPredRel PR PL -> L3NatFunRel fR fL ->
  SubNatRel tR tL ->
  PropSPropRel
    ([seq x <- xsR | PR x] =
      [seq x <- xsR | PR x & leq (fR x) tR] ++
      [seq x <- xsR | PR x & ltn tR (fR x)])
    (Lean.eq (lr_target_filter PL xsL)
      (lr_target_append
        (lr_target_filter
          (fun x => ImportedListLast.Bool_and (PL x)
            (l3_target_decide_le (fL x) tL)) xsL)
        (lr_target_filter
          (fun x => ImportedListLast.Bool_and (PL x)
            (l3_target_decide_lt tL (fL x))) xsL))).
Proof.
  intros Hxs HP Hf Ht. apply lr_list_eq_correspondence.
  - exact (lr_filter_related T PR PL xsR xsL HP Hxs).
  - apply lr_append_related.
    + exact (lr_filter_related T _ _ xsR xsL
        (l3_low_pred_related PR PL fR fL tR tL HP Hf Ht) Hxs).
    + exact (lr_filter_related T _ _ xsR xsL
        (l3_high_pred_related PR PL fR fL tR tL HP Hf Ht) Hxs).
Qed.

(** 7. [sorted_split] *)
Theorem sorted_split_statement_certificate :
  PropSPropRel GeneratedListLastSource.statement_sorted_split
    l3_target_sorted_split_statement.
Proof.
  unfold GeneratedListLastSource.statement_sorted_split,
    l3_target_sorted_split_statement.
  apply prop_sprop_rel_intro.
  - intros Hsource T xsL PL fL tL HsortedL.
    pose xsR := lr_to_rocq xsL. pose PR := lr_pred_to_rocq PL.
    pose fR := l3_nat_fun_to_rocq fL. pose tR := sub_nat_to_rocq tL.
    have Hxs : LrListRel xsR xsL := lr_target_roundtrip xsL.
    have HP : LrPredRel PR PL := lr_pred_surjective PL.
    have Hf : L3NatFunRel fR fL := l3_nat_fun_surjective fL.
    have Ht : SubNatRel tR tL := sub_nat_rel_surjective tL.
    have HsortedR := sprop_to_prop _ _
      (l3_sorted_correspondence T _ _ xsR xsL
        (l3_order_binary_related fR fL Hf) Hxs) HsortedL.
    exact (prop_to_sprop _ _
      (l3_sorted_split_conclusion_correspondence T xsR xsL
        PR PL fR fL tR tL Hxs HP Hf Ht)
      (Hsource T xsR PR fR tR HsortedR)).
  - intro Htarget. apply strictly_inhabits.
    intros T xsR PR fR tR HsortedR.
    have Hxs : LrListRel xsR (lr_to_imported xsR) := @Lean.eq_refl _ _.
    have HP : LrPredRel PR (lr_pred_to_imported PR) := lr_pred_canonical PR.
    have Hf : L3NatFunRel fR (l3_nat_fun_to_imported fR) :=
      l3_nat_fun_canonical fR.
    have Ht : SubNatRel tR (sub_nat_to_imported tR) :=
      sub_nat_rel_canonical tR.
    have HsortedL := prop_to_sprop _ _
      (l3_sorted_correspondence T _ _ xsR _
        (l3_order_binary_related fR _ Hf) Hxs) HsortedR.
    exact (sprop_to_prop _ _
      (l3_sorted_split_conclusion_correspondence T xsR _ PR _ fR _ tR _
        Hxs HP Hf Ht)
      (Htarget T (lr_to_imported xsR) (lr_pred_to_imported PR)
        (l3_nat_fun_to_imported fR) (sub_nat_to_imported tR) HsortedL)).
Qed.

(** 8. [sorted_cat] *)
Theorem sorted_cat_statement_certificate :
  PropSPropRel GeneratedListLastSource.statement_sorted_cat
    l3_target_sorted_cat_statement.
Proof.
  unfold GeneratedListLastSource.statement_sorted_cat,
    l3_target_sorted_cat_statement.
  apply prop_sprop_rel_intro.
  - intros Hsource T RL xsL ysL HtransL HsortedL.
    pose RR := l3_binary_pred_to_rocq RL.
    pose xsR := lr_to_rocq xsL. pose ysR := lr_to_rocq ysL.
    have HR : L3BinaryPredRel RR RL := l3_binary_pred_surjective RL.
    have Hxs : LrListRel xsR xsL := lr_target_roundtrip xsL.
    have Hys : LrListRel ysR ysL := lr_target_roundtrip ysL.
    have Happ := lr_append_related T xsR ysR xsL ysL Hxs Hys.
    have HtransR := sprop_to_prop _ _
      (l3_transitive_correspondence T RR RL HR) HtransL.
    have HsortedR := sprop_to_prop _ _
      (l3_sorted_correspondence T RR RL (xsR ++ ysR)
        (lr_target_append xsL ysL) HR Happ) HsortedL.
    exact (prop_to_sprop _ _
      (lr_and_correspondence _ _ _ _
        (l3_sorted_correspondence T RR RL xsR xsL HR Hxs)
        (l3_sorted_correspondence T RR RL ysR ysL HR Hys))
      (Hsource T RR xsR ysR HtransR HsortedR)).
  - intro Htarget. apply strictly_inhabits.
    intros T RR xsR ysR HtransR HsortedR.
    have HR : L3BinaryPredRel RR (l3_binary_pred_to_imported RR) :=
      l3_binary_pred_canonical RR.
    have Hxs : LrListRel xsR (lr_to_imported xsR) := @Lean.eq_refl _ _.
    have Hys : LrListRel ysR (lr_to_imported ysR) := @Lean.eq_refl _ _.
    have Happ := lr_append_related T xsR ysR _ _ Hxs Hys.
    have HtransL := prop_to_sprop _ _
      (l3_transitive_correspondence T RR _ HR) HtransR.
    have HsortedL := prop_to_sprop _ _
      (l3_sorted_correspondence T RR _ (xsR ++ ysR) _ HR Happ) HsortedR.
    exact (sprop_to_prop _ _
      (lr_and_correspondence _ _ _ _
        (l3_sorted_correspondence T RR _ xsR _ HR Hxs)
        (l3_sorted_correspondence T RR _ ysR _ HR Hys))
      (Htarget T (l3_binary_pred_to_imported RR)
        (lr_to_imported xsR) (lr_to_imported ysR) HtransL HsortedL)).
Qed.

(** 9. [nonnil_last] *)
Theorem nonnil_last_statement_certificate :
  PropSPropRel GeneratedListLastSource.statement_nonnil_last
    l3_target_nonnil_last_statement.
Proof.
  unfold GeneratedListLastSource.statement_nonnil_last,
    l3_target_nonnil_last_statement.
  apply prop_sprop_rel_intro.
  - intros Hsource T xsL d1 d2 HneL.
    pose xsR := lr_to_rocq xsL.
    have Hxs : LrListRel xsR xsL := lr_target_roundtrip xsL.
    have HneR := sprop_to_prop _ _
      (l3_nonempty_correspondence T xsR xsL Hxs) HneL.
    exact (prop_to_sprop _ _
      (l3_element_eq_correspondence
        (last d1 xsR) (l3_target_last xsL d1)
        (last d2 xsR) (l3_target_last xsL d2)
        (l3_last_related d1 xsR xsL Hxs)
        (l3_last_related d2 xsR xsL Hxs))
      (Hsource T xsR d1 d2 HneR)).
  - intro Htarget. apply strictly_inhabits.
    intros T xsR d1 d2 HneR.
    have Hxs : LrListRel xsR (lr_to_imported xsR) := @Lean.eq_refl _ _.
    have HneL := prop_to_sprop _ _
      (l3_nonempty_correspondence T xsR _ Hxs) HneR.
    exact (sprop_to_prop _ _
      (l3_element_eq_correspondence
        (last d1 xsR) (l3_target_last (lr_to_imported xsR) d1)
        (last d2 xsR) (l3_target_last (lr_to_imported xsR) d2)
        (l3_last_related d1 xsR _ Hxs)
        (l3_last_related d2 xsR _ Hxs))
      (Htarget T (lr_to_imported xsR) d1 d2 HneL)).
Qed.

Print Assumptions subseq_leq_size_statement_certificate.
Print Assumptions in_zip_statement_certificate.
Print Assumptions eq_ind_in_seq_statement_certificate.
Print Assumptions default_or_in_statement_certificate.
Print Assumptions exists_two_statement_certificate.
Print Assumptions has_all_nilp_statement_certificate.
Print Assumptions sorted_split_statement_certificate.
Print Assumptions sorted_cat_statement_certificate.
Print Assumptions nonnil_last_statement_certificate.
