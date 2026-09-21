From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq fintype bigop.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedListLast.
From FoundationCertificates Require Import
  PropSPropFoundation LogicalRelation SubadditivityNatCorrespondence
  ListLastCertificate ListRemCertificate ListBatch2Certificate
  ListBatch3Operations ListBatch4Operations.
From prosa Require Import GeneratedListLastSource.

(** Structural target propositions for the exact compiled theorem types. *)

Definition l4_target_filter_last_mem_statement : SProp :=
  forall (T : eqType) (xs : ImportedListLast.List T) (d : T)
    (P : T -> ImportedListLast.Bool),
    Lean.eq (l3_target_any xs P) ImportedListLast.Bool_true ->
    lr_target_mem (l3_target_last (lr_target_filter P xs) d) xs.

Definition l4_target_iotaD_impl_statement : SProp :=
  forall nle m n : Lean.Nat,
    ll_target_le nle n ->
    Lean.eq (l4_target_range_prime m n)
      (ll_target_append (l4_target_range_prime m nle)
        (l4_target_range_prime (lr_target_add m nle)
          (ll_target_sub n nle))).

Definition l4_target_index_iota_lt_step_statement : SProp :=
  forall a b : Lean.Nat,
    ll_target_lt a b ->
    Lean.eq (l4_target_index_iota a b)
      (ImportedListLast.List_cons_inst1 Lean.Nat a
        (l4_target_index_iota (lr_target_add a ll_target_one) b)).

Definition l4_target_index_iota_cat_statement : SProp :=
  forall t t1 t2 : Lean.Nat,
    Lean.And (ll_target_le t1 t) (ll_target_le t t2) ->
    Lean.eq (l4_target_index_iota t1 t2)
      (ll_target_append (l4_target_index_iota t1 t)
        (l4_target_index_iota t t2)).

Definition l4_target_range_filter_2cons_statement : SProp :=
  forall (x : Lean.Nat) (xs : ImportedListLast.List_inst1 Lean.Nat)
    (k : Lean.Nat),
    Lean.eq
      (ll_target_filter
        (fun rho => l4_target_decide_mem rho
          (ImportedListLast.List_cons_inst1 Lean.Nat x
            (ImportedListLast.List_cons_inst1 Lean.Nat x xs)))
        (l4_target_range ll_target_zero k))
      (ll_target_filter
        (fun rho => l4_target_decide_mem rho
          (ImportedListLast.List_cons_inst1 Lean.Nat x xs))
        (l4_target_range ll_target_zero k)).

Definition l4_target_index_iota_filter_eqx_statement : SProp :=
  forall x a b : Lean.Nat,
    Lean.And (ll_target_le a x) (ll_target_lt x b) ->
    Lean.eq
      (ll_target_filter (fun rho => l4_target_decide_eq rho x)
        (l4_target_index_iota a b))
      (ImportedListLast.List_cons_inst1 Lean.Nat x
        (ImportedListLast.List_nil_inst1 Lean.Nat)).

Definition l4_target_index_iota_filter_singl_statement : SProp :=
  forall x a b : Lean.Nat,
    Lean.And (ll_target_le a x) (ll_target_lt x b) ->
    Lean.eq
      (ll_target_filter
        (fun rho => l4_target_decide_mem rho
          (ImportedListLast.List_cons_inst1 Lean.Nat x
            (ImportedListLast.List_nil_inst1 Lean.Nat)))
        (l4_target_index_iota a b))
      (ImportedListLast.List_cons_inst1 Lean.Nat x
        (ImportedListLast.List_nil_inst1 Lean.Nat)).

Definition l4_target_index_iota_filter_inxs_statement : SProp :=
  forall (a b x : Lean.Nat)
    (xs : ImportedListLast.List_inst1 Lean.Nat),
    ll_target_lt x a ->
    Lean.eq
      (ll_target_filter (fun rho => l4_target_decide_mem rho xs)
        (l4_target_index_iota a b))
      (ll_target_filter
        (fun rho => l4_target_decide_mem rho (l4_target_rem_all x xs))
        (l4_target_index_iota a b)).

Definition l4_andb_prop_intro (a b : bool) :
    is_true a -> is_true b -> is_true (a && b).
Proof.
  destruct a, b; cbn; intros; try discriminate; reflexivity.
Defined.

Definition l4_andb_prop_left (a b : bool) :
    is_true (a && b) -> is_true a.
Proof. destruct a, b; cbn; intros; try discriminate; reflexivity. Defined.

Definition l4_andb_prop_right (a b : bool) :
    is_true (a && b) -> is_true b.
Proof. destruct a, b; cbn; intros; try discriminate; reflexivity. Defined.

Lemma l4_interval_correspondence aR aL xR xL bR bL :
  SubNatRel aR aL -> SubNatRel xR xL -> SubNatRel bR bL ->
  PropSPropRel (aR <= xR < bR)
    (Lean.And (ll_target_le aL xL) (ll_target_lt xL bL)).
Proof.
  intros Ha Hx Hb. apply prop_sprop_rel_intro.
  - intro Hboth.
    have Hle := l4_andb_prop_left _ _ Hboth.
    have Hlt := l4_andb_prop_right _ _ Hboth.
    exact (Lean.And_intro _ _
      (prop_to_sprop _ _ (sub_nat_le_correspondence _ _ _ _ Ha Hx) Hle)
      (prop_to_sprop _ _ (sub_nat_lt_correspondence _ _ _ _ Hx Hb) Hlt)).
  - intros [Hle Hlt].
    have HleR := sprop_to_prop _ _
      (sub_nat_le_correspondence _ _ _ _ Ha Hx) Hle.
    have HltR := sprop_to_prop _ _
      (sub_nat_lt_correspondence _ _ _ _ Hx Hb) Hlt.
    exact (strictly_inhabits (l4_andb_prop_intro _ _ HleR HltR)).
Qed.

Lemma l4_source_chain_correspondence t1R t1L tR tL t2R t2L :
  SubNatRel t1R t1L -> SubNatRel tR tL -> SubNatRel t2R t2L ->
  PropSPropRel (t1R <= tR <= t2R)
    (Lean.And (ll_target_le t1L tL) (ll_target_le tL t2L)).
Proof.
  intros H1 H H2. apply prop_sprop_rel_intro.
  - intro Hboth.
    have Ha := l4_andb_prop_left _ _ Hboth.
    have Hb := l4_andb_prop_right _ _ Hboth.
    exact (Lean.And_intro _ _
      (prop_to_sprop _ _ (sub_nat_le_correspondence _ _ _ _ H1 H) Ha)
      (prop_to_sprop _ _ (sub_nat_le_correspondence _ _ _ _ H H2) Hb)).
  - intros [Ha Hb].
    have HaR := sprop_to_prop _ _
      (sub_nat_le_correspondence _ _ _ _ H1 H) Ha.
    have HbR := sprop_to_prop _ _
      (sub_nat_le_correspondence _ _ _ _ H H2) Hb.
    exact (strictly_inhabits (l4_andb_prop_intro _ _ HaR HbR)).
Qed.

Lemma l4_singleton_related xR xL : SubNatRel xR xL ->
  LlListRel [:: xR]
    (ImportedListLast.List_cons_inst1 Lean.Nat xL
      (ImportedListLast.List_nil_inst1 Lean.Nat)).
Proof. intro Hx. exact (ll_cons_related _ _ _ _ Hx ll_nil_related). Qed.

(** 1. [filter_last_mem]. *)
Theorem filter_last_mem_statement_certificate :
  PropSPropRel GeneratedListLastSource.statement_filter_last_mem
    l4_target_filter_last_mem_statement.
Proof.
  unfold GeneratedListLastSource.statement_filter_last_mem,
    l4_target_filter_last_mem_statement.
  apply prop_sprop_rel_intro.
  - intros Hsource T xsL d PL HhasL.
    pose xsR := lr_to_rocq xsL. pose PR := lr_pred_to_rocq PL.
    have Hxs : LrListRel xsR xsL := lr_target_roundtrip xsL.
    have HP : LrPredRel PR PL := lr_pred_surjective PL.
    have HhasR := sprop_to_prop _ _
      (ll_bool_true_correspondence _ _
        (l3_any_related T PR PL xsR xsL HP Hxs)) HhasL.
    have Hfilter := lr_filter_related T PR PL xsR xsL HP Hxs.
    have Hlast := l3_last_related d _ _ Hfilter.
    exact (prop_to_sprop _ _
      (l3_membership_related T _ _ xsR xsL Hlast Hxs)
      (Hsource T xsR d PR HhasR)).
  - intro Htarget. apply strictly_inhabits.
    intros T xsR d PR HhasR.
    have Hxs : LrListRel xsR (lr_to_imported xsR) := @Lean.eq_refl _ _.
    have HP : LrPredRel PR (lr_pred_to_imported PR) := lr_pred_canonical PR.
    have HhasL := prop_to_sprop _ _
      (ll_bool_true_correspondence _ _
        (l3_any_related T PR _ xsR _ HP Hxs)) HhasR.
    have Hfilter := lr_filter_related T PR _ xsR _ HP Hxs.
    have Hlast := l3_last_related d _ _ Hfilter.
    exact (sprop_to_prop _ _
      (l3_membership_related T _ _ xsR _ Hlast Hxs)
      (Htarget T (lr_to_imported xsR) d (lr_pred_to_imported PR) HhasL)).
Qed.

(** 2. [range], a computational definition. *)
Theorem range_definition_certificate aR aL bR bL :
  SubNatRel aR aL -> SubNatRel bR bL ->
  LlListRel (GeneratedListLastSource.range aR bR)
    (l4_target_range aL bL).
Proof. exact (l4_range_related aR aL bR bL). Qed.

(** 3. [iotaD_impl]. *)
Theorem iotaD_impl_statement_certificate :
  PropSPropRel GeneratedListLastSource.statement_iotaD_impl
    l4_target_iotaD_impl_statement.
Proof.
  unfold GeneratedListLastSource.statement_iotaD_impl,
    l4_target_iotaD_impl_statement.
  apply prop_sprop_rel_intro.
  - intros Hsource nleL mL nL HleL.
    pose nleR := sub_nat_to_rocq nleL.
    pose mR := sub_nat_to_rocq mL. pose nR := sub_nat_to_rocq nL.
    have Hnle : SubNatRel nleR nleL := sub_nat_rel_surjective nleL.
    have Hm : SubNatRel mR mL := sub_nat_rel_surjective mL.
    have Hn : SubNatRel nR nL := sub_nat_rel_surjective nL.
    have HleR := sprop_to_prop _ _
      (sub_nat_le_correspondence _ _ _ _ Hnle Hn) HleL.
    have Hleft := l4_iota_related mR mL nR nL Hm Hn.
    have Hprefix := l4_iota_related mR mL nleR nleL Hm Hnle.
    have Hstart := lr_add_related mR mL nleR nleL Hm Hnle.
    have Hlen := l4_local_sub_related nR nL nleR nleL Hn Hnle.
    have Hsuffix := l4_iota_related (mR + nleR) (lr_target_add mL nleL)
      (nR - nleR) (ll_target_sub nL nleL) Hstart Hlen.
    have Hright := ll_append_related _ _ _ _ Hprefix Hsuffix.
    exact (prop_to_sprop _ _
      (ll_list_eq_correspondence _ _ _ _ Hleft Hright)
      (Hsource nleR mR nR HleR)).
  - intro Htarget. apply strictly_inhabits.
    intros nleR mR nR HleR.
    have Hnle := sub_nat_rel_canonical nleR.
    have Hm := sub_nat_rel_canonical mR. have Hn := sub_nat_rel_canonical nR.
    have HleL := prop_to_sprop _ _
      (sub_nat_le_correspondence _ _ _ _ Hnle Hn) HleR.
    have Hleft := l4_iota_related mR _ nR _ Hm Hn.
    have Hprefix := l4_iota_related mR _ nleR _ Hm Hnle.
    have Hstart := lr_add_related mR _ nleR _ Hm Hnle.
    have Hlen := l4_local_sub_related nR _ nleR _ Hn Hnle.
    have Hsuffix := l4_iota_related (mR + nleR) _ (nR - nleR) _
      Hstart Hlen.
    have Hright := ll_append_related _ _ _ _ Hprefix Hsuffix.
    exact (sprop_to_prop _ _
      (ll_list_eq_correspondence _ _ _ _ Hleft Hright)
      (Htarget (sub_nat_to_imported nleR) (sub_nat_to_imported mR)
        (sub_nat_to_imported nR) HleL)).
Qed.

(** 4. [index_iota_lt_step]. *)
Theorem index_iota_lt_step_statement_certificate :
  PropSPropRel GeneratedListLastSource.statement_index_iota_lt_step
    l4_target_index_iota_lt_step_statement.
Proof.
  unfold GeneratedListLastSource.statement_index_iota_lt_step,
    l4_target_index_iota_lt_step_statement.
  apply prop_sprop_rel_intro.
  - intros Hsource aL bL HltL.
    pose aR := sub_nat_to_rocq aL. pose bR := sub_nat_to_rocq bL.
    have Ha := sub_nat_rel_surjective aL. have Hb := sub_nat_rel_surjective bL.
    have HltR := sprop_to_prop _ _
      (sub_nat_lt_correspondence _ _ _ _ Ha Hb) HltL.
    have Hleft := l4_index_iota_related aR aL bR bL Ha Hb.
    have Ha1 := lr_add_related aR aL 1 ll_target_one Ha lr_one_related.
    rewrite addn1 in Ha1.
    have Htail := l4_index_iota_related aR.+1
      (lr_target_add aL ll_target_one) bR bL Ha1 Hb.
    have Hright := ll_cons_related aR aL _ _ Ha Htail.
    exact (prop_to_sprop _ _
      (ll_list_eq_correspondence _ _ _ _ Hleft Hright)
      (Hsource aR bR HltR)).
  - intro Htarget. apply strictly_inhabits.
    intros aR bR HltR.
    have Ha := sub_nat_rel_canonical aR. have Hb := sub_nat_rel_canonical bR.
    have HltL := prop_to_sprop _ _
      (sub_nat_lt_correspondence _ _ _ _ Ha Hb) HltR.
    have Hleft := l4_index_iota_related aR _ bR _ Ha Hb.
    have Ha1 := lr_add_related aR _ 1 ll_target_one Ha lr_one_related.
    rewrite addn1 in Ha1.
    have Htail := l4_index_iota_related aR.+1 _ bR _ Ha1 Hb.
    have Hright := ll_cons_related aR _ _ _ Ha Htail.
    exact (sprop_to_prop _ _
      (ll_list_eq_correspondence _ _ _ _ Hleft Hright)
      (Htarget (sub_nat_to_imported aR) (sub_nat_to_imported bR) HltL)).
Qed.

(** 5. [index_iota_cat]. *)
Theorem index_iota_cat_statement_certificate :
  PropSPropRel GeneratedListLastSource.statement_index_iota_cat
    l4_target_index_iota_cat_statement.
Proof.
  unfold GeneratedListLastSource.statement_index_iota_cat,
    l4_target_index_iota_cat_statement.
  apply prop_sprop_rel_intro.
  - intros Hsource tL t1L t2L HboundsL.
    pose tR := sub_nat_to_rocq tL. pose t1R := sub_nat_to_rocq t1L.
    pose t2R := sub_nat_to_rocq t2L.
    have Ht := sub_nat_rel_surjective tL. have H1 := sub_nat_rel_surjective t1L.
    have H2 := sub_nat_rel_surjective t2L.
    have HboundsR := sprop_to_prop _ _
      (l4_source_chain_correspondence _ _ _ _ _ _ H1 Ht H2) HboundsL.
    have Hleft := l4_index_iota_related t1R t1L t2R t2L H1 H2.
    have Ha := l4_index_iota_related t1R t1L tR tL H1 Ht.
    have Hb := l4_index_iota_related tR tL t2R t2L Ht H2.
    have Hright := ll_append_related _ _ _ _ Ha Hb.
    exact (prop_to_sprop _ _
      (ll_list_eq_correspondence _ _ _ _ Hleft Hright)
      (Hsource tR t1R t2R HboundsR)).
  - intro Htarget. apply strictly_inhabits.
    intros tR t1R t2R HboundsR.
    have Ht := sub_nat_rel_canonical tR. have H1 := sub_nat_rel_canonical t1R.
    have H2 := sub_nat_rel_canonical t2R.
    have HboundsL := prop_to_sprop _ _
      (l4_source_chain_correspondence _ _ _ _ _ _ H1 Ht H2) HboundsR.
    have Hleft := l4_index_iota_related t1R _ t2R _ H1 H2.
    have Ha := l4_index_iota_related t1R _ tR _ H1 Ht.
    have Hb := l4_index_iota_related tR _ t2R _ Ht H2.
    have Hright := ll_append_related _ _ _ _ Ha Hb.
    exact (sprop_to_prop _ _
      (ll_list_eq_correspondence _ _ _ _ Hleft Hright)
      (Htarget (sub_nat_to_imported tR) (sub_nat_to_imported t1R)
        (sub_nat_to_imported t2R) HboundsL)).
Qed.

(** Predicate relations for the three filter families. *)
Lemma l4_mem_pred_related xR xL xsR xsL :
  SubNatRel xR xL -> LlListRel xsR xsL ->
  LlPredRel (fun rho => rho \in xsR)
    (fun rho => l4_target_decide_mem rho xsL).
Proof.
  intros Hx Hxs rhoR rhoL Hrho.
  exact (l4_decide_mem_related _ _ _ _ Hrho Hxs).
Qed.

Lemma l4_eq_pred_related xR xL : SubNatRel xR xL ->
  LlPredRel (fun rho => rho == xR)
    (fun rho => l4_target_decide_eq rho xL).
Proof.
  intros Hx rhoR rhoL Hrho.
  exact (l4_decide_eq_related _ _ _ _ Hrho Hx).
Qed.

(** 6. [range_filter_2cons]. *)
Theorem range_filter_2cons_statement_certificate :
  PropSPropRel GeneratedListLastSource.statement_range_filter_2cons
    l4_target_range_filter_2cons_statement.
Proof.
  unfold GeneratedListLastSource.statement_range_filter_2cons,
    l4_target_range_filter_2cons_statement.
  apply prop_sprop_rel_intro.
  - intros Hsource xL xsL kL.
    pose xR := sub_nat_to_rocq xL. pose xsR := ll_to_rocq xsL.
    pose kR := sub_nat_to_rocq kL.
    have Hx := sub_nat_rel_surjective xL. have Hxs := ll_target_roundtrip xsL.
    have Hk := sub_nat_rel_surjective kL.
    have Hrange := l4_range_related 0 ll_target_zero kR kL
      l3_zero_related Hk.
    have Hxxs := ll_cons_related xR xL _ _ Hx
      (ll_cons_related xR xL xsR xsL Hx Hxs).
    have Hxs1 := ll_cons_related xR xL xsR xsL Hx Hxs.
    have Hp1 := l4_mem_pred_related xR xL (xR :: xR :: xsR) _ Hx Hxxs.
    have Hp2 := l4_mem_pred_related xR xL (xR :: xsR) _ Hx Hxs1.
    have Hf1 := ll_filter_related _ _ _ _ Hp1 Hrange.
    have Hf2 := ll_filter_related _ _ _ _ Hp2 Hrange.
    exact (prop_to_sprop _ _
      (ll_list_eq_correspondence _ _ _ _ Hf1 Hf2)
      (Hsource xR xsR kR)).
  - intro Htarget. apply strictly_inhabits.
    intros xR xsR kR.
    have Hx := sub_nat_rel_canonical xR. have Hxs : LlListRel xsR _ := @Lean.eq_refl _ _.
    have Hk := sub_nat_rel_canonical kR.
    have Hrange := l4_range_related 0 ll_target_zero kR _ l3_zero_related Hk.
    have Hxxs := ll_cons_related xR _ _ _ Hx
      (ll_cons_related xR _ xsR _ Hx Hxs).
    have Hxs1 := ll_cons_related xR _ xsR _ Hx Hxs.
    have Hp1 := l4_mem_pred_related xR _ (xR :: xR :: xsR) _ Hx Hxxs.
    have Hp2 := l4_mem_pred_related xR _ (xR :: xsR) _ Hx Hxs1.
    have Hf1 := ll_filter_related _ _ _ _ Hp1 Hrange.
    have Hf2 := ll_filter_related _ _ _ _ Hp2 Hrange.
    exact (sprop_to_prop _ _
      (ll_list_eq_correspondence _ _ _ _ Hf1 Hf2)
      (Htarget (sub_nat_to_imported xR) (ll_to_imported xsR)
        (sub_nat_to_imported kR))).
Qed.

(** Shared correspondence of filtered interval results. *)
Lemma l4_eq_filter_result_correspondence xR xL aR aL bR bL :
  SubNatRel xR xL -> SubNatRel aR aL -> SubNatRel bR bL ->
  PropSPropRel
    ([seq rho <- index_iota aR bR | rho == xR] = [:: xR])
    (Lean.eq
      (ll_target_filter (fun rho => l4_target_decide_eq rho xL)
        (l4_target_index_iota aL bL))
      (ImportedListLast.List_cons_inst1 Lean.Nat xL
        (ImportedListLast.List_nil_inst1 Lean.Nat))).
Proof.
  intros Hx Ha Hb. apply ll_list_eq_correspondence.
  - apply ll_filter_related.
    + exact (l4_eq_pred_related xR xL Hx).
    + exact (l4_index_iota_related aR aL bR bL Ha Hb).
  - exact (l4_singleton_related xR xL Hx).
Qed.

(** 7. [index_iota_filter_eqx]. *)
Theorem index_iota_filter_eqx_statement_certificate :
  PropSPropRel GeneratedListLastSource.statement_index_iota_filter_eqx
    l4_target_index_iota_filter_eqx_statement.
Proof.
  unfold GeneratedListLastSource.statement_index_iota_filter_eqx,
    l4_target_index_iota_filter_eqx_statement.
  apply prop_sprop_rel_intro.
  - intros Hsource xL aL bL HboundL.
    pose xR := sub_nat_to_rocq xL. pose aR := sub_nat_to_rocq aL.
    pose bR := sub_nat_to_rocq bL.
    have Hx := sub_nat_rel_surjective xL. have Ha := sub_nat_rel_surjective aL.
    have Hb := sub_nat_rel_surjective bL.
    have HboundR := sprop_to_prop _ _
      (l4_interval_correspondence _ _ _ _ _ _ Ha Hx Hb) HboundL.
    exact (prop_to_sprop _ _
      (l4_eq_filter_result_correspondence _ _ _ _ _ _ Hx Ha Hb)
      (Hsource xR aR bR HboundR)).
  - intro Htarget. apply strictly_inhabits.
    intros xR aR bR HboundR.
    have Hx := sub_nat_rel_canonical xR. have Ha := sub_nat_rel_canonical aR.
    have Hb := sub_nat_rel_canonical bR.
    have HboundL := prop_to_sprop _ _
      (l4_interval_correspondence _ _ _ _ _ _ Ha Hx Hb) HboundR.
    exact (sprop_to_prop _ _
      (l4_eq_filter_result_correspondence _ _ _ _ _ _ Hx Ha Hb)
      (Htarget (sub_nat_to_imported xR) (sub_nat_to_imported aR)
        (sub_nat_to_imported bR) HboundL)).
Qed.

Lemma l4_singleton_mem_pred_related xR xL : SubNatRel xR xL ->
  LlPredRel (fun rho => rho \in [:: xR])
    (fun rho => l4_target_decide_mem rho
      (ImportedListLast.List_cons_inst1 Lean.Nat xL
        (ImportedListLast.List_nil_inst1 Lean.Nat))).
Proof.
  intro Hx.
  exact (l4_mem_pred_related xR xL [:: xR]
    (ImportedListLast.List_cons_inst1 Lean.Nat xL
      (ImportedListLast.List_nil_inst1 Lean.Nat)) Hx
    (l4_singleton_related xR xL Hx)).
Qed.

Lemma l4_singleton_filter_result_correspondence xR xL aR aL bR bL :
  SubNatRel xR xL -> SubNatRel aR aL -> SubNatRel bR bL ->
  PropSPropRel
    ([seq rho <- index_iota aR bR | rho \in [:: xR]] = [:: xR])
    (Lean.eq
      (ll_target_filter
        (fun rho => l4_target_decide_mem rho
          (ImportedListLast.List_cons_inst1 Lean.Nat xL
            (ImportedListLast.List_nil_inst1 Lean.Nat)))
        (l4_target_index_iota aL bL))
      (ImportedListLast.List_cons_inst1 Lean.Nat xL
        (ImportedListLast.List_nil_inst1 Lean.Nat))).
Proof.
  intros Hx Ha Hb. apply ll_list_eq_correspondence.
  - apply ll_filter_related.
    + exact (l4_singleton_mem_pred_related xR xL Hx).
    + exact (l4_index_iota_related aR aL bR bL Ha Hb).
  - exact (l4_singleton_related xR xL Hx).
Qed.

(** 8. [index_iota_filter_singl]. *)
Theorem index_iota_filter_singl_statement_certificate :
  PropSPropRel GeneratedListLastSource.statement_index_iota_filter_singl
    l4_target_index_iota_filter_singl_statement.
Proof.
  unfold GeneratedListLastSource.statement_index_iota_filter_singl,
    l4_target_index_iota_filter_singl_statement.
  apply prop_sprop_rel_intro.
  - intros Hsource xL aL bL HboundL.
    pose xR := sub_nat_to_rocq xL. pose aR := sub_nat_to_rocq aL.
    pose bR := sub_nat_to_rocq bL.
    have Hx := sub_nat_rel_surjective xL. have Ha := sub_nat_rel_surjective aL.
    have Hb := sub_nat_rel_surjective bL.
    have HboundR := sprop_to_prop _ _
      (l4_interval_correspondence _ _ _ _ _ _ Ha Hx Hb) HboundL.
    exact (prop_to_sprop _ _
      (l4_singleton_filter_result_correspondence _ _ _ _ _ _ Hx Ha Hb)
      (Hsource xR aR bR HboundR)).
  - intro Htarget. apply strictly_inhabits.
    intros xR aR bR HboundR.
    have Hx := sub_nat_rel_canonical xR. have Ha := sub_nat_rel_canonical aR.
    have Hb := sub_nat_rel_canonical bR.
    have HboundL := prop_to_sprop _ _
      (l4_interval_correspondence _ _ _ _ _ _ Ha Hx Hb) HboundR.
    exact (sprop_to_prop _ _
      (l4_singleton_filter_result_correspondence _ _ _ _ _ _ Hx Ha Hb)
      (Htarget (sub_nat_to_imported xR) (sub_nat_to_imported aR)
        (sub_nat_to_imported bR) HboundL)).
Qed.

Lemma l4_inxs_filter_result_correspondence aR aL bR bL xR xL xsR xsL :
  SubNatRel aR aL -> SubNatRel bR bL -> SubNatRel xR xL ->
  LlListRel xsR xsL ->
  PropSPropRel
    ([seq rho <- index_iota aR bR | rho \in xsR] =
      [seq rho <- index_iota aR bR |
        rho \in GeneratedListLastSource.rem_all xR xsR])
    (Lean.eq
      (ll_target_filter (fun rho => l4_target_decide_mem rho xsL)
        (l4_target_index_iota aL bL))
      (ll_target_filter
        (fun rho => l4_target_decide_mem rho (l4_target_rem_all xL xsL))
        (l4_target_index_iota aL bL))).
Proof.
  intros Ha Hb Hx Hxs. apply ll_list_eq_correspondence.
  - apply ll_filter_related.
    + exact (l4_mem_pred_related xR xL xsR xsL Hx Hxs).
    + exact (l4_index_iota_related aR aL bR bL Ha Hb).
  - apply ll_filter_related.
    + exact (l4_mem_pred_related xR xL
        (GeneratedListLastSource.rem_all xR xsR)
        (l4_target_rem_all xL xsL) Hx
        (l4_rem_all_related xR xL xsR xsL Hx Hxs)).
    + exact (l4_index_iota_related aR aL bR bL Ha Hb).
Qed.

(** 9. [index_iota_filter_inxs]. *)
Theorem index_iota_filter_inxs_statement_certificate :
  PropSPropRel GeneratedListLastSource.statement_index_iota_filter_inxs
    l4_target_index_iota_filter_inxs_statement.
Proof.
  unfold GeneratedListLastSource.statement_index_iota_filter_inxs,
    l4_target_index_iota_filter_inxs_statement.
  apply prop_sprop_rel_intro.
  - intros Hsource aL bL xL xsL HltL.
    pose aR := sub_nat_to_rocq aL. pose bR := sub_nat_to_rocq bL.
    pose xR := sub_nat_to_rocq xL. pose xsR := ll_to_rocq xsL.
    have Ha := sub_nat_rel_surjective aL. have Hb := sub_nat_rel_surjective bL.
    have Hx := sub_nat_rel_surjective xL. have Hxs := ll_target_roundtrip xsL.
    have HltR := sprop_to_prop _ _
      (sub_nat_lt_correspondence _ _ _ _ Hx Ha) HltL.
    exact (prop_to_sprop _ _
      (l4_inxs_filter_result_correspondence _ _ _ _ _ _ _ _
        Ha Hb Hx Hxs)
      (Hsource aR bR xR xsR HltR)).
  - intro Htarget. apply strictly_inhabits.
    intros aR bR xR xsR HltR.
    have Ha := sub_nat_rel_canonical aR. have Hb := sub_nat_rel_canonical bR.
    have Hx := sub_nat_rel_canonical xR.
    have Hxs : LlListRel xsR (ll_to_imported xsR) := @Lean.eq_refl _ _.
    have HltL := prop_to_sprop _ _
      (sub_nat_lt_correspondence _ _ _ _ Hx Ha) HltR.
    exact (sprop_to_prop _ _
      (l4_inxs_filter_result_correspondence _ _ _ _ _ _ _ _
        Ha Hb Hx Hxs)
      (Htarget (sub_nat_to_imported aR) (sub_nat_to_imported bR)
        (sub_nat_to_imported xR) (ll_to_imported xsR) HltL)).
Qed.

Print Assumptions filter_last_mem_statement_certificate.
Print Assumptions range_definition_certificate.
Print Assumptions iotaD_impl_statement_certificate.
Print Assumptions index_iota_lt_step_statement_certificate.
Print Assumptions index_iota_cat_statement_certificate.
Print Assumptions range_filter_2cons_statement_certificate.
Print Assumptions index_iota_filter_eqx_statement_certificate.
Print Assumptions index_iota_filter_singl_statement_certificate.
Print Assumptions index_iota_filter_inxs_statement_certificate.
