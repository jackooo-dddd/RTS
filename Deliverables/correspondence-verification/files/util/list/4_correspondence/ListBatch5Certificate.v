From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq fintype bigop.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedListLast.
From FoundationCertificates Require Import
  PropSPropFoundation LogicalRelation SubadditivityNatCorrespondence
  ListLastCertificate ListRemCertificate ListBatch2Certificate
  ListBatch3Operations ListBatch4Operations ListBatch4Certificate
  ListBatch5Operations.
From prosa Require Import GeneratedListLastSource.

(** Exact structural target propositions.  The accompanying type-audit file
    binds these aliases to the target theorem types from the current imported
    compiled Lean artifact. *)

Definition l5_target_index_iota_filter_step_statement : SProp :=
  forall (x : Lean.Nat) (xs : ImportedListLast.List_inst1 Lean.Nat)
    (a b : Lean.Nat),
    Lean.And (ll_target_le a x) (ll_target_lt x b) ->
    (forall y : Lean.Nat, ll_target_mem y xs -> ll_target_le x y) ->
    Lean.eq
      (ll_target_filter
        (fun rho => l4_target_decide_mem rho
          (ImportedListLast.List_cons_inst1 Lean.Nat x xs))
        (l4_target_index_iota a b))
      (ImportedListLast.List_cons_inst1 Lean.Nat x
        (ll_target_filter
          (fun rho => l4_target_decide_mem rho (l4_target_rem_all x xs))
          (l4_target_index_iota a b))).

Definition l5_target_range_iota_filter_step_statement : SProp :=
  forall (x : Lean.Nat) (xs : ImportedListLast.List_inst1 Lean.Nat)
    (k : Lean.Nat),
    ll_target_le x k ->
    (forall y : Lean.Nat, ll_target_mem y xs -> ll_target_le x y) ->
    Lean.eq
      (ll_target_filter
        (fun rho => l4_target_decide_mem rho
          (ImportedListLast.List_cons_inst1 Lean.Nat x xs))
        (l4_target_range ll_target_zero k))
      (ImportedListLast.List_cons_inst1 Lean.Nat x
        (ll_target_filter
          (fun rho => l4_target_decide_mem rho (l4_target_rem_all x xs))
          (l4_target_range ll_target_zero k))).

Definition l5_target_iota_filter_gt_statement : SProp :=
  forall (x a b idx : Lean.Nat) (P : Lean.Nat -> ImportedListLast.Bool),
    ll_target_lt x a ->
    ll_target_lt idx
      (ll_target_length (ll_target_filter P (l4_target_index_iota a b))) ->
    ll_target_lt x
      (ll_target_getD (ll_target_filter P (l4_target_index_iota a b)) idx).

Definition l5_target_sub_count_seq_statement : SProp :=
  forall (T : eqType) (f g : T -> ImportedListLast.Bool)
    (xs : ImportedListLast.List T),
    (forall x : T, lr_target_mem x xs ->
      Lean.eq (f x) ImportedListLast.Bool_true ->
      Lean.eq (g x) ImportedListLast.Bool_true) ->
    ll_target_le (l5_target_countP f xs) (l5_target_countP g xs).

Definition l5_target_count_predUI_statement : SProp :=
  forall (P1 P2 : Lean.Nat -> ImportedListLast.Bool)
    (xs : ImportedListLast.List_inst1 Lean.Nat),
    Lean.eq
      (l5_target_nat_countP
        (fun x => ImportedListLast.Bool_or (P1 x) (P2 x)) xs)
      (ll_target_sub
        (lr_target_add (l5_target_nat_countP P1 xs)
          (l5_target_nat_countP P2 xs))
        (l5_target_nat_countP
          (fun x => ImportedListLast.Bool_and (P1 x) (P2 x)) xs)).

(** A pointwise lower-bound proposition is preserved by the already
    certified Nat, membership, and order relations. *)
Lemma l5_minimum_correspondence xR xL xsR xsL :
  SubNatRel xR xL -> LlListRel xsR xsL ->
  PropSPropRel
    (forall y : nat, y \in xsR -> is_true (leq xR y))
    (forall y : Lean.Nat, ll_target_mem y xsL -> ll_target_le xL y).
Proof.
  intros Hx Hxs. apply prop_sprop_rel_intro.
  - intros HR yL HmemL.
    pose yR := sub_nat_to_rocq yL.
    have Hy : SubNatRel yR yL := sub_nat_rel_surjective yL.
    have HmemR := sprop_to_prop _ _
      (ll_membership_correspondence yR yL xsR xsL Hy Hxs) HmemL.
    exact (prop_to_sprop _ _
      (sub_nat_le_correspondence xR xL yR yL Hx Hy)
      (HR yR HmemR)).
  - intro HL. apply strictly_inhabits. intros yR HmemR.
    have Hy := sub_nat_rel_canonical yR.
    have HmemL := prop_to_sprop _ _
      (ll_membership_correspondence yR _ xsR xsL Hy Hxs) HmemR.
    exact (sprop_to_prop _ _
      (sub_nat_le_correspondence xR xL yR _ Hx Hy)
      (HL (sub_nat_to_imported yR) HmemL)).
Qed.

Lemma l5_index_filter_step_result_correspondence
    xR xL xsR xsL aR aL bR bL :
  SubNatRel xR xL -> LlListRel xsR xsL ->
  SubNatRel aR aL -> SubNatRel bR bL ->
  PropSPropRel
    ([seq rho <- index_iota aR bR | rho \in xR :: xsR] =
      xR :: [seq rho <- index_iota aR bR |
        rho \in GeneratedListLastSource.rem_all xR xsR])
    (Lean.eq
      (ll_target_filter
        (fun rho => l4_target_decide_mem rho
          (ImportedListLast.List_cons_inst1 Lean.Nat xL xsL))
        (l4_target_index_iota aL bL))
      (ImportedListLast.List_cons_inst1 Lean.Nat xL
        (ll_target_filter
          (fun rho => l4_target_decide_mem rho (l4_target_rem_all xL xsL))
          (l4_target_index_iota aL bL)))).
Proof.
  intros Hx Hxs Ha Hb.
  have Hidx := l4_index_iota_related aR aL bR bL Ha Hb.
  have Hcons := ll_cons_related xR xL xsR xsL Hx Hxs.
  have Hleft := ll_filter_related _ _ _ _
    (l4_mem_pred_related xR xL _ _ Hx Hcons) Hidx.
  have Hrem := l4_rem_all_related xR xL xsR xsL Hx Hxs.
  have Htail := ll_filter_related _ _ _ _
    (l4_mem_pred_related xR xL _ _ Hx Hrem) Hidx.
  have Hright := ll_cons_related xR xL _ _ Hx Htail.
  exact (ll_list_eq_correspondence _ _ _ _ Hleft Hright).
Qed.

Lemma l5_range_filter_step_result_correspondence
    xR xL xsR xsL kR kL :
  SubNatRel xR xL -> LlListRel xsR xsL -> SubNatRel kR kL ->
  PropSPropRel
    ([seq rho <- GeneratedListLastSource.range 0 kR | rho \in xR :: xsR] =
      xR :: [seq rho <- GeneratedListLastSource.range 0 kR |
        rho \in GeneratedListLastSource.rem_all xR xsR])
    (Lean.eq
      (ll_target_filter
        (fun rho => l4_target_decide_mem rho
          (ImportedListLast.List_cons_inst1 Lean.Nat xL xsL))
        (l4_target_range ll_target_zero kL))
      (ImportedListLast.List_cons_inst1 Lean.Nat xL
        (ll_target_filter
          (fun rho => l4_target_decide_mem rho (l4_target_rem_all xL xsL))
          (l4_target_range ll_target_zero kL)))).
Proof.
  intros Hx Hxs Hk.
  have Hrange := l4_range_related 0 ll_target_zero kR kL
    l3_zero_related Hk.
  have Hcons := ll_cons_related xR xL xsR xsL Hx Hxs.
  have Hleft := ll_filter_related _ _ _ _
    (l4_mem_pred_related xR xL _ _ Hx Hcons) Hrange.
  have Hrem := l4_rem_all_related xR xL xsR xsL Hx Hxs.
  have Htail := ll_filter_related _ _ _ _
    (l4_mem_pred_related xR xL _ _ Hx Hrem) Hrange.
  have Hright := ll_cons_related xR xL _ _ Hx Htail.
  exact (ll_list_eq_correspondence _ _ _ _ Hleft Hright).
Qed.

(** 1. [index_iota_filter_step]. *)
Theorem index_iota_filter_step_statement_certificate :
  PropSPropRel GeneratedListLastSource.statement_index_iota_filter_step
    l5_target_index_iota_filter_step_statement.
Proof.
  unfold GeneratedListLastSource.statement_index_iota_filter_step,
    l5_target_index_iota_filter_step_statement.
  apply prop_sprop_rel_intro.
  - intros Hsource xL xsL aL bL HboundsL HminL.
    pose xR := sub_nat_to_rocq xL. pose xsR := ll_to_rocq xsL.
    pose aR := sub_nat_to_rocq aL. pose bR := sub_nat_to_rocq bL.
    have Hx := sub_nat_rel_surjective xL. have Hxs := ll_target_roundtrip xsL.
    have Ha := sub_nat_rel_surjective aL. have Hb := sub_nat_rel_surjective bL.
    have HboundsR := sprop_to_prop _ _
      (l4_interval_correspondence _ _ _ _ _ _ Ha Hx Hb) HboundsL.
    have HminR := sprop_to_prop _ _
      (l5_minimum_correspondence _ _ _ _ Hx Hxs) HminL.
    exact (prop_to_sprop _ _
      (l5_index_filter_step_result_correspondence
        xR xL xsR xsL aR aL bR bL Hx Hxs Ha Hb)
      (Hsource xR xsR aR bR HboundsR HminR)).
  - intro Htarget. apply strictly_inhabits.
    intros xR xsR aR bR HboundsR HminR.
    have Hx := sub_nat_rel_canonical xR. have Hxs : LlListRel xsR _ := @Lean.eq_refl _ _.
    have Ha := sub_nat_rel_canonical aR. have Hb := sub_nat_rel_canonical bR.
    have HboundsL := prop_to_sprop _ _
      (l4_interval_correspondence _ _ _ _ _ _ Ha Hx Hb) HboundsR.
    have HminL := prop_to_sprop _ _
      (l5_minimum_correspondence _ _ _ _ Hx Hxs) HminR.
    exact (sprop_to_prop _ _
      (l5_index_filter_step_result_correspondence
        xR _ xsR _ aR _ bR _ Hx Hxs Ha Hb)
      (Htarget (sub_nat_to_imported xR) (ll_to_imported xsR)
        (sub_nat_to_imported aR) (sub_nat_to_imported bR)
        HboundsL HminL)).
Qed.

(** 2. [range_iota_filter_step]. *)
Theorem range_iota_filter_step_statement_certificate :
  PropSPropRel GeneratedListLastSource.statement_range_iota_filter_step
    l5_target_range_iota_filter_step_statement.
Proof.
  unfold GeneratedListLastSource.statement_range_iota_filter_step,
    l5_target_range_iota_filter_step_statement.
  apply prop_sprop_rel_intro.
  - intros Hsource xL xsL kL HboundL HminL.
    pose xR := sub_nat_to_rocq xL. pose xsR := ll_to_rocq xsL.
    pose kR := sub_nat_to_rocq kL.
    have Hx := sub_nat_rel_surjective xL. have Hxs := ll_target_roundtrip xsL.
    have Hk := sub_nat_rel_surjective kL.
    have HboundR := sprop_to_prop _ _
      (sub_nat_le_correspondence _ _ _ _ Hx Hk) HboundL.
    have HminR := sprop_to_prop _ _
      (l5_minimum_correspondence _ _ _ _ Hx Hxs) HminL.
    exact (prop_to_sprop _ _
      (l5_range_filter_step_result_correspondence
        xR xL xsR xsL kR kL Hx Hxs Hk)
      (Hsource xR xsR kR HboundR HminR)).
  - intro Htarget. apply strictly_inhabits.
    intros xR xsR kR HboundR HminR.
    have Hx := sub_nat_rel_canonical xR. have Hxs : LlListRel xsR _ := @Lean.eq_refl _ _.
    have Hk := sub_nat_rel_canonical kR.
    have HboundL := prop_to_sprop _ _
      (sub_nat_le_correspondence _ _ _ _ Hx Hk) HboundR.
    have HminL := prop_to_sprop _ _
      (l5_minimum_correspondence _ _ _ _ Hx Hxs) HminR.
    exact (sprop_to_prop _ _
      (l5_range_filter_step_result_correspondence
        xR _ xsR _ kR _ Hx Hxs Hk)
      (Htarget (sub_nat_to_imported xR) (ll_to_imported xsR)
        (sub_nat_to_imported kR) HboundL HminL)).
Qed.

(** 3. [iota_filter_gt]. *)
Theorem iota_filter_gt_statement_certificate :
  PropSPropRel GeneratedListLastSource.statement_iota_filter_gt
    l5_target_iota_filter_gt_statement.
Proof.
  unfold GeneratedListLastSource.statement_iota_filter_gt,
    l5_target_iota_filter_gt_statement.
  apply prop_sprop_rel_intro.
  - intros Hsource xL aL bL idxL PL HlowerL HidxL.
    pose xR := sub_nat_to_rocq xL. pose aR := sub_nat_to_rocq aL.
    pose bR := sub_nat_to_rocq bL. pose idxR := sub_nat_to_rocq idxL.
    pose PR := ll_pred_from_imported PL.
    have Hx := sub_nat_rel_surjective xL. have Ha := sub_nat_rel_surjective aL.
    have Hb := sub_nat_rel_surjective bL. have Hidx := sub_nat_rel_surjective idxL.
    have HP := ll_pred_rel_surjective PL.
    have Hinterval := l4_index_iota_related aR aL bR bL Ha Hb.
    have Hfilter := ll_filter_related PR PL _ _ HP Hinterval.
    have Hlength := ll_length_related _ _ Hfilter.
    have HlowerR := sprop_to_prop _ _
      (sub_nat_lt_correspondence _ _ _ _ Hx Ha) HlowerL.
    have HidxR := sprop_to_prop _ _
      (sub_nat_lt_correspondence _ _ _ _ Hidx Hlength) HidxL.
    have Hget := ll_getD_related _ _ _ _ Hfilter Hidx.
    exact (prop_to_sprop _ _
      (sub_nat_lt_correspondence _ _ _ _ Hx Hget)
      (Hsource xR aR bR idxR PR HlowerR HidxR)).
  - intro Htarget. apply strictly_inhabits.
    intros xR aR bR idxR PR HlowerR HidxR.
    have Hx := sub_nat_rel_canonical xR. have Ha := sub_nat_rel_canonical aR.
    have Hb := sub_nat_rel_canonical bR. have Hidx := sub_nat_rel_canonical idxR.
    have HP := ll_pred_rel_canonical PR.
    have Hinterval := l4_index_iota_related aR _ bR _ Ha Hb.
    have Hfilter := ll_filter_related PR _ _ _ HP Hinterval.
    have Hlength := ll_length_related _ _ Hfilter.
    have HlowerL := prop_to_sprop _ _
      (sub_nat_lt_correspondence _ _ _ _ Hx Ha) HlowerR.
    have HidxL := prop_to_sprop _ _
      (sub_nat_lt_correspondence _ _ _ _ Hidx Hlength) HidxR.
    have Hget := ll_getD_related _ _ _ _ Hfilter Hidx.
    exact (sprop_to_prop _ _
      (sub_nat_lt_correspondence _ _ _ _ Hx Hget)
      (Htarget (sub_nat_to_imported xR) (sub_nat_to_imported aR)
        (sub_nat_to_imported bR) (sub_nat_to_imported idxR)
        (ll_target_pred PR) HlowerL HidxL)).
Qed.

(** 4. [sub_count_seq]. *)
Theorem sub_count_seq_statement_certificate :
  PropSPropRel GeneratedListLastSource.statement_sub_count_seq
    l5_target_sub_count_seq_statement.
Proof.
  unfold GeneratedListLastSource.statement_sub_count_seq,
    l5_target_sub_count_seq_statement.
  apply prop_sprop_rel_intro.
  - intros Hsource T fL gL xsL HimplL.
    pose fR := lr_pred_to_rocq fL. pose gR := lr_pred_to_rocq gL.
    pose xsR := lr_to_rocq xsL.
    have Hf := lr_pred_surjective fL. have Hg := lr_pred_surjective gL.
    have Hxs := lr_target_roundtrip xsL.
    have HimplR : forall x : T, x \in xsR -> fR x -> gR x.
    { intros x HmemR HtrueR.
      have HmemL := prop_to_sprop _ _
        (lr_membership_correspondence T x xsR xsL Hxs) HmemR.
      have HtrueL := prop_to_sprop _ _
        (ll_bool_true_correspondence _ _ (Hf x)) HtrueR.
      exact (sprop_to_prop _ _
        (ll_bool_true_correspondence _ _ (Hg x))
        (HimplL x HmemL HtrueL)). }
    have Hcf := l5_countP_related T fR fL xsR xsL Hf Hxs.
    have Hcg := l5_countP_related T gR gL xsR xsL Hg Hxs.
    exact (prop_to_sprop _ _
      (sub_nat_le_correspondence _ _ _ _ Hcf Hcg)
      (Hsource T fR gR xsR HimplR)).
  - intro Htarget. apply strictly_inhabits.
    intros T fR gR xsR HimplR.
    have Hf := lr_pred_canonical fR. have Hg := lr_pred_canonical gR.
    have Hxs : LrListRel xsR (lr_to_imported xsR) := @Lean.eq_refl _ _.
    have Hcf := l5_countP_related T fR _ xsR _ Hf Hxs.
    have Hcg := l5_countP_related T gR _ xsR _ Hg Hxs.
    exact (sprop_to_prop _ _
      (sub_nat_le_correspondence _ _ _ _ Hcf Hcg)
      (Htarget T (lr_pred_to_imported fR) (lr_pred_to_imported gR)
        (lr_to_imported xsR)
        (fun x HmemL HtrueL =>
          prop_to_sprop _ _
            (ll_bool_true_correspondence _ _ (Hg x))
            (HimplR x
              (sprop_to_prop _ _
                (lr_membership_correspondence T x xsR _ Hxs) HmemL)
              (sprop_to_prop _ _
                (ll_bool_true_correspondence _ _ (Hf x)) HtrueL))))).
Qed.

(** 5. [count_predUI']. *)
Theorem count_predUI_statement_certificate :
  PropSPropRel GeneratedListLastSource.statement_count_predUI'
    l5_target_count_predUI_statement.
Proof.
  unfold GeneratedListLastSource.statement_count_predUI',
    l5_target_count_predUI_statement.
  apply prop_sprop_rel_intro.
  - intros Hsource P1L P2L xsL.
    pose P1R := ll_pred_from_imported P1L.
    pose P2R := ll_pred_from_imported P2L.
    pose xsR := ll_to_rocq xsL.
    have HP1 := ll_pred_rel_surjective P1L.
    have HP2 := ll_pred_rel_surjective P2L.
    have Hxs := ll_target_roundtrip xsL.
    have Hunion := l5_nat_countP_related
      (fun x => P1R x || P2R x)
      (fun x => ImportedListLast.Bool_or (P1L x) (P2L x)) xsR xsL
      (fun xR xL Hx => l3_bool_or_related _ _ _ _
        (HP1 xR xL Hx) (HP2 xR xL Hx)) Hxs.
    have HC1 := l5_nat_countP_related P1R P1L xsR xsL HP1 Hxs.
    have HC2 := l5_nat_countP_related P2R P2L xsR xsL HP2 Hxs.
    have Hinter := l5_nat_countP_related
      (fun x => P1R x && P2R x)
      (fun x => ImportedListLast.Bool_and (P1L x) (P2L x)) xsR xsL
      (fun xR xL Hx => l3_bool_and_related _ _ _ _
        (HP1 xR xL Hx) (HP2 xR xL Hx)) Hxs.
    have Hadd := lr_add_related (count P1R xsR) _ (count P2R xsR) _ HC1 HC2.
    have Hsub := l4_local_sub_related
      (count P1R xsR + count P2R xsR) _
      (count (fun x => P1R x && P2R x) xsR) _ Hadd Hinter.
    exact (prop_to_sprop _ _
      (sub_nat_eq_correspondence _ _ _ _ Hunion Hsub)
      (Hsource P1R P2R xsR)).
  - intro Htarget. apply strictly_inhabits.
    intros P1R P2R xsR.
    have HP1 := ll_pred_rel_canonical P1R.
    have HP2 := ll_pred_rel_canonical P2R.
    have Hxs : LlListRel xsR (ll_to_imported xsR) := @Lean.eq_refl _ _.
    have Hunion := l5_nat_countP_related
      (fun x => P1R x || P2R x)
      (fun x => ImportedListLast.Bool_or
        (ll_target_pred P1R x) (ll_target_pred P2R x)) xsR _
      (fun xR xL Hx => l3_bool_or_related _ _ _ _
        (HP1 xR xL Hx) (HP2 xR xL Hx)) Hxs.
    have HC1 := l5_nat_countP_related P1R _ xsR _ HP1 Hxs.
    have HC2 := l5_nat_countP_related P2R _ xsR _ HP2 Hxs.
    have Hinter := l5_nat_countP_related
      (fun x => P1R x && P2R x)
      (fun x => ImportedListLast.Bool_and
        (ll_target_pred P1R x) (ll_target_pred P2R x)) xsR _
      (fun xR xL Hx => l3_bool_and_related _ _ _ _
        (HP1 xR xL Hx) (HP2 xR xL Hx)) Hxs.
    have Hadd := lr_add_related (count P1R xsR) _ (count P2R xsR) _ HC1 HC2.
    have Hsub := l4_local_sub_related
      (count P1R xsR + count P2R xsR) _
      (count (fun x => P1R x && P2R x) xsR) _ Hadd Hinter.
    exact (sprop_to_prop _ _
      (sub_nat_eq_correspondence _ _ _ _ Hunion Hsub)
      (Htarget (ll_target_pred P1R) (ll_target_pred P2R)
        (ll_to_imported xsR))).
Qed.

(** [prefix_of], directly against the imported production definition. *)
Theorem prefix_of_definition_certificate (T : eqType)
    (xsR ysR : seq T) (xsL ysL : ImportedListLast.List T) :
  LrListRel xsR xsL -> LrListRel ysR ysL ->
  PropSPropRel (GeneratedListLastSource.prefix_of xsR ysR)
    (l5_target_prefix_of T xsL ysL).
Proof.
  intros Hxs Hys.
  unfold GeneratedListLastSource.prefix_of, l5_target_prefix_of,
    ImportedListLast.Prosa_Util_List_prefix_of.
  apply lr_exists_list_correspondence. intros tailR tailL Htail.
  exact (lr_list_eq_correspondence _ _ _ _
    (lr_append_related T xsR tailR xsL tailL Hxs Htail) Hys).
Qed.

(** [strict_prefix_of], including the non-empty residual observation. *)
Theorem strict_prefix_of_definition_certificate (T : eqType)
    (xsR ysR : seq T) (xsL ysL : ImportedListLast.List T) :
  LrListRel xsR xsL -> LrListRel ysR ysL ->
  PropSPropRel (GeneratedListLastSource.strict_prefix_of xsR ysR)
    (l5_target_strict_prefix_of T xsL ysL).
Proof.
  intros Hxs Hys.
  unfold GeneratedListLastSource.strict_prefix_of,
    l5_target_strict_prefix_of,
    ImportedListLast.Prosa_Util_List_strict_prefix_of.
  apply lr_exists_list_correspondence. intros tailR tailL Htail.
  apply lr_and_correspondence.
  - have Hnil : LrListRel [::] (ImportedListLast.List_nil T) :=
      @Lean.eq_refl _ _.
    exact (lb_not_correspondence
      (Logic.eq tailR [::])
      (Lean.eq tailL (ImportedListLast.List_nil T))
      (lr_list_eq_correspondence _ _ _ _ Htail Hnil)).
  - exact (lr_list_eq_correspondence _ _ _ _
      (lr_append_related T xsR tailR xsL tailL Hxs Htail) Hys).
Qed.

(** [shift_points_pos], preserving ordered map computation. *)
Theorem shift_points_pos_definition_certificate xsR xsL sR sL :
  LlListRel xsR xsL -> SubNatRel sR sL ->
  LlListRel (GeneratedListLastSource.shift_points_pos xsR sR)
    (l5_target_shift_points_pos xsL sL).
Proof.
  intros Hxs Hs.
  have Hmap := l5_nat_map_related _ _ _ _
    (fun xR xL Hx => lr_add_related sR sL xR xL Hs Hx) Hxs.
  unfold GeneratedListLastSource.shift_points_pos.
  unfold LlListRel in Hmap |- *.
  exact (sub_imported_eq_trans _ _ _ Hmap
    (sub_imported_eq_sym _ _
      (ImportedListLast.Prosa_Validation_ListLastInterface_production_shift_points_pos_eq
        xsL sL))).
Qed.

(** [shift_points_neg], composing filter, truncated subtraction, and map. *)
Theorem shift_points_neg_definition_certificate xsR xsL sR sL :
  LlListRel xsR xsL -> SubNatRel sR sL ->
  LlListRel (GeneratedListLastSource.shift_points_neg xsR sR)
    (l5_target_shift_points_neg xsL sL).
Proof.
  intros Hxs Hs.
  have Hfilter := ll_filter_related _ _ _ _
    (fun xR xL Hx => l3_decide_le_related _ _ _ _ Hs Hx) Hxs.
  have Hmap := l5_nat_map_related _ _ _ _
    (fun xR xL Hx => l4_local_sub_related _ _ _ _ Hx Hs) Hfilter.
  unfold GeneratedListLastSource.shift_points_neg.
  unfold LlListRel in Hmap |- *.
  exact (sub_imported_eq_trans _ _ _ Hmap
    (sub_imported_eq_sym _ _
      (ImportedListLast.Prosa_Validation_ListLastInterface_production_shift_points_neg_eq
        xsL sL))).
Qed.

Print Assumptions prefix_of_definition_certificate.
Print Assumptions strict_prefix_of_definition_certificate.
Print Assumptions shift_points_pos_definition_certificate.
Print Assumptions shift_points_neg_definition_certificate.
