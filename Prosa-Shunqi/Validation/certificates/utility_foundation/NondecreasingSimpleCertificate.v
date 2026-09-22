From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq
  fintype bigop.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedNondecreasing.
From FoundationCertificates Require Import
  PropSPropFoundation LogicalRelation SubadditivityNatCorrespondence
  NondecreasingBaseAdapter NondecreasingCorrespondence.
From prosa Require Import GeneratedNondecreasingSource.

(** First theorem-statement cluster for [util/nondecreasing.v].  The target
    theorem constants occur only in the separate type-audit module; none is
    used to construct these correspondence proofs. *)

Lemma nd_cons_related xR xL xsR xsL :
  SubNatRel xR xL -> NdNatListRel xsR xsL ->
  NdNatListRel (xR :: xsR)
    (ImportedNondecreasing.List_cons_inst1 Lean.Nat xL xsL).
Proof.
  intros Hx Hxs. unfold NdNatListRel. cbn [nd_nat_list_to_imported].
  exact (nd_nat_list_cons_congr _ _ _ _ Hx Hxs).
Qed.

Lemma nd_list_eq_correspondence xsR xsL ysR ysL :
  NdNatListRel xsR xsL -> NdNatListRel ysR ysL ->
  PropSPropRel (Logic.eq xsR ysR) (Lean.eq xsL ysL).
Proof.
  intros Hxs Hys. apply prop_sprop_rel_intro.
  - intro Hxy. subst ysR.
    exact (sub_imported_eq_trans _ _ _
      (sub_imported_eq_sym _ _ Hxs) Hys).
  - intro Hxy. apply strictly_inhabits.
    have Hmap : Lean.eq (nd_nat_list_to_imported xsR)
        (nd_nat_list_to_imported ysR) :=
      sub_imported_eq_trans _ _ _ Hxs
        (sub_imported_eq_trans _ _ _ Hxy
          (sub_imported_eq_sym _ _ Hys)).
    have Hdecoded : Logic.eq
        (nd_nat_list_to_rocq (nd_nat_list_to_imported xsR))
        (nd_nat_list_to_rocq (nd_nat_list_to_imported ysR)) :=
      f_equal nd_nat_list_to_rocq
        (imported_eq_to_coq_eq _ _ Hmap).
    rewrite (nd_nat_list_source_roundtrip xsR) in Hdecoded.
    rewrite (nd_nat_list_source_roundtrip ysR) in Hdecoded.
    exact Hdecoded.
Qed.

Lemma nd_list1_eq_correspondence (T : eqType)
    (xsR ysR : seq T)
    (xsL ysL : ImportedNondecreasing.List_inst1 T) :
  NdList1Rel xsR xsL -> NdList1Rel ysR ysL ->
  PropSPropRel (Logic.eq xsR ysR) (Lean.eq xsL ysL).
Proof.
  intros Hxs Hys. apply prop_sprop_rel_intro.
  - intro Hxy. subst ysR.
    exact (sub_imported_eq_trans _ _ _
      (sub_imported_eq_sym _ _ Hxs) Hys).
  - intro Hxy. apply strictly_inhabits.
    have Hmap : Lean.eq (nd_list1_to_imported xsR)
        (nd_list1_to_imported ysR) :=
      sub_imported_eq_trans _ _ _ Hxs
        (sub_imported_eq_trans _ _ _ Hxy
          (sub_imported_eq_sym _ _ Hys)).
    have Hdecoded : Logic.eq
        (nd_list1_to_rocq (nd_list1_to_imported xsR))
        (nd_list1_to_rocq (nd_list1_to_imported ysR)) :=
      f_equal nd_list1_to_rocq
        (imported_eq_to_coq_eq _ _ Hmap).
    rewrite (nd_list1_source_roundtrip xsR) in Hdecoded.
    rewrite (nd_list1_source_roundtrip ysR) in Hdecoded.
    exact Hdecoded.
Qed.

Lemma nd_or_correspondence (P Q : Prop) (PL QL : SProp) :
  PropSPropRel P PL -> PropSPropRel Q QL ->
  PropSPropRel (P \/ Q) (Lean.Or PL QL).
Proof.
  intros HP HQ. apply prop_sprop_rel_intro.
  - intros [p | q].
    + exact (Lean.Or_inl PL QL (prop_to_sprop _ _ HP p)).
    + exact (Lean.Or_inr PL QL (prop_to_sprop _ _ HQ q)).
  - intros [p | q]; apply strictly_inhabits.
    + left. exact (sprop_to_prop _ _ HP p).
    + right. exact (sprop_to_prop _ _ HQ q).
Qed.

Lemma nd_and_correspondence (P Q : Prop) (PL QL : SProp) :
  PropSPropRel P PL -> PropSPropRel Q QL ->
  PropSPropRel (P /\ Q) (Lean.And PL QL).
Proof.
  intros HP HQ. apply prop_sprop_rel_intro.
  - intros [p q]. exact (Lean.And_intro PL QL
      (prop_to_sprop _ _ HP p) (prop_to_sprop _ _ HQ q)).
  - intros [p q]. apply strictly_inhabits. split.
    + exact (sprop_to_prop _ _ HP p).
    + exact (sprop_to_prop _ _ HQ q).
Qed.

Lemma nd_bool_and_intro (a b : bool) :
  is_true a -> is_true b -> is_true (a && b).
Proof.
  destruct a, b; cbn.
  - intros _ _. exact (Logic.eq_refl true).
  - intros _ Hb. exact Hb.
  - intros Ha _. exact Ha.
  - intros Ha _. exact Ha.
Qed.

Lemma nd_bool_and_left (a b : bool) : is_true (a && b) -> is_true a.
Proof.
  destruct a, b; cbn.
  - intros _. exact (Logic.eq_refl true).
  - intros _. exact (Logic.eq_refl true).
  - intro H. exact H.
  - intro H. exact H.
Qed.

Lemma nd_bool_and_right (a b : bool) : is_true (a && b) -> is_true b.
Proof.
  destruct a, b; cbn.
  - intros _. exact (Logic.eq_refl true).
  - intro H. exact H.
  - intros _. exact (Logic.eq_refl true).
  - intro H. exact H.
Qed.

Lemma nd_bool_and_correspondence (a b : bool) (PL QL : SProp) :
  PropSPropRel (is_true a) PL -> PropSPropRel (is_true b) QL ->
  PropSPropRel (is_true (a && b)) (Lean.And PL QL).
Proof.
  intros HP HQ. apply prop_sprop_rel_intro.
  - intro H. exact (Lean.And_intro PL QL
      (prop_to_sprop _ _ HP (nd_bool_and_left a b H))
      (prop_to_sprop _ _ HQ (nd_bool_and_right a b H))).
  - exact (fun H =>
      match H with
      | Lean.And_intro Ha Hb =>
          strictly_inhabits
            (nd_bool_and_intro a b
              (sprop_to_prop _ _ HP Ha) (sprop_to_prop _ _ HQ Hb))
      end).
Qed.

Lemma nd_exists_nat_correspondence
    (PR : nat -> Prop) (PL : Lean.Nat -> SProp) :
  (forall nR nL, SubNatRel nR nL -> PropSPropRel (PR nR) (PL nL)) ->
  PropSPropRel (exists nR, PR nR)
    (ImportedNondecreasing.Exists Lean.Nat PL).
Proof.
  intro HP. apply prop_sprop_rel_intro.
  - intros [nR Hn]. exact (ImportedNondecreasing.Exists_intro Lean.Nat PL
      (sub_nat_to_imported nR)
      (prop_to_sprop _ _
        (HP nR (sub_nat_to_imported nR) (sub_nat_rel_canonical nR)) Hn)).
  - intros [nL Hn]. apply strictly_inhabits.
    exists (sub_nat_to_rocq nL).
    exact (sprop_to_prop _ _
      (HP (sub_nat_to_rocq nL) nL (sub_nat_rel_surjective nL)) Hn).
Qed.

Definition nd_target_false_to_strict
    (H : ImportedNondecreasing.False) : StrictlyInhabited Logic.False :=
  match H return StrictlyInhabited Logic.False with end.

Lemma nd_false_correspondence :
  PropSPropRel Logic.False ImportedNondecreasing.False.
Proof.
  apply prop_sprop_rel_intro.
  - exact nd_coq_false_to_target.
  - exact nd_target_false_to_strict.
Qed.

Lemma nd_not_correspondence (P : Prop) (PL : SProp) :
  PropSPropRel P PL ->
  PropSPropRel (Logic.not P) (ImportedNondecreasing.Not PL).
Proof.
  intro HP. apply prop_sprop_rel_intro.
  - intros Hnot pL. apply nd_coq_false_to_target. apply Hnot.
    exact (sprop_to_prop _ _ HP pL).
  - intro Hnot. apply strictly_inhabits. intro p.
    exact (sprop_to_prop _ _ nd_false_correspondence
      (Hnot (prop_to_sprop _ _ HP p))).
Qed.

Lemma nd_nat_nonmembership_correspondence xR xL xsR xsL :
  SubNatRel xR xL -> NdNatListRel xsR xsL ->
  PropSPropRel (xR \notin xsR)
    (ImportedNondecreasing.Not (nd_target_nat_mem xL xsL)).
Proof.
  intros Hx Hxs. apply prop_sprop_rel_intro.
  - move=> /negP Hnot HmemL. apply nd_coq_false_to_target. apply Hnot.
    exact (sprop_to_prop _ _
      (nd_nat_membership_correspondence _ _ _ _ Hx Hxs) HmemL).
  - intro Hnot. apply strictly_inhabits. apply/negP. intro HmemR.
    exact (sprop_to_prop _ _ nd_false_correspondence
      (Hnot (prop_to_sprop _ _
        (nd_nat_membership_correspondence _ _ _ _ Hx Hxs) HmemR))).
Qed.

Lemma nd_nat_eq_correspondence aR aL bR bL :
  SubNatRel aR aL -> SubNatRel bR bL ->
  PropSPropRel (Logic.eq aR bR) (Lean.eq aL bL).
Proof. exact (sub_nat_eq_correspondence aR aL bR bL). Qed.

Definition nd_target_add (a b : Lean.Nat) : Lean.Nat :=
  ImportedNondecreasing.HAdd_hAdd_inst7 Lean.Nat Lean.Nat Lean.Nat
    (ImportedNondecreasing.instHAdd_inst1 Lean.Nat
      ImportedNondecreasing.instAddNat) a b.

Definition nd_target_one : Lean.Nat := Lean.Nat_succ Lean.Nat_zero.
Definition nd_target_two : Lean.Nat := Lean.Nat_succ nd_target_one.

Lemma nd_target_add_correspondence aR aL bR bL :
  SubNatRel aR aL -> SubNatRel bR bL ->
  SubNatRel (aR + bR) (nd_target_add aL bL).
Proof. exact (sub_add_correspondence aR aL bR bL). Qed.

Lemma nd_succ_correspondence nR nL :
  SubNatRel nR nL ->
  SubNatRel nR.+1 (nd_target_add nL nd_target_one).
Proof.
  intro Hn. rewrite -addn1.
  exact (nd_target_add_correspondence _ _ _ _ Hn
    (sub_nat_rel_canonical 1)).
Qed.

Lemma nd_pred2_is_sub2 (n : nat) : Logic.eq n.-2 (n - 2).
Proof. exact (Logic.eq_sym (subn2 n)). Qed.

Lemma nd_pred2_correspondence nR nL :
  SubNatRel nR nL ->
  SubNatRel nR.-2 (nd_target_hsub nL nd_target_two).
Proof.
  intro Hn. rewrite nd_pred2_is_sub2.
  exact (nd_target_hsub_correspondence _ _ 2 nd_target_two Hn
    (sub_nat_rel_canonical 2)).
Qed.

Lemma nd_nontrivial_length_correspondence xsR xsL :
  NdNatListRel xsR xsL ->
  PropSPropRel (is_true (ltn (S O) (size xsR)))
    (nd_target_le nd_target_two (nd_target_length xsL)).
Proof.
  intro Hxs.
  change (PropSPropRel (is_true (leq (S (S O)) (size xsR)))
    (nd_target_le nd_target_two (nd_target_length xsL))).
  exact (nd_le_correspondence _ _ _ _
    (sub_nat_rel_canonical (S (S O)))
    (nd_length_related xsR xsL Hxs)).
Qed.

Lemma nd_positive_length_correspondence xsR xsL :
  NdNatListRel xsR xsL ->
  PropSPropRel (is_true (ltn O (size xsR)))
    (nd_target_le nd_target_one (nd_target_length xsL)).
Proof.
  intro Hxs. change (PropSPropRel (is_true (leq 1 (size xsR)))
    (nd_target_le nd_target_one (nd_target_length xsL))).
  exact (nd_le_correspondence _ _ _ _
    (sub_nat_rel_canonical 1) (nd_length_related _ _ Hxs)).
Qed.

(** [iota_is_increasing_sequence]: arbitrary Boolean predicates are related
    bidirectionally, then the already-certified interval and filter operations
    feed the certified [increasing_sequence] definition. *)
Definition nd_target_iota_is_increasing_sequence : SProp :=
  forall (a b : Lean.Nat) (P : Lean.Nat -> ImportedNondecreasing.Bool),
    ImportedNondecreasing.Prosa_Util_Nondecreasing_increasing_sequence
      (nd_target_filter P (nd_target_index_iota a b)).

Theorem iota_is_increasing_sequence_correspondence_certificate :
  PropSPropRel
    GeneratedNondecreasingSource.statement_iota_is_increasing_sequence
    nd_target_iota_is_increasing_sequence.
Proof.
  apply prop_sprop_rel_intro.
  - intros HR aL bL PL.
    set aR := sub_nat_to_rocq aL.
    set bR := sub_nat_to_rocq bL.
    set PR := nd_nat_pred_from_imported PL.
    have Ha : SubNatRel aR aL := sub_nat_rel_surjective aL.
    have Hb : SubNatRel bR bL := sub_nat_rel_surjective bL.
    have HP : NdNatPredRel PR PL := nd_nat_pred_rel_surjective PL.
    have Hidx := nd_index_iota_related aR aL bR bL Ha Hb.
    have Hfilter := nd_filter_related PR PL _ _ HP Hidx.
    exact (prop_to_sprop _ _
      (increasing_sequence_definition_certificate _ _ Hfilter)
      (HR aR bR PR)).
  - intro HL. apply strictly_inhabits. intros aR bR PR.
    have Ha := sub_nat_rel_canonical aR.
    have Hb := sub_nat_rel_canonical bR.
    have HP := nd_nat_pred_rel_canonical PR.
    have Hidx := nd_index_iota_related aR (sub_nat_to_imported aR)
      bR (sub_nat_to_imported bR) Ha Hb.
    have Hfilter := nd_filter_related PR (nd_nat_pred_to_imported PR)
      _ _ HP Hidx.
    exact (sprop_to_prop _ _
      (increasing_sequence_definition_certificate _ _ Hfilter)
      (HL (sub_nat_to_imported aR) (sub_nat_to_imported bR)
        (nd_nat_pred_to_imported PR))).
Qed.

Definition nd_target_distances_of_iota_epsilon : SProp :=
  forall (n x : Lean.Nat),
    nd_target_nat_mem x
      (ImportedNondecreasing.Prosa_Util_Nondecreasing_distances
        (nd_target_index_iota Lean.Nat_zero n)) ->
    Lean.eq x nd_op_target_one.

Theorem distances_of_iota_epsilon_correspondence_certificate :
  PropSPropRel GeneratedNondecreasingSource.statement_distances_of_iota_ε
    nd_target_distances_of_iota_epsilon.
Proof.
  apply prop_sprop_rel_intro.
  - intros HR nL xL HmemL.
    set nR := sub_nat_to_rocq nL.
    set xR := sub_nat_to_rocq xL.
    have Hn : SubNatRel nR nL := sub_nat_rel_surjective nL.
    have Hx : SubNatRel xR xL := sub_nat_rel_surjective xL.
    have Hzero := sub_nat_rel_canonical 0.
    have Hidx := nd_index_iota_related 0 Lean.Nat_zero nR nL Hzero Hn.
    have Hdist := distances_definition_certificate _ _ Hidx.
    have Hmem := nd_nat_membership_correspondence xR xL _ _ Hx Hdist.
    apply (prop_to_sprop _ _
      (nd_nat_eq_correspondence _ _ 1 nd_op_target_one Hx
        (sub_nat_rel_canonical 1))).
    exact (HR nR xR (sprop_to_prop _ _ Hmem HmemL)).
  - intro HL. apply strictly_inhabits. intros nR xR HmemR.
    have Hn := sub_nat_rel_canonical nR.
    have Hx := sub_nat_rel_canonical xR.
    have Hzero := sub_nat_rel_canonical 0.
    have Hidx := nd_index_iota_related 0 Lean.Nat_zero nR
      (sub_nat_to_imported nR) Hzero Hn.
    have Hdist := distances_definition_certificate _ _ Hidx.
    have Hmem := nd_nat_membership_correspondence xR
      (sub_nat_to_imported xR) _ _ Hx Hdist.
    exact (sprop_to_prop _ _
      (nd_nat_eq_correspondence _ _ 1 nd_op_target_one Hx
        (sub_nat_rel_canonical 1))
      (HL (sub_nat_to_imported nR) (sub_nat_to_imported xR)
        (prop_to_sprop _ _ Hmem HmemR))).
Qed.

Definition nd_target_distances_iota_filtered : SProp :=
  forall (xs : ImportedNondecreasing.List_inst1 Lean.Nat) (k : Lean.Nat),
    (forall x : Lean.Nat,
      nd_target_nat_mem x xs -> nd_target_le x k) ->
    ImportedNondecreasing.Prosa_Util_Nondecreasing_nondecreasing_sequence xs ->
    Lean.eq
      (ImportedNondecreasing.Prosa_Util_Nondecreasing_distances
        (nd_target_filter (fun x => nd_target_decide_mem x xs)
          (nd_target_index_iota Lean.Nat_zero
            (nd_op_target_add k nd_op_target_one))))
      (nd_target_filter nd_target_positive
        (ImportedNondecreasing.Prosa_Util_Nondecreasing_distances xs)).

Theorem distances_iota_filtered_correspondence_certificate :
  PropSPropRel GeneratedNondecreasingSource.statement_distances_iota_filtered
    nd_target_distances_iota_filtered.
Proof.
  apply prop_sprop_rel_intro.
  - intros HR xsL kL HboundL HndL.
    set xsR := nd_nat_list_to_rocq xsL.
    set kR := sub_nat_to_rocq kL.
    have Hxs : NdNatListRel xsR xsL := nd_nat_list_target_roundtrip xsL.
    have Hk : SubNatRel kR kL := sub_nat_rel_surjective kL.
    have HboundR : forall xR : nat, xR \in xsR -> is_true (leq xR kR).
    { intros xR HmemR. have Hx := sub_nat_rel_canonical xR.
      exact (sprop_to_prop _ _ (nd_le_correspondence _ _ _ _ Hx Hk)
        (HboundL (sub_nat_to_imported xR)
          (prop_to_sprop _ _
            (nd_nat_membership_correspondence _ _ _ _ Hx Hxs) HmemR))). }
    have HndR := sprop_to_prop _ _
      (nondecreasing_sequence_definition_certificate _ _ Hxs) HndL.
    have Hsource := HR xsR kR HboundR HndR.
    have Hk1 := nd_op_succ_correspondence kR kL Hk.
    have Hidx := nd_index_iota_related O Lean.Nat_zero kR.+1
      (nd_op_target_add kL nd_op_target_one)
      (sub_nat_rel_canonical O) Hk1.
    have HleftFilter := nd_filter_related
      (fun x => x \in xsR) (fun x => nd_target_decide_mem x xsL)
      _ _ (fun xR xL Hx => nd_decide_mem_related _ _ _ _ Hx Hxs) Hidx.
    have Hleft := distances_definition_certificate _ _ HleftFilter.
    have Hdist := distances_definition_certificate _ _ Hxs.
    have Hright := nd_filter_related (fun x => ltn O x)
      nd_target_positive _ _ nd_positive_pred_related Hdist.
    exact (prop_to_sprop _ _
      (nd_list_eq_correspondence _ _ _ _ Hleft Hright) Hsource).
  - intro HL. apply strictly_inhabits. intros xsR kR HboundR HndR.
    have Hxs : NdNatListRel xsR (nd_nat_list_to_imported xsR) :=
      @Lean.eq_refl _ _.
    have Hk := sub_nat_rel_canonical kR.
    have HndL := prop_to_sprop _ _
      (nondecreasing_sequence_definition_certificate _ _ Hxs) HndR.
    have Htarget := HL (nd_nat_list_to_imported xsR)
      (sub_nat_to_imported kR)
      (fun xL HmemL =>
        let xR := sub_nat_to_rocq xL in
        let Hx : SubNatRel xR xL := sub_nat_rel_surjective xL in
        prop_to_sprop _ _ (nd_le_correspondence _ _ _ _ Hx Hk)
          (HboundR xR (sprop_to_prop _ _
            (nd_nat_membership_correspondence _ _ _ _ Hx Hxs) HmemL)))
      HndL.
    have Hk1 := nd_op_succ_correspondence kR _ Hk.
    have Hidx := nd_index_iota_related O Lean.Nat_zero kR.+1
      (nd_op_target_add (sub_nat_to_imported kR) nd_op_target_one)
      (sub_nat_rel_canonical O) Hk1.
    have HleftFilter := nd_filter_related
      (fun x => x \in xsR)
      (fun x => nd_target_decide_mem x (nd_nat_list_to_imported xsR))
      _ _ (fun xR xL Hx => nd_decide_mem_related _ _ _ _ Hx Hxs) Hidx.
    have Hleft := distances_definition_certificate _ _ HleftFilter.
    have Hdist := distances_definition_certificate _ _ Hxs.
    have Hright := nd_filter_related (fun x => ltn O x)
      nd_target_positive _ _ nd_positive_pred_related Hdist.
    exact (sprop_to_prop _ _
      (nd_list_eq_correspondence _ _ _ _ Hleft Hright) Htarget).
Qed.

Definition nd_target_increasing_implies_nondecreasing : SProp :=
  forall xs : ImportedNondecreasing.List_inst1 Lean.Nat,
    ImportedNondecreasing.Prosa_Util_Nondecreasing_increasing_sequence xs ->
    ImportedNondecreasing.Prosa_Util_Nondecreasing_nondecreasing_sequence xs.

Theorem increasing_implies_nondecreasing_correspondence_certificate :
  PropSPropRel
    GeneratedNondecreasingSource.statement_increasing_implies_nondecreasing
    nd_target_increasing_implies_nondecreasing.
Proof.
  apply prop_sprop_rel_intro.
  - intros HR xsL HincL.
    set xsR := nd_nat_list_to_rocq xsL.
    have Hxs : NdNatListRel xsR xsL := nd_nat_list_target_roundtrip xsL.
    exact (prop_to_sprop _ _
      (nondecreasing_sequence_definition_certificate xsR xsL Hxs)
      (HR xsR (sprop_to_prop _ _
        (increasing_sequence_definition_certificate xsR xsL Hxs) HincL))).
  - intro HL. apply strictly_inhabits. intros xsR HincR.
    have Hxs : NdNatListRel xsR (nd_nat_list_to_imported xsR) :=
      @Lean.eq_refl _ _.
    exact (sprop_to_prop _ _
      (nondecreasing_sequence_definition_certificate _ _ Hxs)
      (HL (nd_nat_list_to_imported xsR)
        (prop_to_sprop _ _
          (increasing_sequence_definition_certificate _ _ Hxs) HincR))).
Qed.

Definition nd_target_nondecreasing_sequence_cons : SProp :=
  forall (x : Lean.Nat) (xs : ImportedNondecreasing.List_inst1 Lean.Nat),
    ImportedNondecreasing.Prosa_Util_Nondecreasing_nondecreasing_sequence
      (ImportedNondecreasing.List_cons_inst1 Lean.Nat x xs) ->
    ImportedNondecreasing.Prosa_Util_Nondecreasing_nondecreasing_sequence xs.

Theorem nondecreasing_sequence_cons_correspondence_certificate :
  PropSPropRel GeneratedNondecreasingSource.statement_nondecreasing_sequence_cons
    nd_target_nondecreasing_sequence_cons.
Proof.
  apply prop_sprop_rel_intro.
  - intros HR xL xsL HconsL.
    set xR := sub_nat_to_rocq xL.
    set xsR := nd_nat_list_to_rocq xsL.
    have Hx : SubNatRel xR xL := sub_nat_rel_surjective xL.
    have Hxs : NdNatListRel xsR xsL := nd_nat_list_target_roundtrip xsL.
    have Hcons := nd_cons_related xR xL xsR xsL Hx Hxs.
    exact (prop_to_sprop _ _
      (nondecreasing_sequence_definition_certificate xsR xsL Hxs)
      (HR xR xsR (sprop_to_prop _ _
        (nondecreasing_sequence_definition_certificate _ _ Hcons) HconsL))).
  - intro HL. apply strictly_inhabits. intros xR xsR HconsR.
    have Hx := sub_nat_rel_canonical xR.
    have Hxs : NdNatListRel xsR (nd_nat_list_to_imported xsR) :=
      @Lean.eq_refl _ _.
    have Hcons := nd_cons_related _ _ _ _ Hx Hxs.
    exact (sprop_to_prop _ _
      (nondecreasing_sequence_definition_certificate xsR _ Hxs)
      (HL (sub_nat_to_imported xR) (nd_nat_list_to_imported xsR)
        (prop_to_sprop _ _
          (nondecreasing_sequence_definition_certificate _ _ Hcons) HconsR))).
Qed.

Definition nd_target_nondec_seq_zero_first : SProp :=
  forall xs : ImportedNondecreasing.List_inst1 Lean.Nat,
    nd_target_nat_mem Lean.Nat_zero xs ->
    ImportedNondecreasing.Prosa_Util_Nondecreasing_nondecreasing_sequence xs ->
    Lean.eq (nd_target_first0 xs) Lean.Nat_zero.

Theorem nondec_seq_zero_first_correspondence_certificate :
  PropSPropRel GeneratedNondecreasingSource.statement_nondec_seq_zero_first
    nd_target_nondec_seq_zero_first.
Proof.
  apply prop_sprop_rel_intro.
  - intros HR xsL HmemL HndL.
    set xsR := nd_nat_list_to_rocq xsL.
    have Hxs : NdNatListRel xsR xsL := nd_nat_list_target_roundtrip xsL.
    apply (prop_to_sprop _ _
      (nd_nat_eq_correspondence _ _ O Lean.Nat_zero
        (nd_first0_related _ _ Hxs) (sub_nat_rel_canonical O))).
    apply (HR xsR).
    + exact (sprop_to_prop _ _
        (nd_nat_membership_correspondence O Lean.Nat_zero _ _
          (sub_nat_rel_canonical O) Hxs) HmemL).
    + exact (sprop_to_prop _ _
        (nondecreasing_sequence_definition_certificate _ _ Hxs) HndL).
  - intro HL. apply strictly_inhabits. intros xsR HmemR HndR.
    have Hxs : NdNatListRel xsR (nd_nat_list_to_imported xsR) :=
      @Lean.eq_refl _ _.
    exact (sprop_to_prop _ _
      (nd_nat_eq_correspondence _ _ O Lean.Nat_zero
        (nd_first0_related _ _ Hxs) (sub_nat_rel_canonical O))
      (HL (nd_nat_list_to_imported xsR)
        (prop_to_sprop _ _
          (nd_nat_membership_correspondence O Lean.Nat_zero _ _
            (sub_nat_rel_canonical O) Hxs) HmemR)
        (prop_to_sprop _ _
          (nondecreasing_sequence_definition_certificate _ _ Hxs) HndR))).
Qed.

Definition nd_target_nondecreasing_sequence_2cons_leVeq : SProp :=
  forall (x1 x2 : Lean.Nat)
      (xs : ImportedNondecreasing.List_inst1 Lean.Nat),
    ImportedNondecreasing.Prosa_Util_Nondecreasing_nondecreasing_sequence
      (ImportedNondecreasing.List_cons_inst1 Lean.Nat x1
        (ImportedNondecreasing.List_cons_inst1 Lean.Nat x2 xs)) ->
    Lean.Or (Lean.eq x1 x2) (nd_target_lt x1 x2).

Theorem nondecreasing_sequence_2cons_leVeq_correspondence_certificate :
  PropSPropRel
    GeneratedNondecreasingSource.statement_nondecreasing_sequence_2cons_leVeq
    nd_target_nondecreasing_sequence_2cons_leVeq.
Proof.
  apply prop_sprop_rel_intro.
  - intros HR x1L x2L xsL HndL.
    set x1R := sub_nat_to_rocq x1L.
    set x2R := sub_nat_to_rocq x2L.
    set xsR := nd_nat_list_to_rocq xsL.
    have Hx1 : SubNatRel x1R x1L := sub_nat_rel_surjective x1L.
    have Hx2 : SubNatRel x2R x2L := sub_nat_rel_surjective x2L.
    have Hxs : NdNatListRel xsR xsL := nd_nat_list_target_roundtrip xsL.
    have Htail := nd_cons_related x2R x2L xsR xsL Hx2 Hxs.
    have Hfull := nd_cons_related x1R x1L _ _ Hx1 Htail.
    exact (prop_to_sprop _ _
      (nd_or_correspondence _ _ _ _
        (nd_nat_eq_correspondence _ _ _ _ Hx1 Hx2)
        (nd_lt_correspondence _ _ _ _ Hx1 Hx2))
      (HR x1R x2R xsR (sprop_to_prop _ _
        (nondecreasing_sequence_definition_certificate _ _ Hfull) HndL))).
  - intro HL. apply strictly_inhabits. intros x1R x2R xsR HndR.
    have Hx1 := sub_nat_rel_canonical x1R.
    have Hx2 := sub_nat_rel_canonical x2R.
    have Hxs : NdNatListRel xsR (nd_nat_list_to_imported xsR) :=
      @Lean.eq_refl _ _.
    have Htail := nd_cons_related x2R _ xsR _ Hx2 Hxs.
    have Hfull := nd_cons_related x1R _ _ _ Hx1 Htail.
    exact (sprop_to_prop _ _
      (nd_or_correspondence _ _ _ _
        (nd_nat_eq_correspondence _ _ _ _ Hx1 Hx2)
        (nd_lt_correspondence _ _ _ _ Hx1 Hx2))
      (HL (sub_nat_to_imported x1R) (sub_nat_to_imported x2R)
        (nd_nat_list_to_imported xsR)
        (prop_to_sprop _ _
          (nondecreasing_sequence_definition_certificate _ _ Hfull) HndR))).
Qed.

Definition nd_target_nondecreasing_sequence_cons_double : SProp :=
  forall (x : Lean.Nat) (xs : ImportedNondecreasing.List_inst1 Lean.Nat),
    ImportedNondecreasing.Prosa_Util_Nondecreasing_nondecreasing_sequence
      (ImportedNondecreasing.List_cons_inst1 Lean.Nat x xs) ->
    ImportedNondecreasing.Prosa_Util_Nondecreasing_nondecreasing_sequence
      (ImportedNondecreasing.List_cons_inst1 Lean.Nat x
        (ImportedNondecreasing.List_cons_inst1 Lean.Nat x xs)).

Theorem nondecreasing_sequence_cons_double_correspondence_certificate :
  PropSPropRel
    GeneratedNondecreasingSource.statement_nondecreasing_sequence_cons_double
    nd_target_nondecreasing_sequence_cons_double.
Proof.
  apply prop_sprop_rel_intro.
  - intros HR xL xsL HsingleL.
    set xR := sub_nat_to_rocq xL.
    set xsR := nd_nat_list_to_rocq xsL.
    have Hx : SubNatRel xR xL := sub_nat_rel_surjective xL.
    have Hxs : NdNatListRel xsR xsL := nd_nat_list_target_roundtrip xsL.
    have Hsingle := nd_cons_related xR xL xsR xsL Hx Hxs.
    have Hdouble := nd_cons_related xR xL _ _ Hx Hsingle.
    exact (prop_to_sprop _ _
      (nondecreasing_sequence_definition_certificate _ _ Hdouble)
      (HR xR xsR (sprop_to_prop _ _
        (nondecreasing_sequence_definition_certificate _ _ Hsingle)
        HsingleL))).
  - intro HL. apply strictly_inhabits. intros xR xsR HsingleR.
    have Hx := sub_nat_rel_canonical xR.
    have Hxs : NdNatListRel xsR (nd_nat_list_to_imported xsR) :=
      @Lean.eq_refl _ _.
    have Hsingle := nd_cons_related xR _ xsR _ Hx Hxs.
    have Hdouble := nd_cons_related xR _ _ _ Hx Hsingle.
    exact (sprop_to_prop _ _
      (nondecreasing_sequence_definition_certificate _ _ Hdouble)
      (HL (sub_nat_to_imported xR) (nd_nat_list_to_imported xsR)
        (prop_to_sprop _ _
          (nondecreasing_sequence_definition_certificate _ _ Hsingle)
          HsingleR))).
Qed.

Definition nd_target_nondecreasing_sequence_add_min : SProp :=
  forall (x : Lean.Nat) (xs : ImportedNondecreasing.List_inst1 Lean.Nat),
    (forall y : Lean.Nat, nd_target_nat_mem y xs -> nd_target_le x y) ->
    ImportedNondecreasing.Prosa_Util_Nondecreasing_nondecreasing_sequence xs ->
    ImportedNondecreasing.Prosa_Util_Nondecreasing_nondecreasing_sequence
      (ImportedNondecreasing.List_cons_inst1 Lean.Nat x xs).

Theorem nondecreasing_sequence_add_min_correspondence_certificate :
  PropSPropRel
    GeneratedNondecreasingSource.statement_nondecreasing_sequence_add_min
    nd_target_nondecreasing_sequence_add_min.
Proof.
  apply prop_sprop_rel_intro.
  - intros HR xL xsL HminL HndL.
    set xR := sub_nat_to_rocq xL.
    set xsR := nd_nat_list_to_rocq xsL.
    have Hx : SubNatRel xR xL := sub_nat_rel_surjective xL.
    have Hxs : NdNatListRel xsR xsL := nd_nat_list_target_roundtrip xsL.
    have Hcons := nd_cons_related xR xL xsR xsL Hx Hxs.
    apply (prop_to_sprop _ _
      (nondecreasing_sequence_definition_certificate _ _ Hcons)).
    apply (HR xR xsR).
    + intros yR HyR.
      have Hy := sub_nat_rel_canonical yR.
      exact (sprop_to_prop _ _ (nd_le_correspondence _ _ _ _ Hx Hy)
        (HminL (sub_nat_to_imported yR)
          (prop_to_sprop _ _
            (nd_nat_membership_correspondence _ _ _ _ Hy Hxs) HyR))).
    + exact (sprop_to_prop _ _
        (nondecreasing_sequence_definition_certificate _ _ Hxs) HndL).
  - intro HL. apply strictly_inhabits. intros xR xsR HminR HndR.
    have Hx := sub_nat_rel_canonical xR.
    have Hxs : NdNatListRel xsR (nd_nat_list_to_imported xsR) :=
      @Lean.eq_refl _ _.
    have Hcons := nd_cons_related xR _ xsR _ Hx Hxs.
    apply (sprop_to_prop _ _
      (nondecreasing_sequence_definition_certificate _ _ Hcons)).
    apply HL.
    + intros yL HyL.
      set yR := sub_nat_to_rocq yL.
      have Hy : SubNatRel yR yL := sub_nat_rel_surjective yL.
      exact (prop_to_sprop _ _ (nd_le_correspondence _ _ _ _ Hx Hy)
        (HminR yR (sprop_to_prop _ _
          (nd_nat_membership_correspondence _ _ _ _ Hy Hxs) HyL))).
    + exact (prop_to_sprop _ _
        (nondecreasing_sequence_definition_certificate _ _ Hxs) HndR).
Qed.

Definition nd_target_nondecreasing_sequence_cons_min : SProp :=
  forall (x : Lean.Nat) (xs : ImportedNondecreasing.List_inst1 Lean.Nat),
    ImportedNondecreasing.Prosa_Util_Nondecreasing_nondecreasing_sequence
      (ImportedNondecreasing.List_cons_inst1 Lean.Nat x xs) ->
    forall y : Lean.Nat, nd_target_nat_mem y xs -> nd_target_le x y.

Theorem nondecreasing_sequence_cons_min_correspondence_certificate :
  PropSPropRel
    GeneratedNondecreasingSource.statement_nondecreasing_sequence_cons_min
    nd_target_nondecreasing_sequence_cons_min.
Proof.
  apply prop_sprop_rel_intro.
  - intros HR xL xsL HndL yL HyL.
    set xR := sub_nat_to_rocq xL.
    set yR := sub_nat_to_rocq yL.
    set xsR := nd_nat_list_to_rocq xsL.
    have Hx : SubNatRel xR xL := sub_nat_rel_surjective xL.
    have Hy : SubNatRel yR yL := sub_nat_rel_surjective yL.
    have Hxs : NdNatListRel xsR xsL := nd_nat_list_target_roundtrip xsL.
    have Hcons := nd_cons_related xR xL xsR xsL Hx Hxs.
    apply (prop_to_sprop _ _ (nd_le_correspondence _ _ _ _ Hx Hy)).
    apply (HR xR xsR).
    + exact (sprop_to_prop _ _
        (nondecreasing_sequence_definition_certificate _ _ Hcons) HndL).
    + exact (sprop_to_prop _ _
        (nd_nat_membership_correspondence _ _ _ _ Hy Hxs) HyL).
  - intro HL. apply strictly_inhabits. intros xR xsR HndR yR HyR.
    have Hx := sub_nat_rel_canonical xR.
    have Hy := sub_nat_rel_canonical yR.
    have Hxs : NdNatListRel xsR (nd_nat_list_to_imported xsR) :=
      @Lean.eq_refl _ _.
    have Hcons := nd_cons_related xR _ xsR _ Hx Hxs.
    exact (sprop_to_prop _ _ (nd_le_correspondence _ _ _ _ Hx Hy)
      (HL (sub_nat_to_imported xR) (nd_nat_list_to_imported xsR)
        (prop_to_sprop _ _
          (nondecreasing_sequence_definition_certificate _ _ Hcons) HndR)
        (sub_nat_to_imported yR)
        (prop_to_sprop _ _
          (nd_nat_membership_correspondence _ _ _ _ Hy Hxs) HyR))).
Qed.

Definition nd_target_nondecreasing_sequence_cons_smin : SProp :=
  forall (x1 x2 : Lean.Nat)
      (xs : ImportedNondecreasing.List_inst1 Lean.Nat),
    nd_target_lt x1 x2 ->
    ImportedNondecreasing.Prosa_Util_Nondecreasing_nondecreasing_sequence
      (ImportedNondecreasing.List_cons_inst1 Lean.Nat x1
        (ImportedNondecreasing.List_cons_inst1 Lean.Nat x2 xs)) ->
    forall y : Lean.Nat,
      nd_target_nat_mem y
        (ImportedNondecreasing.List_cons_inst1 Lean.Nat x2 xs) ->
      nd_target_lt x1 y.

Theorem nondecreasing_sequence_cons_smin_correspondence_certificate :
  PropSPropRel
    GeneratedNondecreasingSource.statement_nondecreasing_sequence_cons_smin
    nd_target_nondecreasing_sequence_cons_smin.
Proof.
  apply prop_sprop_rel_intro.
  - intros HR x1L x2L xsL HltL HndL yL HyL.
    set x1R := sub_nat_to_rocq x1L.
    set x2R := sub_nat_to_rocq x2L.
    set yR := sub_nat_to_rocq yL.
    set xsR := nd_nat_list_to_rocq xsL.
    have Hx1 : SubNatRel x1R x1L := sub_nat_rel_surjective x1L.
    have Hx2 : SubNatRel x2R x2L := sub_nat_rel_surjective x2L.
    have Hy : SubNatRel yR yL := sub_nat_rel_surjective yL.
    have Hxs : NdNatListRel xsR xsL := nd_nat_list_target_roundtrip xsL.
    have Htail := nd_cons_related x2R x2L xsR xsL Hx2 Hxs.
    have Hfull := nd_cons_related x1R x1L _ _ Hx1 Htail.
    apply (prop_to_sprop _ _ (nd_lt_correspondence _ _ _ _ Hx1 Hy)).
    apply (HR x1R x2R xsR).
    + exact (sprop_to_prop _ _ (nd_lt_correspondence _ _ _ _ Hx1 Hx2) HltL).
    + exact (sprop_to_prop _ _
        (nondecreasing_sequence_definition_certificate _ _ Hfull) HndL).
    + exact (sprop_to_prop _ _
        (nd_nat_membership_correspondence _ _ _ _ Hy Htail) HyL).
  - intro HL. apply strictly_inhabits.
    intros x1R x2R xsR HltR HndR yR HyR.
    have Hx1 := sub_nat_rel_canonical x1R.
    have Hx2 := sub_nat_rel_canonical x2R.
    have Hy := sub_nat_rel_canonical yR.
    have Hxs : NdNatListRel xsR (nd_nat_list_to_imported xsR) :=
      @Lean.eq_refl _ _.
    have Htail := nd_cons_related x2R _ xsR _ Hx2 Hxs.
    have Hfull := nd_cons_related x1R _ _ _ Hx1 Htail.
    exact (sprop_to_prop _ _ (nd_lt_correspondence _ _ _ _ Hx1 Hy)
      (HL (sub_nat_to_imported x1R) (sub_nat_to_imported x2R)
        (nd_nat_list_to_imported xsR)
        (prop_to_sprop _ _ (nd_lt_correspondence _ _ _ _ Hx1 Hx2) HltR)
        (prop_to_sprop _ _
          (nondecreasing_sequence_definition_certificate _ _ Hfull) HndR)
        (sub_nat_to_imported yR)
        (prop_to_sprop _ _
          (nd_nat_membership_correspondence _ _ _ _ Hy Htail) HyR))).
Qed.

Definition nd_target_last_is_max_in_nondecreasing_seq : SProp :=
  forall (xs : ImportedNondecreasing.List_inst1 Lean.Nat) (x : Lean.Nat),
    ImportedNondecreasing.Prosa_Util_Nondecreasing_nondecreasing_sequence xs ->
    nd_target_nat_mem x xs -> nd_target_le x (nd_target_last0 xs).

Theorem last_is_max_in_nondecreasing_seq_correspondence_certificate :
  PropSPropRel
    GeneratedNondecreasingSource.statement_last_is_max_in_nondecreasing_seq
    nd_target_last_is_max_in_nondecreasing_seq.
Proof.
  apply prop_sprop_rel_intro.
  - intros HR xsL xL HndL HmemL.
    set xsR := nd_nat_list_to_rocq xsL.
    set xR := sub_nat_to_rocq xL.
    have Hxs : NdNatListRel xsR xsL := nd_nat_list_target_roundtrip xsL.
    have Hx : SubNatRel xR xL := sub_nat_rel_surjective xL.
    apply (prop_to_sprop _ _
      (nd_le_correspondence _ _ _ _ Hx (nd_last0_related _ _ Hxs))).
    apply HR.
    + exact (sprop_to_prop _ _
        (nondecreasing_sequence_definition_certificate _ _ Hxs) HndL).
    + exact (sprop_to_prop _ _
        (nd_nat_membership_correspondence _ _ _ _ Hx Hxs) HmemL).
  - intro HL. apply strictly_inhabits. intros xsR xR HndR HmemR.
    have Hxs : NdNatListRel xsR (nd_nat_list_to_imported xsR) :=
      @Lean.eq_refl _ _.
    have Hx := sub_nat_rel_canonical xR.
    exact (sprop_to_prop _ _
      (nd_le_correspondence _ _ _ _ Hx (nd_last0_related _ _ Hxs))
      (HL (nd_nat_list_to_imported xsR) (sub_nat_to_imported xR)
        (prop_to_sprop _ _
          (nondecreasing_sequence_definition_certificate _ _ Hxs) HndR)
        (prop_to_sprop _ _
          (nd_nat_membership_correspondence _ _ _ _ Hx Hxs) HmemR))).
Qed.

Definition nd_target_antidensity_of_nondecreasing_seq : SProp :=
  forall (xs : ImportedNondecreasing.List_inst1 Lean.Nat)
      (x n : Lean.Nat),
    ImportedNondecreasing.Prosa_Util_Nondecreasing_nondecreasing_sequence xs ->
    Lean.And (nd_target_lt (nd_target_nthD xs n) x)
      (nd_target_lt x (nd_target_nthD xs (nd_target_add n nd_target_one))) ->
    ImportedNondecreasing.Not (nd_target_nat_mem x xs).

Theorem antidensity_of_nondecreasing_seq_correspondence_certificate :
  PropSPropRel
    GeneratedNondecreasingSource.statement_antidensity_of_nondecreasing_seq
    nd_target_antidensity_of_nondecreasing_seq.
Proof.
  apply prop_sprop_rel_intro.
  - intros HR xsL xL nL HndL HbetweenL.
    set xsR := nd_nat_list_to_rocq xsL.
    set xR := sub_nat_to_rocq xL.
    set nR := sub_nat_to_rocq nL.
    have Hxs : NdNatListRel xsR xsL := nd_nat_list_target_roundtrip xsL.
    have Hx : SubNatRel xR xL := sub_nat_rel_surjective xL.
    have Hn : SubNatRel nR nL := sub_nat_rel_surjective nL.
    have Hsucc := nd_succ_correspondence nR nL Hn.
    have Hleft := nd_lt_correspondence _ _ _ _
      (nd_nthD_related _ _ _ _ Hxs Hn) Hx.
    have Hright := nd_lt_correspondence _ _ _ _ Hx
      (nd_nthD_related _ _ _ _ Hxs Hsucc).
    apply (prop_to_sprop _ _
      (nd_nat_nonmembership_correspondence _ _ _ _ Hx Hxs)).
    apply (HR xsR xR nR).
    + exact (sprop_to_prop _ _
        (nondecreasing_sequence_definition_certificate _ _ Hxs) HndL).
    + destruct HbetweenL as [HleftL HrightL]. apply/andP; split.
      * exact (sprop_to_prop _ _ Hleft HleftL).
      * exact (sprop_to_prop _ _ Hright HrightL).
  - intro HL. apply strictly_inhabits. intros xsR xR nR HndR HbetweenR.
    have Hxs : NdNatListRel xsR (nd_nat_list_to_imported xsR) :=
      @Lean.eq_refl _ _.
    have Hx := sub_nat_rel_canonical xR.
    have Hn := sub_nat_rel_canonical nR.
    have Hsucc := nd_succ_correspondence nR _ Hn.
    have Hleft := nd_lt_correspondence _ _ _ _
      (nd_nthD_related _ _ _ _ Hxs Hn) Hx.
    have Hright := nd_lt_correspondence _ _ _ _ Hx
      (nd_nthD_related _ _ _ _ Hxs Hsucc).
    have HndL := prop_to_sprop _ _
      (nondecreasing_sequence_definition_certificate _ _ Hxs) HndR.
    move: HbetweenR => /andP [HleftR HrightR].
    have HleftL := prop_to_sprop _ _ Hleft HleftR.
    have HrightL := prop_to_sprop _ _ Hright HrightR.
    have HbetweenL : Lean.And
        (nd_target_lt
          (nd_target_nthD (nd_nat_list_to_imported xsR)
            (sub_nat_to_imported nR)) (sub_nat_to_imported xR))
        (nd_target_lt (sub_nat_to_imported xR)
          (nd_target_nthD (nd_nat_list_to_imported xsR)
            (nd_target_add (sub_nat_to_imported nR) nd_target_one))) :=
      Lean.And_intro _ _ HleftL HrightL.
    have HnotL := HL (nd_nat_list_to_imported xsR)
      (sub_nat_to_imported xR) (sub_nat_to_imported nR) HndL HbetweenL.
    exact (sprop_to_prop _ _
      (nd_nat_nonmembership_correspondence _ _ _ _ Hx Hxs) HnotL).
Qed.

Definition nd_target_belonging_to_segment_of_seq_is_total : SProp :=
  forall (xs : ImportedNondecreasing.List_inst1 Lean.Nat) (x : Lean.Nat),
    nd_target_le nd_target_two (nd_target_length xs) ->
    Lean.And (nd_target_le (nd_target_first0 xs) x)
      (nd_target_lt x (nd_target_last0 xs)) ->
    ImportedNondecreasing.Exists Lean.Nat (fun n =>
      Lean.And
        (nd_target_lt (nd_target_add n nd_target_one) (nd_target_length xs))
        (Lean.And (nd_target_le (nd_target_nthD xs n) x)
          (nd_target_lt x
            (nd_target_nthD xs (nd_target_add n nd_target_one))))).

Theorem belonging_to_segment_of_seq_is_total_correspondence_certificate :
  PropSPropRel
    GeneratedNondecreasingSource.statement_belonging_to_segment_of_seq_is_total
    nd_target_belonging_to_segment_of_seq_is_total.
Proof.
  apply prop_sprop_rel_intro.
  - intros HR xsL xL HlenL HboundsL.
    set xsR := nd_nat_list_to_rocq xsL.
    set xR := sub_nat_to_rocq xL.
    have Hxs : NdNatListRel xsR xsL := nd_nat_list_target_roundtrip xsL.
    have Hx : SubNatRel xR xL := sub_nat_rel_surjective xL.
    have Hboundary := nd_bool_and_correspondence _ _ _ _
      (nd_le_correspondence _ _ _ _ (nd_first0_related _ _ Hxs) Hx)
      (nd_lt_correspondence _ _ _ _ Hx (nd_last0_related _ _ Hxs)).
    have Hexists := nd_exists_nat_correspondence
      (fun nR => is_true (ltn nR.+1 (size xsR)) /\
        is_true (leq (nth O xsR nR) xR && ltn xR (nth O xsR nR.+1)))
      (fun nL => Lean.And
        (nd_target_lt (nd_target_add nL nd_target_one)
          (nd_target_length xsL))
        (Lean.And (nd_target_le (nd_target_nthD xsL nL) xL)
          (nd_target_lt xL
            (nd_target_nthD xsL (nd_target_add nL nd_target_one)))))
      (fun nR nL Hn =>
        let Hsucc := nd_succ_correspondence nR nL Hn in
        nd_and_correspondence _ _ _ _
          (nd_lt_correspondence _ _ _ _ Hsucc
            (nd_length_related _ _ Hxs))
          (nd_bool_and_correspondence _ _ _ _
            (nd_le_correspondence _ _ _ _
              (nd_nthD_related _ _ _ _ Hxs Hn) Hx)
            (nd_lt_correspondence _ _ _ _ Hx
              (nd_nthD_related _ _ _ _ Hxs Hsucc)))).
    exact (prop_to_sprop _ _ Hexists
      (HR xsR xR
        (sprop_to_prop _ _
          (nd_nontrivial_length_correspondence _ _ Hxs) HlenL)
        (sprop_to_prop _ _ Hboundary HboundsL))).
  - intro HL. apply strictly_inhabits. intros xsR xR HlenR HboundsR.
    have Hxs : NdNatListRel xsR (nd_nat_list_to_imported xsR) :=
      @Lean.eq_refl _ _.
    have Hx := sub_nat_rel_canonical xR.
    have Hboundary := nd_bool_and_correspondence _ _ _ _
      (nd_le_correspondence _ _ _ _ (nd_first0_related _ _ Hxs) Hx)
      (nd_lt_correspondence _ _ _ _ Hx (nd_last0_related _ _ Hxs)).
    have Hexists := nd_exists_nat_correspondence
      (fun nR => is_true (ltn nR.+1 (size xsR)) /\
        is_true (leq (nth O xsR nR) xR && ltn xR (nth O xsR nR.+1)))
      (fun nL => Lean.And
        (nd_target_lt (nd_target_add nL nd_target_one)
          (nd_target_length (nd_nat_list_to_imported xsR)))
        (Lean.And
          (nd_target_le
            (nd_target_nthD (nd_nat_list_to_imported xsR) nL)
            (sub_nat_to_imported xR))
          (nd_target_lt (sub_nat_to_imported xR)
            (nd_target_nthD (nd_nat_list_to_imported xsR)
              (nd_target_add nL nd_target_one)))))
      (fun nR nL Hn =>
        let Hsucc := nd_succ_correspondence nR nL Hn in
        nd_and_correspondence _ _ _ _
          (nd_lt_correspondence _ _ _ _ Hsucc
            (nd_length_related _ _ Hxs))
          (nd_bool_and_correspondence _ _ _ _
            (nd_le_correspondence _ _ _ _
              (nd_nthD_related _ _ _ _ Hxs Hn) Hx)
            (nd_lt_correspondence _ _ _ _ Hx
              (nd_nthD_related _ _ _ _ Hxs Hsucc)))).
    exact (sprop_to_prop _ _ Hexists
      (HL (nd_nat_list_to_imported xsR) (sub_nat_to_imported xR)
        (prop_to_sprop _ _
          (nd_nontrivial_length_correspondence _ _ Hxs) HlenR)
        (prop_to_sprop _ _ Hboundary HboundsR))).
Qed.

Definition nd_target_distances_unfold_2cons : SProp :=
  forall (x0 x1 : Lean.Nat)
      (xs : ImportedNondecreasing.List_inst1 Lean.Nat),
    Lean.eq
      (ImportedNondecreasing.Prosa_Util_Nondecreasing_distances
        (ImportedNondecreasing.List_cons_inst1 Lean.Nat x0
          (ImportedNondecreasing.List_cons_inst1 Lean.Nat x1 xs)))
      (ImportedNondecreasing.List_cons_inst1 Lean.Nat
        (nd_target_hsub x1 x0)
        (ImportedNondecreasing.Prosa_Util_Nondecreasing_distances
          (ImportedNondecreasing.List_cons_inst1 Lean.Nat x1 xs))).

Theorem distances_unfold_2cons_correspondence_certificate :
  PropSPropRel GeneratedNondecreasingSource.statement_distances_unfold_2cons
    nd_target_distances_unfold_2cons.
Proof.
  apply prop_sprop_rel_intro.
  - intros HR x0L x1L xsL.
    set x0R := sub_nat_to_rocq x0L.
    set x1R := sub_nat_to_rocq x1L.
    set xsR := nd_nat_list_to_rocq xsL.
    have Hx0 : SubNatRel x0R x0L := sub_nat_rel_surjective x0L.
    have Hx1 : SubNatRel x1R x1L := sub_nat_rel_surjective x1L.
    have Hxs : NdNatListRel xsR xsL := nd_nat_list_target_roundtrip xsL.
    have Htail := nd_cons_related x1R x1L xsR xsL Hx1 Hxs.
    have Hfull := nd_cons_related x0R x0L _ _ Hx0 Htail.
    have Hleft := distances_definition_certificate _ _ Hfull.
    have Hhead := nd_target_hsub_correspondence _ _ _ _ Hx1 Hx0.
    have Hright := nd_cons_related _ _ _ _ Hhead
      (distances_definition_certificate _ _ Htail).
    exact (prop_to_sprop _ _
      (nd_list_eq_correspondence _ _ _ _ Hleft Hright)
      (HR x0R x1R xsR)).
  - intro HL. apply strictly_inhabits. intros x0R x1R xsR.
    have Hx0 := sub_nat_rel_canonical x0R.
    have Hx1 := sub_nat_rel_canonical x1R.
    have Hxs : NdNatListRel xsR (nd_nat_list_to_imported xsR) :=
      @Lean.eq_refl _ _.
    have Htail := nd_cons_related x1R _ xsR _ Hx1 Hxs.
    have Hfull := nd_cons_related x0R _ _ _ Hx0 Htail.
    have Hleft := distances_definition_certificate _ _ Hfull.
    have Hhead := nd_target_hsub_correspondence _ _ _ _ Hx1 Hx0.
    have Hright := nd_cons_related _ _ _ _ Hhead
      (distances_definition_certificate _ _ Htail).
    exact (sprop_to_prop _ _
      (nd_list_eq_correspondence _ _ _ _ Hleft Hright)
      (HL (sub_nat_to_imported x0R) (sub_nat_to_imported x1R)
        (nd_nat_list_to_imported xsR))).
Qed.

Definition nd_target_distances_unfold_2app_last : SProp :=
  forall (a b : Lean.Nat) (xs : ImportedNondecreasing.List_inst1 Lean.Nat),
    Lean.eq
      (ImportedNondecreasing.Prosa_Util_Nondecreasing_distances
        (nd_target_append xs
          (ImportedNondecreasing.List_cons_inst1 Lean.Nat a
            (ImportedNondecreasing.List_cons_inst1 Lean.Nat b
              (ImportedNondecreasing.List_nil_inst1 Lean.Nat)))))
      (nd_target_append
        (ImportedNondecreasing.Prosa_Util_Nondecreasing_distances
          (nd_target_append xs
            (ImportedNondecreasing.List_cons_inst1 Lean.Nat a
              (ImportedNondecreasing.List_nil_inst1 Lean.Nat))))
        (ImportedNondecreasing.List_cons_inst1 Lean.Nat
          (nd_target_hsub b a)
          (ImportedNondecreasing.List_nil_inst1 Lean.Nat))).

Theorem distances_unfold_2app_last_correspondence_certificate :
  PropSPropRel
    GeneratedNondecreasingSource.statement_distances_unfold_2app_last
    nd_target_distances_unfold_2app_last.
Proof.
  apply prop_sprop_rel_intro.
  - intros HR aL bL xsL.
    set aR := sub_nat_to_rocq aL.
    set bR := sub_nat_to_rocq bL.
    set xsR := nd_nat_list_to_rocq xsL.
    have Ha : SubNatRel aR aL := sub_nat_rel_surjective aL.
    have Hb : SubNatRel bR bL := sub_nat_rel_surjective bL.
    have Hxs : NdNatListRel xsR xsL := nd_nat_list_target_roundtrip xsL.
    have Hnil : NdNatListRel [::]
        (ImportedNondecreasing.List_nil_inst1 Lean.Nat) := @Lean.eq_refl _ _.
    have HbList := nd_cons_related bR bL [::] _ Hb Hnil.
    have HabList := nd_cons_related aR aL _ _ Ha HbList.
    have HaList := nd_cons_related aR aL [::] _ Ha Hnil.
    have Hleft := distances_definition_certificate _ _
      (nd_append_related _ _ _ _ Hxs HabList).
    have Hprefix := distances_definition_certificate _ _
      (nd_append_related _ _ _ _ Hxs HaList).
    have Hdiff := nd_target_hsub_correspondence _ _ _ _ Hb Ha.
    have HdiffList := nd_cons_related _ _ [::] _ Hdiff Hnil.
    have Hright := nd_append_related _ _ _ _ Hprefix HdiffList.
    exact (prop_to_sprop _ _
      (nd_list_eq_correspondence _ _ _ _ Hleft Hright) (HR aR bR xsR)).
  - intro HL. apply strictly_inhabits. intros aR bR xsR.
    have Ha := sub_nat_rel_canonical aR.
    have Hb := sub_nat_rel_canonical bR.
    have Hxs : NdNatListRel xsR (nd_nat_list_to_imported xsR) :=
      @Lean.eq_refl _ _.
    have Hnil : NdNatListRel [::]
        (ImportedNondecreasing.List_nil_inst1 Lean.Nat) := @Lean.eq_refl _ _.
    have HbList := nd_cons_related bR _ [::] _ Hb Hnil.
    have HabList := nd_cons_related aR _ _ _ Ha HbList.
    have HaList := nd_cons_related aR _ [::] _ Ha Hnil.
    have Hleft := distances_definition_certificate _ _
      (nd_append_related _ _ _ _ Hxs HabList).
    have Hprefix := distances_definition_certificate _ _
      (nd_append_related _ _ _ _ Hxs HaList).
    have Hdiff := nd_target_hsub_correspondence _ _ _ _ Hb Ha.
    have HdiffList := nd_cons_related _ _ [::] _ Hdiff Hnil.
    have Hright := nd_append_related _ _ _ _ Hprefix HdiffList.
    exact (sprop_to_prop _ _
      (nd_list_eq_correspondence _ _ _ _ Hleft Hright)
      (HL (sub_nat_to_imported aR) (sub_nat_to_imported bR)
        (nd_nat_list_to_imported xsR))).
Qed.

Definition nd_target_distances_unfold_1app_last : SProp :=
  forall (x : Lean.Nat) (xs : ImportedNondecreasing.List_inst1 Lean.Nat),
    nd_target_le nd_target_one (nd_target_length xs) ->
    Lean.eq
      (ImportedNondecreasing.Prosa_Util_Nondecreasing_distances
        (nd_target_append xs
          (ImportedNondecreasing.List_cons_inst1 Lean.Nat x
            (ImportedNondecreasing.List_nil_inst1 Lean.Nat))))
      (nd_target_append
        (ImportedNondecreasing.Prosa_Util_Nondecreasing_distances xs)
        (ImportedNondecreasing.List_cons_inst1 Lean.Nat
          (nd_target_hsub x (nd_target_last0 xs))
          (ImportedNondecreasing.List_nil_inst1 Lean.Nat))).

Theorem distances_unfold_1app_last_correspondence_certificate :
  PropSPropRel
    GeneratedNondecreasingSource.statement_distances_unfold_1app_last
    nd_target_distances_unfold_1app_last.
Proof.
  apply prop_sprop_rel_intro.
  - intros HR xL xsL HposL.
    set xR := sub_nat_to_rocq xL.
    set xsR := nd_nat_list_to_rocq xsL.
    have Hx : SubNatRel xR xL := sub_nat_rel_surjective xL.
    have Hxs : NdNatListRel xsR xsL := nd_nat_list_target_roundtrip xsL.
    have Hnil : NdNatListRel [::]
        (ImportedNondecreasing.List_nil_inst1 Lean.Nat) := @Lean.eq_refl _ _.
    have HxList := nd_cons_related xR xL [::] _ Hx Hnil.
    have Hleft := distances_definition_certificate _ _
      (nd_append_related _ _ _ _ Hxs HxList).
    have Hdist := distances_definition_certificate _ _ Hxs.
    have Hdiff := nd_target_hsub_correspondence _ _ _ _ Hx
      (nd_last0_related _ _ Hxs).
    have HdiffList := nd_cons_related _ _ [::] _ Hdiff Hnil.
    have Hright := nd_append_related _ _ _ _ Hdist HdiffList.
    exact (prop_to_sprop _ _
      (nd_list_eq_correspondence _ _ _ _ Hleft Hright)
      (HR xR xsR (sprop_to_prop _ _
        (nd_positive_length_correspondence _ _ Hxs) HposL))).
  - intro HL. apply strictly_inhabits. intros xR xsR HposR.
    have Hx := sub_nat_rel_canonical xR.
    have Hxs : NdNatListRel xsR (nd_nat_list_to_imported xsR) :=
      @Lean.eq_refl _ _.
    have Hnil : NdNatListRel [::]
        (ImportedNondecreasing.List_nil_inst1 Lean.Nat) := @Lean.eq_refl _ _.
    have HxList := nd_cons_related xR _ [::] _ Hx Hnil.
    have Hleft := distances_definition_certificate _ _
      (nd_append_related _ _ _ _ Hxs HxList).
    have Hdist := distances_definition_certificate _ _ Hxs.
    have Hdiff := nd_target_hsub_correspondence _ _ _ _ Hx
      (nd_last0_related _ _ Hxs).
    have HdiffList := nd_cons_related _ _ [::] _ Hdiff Hnil.
    have Hright := nd_append_related _ _ _ _ Hdist HdiffList.
    exact (sprop_to_prop _ _
      (nd_list_eq_correspondence _ _ _ _ Hleft Hright)
      (HL (sub_nat_to_imported xR) (nd_nat_list_to_imported xsR)
        (prop_to_sprop _ _
          (nd_positive_length_correspondence _ _ Hxs) HposR))).
Qed.

Definition nd_target_distance_between_neighboring_elements_le_max_distance_in_seq :
    SProp :=
  forall (xs : ImportedNondecreasing.List_inst1 Lean.Nat) (n : Lean.Nat),
    nd_target_le
      (nd_target_hsub
        (nd_target_nthD xs (nd_target_add n nd_target_one))
        (nd_target_nthD xs n))
      (nd_target_max0
        (ImportedNondecreasing.Prosa_Util_Nondecreasing_distances xs)).

Theorem distance_between_neighboring_elements_le_max_distance_in_seq_correspondence_certificate :
  PropSPropRel
    GeneratedNondecreasingSource.statement_distance_between_neighboring_elements_le_max_distance_in_seq
    nd_target_distance_between_neighboring_elements_le_max_distance_in_seq.
Proof.
  apply prop_sprop_rel_intro.
  - intros HR xsL nL.
    set xsR := nd_nat_list_to_rocq xsL.
    set nR := sub_nat_to_rocq nL.
    have Hxs : NdNatListRel xsR xsL := nd_nat_list_target_roundtrip xsL.
    have Hn : SubNatRel nR nL := sub_nat_rel_surjective nL.
    have Hsucc := nd_succ_correspondence nR nL Hn.
    have Hleft := nd_target_hsub_correspondence _ _ _ _
      (nd_nthD_related _ _ _ _ Hxs Hsucc)
      (nd_nthD_related _ _ _ _ Hxs Hn).
    have Hdist := distances_definition_certificate _ _ Hxs.
    have Hright := nd_max0_related _ _ Hdist.
    exact (prop_to_sprop _ _
      (nd_le_correspondence _ _ _ _ Hleft Hright) (HR xsR nR)).
  - intro HL. apply strictly_inhabits. intros xsR nR.
    have Hxs : NdNatListRel xsR (nd_nat_list_to_imported xsR) :=
      @Lean.eq_refl _ _.
    have Hn := sub_nat_rel_canonical nR.
    have Hsucc := nd_succ_correspondence nR _ Hn.
    have Hleft := nd_target_hsub_correspondence _ _ _ _
      (nd_nthD_related _ _ _ _ Hxs Hsucc)
      (nd_nthD_related _ _ _ _ Hxs Hn).
    have Hdist := distances_definition_certificate _ _ Hxs.
    have Hright := nd_max0_related _ _ Hdist.
    exact (sprop_to_prop _ _
      (nd_le_correspondence _ _ _ _ Hleft Hright)
      (HL (nd_nat_list_to_imported xsR) (sub_nat_to_imported nR))).
Qed.

Definition nd_target_max_distance_in_seq_le_last_element_of_seq : SProp :=
  forall xs : ImportedNondecreasing.List_inst1 Lean.Nat,
    ImportedNondecreasing.Prosa_Util_Nondecreasing_nondecreasing_sequence xs ->
    nd_target_le
      (nd_target_max0
        (ImportedNondecreasing.Prosa_Util_Nondecreasing_distances xs))
      (nd_target_last0 xs).

Theorem max_distance_in_seq_le_last_element_of_seq_correspondence_certificate :
  PropSPropRel
    GeneratedNondecreasingSource.statement_max_distance_in_seq_le_last_element_of_seq
    nd_target_max_distance_in_seq_le_last_element_of_seq.
Proof.
  apply prop_sprop_rel_intro.
  - intros HR xsL HndL.
    set xsR := nd_nat_list_to_rocq xsL.
    have Hxs : NdNatListRel xsR xsL := nd_nat_list_target_roundtrip xsL.
    have Hdist := distances_definition_certificate _ _ Hxs.
    apply (prop_to_sprop _ _
      (nd_le_correspondence _ _ _ _
        (nd_max0_related _ _ Hdist) (nd_last0_related _ _ Hxs))).
    exact (HR xsR (sprop_to_prop _ _
      (nondecreasing_sequence_definition_certificate _ _ Hxs) HndL)).
  - intro HL. apply strictly_inhabits. intros xsR HndR.
    have Hxs : NdNatListRel xsR (nd_nat_list_to_imported xsR) :=
      @Lean.eq_refl _ _.
    have Hdist := distances_definition_certificate _ _ Hxs.
    exact (sprop_to_prop _ _
      (nd_le_correspondence _ _ _ _
        (nd_max0_related _ _ Hdist) (nd_last0_related _ _ Hxs))
      (HL (nd_nat_list_to_imported xsR)
        (prop_to_sprop _ _
          (nondecreasing_sequence_definition_certificate _ _ Hxs) HndR))).
Qed.

Definition nd_target_last_seq_minus_last_distance_seq : SProp :=
  forall xs : ImportedNondecreasing.List_inst1 Lean.Nat,
    ImportedNondecreasing.Prosa_Util_Nondecreasing_nondecreasing_sequence xs ->
    Lean.eq
      (nd_target_hsub (nd_target_last0 xs)
        (nd_target_last0
          (ImportedNondecreasing.Prosa_Util_Nondecreasing_distances xs)))
      (nd_target_nthD xs
        (nd_target_hsub (nd_target_length xs) nd_target_two)).

Theorem last_seq_minus_last_distance_seq_correspondence_certificate :
  PropSPropRel
    GeneratedNondecreasingSource.statement_last_seq_minus_last_distance_seq
    nd_target_last_seq_minus_last_distance_seq.
Proof.
  apply prop_sprop_rel_intro.
  - intros HR xsL HndL.
    set xsR := nd_nat_list_to_rocq xsL.
    have Hxs : NdNatListRel xsR xsL := nd_nat_list_target_roundtrip xsL.
    have Hdist := distances_definition_certificate _ _ Hxs.
    have Hleft := nd_target_hsub_correspondence _ _ _ _
      (nd_last0_related _ _ Hxs) (nd_last0_related _ _ Hdist).
    have Hidx := nd_pred2_correspondence _ _ (nd_length_related _ _ Hxs).
    have Hright := nd_nthD_related _ _ _ _ Hxs Hidx.
    exact (prop_to_sprop _ _
      (nd_nat_eq_correspondence _ _ _ _ Hleft Hright)
      (HR xsR (sprop_to_prop _ _
        (nondecreasing_sequence_definition_certificate _ _ Hxs) HndL))).
  - intro HL. apply strictly_inhabits. intros xsR HndR.
    have Hxs : NdNatListRel xsR (nd_nat_list_to_imported xsR) :=
      @Lean.eq_refl _ _.
    have Hdist := distances_definition_certificate _ _ Hxs.
    have Hleft := nd_target_hsub_correspondence _ _ _ _
      (nd_last0_related _ _ Hxs) (nd_last0_related _ _ Hdist).
    have Hidx := nd_pred2_correspondence _ _ (nd_length_related _ _ Hxs).
    have Hright := nd_nthD_related _ _ _ _ Hxs Hidx.
    exact (sprop_to_prop _ _
      (nd_nat_eq_correspondence _ _ _ _ Hleft Hright)
      (HL (nd_nat_list_to_imported xsR)
        (prop_to_sprop _ _
          (nondecreasing_sequence_definition_certificate _ _ Hxs) HndR))).
Qed.

Definition nd_target_max_distance_in_nontrivial_seq_is_positive : SProp :=
  forall xs : ImportedNondecreasing.List_inst1 Lean.Nat,
    ImportedNondecreasing.Prosa_Util_Nondecreasing_nondecreasing_sequence xs ->
    ImportedNondecreasing.Exists Lean.Nat (fun x =>
      ImportedNondecreasing.Exists Lean.Nat (fun y =>
        Lean.And (nd_target_nat_mem x xs)
          (Lean.And (nd_target_nat_mem y xs)
            (ImportedNondecreasing.Not (Lean.eq x y))))) ->
    nd_target_lt Lean.Nat_zero
      (nd_target_max0
        (ImportedNondecreasing.Prosa_Util_Nondecreasing_distances xs)).

Theorem max_distance_in_nontrivial_seq_is_positive_correspondence_certificate :
  PropSPropRel
    GeneratedNondecreasingSource.statement_max_distance_in_nontrivial_seq_is_positive
    nd_target_max_distance_in_nontrivial_seq_is_positive.
Proof.
  apply prop_sprop_rel_intro.
  - intros HR xsL HndL HdistinctL.
    set xsR := nd_nat_list_to_rocq xsL.
    have Hxs : NdNatListRel xsR xsL := nd_nat_list_target_roundtrip xsL.
    have Hdist := distances_definition_certificate _ _ Hxs.
    have Hprem := nd_exists_nat_correspondence
      (fun xR => exists yR, xR \in xsR /\ yR \in xsR /\ xR <> yR)
      (fun xL => ImportedNondecreasing.Exists Lean.Nat (fun yL =>
        Lean.And (nd_target_nat_mem xL xsL)
          (Lean.And (nd_target_nat_mem yL xsL)
            (ImportedNondecreasing.Not (Lean.eq xL yL)))))
      (fun xR xL Hx => nd_exists_nat_correspondence
        (fun yR => xR \in xsR /\ yR \in xsR /\ xR <> yR)
        (fun yL => Lean.And (nd_target_nat_mem xL xsL)
          (Lean.And (nd_target_nat_mem yL xsL)
            (ImportedNondecreasing.Not (Lean.eq xL yL))))
        (fun yR yL Hy => nd_and_correspondence _ _ _ _
          (nd_nat_membership_correspondence _ _ _ _ Hx Hxs)
          (nd_and_correspondence _ _ _ _
            (nd_nat_membership_correspondence _ _ _ _ Hy Hxs)
            (nd_not_correspondence _ _
              (nd_nat_eq_correspondence _ _ _ _ Hx Hy))))).
    exact (prop_to_sprop _ _
      (nd_lt_correspondence O Lean.Nat_zero _ _
        (sub_nat_rel_canonical O) (nd_max0_related _ _ Hdist))
      (HR xsR
        (sprop_to_prop _ _
          (nondecreasing_sequence_definition_certificate _ _ Hxs) HndL)
        (sprop_to_prop _ _ Hprem HdistinctL))).
  - intro HL. apply strictly_inhabits. intros xsR HndR HdistinctR.
    have Hxs : NdNatListRel xsR (nd_nat_list_to_imported xsR) :=
      @Lean.eq_refl _ _.
    have Hdist := distances_definition_certificate _ _ Hxs.
    have Hprem := nd_exists_nat_correspondence
      (fun xR => exists yR, xR \in xsR /\ yR \in xsR /\ xR <> yR)
      (fun xL => ImportedNondecreasing.Exists Lean.Nat (fun yL =>
        Lean.And (nd_target_nat_mem xL (nd_nat_list_to_imported xsR))
          (Lean.And (nd_target_nat_mem yL (nd_nat_list_to_imported xsR))
            (ImportedNondecreasing.Not (Lean.eq xL yL)))))
      (fun xR xL Hx => nd_exists_nat_correspondence
        (fun yR => xR \in xsR /\ yR \in xsR /\ xR <> yR)
        (fun yL => Lean.And
          (nd_target_nat_mem xL (nd_nat_list_to_imported xsR))
          (Lean.And (nd_target_nat_mem yL (nd_nat_list_to_imported xsR))
            (ImportedNondecreasing.Not (Lean.eq xL yL))))
        (fun yR yL Hy => nd_and_correspondence _ _ _ _
          (nd_nat_membership_correspondence _ _ _ _ Hx Hxs)
          (nd_and_correspondence _ _ _ _
            (nd_nat_membership_correspondence _ _ _ _ Hy Hxs)
            (nd_not_correspondence _ _
              (nd_nat_eq_correspondence _ _ _ _ Hx Hy))))).
    exact (sprop_to_prop _ _
      (nd_lt_correspondence O Lean.Nat_zero _ _
        (sub_nat_rel_canonical O) (nd_max0_related _ _ Hdist))
      (HL (nd_nat_list_to_imported xsR)
        (prop_to_sprop _ _
          (nondecreasing_sequence_definition_certificate _ _ Hxs) HndR)
        (prop_to_sprop _ _ Hprem HdistinctR))).
Qed.

Definition nd_target_domination_of_distances_implies_domination_of_seq : SProp :=
  forall (xs ys : ImportedNondecreasing.List_inst1 Lean.Nat),
    nd_target_le (nd_target_first0 xs) (nd_target_first0 ys) ->
    nd_target_le nd_target_two (nd_target_length xs) ->
    nd_target_le nd_target_two (nd_target_length ys) ->
    Lean.eq (nd_target_length xs) (nd_target_length ys) ->
    ImportedNondecreasing.Prosa_Util_Nondecreasing_nondecreasing_sequence xs ->
    ImportedNondecreasing.Prosa_Util_Nondecreasing_nondecreasing_sequence ys ->
    (forall n : Lean.Nat,
      nd_target_le
        (nd_target_nthD
          (ImportedNondecreasing.Prosa_Util_Nondecreasing_distances xs) n)
        (nd_target_nthD
          (ImportedNondecreasing.Prosa_Util_Nondecreasing_distances ys) n)) ->
    forall n : Lean.Nat,
      nd_target_le (nd_target_nthD xs n) (nd_target_nthD ys n).

Theorem domination_of_distances_implies_domination_of_seq_correspondence_certificate :
  PropSPropRel
    GeneratedNondecreasingSource.statement_domination_of_distances_implies_domination_of_seq
    nd_target_domination_of_distances_implies_domination_of_seq.
Proof.
  apply prop_sprop_rel_intro.
  - intros HR xsL ysL HfirstL HxlenL HylenL HleneqL HxndL HyndL HdistL nL.
    set xsR := nd_nat_list_to_rocq xsL.
    set ysR := nd_nat_list_to_rocq ysL.
    set nR := sub_nat_to_rocq nL.
    have Hxs : NdNatListRel xsR xsL := nd_nat_list_target_roundtrip xsL.
    have Hys : NdNatListRel ysR ysL := nd_nat_list_target_roundtrip ysL.
    have Hn : SubNatRel nR nL := sub_nat_rel_surjective nL.
    have Hdx := distances_definition_certificate _ _ Hxs.
    have Hdy := distances_definition_certificate _ _ Hys.
    apply (prop_to_sprop _ _ (nd_le_correspondence _ _ _ _
      (nd_nthD_related _ _ _ _ Hxs Hn)
      (nd_nthD_related _ _ _ _ Hys Hn))).
    apply (HR xsR ysR).
    + exact (sprop_to_prop _ _ (nd_le_correspondence _ _ _ _
        (nd_first0_related _ _ Hxs) (nd_first0_related _ _ Hys)) HfirstL).
    + exact (sprop_to_prop _ _
        (nd_nontrivial_length_correspondence _ _ Hxs) HxlenL).
    + exact (sprop_to_prop _ _
        (nd_nontrivial_length_correspondence _ _ Hys) HylenL).
    + exact (sprop_to_prop _ _ (nd_nat_eq_correspondence _ _ _ _
        (nd_length_related _ _ Hxs) (nd_length_related _ _ Hys)) HleneqL).
    + exact (sprop_to_prop _ _
        (nondecreasing_sequence_definition_certificate _ _ Hxs) HxndL).
    + exact (sprop_to_prop _ _
        (nondecreasing_sequence_definition_certificate _ _ Hys) HyndL).
    + intro kR. have Hk := sub_nat_rel_canonical kR.
      exact (sprop_to_prop _ _ (nd_le_correspondence _ _ _ _
        (nd_nthD_related _ _ _ _ Hdx Hk)
        (nd_nthD_related _ _ _ _ Hdy Hk))
        (HdistL (sub_nat_to_imported kR))).
  - intro HL. apply strictly_inhabits.
    intros xsR ysR HfirstR HxlenR HylenR HleneqR HxndR HyndR HdistR nR.
    have Hxs : NdNatListRel xsR (nd_nat_list_to_imported xsR) :=
      @Lean.eq_refl _ _.
    have Hys : NdNatListRel ysR (nd_nat_list_to_imported ysR) :=
      @Lean.eq_refl _ _.
    have Hn := sub_nat_rel_canonical nR.
    have Hdx := distances_definition_certificate _ _ Hxs.
    have Hdy := distances_definition_certificate _ _ Hys.
    apply (sprop_to_prop _ _ (nd_le_correspondence _ _ _ _
      (nd_nthD_related _ _ _ _ Hxs Hn)
      (nd_nthD_related _ _ _ _ Hys Hn))).
    apply (HL (nd_nat_list_to_imported xsR) (nd_nat_list_to_imported ysR)).
    + exact (prop_to_sprop _ _ (nd_le_correspondence _ _ _ _
        (nd_first0_related _ _ Hxs) (nd_first0_related _ _ Hys)) HfirstR).
    + exact (prop_to_sprop _ _
        (nd_nontrivial_length_correspondence _ _ Hxs) HxlenR).
    + exact (prop_to_sprop _ _
        (nd_nontrivial_length_correspondence _ _ Hys) HylenR).
    + exact (prop_to_sprop _ _ (nd_nat_eq_correspondence _ _ _ _
        (nd_length_related _ _ Hxs) (nd_length_related _ _ Hys)) HleneqR).
    + exact (prop_to_sprop _ _
        (nondecreasing_sequence_definition_certificate _ _ Hxs) HxndR).
    + exact (prop_to_sprop _ _
        (nondecreasing_sequence_definition_certificate _ _ Hys) HyndR).
    + intro kL. set kR := sub_nat_to_rocq kL.
      have Hk : SubNatRel kR kL := sub_nat_rel_surjective kL.
      exact (prop_to_sprop _ _ (nd_le_correspondence _ _ _ _
        (nd_nthD_related _ _ _ _ Hdx Hk)
        (nd_nthD_related _ _ _ _ Hdy Hk)) (HdistR kR)).
Qed.

Definition nd_target_function_of_distances_is_correct : SProp :=
  forall (xs : ImportedNondecreasing.List_inst1 Lean.Nat) (n : Lean.Nat),
    Lean.eq
      (nd_target_nthD
        (ImportedNondecreasing.Prosa_Util_Nondecreasing_distances xs) n)
      (nd_target_hsub
        (nd_target_nthD xs (nd_target_add n nd_target_one))
        (nd_target_nthD xs n)).

Theorem function_of_distances_is_correct_correspondence_certificate :
  PropSPropRel
    GeneratedNondecreasingSource.statement_function_of_distances_is_correct
    nd_target_function_of_distances_is_correct.
Proof.
  apply prop_sprop_rel_intro.
  - intros HR xsL nL.
    set xsR := nd_nat_list_to_rocq xsL.
    set nR := sub_nat_to_rocq nL.
    have Hxs : NdNatListRel xsR xsL := nd_nat_list_target_roundtrip xsL.
    have Hn : SubNatRel nR nL := sub_nat_rel_surjective nL.
    have Hdist := distances_definition_certificate xsR xsL Hxs.
    have Hleft := nd_nthD_related _ _ _ _ Hdist Hn.
    have Hsucc := nd_succ_correspondence nR nL Hn.
    have Hnext := nd_nthD_related xsR xsL nR.+1
      (nd_target_add nL nd_target_one) Hxs Hsucc.
    have Hcur := nd_nthD_related xsR xsL nR nL Hxs Hn.
    have Hright := nd_target_hsub_correspondence _ _ _ _ Hnext Hcur.
    exact (prop_to_sprop _ _
      (nd_nat_eq_correspondence _ _ _ _ Hleft Hright) (HR xsR nR)).
  - intro HL. apply strictly_inhabits. intros xsR nR.
    have Hxs : NdNatListRel xsR (nd_nat_list_to_imported xsR) :=
      @Lean.eq_refl _ _.
    have Hn := sub_nat_rel_canonical nR.
    have Hdist := distances_definition_certificate _ _ Hxs.
    have Hleft := nd_nthD_related _ _ _ _ Hdist Hn.
    have Hsucc := nd_succ_correspondence nR (sub_nat_to_imported nR) Hn.
    have Hnext := nd_nthD_related xsR _ nR.+1 _ Hxs Hsucc.
    have Hcur := nd_nthD_related xsR _ nR _ Hxs Hn.
    have Hright := nd_target_hsub_correspondence _ _ _ _ Hnext Hcur.
    exact (sprop_to_prop _ _
      (nd_nat_eq_correspondence _ _ _ _ Hleft Hright)
      (HL (nd_nat_list_to_imported xsR) (sub_nat_to_imported nR))).
Qed.

Definition nd_target_size_of_seq_of_distances : SProp :=
  forall xs : ImportedNondecreasing.List_inst1 Lean.Nat,
    nd_target_le nd_target_two (nd_target_length xs) ->
    Lean.eq (nd_target_length xs)
      (nd_target_add
        (nd_target_length
          (ImportedNondecreasing.Prosa_Util_Nondecreasing_distances xs))
        nd_target_one).

Theorem size_of_seq_of_distances_correspondence_certificate :
  PropSPropRel GeneratedNondecreasingSource.statement_size_of_seq_of_distances
    nd_target_size_of_seq_of_distances.
Proof.
  apply prop_sprop_rel_intro.
  - intros HR xsL HnontrivialL.
    set xsR := nd_nat_list_to_rocq xsL.
    have Hxs : NdNatListRel xsR xsL := nd_nat_list_target_roundtrip xsL.
    have Hdist := distances_definition_certificate xsR xsL Hxs.
    have Hleft := nd_length_related xsR xsL Hxs.
    have Hright := nd_target_add_correspondence _ _ 1 nd_target_one
      (nd_length_related _ _ Hdist) (sub_nat_rel_canonical 1).
    exact (prop_to_sprop _ _
      (nd_nat_eq_correspondence _ _ _ _ Hleft Hright)
      (HR xsR (sprop_to_prop _ _
        (nd_nontrivial_length_correspondence xsR xsL Hxs) HnontrivialL))).
  - intro HL. apply strictly_inhabits. intros xsR HnontrivialR.
    have Hxs : NdNatListRel xsR (nd_nat_list_to_imported xsR) :=
      @Lean.eq_refl _ _.
    have Hdist := distances_definition_certificate _ _ Hxs.
    have Hleft := nd_length_related _ _ Hxs.
    have Hright := nd_target_add_correspondence _ _ 1 nd_target_one
      (nd_length_related _ _ Hdist) (sub_nat_rel_canonical 1).
    exact (sprop_to_prop _ _
      (nd_nat_eq_correspondence _ _ _ _ Hleft Hright)
      (HL (nd_nat_list_to_imported xsR)
        (prop_to_sprop _ _
          (nd_nontrivial_length_correspondence _ _ Hxs) HnontrivialR))).
Qed.

(** The final cluster shares the ordered duplicate-removal certificate from
    [NondecreasingCorrespondence].  No theorem constant from either side is
    used below. *)

Definition nd_target_nodup_sort_2cons_lt : SProp :=
  forall (x1 x2 : Lean.Nat)
      (xs : ImportedNondecreasing.List_inst1 Lean.Nat),
    nd_target_lt x1 x2 ->
    ImportedNondecreasing.Prosa_Util_Nondecreasing_nondecreasing_sequence
      (ImportedNondecreasing.List_cons_inst1 Lean.Nat x1
        (ImportedNondecreasing.List_cons_inst1 Lean.Nat x2 xs)) ->
    Lean.eq
      (nd_target_dedup_nat
        (ImportedNondecreasing.List_cons_inst1 Lean.Nat x1
          (ImportedNondecreasing.List_cons_inst1 Lean.Nat x2 xs)))
      (ImportedNondecreasing.List_cons_inst1 Lean.Nat x1
        (nd_target_dedup_nat
          (ImportedNondecreasing.List_cons_inst1 Lean.Nat x2 xs))).

Theorem nodup_sort_2cons_lt_correspondence_certificate :
  PropSPropRel GeneratedNondecreasingSource.statement_nodup_sort_2cons_lt
    nd_target_nodup_sort_2cons_lt.
Proof.
  apply prop_sprop_rel_intro.
  - intros HR x1L x2L xsL HltL HndL.
    set x1R := sub_nat_to_rocq x1L.
    set x2R := sub_nat_to_rocq x2L.
    set xsR := nd_nat_list_to_rocq xsL.
    have Hx1 : SubNatRel x1R x1L := sub_nat_rel_surjective x1L.
    have Hx2 : SubNatRel x2R x2L := sub_nat_rel_surjective x2L.
    have Hxs : NdNatListRel xsR xsL := nd_nat_list_target_roundtrip xsL.
    have Htail := nd_cons_related x2R x2L xsR xsL Hx2 Hxs.
    have Hfull := nd_cons_related x1R x1L _ _ Hx1 Htail.
    have Hleft := nd_undup_nat_related _ _ Hfull.
    have HrightTail := nd_undup_nat_related _ _ Htail.
    have Hright := nd_cons_related x1R x1L _ _ Hx1 HrightTail.
    exact (prop_to_sprop _ _
      (nd_list_eq_correspondence _ _ _ _ Hleft Hright)
      (HR x1R x2R xsR
        (sprop_to_prop _ _ (nd_lt_correspondence _ _ _ _ Hx1 Hx2) HltL)
        (sprop_to_prop _ _
          (nondecreasing_sequence_definition_certificate _ _ Hfull) HndL))).
  - intro HL. apply strictly_inhabits. intros x1R x2R xsR HltR HndR.
    have Hx1 := sub_nat_rel_canonical x1R.
    have Hx2 := sub_nat_rel_canonical x2R.
    have Hxs : NdNatListRel xsR (nd_nat_list_to_imported xsR) :=
      @Lean.eq_refl _ _.
    have Htail := nd_cons_related x2R _ xsR _ Hx2 Hxs.
    have Hfull := nd_cons_related x1R _ _ _ Hx1 Htail.
    have Hleft := nd_undup_nat_related _ _ Hfull.
    have HrightTail := nd_undup_nat_related _ _ Htail.
    have Hright := nd_cons_related x1R _ _ _ Hx1 HrightTail.
    exact (sprop_to_prop _ _
      (nd_list_eq_correspondence _ _ _ _ Hleft Hright)
      (HL (sub_nat_to_imported x1R) (sub_nat_to_imported x2R)
        (nd_nat_list_to_imported xsR)
        (prop_to_sprop _ _ (nd_lt_correspondence _ _ _ _ Hx1 Hx2) HltR)
        (prop_to_sprop _ _
          (nondecreasing_sequence_definition_certificate _ _ Hfull) HndR))).
Qed.

Definition nd_target_last0_undup : SProp :=
  forall xs : ImportedNondecreasing.List_inst1 Lean.Nat,
    ImportedNondecreasing.Prosa_Util_Nondecreasing_nondecreasing_sequence xs ->
    Lean.eq (nd_target_last0 (nd_target_dedup_nat xs))
      (nd_target_last0 xs).

Theorem last0_undup_correspondence_certificate :
  PropSPropRel GeneratedNondecreasingSource.statement_last0_undup
    nd_target_last0_undup.
Proof.
  apply prop_sprop_rel_intro.
  - intros HR xsL HndL.
    set xsR := nd_nat_list_to_rocq xsL.
    have Hxs : NdNatListRel xsR xsL := nd_nat_list_target_roundtrip xsL.
    have Hdedup := nd_undup_nat_related xsR xsL Hxs.
    exact (prop_to_sprop _ _
      (nd_nat_eq_correspondence _ _ _ _
        (nd_last0_related _ _ Hdedup) (nd_last0_related _ _ Hxs))
      (HR xsR (sprop_to_prop _ _
        (nondecreasing_sequence_definition_certificate _ _ Hxs) HndL))).
  - intro HL. apply strictly_inhabits. intros xsR HndR.
    have Hxs : NdNatListRel xsR (nd_nat_list_to_imported xsR) :=
      @Lean.eq_refl _ _.
    have Hdedup := nd_undup_nat_related xsR _ Hxs.
    exact (sprop_to_prop _ _
      (nd_nat_eq_correspondence _ _ _ _
        (nd_last0_related _ _ Hdedup) (nd_last0_related _ _ Hxs))
      (HL (nd_nat_list_to_imported xsR)
        (prop_to_sprop _ _
          (nondecreasing_sequence_definition_certificate _ _ Hxs) HndR))).
Qed.

Definition nd_target_nondecreasing_sequence_undup : SProp :=
  forall xs : ImportedNondecreasing.List_inst1 Lean.Nat,
    ImportedNondecreasing.Prosa_Util_Nondecreasing_nondecreasing_sequence xs ->
    ImportedNondecreasing.Prosa_Util_Nondecreasing_nondecreasing_sequence
      (nd_target_dedup_nat xs).

Theorem nondecreasing_sequence_undup_correspondence_certificate :
  PropSPropRel
    GeneratedNondecreasingSource.statement_nondecreasing_sequence_undup
    nd_target_nondecreasing_sequence_undup.
Proof.
  apply prop_sprop_rel_intro.
  - intros HR xsL HndL.
    set xsR := nd_nat_list_to_rocq xsL.
    have Hxs : NdNatListRel xsR xsL := nd_nat_list_target_roundtrip xsL.
    have Hdedup := nd_undup_nat_related xsR xsL Hxs.
    exact (prop_to_sprop _ _
      (nondecreasing_sequence_definition_certificate _ _ Hdedup)
      (HR xsR (sprop_to_prop _ _
        (nondecreasing_sequence_definition_certificate _ _ Hxs) HndL))).
  - intro HL. apply strictly_inhabits. intros xsR HndR.
    have Hxs : NdNatListRel xsR (nd_nat_list_to_imported xsR) :=
      @Lean.eq_refl _ _.
    have Hdedup := nd_undup_nat_related xsR _ Hxs.
    exact (sprop_to_prop _ _
      (nondecreasing_sequence_definition_certificate _ _ Hdedup)
      (HL (nd_nat_list_to_imported xsR)
        (prop_to_sprop _ _
          (nondecreasing_sequence_definition_certificate _ _ Hxs) HndR))).
Qed.

Definition nd_target_undup_nth_le : SProp :=
  forall xs : ImportedNondecreasing.List_inst1 Lean.Nat,
    ImportedNondecreasing.Prosa_Util_Nondecreasing_nondecreasing_sequence xs ->
    nd_target_le
      (nd_target_nthD (nd_target_dedup_nat xs)
        (nd_target_hsub (nd_target_length (nd_target_dedup_nat xs))
          nd_target_two))
      (nd_target_nthD xs
        (nd_target_hsub (nd_target_length xs) nd_target_two)).

Theorem undup_nth_le_correspondence_certificate :
  PropSPropRel GeneratedNondecreasingSource.statement_undup_nth_le
    nd_target_undup_nth_le.
Proof.
  apply prop_sprop_rel_intro.
  - intros HR xsL HndL.
    set xsR := nd_nat_list_to_rocq xsL.
    have Hxs : NdNatListRel xsR xsL := nd_nat_list_target_roundtrip xsL.
    have Hdedup := nd_undup_nat_related xsR xsL Hxs.
    have Hld := nd_length_related _ _ Hdedup.
    have Hl := nd_length_related _ _ Hxs.
    have Hpd := nd_pred2_correspondence _ _ Hld.
    have Hp := nd_pred2_correspondence _ _ Hl.
    exact (prop_to_sprop _ _ (nd_le_correspondence _ _ _ _
      (nd_nthD_related _ _ _ _ Hdedup Hpd)
      (nd_nthD_related _ _ _ _ Hxs Hp))
      (HR xsR (sprop_to_prop _ _
        (nondecreasing_sequence_definition_certificate _ _ Hxs) HndL))).
  - intro HL. apply strictly_inhabits. intros xsR HndR.
    have Hxs : NdNatListRel xsR (nd_nat_list_to_imported xsR) :=
      @Lean.eq_refl _ _.
    have Hdedup := nd_undup_nat_related xsR _ Hxs.
    have Hld := nd_length_related _ _ Hdedup.
    have Hl := nd_length_related _ _ Hxs.
    have Hpd := nd_pred2_correspondence _ _ Hld.
    have Hp := nd_pred2_correspondence _ _ Hl.
    exact (sprop_to_prop _ _ (nd_le_correspondence _ _ _ _
      (nd_nthD_related _ _ _ _ Hdedup Hpd)
      (nd_nthD_related _ _ _ _ Hxs Hp))
      (HL (nd_nat_list_to_imported xsR)
        (prop_to_sprop _ _
          (nondecreasing_sequence_definition_certificate _ _ Hxs) HndR))).
Qed.

Definition nd_target_distances_positive_undup : SProp :=
  forall xs : ImportedNondecreasing.List_inst1 Lean.Nat,
    ImportedNondecreasing.Prosa_Util_Nondecreasing_nondecreasing_sequence xs ->
    Lean.eq
      (nd_target_filter nd_target_positive
        (ImportedNondecreasing.Prosa_Util_Nondecreasing_distances xs))
      (ImportedNondecreasing.Prosa_Util_Nondecreasing_distances
        (nd_target_dedup_nat xs)).

Theorem distances_positive_undup_correspondence_certificate :
  PropSPropRel
    GeneratedNondecreasingSource.statement_distances_positive_undup
    nd_target_distances_positive_undup.
Proof.
  apply prop_sprop_rel_intro.
  - intros HR xsL HndL.
    set xsR := nd_nat_list_to_rocq xsL.
    have Hxs : NdNatListRel xsR xsL := nd_nat_list_target_roundtrip xsL.
    have Hdist := distances_definition_certificate _ _ Hxs.
    have Hleft := nd_filter_related (fun x => ltn O x)
      nd_target_positive _ _ nd_positive_pred_related Hdist.
    have Hdedup := nd_undup_nat_related xsR xsL Hxs.
    have Hright := distances_definition_certificate _ _ Hdedup.
    exact (prop_to_sprop _ _
      (nd_list_eq_correspondence _ _ _ _ Hleft Hright)
      (HR xsR (sprop_to_prop _ _
        (nondecreasing_sequence_definition_certificate _ _ Hxs) HndL))).
  - intro HL. apply strictly_inhabits. intros xsR HndR.
    have Hxs : NdNatListRel xsR (nd_nat_list_to_imported xsR) :=
      @Lean.eq_refl _ _.
    have Hdist := distances_definition_certificate _ _ Hxs.
    have Hleft := nd_filter_related (fun x => ltn O x)
      nd_target_positive _ _ nd_positive_pred_related Hdist.
    have Hdedup := nd_undup_nat_related xsR _ Hxs.
    have Hright := distances_definition_certificate _ _ Hdedup.
    exact (sprop_to_prop _ _
      (nd_list_eq_correspondence _ _ _ _ Hleft Hright)
      (HL (nd_nat_list_to_imported xsR)
        (prop_to_sprop _ _
          (nondecreasing_sequence_definition_certificate _ _ Hxs) HndR))).
Qed.

(** The source quantifies over MathComp [eqType], whereas Lean quantifies over
    a carrier plus [DecidableEq].  The approved relation for that boundary is
    pointwise: every source [eqType] is paired with its carrier and the
    equality decision procedure [nd_decidable_eq].  It intentionally does not
    claim an isomorphism between [eqType] and the universe of all Lean types. *)
Definition nd_target_nodup_sort_2cons_eq_exact : SProp :=
  forall (T : Type) (inst : ImportedNondecreasing.DecidableEq T)
      (x : T) (xs : ImportedNondecreasing.List_inst1 T),
    Lean.eq
      (ImportedNondecreasing.List_dedup_inst1 T inst
        (ImportedNondecreasing.List_cons_inst1 T x
          (ImportedNondecreasing.List_cons_inst1 T x xs)))
      (ImportedNondecreasing.List_dedup_inst1 T inst
        (ImportedNondecreasing.List_cons_inst1 T x xs)).

Definition nd_nodup_sort_2cons_eq_boundary_rel : Prop :=
  forall (T : eqType) (x : T) (xsR : seq T)
      (xsL : ImportedNondecreasing.List_inst1 T),
    NdList1Rel xsR xsL ->
    PropSPropRel
      (Logic.eq (undup (x :: x :: xsR)) (undup (x :: xsR)))
      (Lean.eq
        (nd_target_dedup T
          (ImportedNondecreasing.List_cons_inst1 T x
            (ImportedNondecreasing.List_cons_inst1 T x xsL)))
        (nd_target_dedup T
          (ImportedNondecreasing.List_cons_inst1 T x xsL))).

Theorem nodup_sort_2cons_eq_correspondence_certificate :
  nd_nodup_sort_2cons_eq_boundary_rel.
Proof.
  intros T x xsR xsL Hxs.
  apply nd_list1_eq_correspondence.
  - apply nd_undup_related.
    unfold NdList1Rel in Hxs |- *. cbn [nd_list1_to_imported].
    exact (sub_imported_eq_congr
      (ImportedNondecreasing.List_cons_inst1 T x) _ _
      (sub_imported_eq_congr
        (ImportedNondecreasing.List_cons_inst1 T x) _ _ Hxs)).
  - apply nd_undup_related.
    unfold NdList1Rel in Hxs |- *. cbn [nd_list1_to_imported].
    exact (sub_imported_eq_congr
      (ImportedNondecreasing.List_cons_inst1 T x) _ _ Hxs).
Qed.

Print Assumptions increasing_implies_nondecreasing_correspondence_certificate.
Print Assumptions nondecreasing_sequence_cons_correspondence_certificate.
Print Assumptions nondec_seq_zero_first_correspondence_certificate.
Print Assumptions nondecreasing_sequence_2cons_leVeq_correspondence_certificate.
Print Assumptions nondecreasing_sequence_cons_double_correspondence_certificate.
Print Assumptions nondecreasing_sequence_add_min_correspondence_certificate.
Print Assumptions nondecreasing_sequence_cons_min_correspondence_certificate.
Print Assumptions nondecreasing_sequence_cons_smin_correspondence_certificate.
Print Assumptions last_is_max_in_nondecreasing_seq_correspondence_certificate.
Print Assumptions antidensity_of_nondecreasing_seq_correspondence_certificate.
Print Assumptions belonging_to_segment_of_seq_is_total_correspondence_certificate.
Print Assumptions distances_unfold_2cons_correspondence_certificate.
Print Assumptions distances_unfold_2app_last_correspondence_certificate.
Print Assumptions distances_unfold_1app_last_correspondence_certificate.
Print Assumptions distance_between_neighboring_elements_le_max_distance_in_seq_correspondence_certificate.
Print Assumptions max_distance_in_seq_le_last_element_of_seq_correspondence_certificate.
Print Assumptions last_seq_minus_last_distance_seq_correspondence_certificate.
Print Assumptions max_distance_in_nontrivial_seq_is_positive_correspondence_certificate.
Print Assumptions domination_of_distances_implies_domination_of_seq_correspondence_certificate.
Print Assumptions function_of_distances_is_correct_correspondence_certificate.
Print Assumptions size_of_seq_of_distances_correspondence_certificate.
Print Assumptions nodup_sort_2cons_lt_correspondence_certificate.
Print Assumptions last0_undup_correspondence_certificate.
Print Assumptions nondecreasing_sequence_undup_correspondence_certificate.
Print Assumptions undup_nth_le_correspondence_certificate.
Print Assumptions distances_positive_undup_correspondence_certificate.
Print Assumptions nodup_sort_2cons_eq_correspondence_certificate.
