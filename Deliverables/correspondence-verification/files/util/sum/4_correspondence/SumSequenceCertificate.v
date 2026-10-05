From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq fintype bigop path.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedSumSequence.
From FoundationCertificates Require Import
  PropSPropFoundation LogicalRelation SubadditivityNatCorrespondence
  SumSequenceCorrespondence.
From prosa Require Import GeneratedSumSequenceSource.

(** Exact structural target propositions at the approved
    [eqType -> carrier Type + canonical DecidableEq] boundary.  A separate
    type-audit module binds each proposition to the actual freshly imported
    theorem constant. *)

Definition ss_target_sum_nat_eq0_nat_statement : SProp :=
  forall (T : eqType) (r : ImportedSumSequence.List T)
    (P : T -> ImportedSumSequence.Bool) (F : T -> Lean.Nat),
  Lean.eq
    (ss_target_decide_nat_eq (ss_target_sumFiltered r P F) ss_target_zero)
    (ss_target_all r
      (fun x => ImportedSumSequence.Bool_or
        (ImportedSumSequence.Bool_not (P x))
        (ss_target_decide_nat_eq (F x) ss_target_zero))).

Definition ss_target_sum_nat_gt0_statement : SProp :=
  forall (T : eqType) (r : ImportedSumSequence.List T)
    (P : T -> ImportedSumSequence.Bool) (F : T -> Lean.Nat),
  Lean.eq
    (ss_target_decide_lt ss_target_zero (ss_target_sumFiltered r P F))
    (ss_target_any r
      (fun x => ImportedSumSequence.Bool_and (P x)
        (ss_target_decide_lt ss_target_zero (F x)))).

Definition ss_target_sum_majorant_constant_statement : SProp :=
  forall (T : eqType) (r : ImportedSumSequence.List T)
    (P : T -> ImportedSumSequence.Bool) (F : T -> Lean.Nat)
    (c : Lean.Nat),
  (forall a, ss_target_mem a r ->
    Lean.eq (P a) ImportedSumSequence.Bool_true ->
    ss_target_le (F a) c) ->
  ss_target_le (ss_target_sumFiltered r P F)
    (ss_target_mul c (ss_target_length (ss_target_filter P r))).

Definition ss_target_bigmax_leq_sum_statement : SProp :=
  forall (T : eqType) (r : ImportedSumSequence.List T)
    (P : T -> ImportedSumSequence.Bool) (F : T -> Lean.Nat),
  ss_target_le (ss_target_maxFiltered r P F)
    (ss_target_sumFiltered r P F).

Definition ss_target_sum_le_subseq_statement : SProp :=
  forall (T : eqType) (P : T -> ImportedSumSequence.Bool)
    (F : T -> Lean.Nat) (r1 r2 : ImportedSumSequence.List T),
  Lean.eq (ss_target_subseqb T r1 r2) ImportedSumSequence.Bool_true ->
  ss_target_le (ss_target_sumFiltered r1 P F)
    (ss_target_sumFiltered r2 P F).

Definition ss_target_leq_sum_subseq_statement : SProp :=
  forall (T : eqType) (r r' : ImportedSumSequence.List T)
    (P : T -> ImportedSumSequence.Bool) (F : T -> Lean.Nat),
  Lean.eq (ss_target_subseqb T r r') ImportedSumSequence.Bool_true ->
  ss_target_le (ss_target_sumFiltered r P F)
    (ss_target_sumFiltered r' P F).

Definition ss_target_leq_sum_seq_statement : SProp :=
  forall (T : eqType) (r : ImportedSumSequence.List T)
    (P : T -> ImportedSumSequence.Bool)
    (E1 E2 : T -> Lean.Nat),
  (forall i, ss_target_mem i r ->
    Lean.eq (P i) ImportedSumSequence.Bool_true ->
    ss_target_le (E1 i) (E2 i)) ->
  ss_target_le (ss_target_sumFiltered r P E1)
    (ss_target_sumFiltered r P E2).

Definition ss_target_eq_sum_seq_statement : SProp :=
  forall (T : eqType) (r : ImportedSumSequence.List T)
    (P : T -> ImportedSumSequence.Bool)
    (E1 E2 : T -> Lean.Nat),
  (forall i, ss_target_mem i r ->
    Lean.eq (P i) ImportedSumSequence.Bool_true ->
    Lean.eq (ss_target_decide_nat_eq (E1 i) (E2 i))
      ImportedSumSequence.Bool_true) ->
  Lean.eq (ss_target_sumFiltered r P E1)
    (ss_target_sumFiltered r P E2).

Definition ss_target_leq_sum_seq_pred_statement : SProp :=
  forall (T : eqType) (r : ImportedSumSequence.List T)
    (E : T -> Lean.Nat)
    (P1 P2 : T -> ImportedSumSequence.Bool),
  (forall i, ss_target_mem i r ->
    Lean.eq (P1 i) ImportedSumSequence.Bool_true ->
    Lean.eq (P2 i) ImportedSumSequence.Bool_true) ->
  ss_target_le (ss_target_sumFiltered r P1 E)
    (ss_target_sumFiltered r P2 E).

Definition ss_target_ltn_sum_leq_seq_statement : SProp :=
  forall (T : eqType) (r : ImportedSumSequence.List T)
    (P : T -> ImportedSumSequence.Bool)
    (E1 E2 : T -> Lean.Nat) (j : T),
  ss_target_mem j r ->
  Lean.eq (P j) ImportedSumSequence.Bool_true ->
  ss_target_lt (E1 j) (E2 j) ->
  (forall i, ss_target_mem i r ->
    Lean.eq (P i) ImportedSumSequence.Bool_true ->
    ss_target_le (E1 i) (E2 i)) ->
  ss_target_lt (ss_target_sumFiltered r P E1)
    (ss_target_sumFiltered r P E2).

Definition ss_target_eq_sum_leq_seq_statement : SProp :=
  forall (T : eqType) (r : ImportedSumSequence.List T)
    (P : T -> ImportedSumSequence.Bool)
    (E1 E2 : T -> Lean.Nat),
  (forall i, ss_target_mem i r ->
    Lean.eq (P i) ImportedSumSequence.Bool_true ->
    ss_target_le (E1 i) (E2 i)) ->
  Lean.eq
    (ss_target_decide_nat_eq
      (ss_target_sumFiltered r P E1) (ss_target_sumFiltered r P E2))
    (ss_target_all r
      (fun x => ImportedSumSequence.Bool_or
        (ImportedSumSequence.Bool_not (P x))
        (ss_target_decide_nat_eq (E1 x) (E2 x)))).

Definition ss_target_leq_sum_sub_uniq_statement : SProp :=
  forall (T : eqType) (r : ImportedSumSequence.List T)
    (F : T -> Lean.Nat) (rs : ImportedSumSequence.List T),
  ImportedSumSequence.List_Nodup T r ->
  (forall x, ss_target_mem x r -> ss_target_mem x rs) ->
  ss_target_le (ss_target_sumSeq r F) (ss_target_sumSeq rs F).

Definition ss_target_sum_split_statement : SProp :=
  forall (T : eqType) (r : ImportedSumSequence.List T)
    (P : T -> ImportedSumSequence.Bool) (F : T -> Lean.Nat)
    (Q R : T -> ImportedSumSequence.Bool),
  (forall x, Lean.eq (P x)
    (ImportedSumSequence.Bool_or (Q x) (R x))) ->
  (forall x,
    Lean.eq
      (ImportedSumSequence.Bool_not
        (ss_target_decide_bool_true
          (ImportedSumSequence.Bool_and (Q x) (R x))))
      ImportedSumSequence.Bool_true) ->
  Lean.eq (ss_target_sumFiltered r P F)
    (ss_target_add (ss_target_sumFiltered r Q F)
      (ss_target_sumFiltered r R F)).

Definition ss_target_sum_over_partitions_le_statement : SProp :=
  forall (X Y : eqType) (xToY : X -> Y)
    (f : X -> Lean.Nat) (P : X -> ImportedSumSequence.Bool)
    (xs : ImportedSumSequence.List X) (ys : ImportedSumSequence.List Y),
  (forall x, ss_target_mem x xs ->
    Lean.eq (P x) ImportedSumSequence.Bool_true ->
    ss_target_mem (xToY x) ys) ->
  ss_target_le (ss_target_sumFiltered xs P f)
    (ss_target_sumOverPartitions X Y xToY f P xs ys).

Definition ss_target_reorder_summation_statement : SProp :=
  forall (X Y : eqType) (xToY : X -> Y)
    (f : X -> Lean.Nat) (P : X -> ImportedSumSequence.Bool)
    (xs : ImportedSumSequence.List X) (ys : ImportedSumSequence.List Y),
  (forall x, ss_target_mem x xs ->
    Lean.eq (P x) ImportedSumSequence.Bool_true ->
    ss_target_mem (xToY x) ys) ->
  forall y',
  ss_target_le
    (ss_target_sumFiltered xs
      (fun x => ImportedSumSequence.Bool_and (P x)
        (ss_target_decide_ne Y (xToY x) y')) f)
    (ss_target_sumOverPartitions X Y xToY f P xs
      (ss_target_filter (fun y => ss_target_decide_ne Y y y') ys)).

Definition ss_target_sum_over_partitions_eq_statement : SProp :=
  forall (X Y : eqType) (xToY : X -> Y)
    (f : X -> Lean.Nat) (P : X -> ImportedSumSequence.Bool)
    (xs : ImportedSumSequence.List X) (ys : ImportedSumSequence.List Y),
  (forall x, ss_target_mem x xs ->
    Lean.eq (P x) ImportedSumSequence.Bool_true ->
    ss_target_mem (xToY x) ys) ->
  ImportedSumSequence.List_Nodup X xs ->
  ImportedSumSequence.List_Nodup Y ys ->
  Lean.eq (ss_target_sumFiltered xs P f)
    (ss_target_sumOverPartitions X Y xToY f P xs ys).

Definition ss_target_sum_leq_mono_statement : SProp :=
  forall (I : eqType) (P : I -> ImportedSumSequence.Bool)
    (F : I -> Lean.Nat -> Lean.Nat) (r : ImportedSumSequence.List I),
  (forall i, ss_target_mem i r -> ss_target_monotone (F i)) ->
  ss_target_monotone
    (fun x => ss_target_sumFiltered r P (fun i => F i x)).

Definition ss_target_sum_unit1_statement : SProp :=
  forall F : ImportedSumSequence.Unit -> Lean.Nat,
  Lean.eq (ss_target_unit_sum F) (F ImportedSumSequence.Unit_unit).

Definition ss_target_sum_ge_2_seq_statement : SProp :=
  forall (T : eqType) (xs : ImportedSumSequence.List T)
    (p : T -> Lean.Nat),
  ImportedSumSequence.List_Nodup T xs ->
  (forall x, ss_target_mem x xs -> ss_target_le (p x) ss_target_one) ->
  ss_target_le ss_target_two (ss_target_sumSeq xs p) ->
  ImportedSumSequence.Exists T (fun x1 =>
    ImportedSumSequence.Exists T (fun x2 =>
      Lean.And
        (Lean.eq (ss_target_decide_ne T x1 x2)
          ImportedSumSequence.Bool_true)
        (Lean.And (ss_target_mem x1 xs)
          (Lean.And (ss_target_mem x2 xs)
            (Lean.And
              (Lean.eq (ss_target_decide_nat_eq (p x1) ss_target_one)
                ImportedSumSequence.Bool_true)
              (Lean.eq (ss_target_decide_nat_eq (p x2) ss_target_one)
                ImportedSumSequence.Bool_true)))))).

Theorem sum_nat_eq0_nat_statement_certificate :
  PropSPropRel GeneratedSumSequenceSource.statement_sum_nat_eq0_nat
    ss_target_sum_nat_eq0_nat_statement.
Proof.
  unfold GeneratedSumSequenceSource.statement_sum_nat_eq0_nat,
    ss_target_sum_nat_eq0_nat_statement.
  apply prop_sprop_rel_intro.
  - intros Hsource T rL PL FL.
    pose rR := ss_to_rocq rL.
    pose PR := ss_pred_to_rocq PL.
    pose FR := ss_nat_fun_to_rocq FL.
    have Hr : SsListRel rR rL := ss_list_target_roundtrip rL.
    have HP : SsPredRel PR PL := ss_pred_surjective PL.
    have HF : SsNatFunRel FR FL := ss_nat_fun_surjective FL.
    have Hsum := ss_sumFiltered_related T PR PL FR FL rR rL HP HF Hr.
    have Hlhs := ss_decide_nat_eq_related
      (\sum_(x <- rR | PR x) FR x) (ss_target_sumFiltered rL PL FL)
      0%N ss_target_zero Hsum ss_zero_related.
    have HQ : SsPredRel (fun x => FR x == 0%N)
        (fun x => ss_target_decide_nat_eq (FL x) ss_target_zero) :=
      fun x => ss_decide_nat_eq_related (FR x) (FL x)
        0%N ss_target_zero (HF x) ss_zero_related.
    have Hrhs := ss_all_filter_imp_related T PR (fun x => FR x == 0%N)
      PL (fun x => ss_target_decide_nat_eq (FL x) ss_target_zero)
      rR rL HP HQ Hr.
    exact (prop_to_sprop _ _
      (ss_bool_eq_correspondence _ _ _ _ Hlhs Hrhs)
      (Hsource T rR PR FR)).
  - intro Htarget. apply strictly_inhabits.
    intros T rR PR FR.
    have Hr : SsListRel rR (ss_to_imported rR) := @Lean.eq_refl _ _.
    have HP : SsPredRel PR (ss_pred_to_imported PR) := ss_pred_canonical PR.
    have HF : SsNatFunRel FR (ss_nat_fun_to_imported FR) :=
      ss_nat_fun_canonical FR.
    have Hsum := ss_sumFiltered_related T PR (ss_pred_to_imported PR)
      FR (ss_nat_fun_to_imported FR) rR (ss_to_imported rR) HP HF Hr.
    have Hlhs := ss_decide_nat_eq_related
      (\sum_(x <- rR | PR x) FR x)
      (ss_target_sumFiltered (ss_to_imported rR)
        (ss_pred_to_imported PR) (ss_nat_fun_to_imported FR))
      0%N ss_target_zero Hsum ss_zero_related.
    have HQ : SsPredRel (fun x => FR x == 0%N)
        (fun x => ss_target_decide_nat_eq
          (ss_nat_fun_to_imported FR x) ss_target_zero) :=
      fun x => ss_decide_nat_eq_related (FR x)
        (ss_nat_fun_to_imported FR x) 0%N ss_target_zero
        (HF x) ss_zero_related.
    have Hrhs := ss_all_filter_imp_related T PR (fun x => FR x == 0%N)
      (ss_pred_to_imported PR)
      (fun x => ss_target_decide_nat_eq
        (ss_nat_fun_to_imported FR x) ss_target_zero)
      rR (ss_to_imported rR) HP HQ Hr.
    exact (sprop_to_prop _ _
      (ss_bool_eq_correspondence _ _ _ _ Hlhs Hrhs)
      (Htarget T (ss_to_imported rR) (ss_pred_to_imported PR)
        (ss_nat_fun_to_imported FR))).
Qed.

Theorem sum_nat_gt0_statement_certificate :
  PropSPropRel GeneratedSumSequenceSource.statement_sum_nat_gt0
    ss_target_sum_nat_gt0_statement.
Proof.
  unfold GeneratedSumSequenceSource.statement_sum_nat_gt0,
    ss_target_sum_nat_gt0_statement.
  apply prop_sprop_rel_intro.
  - intros Hsource T rL PL FL.
    pose rR := ss_to_rocq rL.
    pose PR := ss_pred_to_rocq PL.
    pose FR := ss_nat_fun_to_rocq FL.
    have Hr : SsListRel rR rL := ss_list_target_roundtrip rL.
    have HP : SsPredRel PR PL := ss_pred_surjective PL.
    have HF : SsNatFunRel FR FL := ss_nat_fun_surjective FL.
    have Hsum := ss_sumFiltered_related T PR PL FR FL rR rL HP HF Hr.
    have Hlhs := ss_decide_lt_related 0%N ss_target_zero
      (\sum_(x <- rR | PR x) FR x) (ss_target_sumFiltered rL PL FL)
      ss_zero_related Hsum.
    have HQ : SsPredRel (fun x => ltn 0%N (FR x))
        (fun x => ss_target_decide_lt ss_target_zero (FL x)) :=
      fun x => ss_decide_lt_related 0%N ss_target_zero
        (FR x) (FL x) ss_zero_related (HF x).
    have Hrhs := ss_any_filter_and_related T PR (fun x => ltn 0%N (FR x))
      PL (fun x => ss_target_decide_lt ss_target_zero (FL x))
      rR rL HP HQ Hr.
    exact (prop_to_sprop _ _
      (ss_bool_eq_correspondence _ _ _ _ Hlhs Hrhs)
      (Hsource T rR PR FR)).
  - intro Htarget. apply strictly_inhabits.
    intros T rR PR FR.
    have Hr : SsListRel rR (ss_to_imported rR) := @Lean.eq_refl _ _.
    have HP : SsPredRel PR (ss_pred_to_imported PR) := ss_pred_canonical PR.
    have HF : SsNatFunRel FR (ss_nat_fun_to_imported FR) :=
      ss_nat_fun_canonical FR.
    have Hsum := ss_sumFiltered_related T PR (ss_pred_to_imported PR)
      FR (ss_nat_fun_to_imported FR) rR (ss_to_imported rR) HP HF Hr.
    have Hlhs := ss_decide_lt_related 0%N ss_target_zero
      (\sum_(x <- rR | PR x) FR x)
      (ss_target_sumFiltered (ss_to_imported rR)
        (ss_pred_to_imported PR) (ss_nat_fun_to_imported FR))
      ss_zero_related Hsum.
    have HQ : SsPredRel (fun x => ltn 0%N (FR x))
        (fun x => ss_target_decide_lt ss_target_zero
          (ss_nat_fun_to_imported FR x)) :=
      fun x => ss_decide_lt_related 0%N ss_target_zero
        (FR x) (ss_nat_fun_to_imported FR x)
        ss_zero_related (HF x).
    have Hrhs := ss_any_filter_and_related T PR (fun x => ltn 0%N (FR x))
      (ss_pred_to_imported PR)
      (fun x => ss_target_decide_lt ss_target_zero
        (ss_nat_fun_to_imported FR x))
      rR (ss_to_imported rR) HP HQ Hr.
    exact (sprop_to_prop _ _
      (ss_bool_eq_correspondence _ _ _ _ Hlhs Hrhs)
      (Htarget T (ss_to_imported rR) (ss_pred_to_imported PR)
        (ss_nat_fun_to_imported FR))).
Qed.

Theorem sum_majorant_constant_statement_certificate :
  PropSPropRel GeneratedSumSequenceSource.statement_sum_majorant_constant
    ss_target_sum_majorant_constant_statement.
Proof.
  unfold GeneratedSumSequenceSource.statement_sum_majorant_constant,
    ss_target_sum_majorant_constant_statement.
  apply prop_sprop_rel_intro.
  - intros Hsource T rL PL FL cL HboundL.
    pose rR := ss_to_rocq rL.
    pose PR := ss_pred_to_rocq PL.
    pose FR := ss_nat_fun_to_rocq FL.
    pose cR := sub_nat_to_rocq cL.
    have Hr : SsListRel rR rL := ss_list_target_roundtrip rL.
    have HP : SsPredRel PR PL := ss_pred_surjective PL.
    have HF : SsNatFunRel FR FL := ss_nat_fun_surjective FL.
    have Hc : SubNatRel cR cL := sub_nat_rel_surjective cL.
    have Hconst : SsNatFunRel (fun _ : T => cR) (fun _ : T => cL) :=
      fun _ => Hc.
    have Hpoint := ss_pointwise_le_correspondence T rR rL PR PL
      FR (fun _ => cR) FL (fun _ => cL) Hr HP HF Hconst.
    have HsourceBound := sprop_to_prop _ _ Hpoint HboundL.
    have Hsum := ss_sumFiltered_related T PR PL FR FL rR rL HP HF Hr.
    have Hfilter := ss_filter_related T PR PL rR rL HP Hr.
    have Hlen := ss_length_related T _ _ Hfilter.
    have Hmul := ss_mul_related cR cL
      (size [seq x <- rR | PR x])
      (ss_target_length (ss_target_filter PL rL)) Hc Hlen.
    exact (prop_to_sprop _ _
      (ss_le_correspondence _ _ _ _ Hsum Hmul)
      (Hsource T rR PR FR cR HsourceBound)).
  - intro Htarget. apply strictly_inhabits.
    intros T rR PR FR cR HboundR.
    have Hr : SsListRel rR (ss_to_imported rR) := @Lean.eq_refl _ _.
    have HP : SsPredRel PR (ss_pred_to_imported PR) := ss_pred_canonical PR.
    have HF : SsNatFunRel FR (ss_nat_fun_to_imported FR) :=
      ss_nat_fun_canonical FR.
    have Hc : SubNatRel cR (sub_nat_to_imported cR) :=
      sub_nat_rel_canonical cR.
    have Hconst : SsNatFunRel (fun _ : T => cR)
        (fun _ : T => sub_nat_to_imported cR) := fun _ => Hc.
    have Hpoint := ss_pointwise_le_correspondence T rR
      (ss_to_imported rR) PR (ss_pred_to_imported PR)
      FR (fun _ => cR) (ss_nat_fun_to_imported FR)
      (fun _ => sub_nat_to_imported cR) Hr HP HF Hconst.
    have HboundL := prop_to_sprop _ _ Hpoint HboundR.
    have Hsum := ss_sumFiltered_related T PR (ss_pred_to_imported PR)
      FR (ss_nat_fun_to_imported FR) rR (ss_to_imported rR) HP HF Hr.
    have Hfilter := ss_filter_related T PR (ss_pred_to_imported PR)
      rR (ss_to_imported rR) HP Hr.
    have Hlen := ss_length_related T _ _ Hfilter.
    have Hmul := ss_mul_related cR (sub_nat_to_imported cR)
      (size [seq x <- rR | PR x])
      (ss_target_length
        (ss_target_filter (ss_pred_to_imported PR) (ss_to_imported rR)))
      Hc Hlen.
    exact (sprop_to_prop _ _
      (ss_le_correspondence _ _ _ _ Hsum Hmul)
      (Htarget T (ss_to_imported rR) (ss_pred_to_imported PR)
        (ss_nat_fun_to_imported FR) (sub_nat_to_imported cR) HboundL)).
Qed.

Theorem bigmax_leq_sum_statement_certificate :
  PropSPropRel GeneratedSumSequenceSource.statement_bigmax_leq_sum
    ss_target_bigmax_leq_sum_statement.
Proof.
  unfold GeneratedSumSequenceSource.statement_bigmax_leq_sum,
    ss_target_bigmax_leq_sum_statement.
  apply prop_sprop_rel_intro.
  - intros Hsource T rL PL FL.
    pose rR := ss_to_rocq rL.
    pose PR := ss_pred_to_rocq PL.
    pose FR := ss_nat_fun_to_rocq FL.
    have Hr : SsListRel rR rL := ss_list_target_roundtrip rL.
    have HP : SsPredRel PR PL := ss_pred_surjective PL.
    have HF : SsNatFunRel FR FL := ss_nat_fun_surjective FL.
    have Hmax := ss_maxFiltered_related T PR PL FR FL rR rL HP HF Hr.
    have Hsum := ss_sumFiltered_related T PR PL FR FL rR rL HP HF Hr.
    exact (prop_to_sprop _ _ (ss_le_correspondence _ _ _ _ Hmax Hsum)
      (Hsource T rR PR FR)).
  - intro Htarget. apply strictly_inhabits.
    intros T rR PR FR.
    have Hr : SsListRel rR (ss_to_imported rR) := @Lean.eq_refl _ _.
    have HP : SsPredRel PR (ss_pred_to_imported PR) := ss_pred_canonical PR.
    have HF : SsNatFunRel FR (ss_nat_fun_to_imported FR) :=
      ss_nat_fun_canonical FR.
    have Hmax := ss_maxFiltered_related T PR (ss_pred_to_imported PR)
      FR (ss_nat_fun_to_imported FR) rR (ss_to_imported rR) HP HF Hr.
    have Hsum := ss_sumFiltered_related T PR (ss_pred_to_imported PR)
      FR (ss_nat_fun_to_imported FR) rR (ss_to_imported rR) HP HF Hr.
    exact (sprop_to_prop _ _ (ss_le_correspondence _ _ _ _ Hmax Hsum)
      (Htarget T (ss_to_imported rR) (ss_pred_to_imported PR)
        (ss_nat_fun_to_imported FR))).
Qed.

Theorem sum_le_subseq_statement_certificate :
  PropSPropRel GeneratedSumSequenceSource.statement_sum_le_subseq
    ss_target_sum_le_subseq_statement.
Proof.
  unfold GeneratedSumSequenceSource.statement_sum_le_subseq,
    ss_target_sum_le_subseq_statement.
  apply prop_sprop_rel_intro.
  - intros Hsource T PL FL r1L r2L.
    pose PR := ss_pred_to_rocq PL.
    pose FR := ss_nat_fun_to_rocq FL.
    pose r1R := ss_to_rocq r1L.
    pose r2R := ss_to_rocq r2L.
    have HP : SsPredRel PR PL := ss_pred_surjective PL.
    have HF : SsNatFunRel FR FL := ss_nat_fun_surjective FL.
    have Hr1 : SsListRel r1R r1L := ss_list_target_roundtrip r1L.
    have Hr2 : SsListRel r2R r2L := ss_list_target_roundtrip r2L.
    exact (prop_to_sprop _ _
      (ss_sum_le_subseq_instance_correspondence T PR PL FR FL
        r1R r2R r1L r2L HP HF Hr1 Hr2)
      (Hsource T PR FR r1R r2R)).
  - intro Htarget. apply strictly_inhabits.
    intros T PR FR r1R r2R.
    have HP : SsPredRel PR (ss_pred_to_imported PR) := ss_pred_canonical PR.
    have HF : SsNatFunRel FR (ss_nat_fun_to_imported FR) :=
      ss_nat_fun_canonical FR.
    have Hr1 : SsListRel r1R (ss_to_imported r1R) := @Lean.eq_refl _ _.
    have Hr2 : SsListRel r2R (ss_to_imported r2R) := @Lean.eq_refl _ _.
    exact (sprop_to_prop _ _
      (ss_sum_le_subseq_instance_correspondence T PR
        (ss_pred_to_imported PR) FR (ss_nat_fun_to_imported FR)
        r1R r2R (ss_to_imported r1R) (ss_to_imported r2R)
        HP HF Hr1 Hr2)
      (Htarget T (ss_pred_to_imported PR) (ss_nat_fun_to_imported FR)
        (ss_to_imported r1R) (ss_to_imported r2R))).
Qed.

Theorem leq_sum_subseq_statement_certificate :
  PropSPropRel GeneratedSumSequenceSource.statement_leq_sum_subseq
    ss_target_leq_sum_subseq_statement.
Proof.
  unfold GeneratedSumSequenceSource.statement_leq_sum_subseq,
    ss_target_leq_sum_subseq_statement.
  apply prop_sprop_rel_intro.
  - intros Hsource T rL rL' PL FL.
    pose rR := ss_to_rocq rL.
    pose rR' := ss_to_rocq rL'.
    pose PR := ss_pred_to_rocq PL.
    pose FR := ss_nat_fun_to_rocq FL.
    have Hr : SsListRel rR rL := ss_list_target_roundtrip rL.
    have Hr' : SsListRel rR' rL' := ss_list_target_roundtrip rL'.
    have HP : SsPredRel PR PL := ss_pred_surjective PL.
    have HF : SsNatFunRel FR FL := ss_nat_fun_surjective FL.
    exact (prop_to_sprop _ _
      (ss_sum_le_subseq_instance_correspondence T PR PL FR FL
        rR rR' rL rL' HP HF Hr Hr')
      (Hsource T rR rR' PR FR)).
  - intro Htarget. apply strictly_inhabits.
    intros T rR rR' PR FR.
    have Hr : SsListRel rR (ss_to_imported rR) := @Lean.eq_refl _ _.
    have Hr' : SsListRel rR' (ss_to_imported rR') := @Lean.eq_refl _ _.
    have HP : SsPredRel PR (ss_pred_to_imported PR) := ss_pred_canonical PR.
    have HF : SsNatFunRel FR (ss_nat_fun_to_imported FR) :=
      ss_nat_fun_canonical FR.
    exact (sprop_to_prop _ _
      (ss_sum_le_subseq_instance_correspondence T PR
        (ss_pred_to_imported PR) FR (ss_nat_fun_to_imported FR)
        rR rR' (ss_to_imported rR) (ss_to_imported rR')
        HP HF Hr Hr')
      (Htarget T (ss_to_imported rR) (ss_to_imported rR')
        (ss_pred_to_imported PR) (ss_nat_fun_to_imported FR))).
Qed.

Theorem leq_sum_seq_statement_certificate :
  PropSPropRel GeneratedSumSequenceSource.statement_leq_sum_seq
    ss_target_leq_sum_seq_statement.
Proof.
  unfold GeneratedSumSequenceSource.statement_leq_sum_seq,
    ss_target_leq_sum_seq_statement.
  apply prop_sprop_rel_intro.
  - intros Hsource T rL PL E1L E2L.
    pose rR := ss_to_rocq rL.
    pose PR := ss_pred_to_rocq PL.
    pose E1R := ss_nat_fun_to_rocq E1L.
    pose E2R := ss_nat_fun_to_rocq E2L.
    have Hr : SsListRel rR rL := ss_list_target_roundtrip rL.
    have HP : SsPredRel PR PL := ss_pred_surjective PL.
    have HE1 : SsNatFunRel E1R E1L := ss_nat_fun_surjective E1L.
    have HE2 : SsNatFunRel E2R E2L := ss_nat_fun_surjective E2L.
    exact (prop_to_sprop _ _
      (ss_leq_sum_seq_instance_correspondence T rR rL PR PL
        E1R E2R E1L E2L Hr HP HE1 HE2)
      (Hsource T rR PR E1R E2R)).
  - intro Htarget. apply strictly_inhabits.
    intros T rR PR E1R E2R.
    have Hr : SsListRel rR (ss_to_imported rR) := @Lean.eq_refl _ _.
    have HP : SsPredRel PR (ss_pred_to_imported PR) := ss_pred_canonical PR.
    have HE1 : SsNatFunRel E1R (ss_nat_fun_to_imported E1R) :=
      ss_nat_fun_canonical E1R.
    have HE2 : SsNatFunRel E2R (ss_nat_fun_to_imported E2R) :=
      ss_nat_fun_canonical E2R.
    exact (sprop_to_prop _ _
      (ss_leq_sum_seq_instance_correspondence T rR (ss_to_imported rR)
        PR (ss_pred_to_imported PR) E1R E2R
        (ss_nat_fun_to_imported E1R) (ss_nat_fun_to_imported E2R)
        Hr HP HE1 HE2)
      (Htarget T (ss_to_imported rR) (ss_pred_to_imported PR)
        (ss_nat_fun_to_imported E1R) (ss_nat_fun_to_imported E2R))).
Qed.

Theorem eq_sum_seq_statement_certificate :
  PropSPropRel GeneratedSumSequenceSource.statement_eq_sum_seq
    ss_target_eq_sum_seq_statement.
Proof.
  unfold GeneratedSumSequenceSource.statement_eq_sum_seq,
    ss_target_eq_sum_seq_statement.
  apply prop_sprop_rel_intro.
  - intros Hsource T rL PL E1L E2L.
    pose rR := ss_to_rocq rL.
    pose PR := ss_pred_to_rocq PL.
    pose E1R := ss_nat_fun_to_rocq E1L.
    pose E2R := ss_nat_fun_to_rocq E2L.
    have Hr : SsListRel rR rL := ss_list_target_roundtrip rL.
    have HP : SsPredRel PR PL := ss_pred_surjective PL.
    have HE1 : SsNatFunRel E1R E1L := ss_nat_fun_surjective E1L.
    have HE2 : SsNatFunRel E2R E2L := ss_nat_fun_surjective E2L.
    exact (prop_to_sprop _ _
      (ss_eq_sum_seq_instance_correspondence T rR rL PR PL
        E1R E2R E1L E2L Hr HP HE1 HE2)
      (Hsource T rR PR E1R E2R)).
  - intro Htarget. apply strictly_inhabits.
    intros T rR PR E1R E2R.
    have Hr : SsListRel rR (ss_to_imported rR) := @Lean.eq_refl _ _.
    have HP : SsPredRel PR (ss_pred_to_imported PR) := ss_pred_canonical PR.
    have HE1 : SsNatFunRel E1R (ss_nat_fun_to_imported E1R) :=
      ss_nat_fun_canonical E1R.
    have HE2 : SsNatFunRel E2R (ss_nat_fun_to_imported E2R) :=
      ss_nat_fun_canonical E2R.
    exact (sprop_to_prop _ _
      (ss_eq_sum_seq_instance_correspondence T rR (ss_to_imported rR)
        PR (ss_pred_to_imported PR) E1R E2R
        (ss_nat_fun_to_imported E1R) (ss_nat_fun_to_imported E2R)
        Hr HP HE1 HE2)
      (Htarget T (ss_to_imported rR) (ss_pred_to_imported PR)
        (ss_nat_fun_to_imported E1R) (ss_nat_fun_to_imported E2R))).
Qed.

Theorem leq_sum_seq_pred_statement_certificate :
  PropSPropRel GeneratedSumSequenceSource.statement_leq_sum_seq_pred
    ss_target_leq_sum_seq_pred_statement.
Proof.
  unfold GeneratedSumSequenceSource.statement_leq_sum_seq_pred,
    ss_target_leq_sum_seq_pred_statement.
  apply prop_sprop_rel_intro.
  - intros Hsource T rL EL P1L P2L.
    pose rR := ss_to_rocq rL.
    pose ER := ss_nat_fun_to_rocq EL.
    pose P1R := ss_pred_to_rocq P1L.
    pose P2R := ss_pred_to_rocq P2L.
    have Hr : SsListRel rR rL := ss_list_target_roundtrip rL.
    have HE : SsNatFunRel ER EL := ss_nat_fun_surjective EL.
    have HP1 : SsPredRel P1R P1L := ss_pred_surjective P1L.
    have HP2 : SsPredRel P2R P2L := ss_pred_surjective P2L.
    exact (prop_to_sprop _ _
      (ss_leq_sum_seq_pred_instance_correspondence T rR rL ER EL
        P1R P2R P1L P2L Hr HE HP1 HP2)
      (Hsource T rR ER P1R P2R)).
  - intro Htarget. apply strictly_inhabits.
    intros T rR ER P1R P2R.
    have Hr : SsListRel rR (ss_to_imported rR) := @Lean.eq_refl _ _.
    have HE : SsNatFunRel ER (ss_nat_fun_to_imported ER) :=
      ss_nat_fun_canonical ER.
    have HP1 : SsPredRel P1R (ss_pred_to_imported P1R) :=
      ss_pred_canonical P1R.
    have HP2 : SsPredRel P2R (ss_pred_to_imported P2R) :=
      ss_pred_canonical P2R.
    exact (sprop_to_prop _ _
      (ss_leq_sum_seq_pred_instance_correspondence T rR
        (ss_to_imported rR) ER (ss_nat_fun_to_imported ER)
        P1R P2R (ss_pred_to_imported P1R) (ss_pred_to_imported P2R)
        Hr HE HP1 HP2)
      (Htarget T (ss_to_imported rR) (ss_nat_fun_to_imported ER)
        (ss_pred_to_imported P1R) (ss_pred_to_imported P2R))).
Qed.

Theorem ltn_sum_leq_seq_statement_certificate :
  PropSPropRel GeneratedSumSequenceSource.statement_ltn_sum_leq_seq
    ss_target_ltn_sum_leq_seq_statement.
Proof.
  unfold GeneratedSumSequenceSource.statement_ltn_sum_leq_seq,
    ss_target_ltn_sum_leq_seq_statement.
  apply prop_sprop_rel_intro.
  - intros Hsource T rL PL E1L E2L j.
    pose rR := ss_to_rocq rL.
    pose PR := ss_pred_to_rocq PL.
    pose E1R := ss_nat_fun_to_rocq E1L.
    pose E2R := ss_nat_fun_to_rocq E2L.
    have Hr : SsListRel rR rL := ss_list_target_roundtrip rL.
    have HP : SsPredRel PR PL := ss_pred_surjective PL.
    have HE1 : SsNatFunRel E1R E1L := ss_nat_fun_surjective E1L.
    have HE2 : SsNatFunRel E2R E2L := ss_nat_fun_surjective E2L.
    exact (prop_to_sprop _ _
      (ss_ltn_sum_leq_seq_instance_correspondence T rR rL PR PL
        E1R E2R E1L E2L j Hr HP HE1 HE2)
      (Hsource T rR PR E1R E2R j)).
  - intro Htarget. apply strictly_inhabits.
    intros T rR PR E1R E2R j.
    have Hr : SsListRel rR (ss_to_imported rR) := @Lean.eq_refl _ _.
    have HP : SsPredRel PR (ss_pred_to_imported PR) := ss_pred_canonical PR.
    have HE1 : SsNatFunRel E1R (ss_nat_fun_to_imported E1R) :=
      ss_nat_fun_canonical E1R.
    have HE2 : SsNatFunRel E2R (ss_nat_fun_to_imported E2R) :=
      ss_nat_fun_canonical E2R.
    exact (sprop_to_prop _ _
      (ss_ltn_sum_leq_seq_instance_correspondence T rR
        (ss_to_imported rR) PR (ss_pred_to_imported PR)
        E1R E2R (ss_nat_fun_to_imported E1R)
        (ss_nat_fun_to_imported E2R) j Hr HP HE1 HE2)
      (Htarget T (ss_to_imported rR) (ss_pred_to_imported PR)
        (ss_nat_fun_to_imported E1R) (ss_nat_fun_to_imported E2R) j)).
Qed.

Theorem eq_sum_leq_seq_statement_certificate :
  PropSPropRel GeneratedSumSequenceSource.statement_eq_sum_leq_seq
    ss_target_eq_sum_leq_seq_statement.
Proof.
  unfold GeneratedSumSequenceSource.statement_eq_sum_leq_seq,
    ss_target_eq_sum_leq_seq_statement.
  apply prop_sprop_rel_intro.
  - intros Hsource T rL PL E1L E2L.
    pose rR := ss_to_rocq rL.
    pose PR := ss_pred_to_rocq PL.
    pose E1R := ss_nat_fun_to_rocq E1L.
    pose E2R := ss_nat_fun_to_rocq E2L.
    have Hr : SsListRel rR rL := ss_list_target_roundtrip rL.
    have HP : SsPredRel PR PL := ss_pred_surjective PL.
    have HE1 : SsNatFunRel E1R E1L := ss_nat_fun_surjective E1L.
    have HE2 : SsNatFunRel E2R E2L := ss_nat_fun_surjective E2L.
    exact (prop_to_sprop _ _
      (ss_eq_sum_leq_seq_instance_correspondence T rR rL PR PL
        E1R E2R E1L E2L Hr HP HE1 HE2)
      (Hsource T rR PR E1R E2R)).
  - intro Htarget. apply strictly_inhabits.
    intros T rR PR E1R E2R.
    have Hr : SsListRel rR (ss_to_imported rR) := @Lean.eq_refl _ _.
    have HP : SsPredRel PR (ss_pred_to_imported PR) := ss_pred_canonical PR.
    have HE1 : SsNatFunRel E1R (ss_nat_fun_to_imported E1R) :=
      ss_nat_fun_canonical E1R.
    have HE2 : SsNatFunRel E2R (ss_nat_fun_to_imported E2R) :=
      ss_nat_fun_canonical E2R.
    exact (sprop_to_prop _ _
      (ss_eq_sum_leq_seq_instance_correspondence T rR
        (ss_to_imported rR) PR (ss_pred_to_imported PR)
        E1R E2R (ss_nat_fun_to_imported E1R)
        (ss_nat_fun_to_imported E2R) Hr HP HE1 HE2)
      (Htarget T (ss_to_imported rR) (ss_pred_to_imported PR)
        (ss_nat_fun_to_imported E1R) (ss_nat_fun_to_imported E2R))).
Qed.

Theorem leq_sum_sub_uniq_statement_certificate :
  PropSPropRel GeneratedSumSequenceSource.statement_leq_sum_sub_uniq
    ss_target_leq_sum_sub_uniq_statement.
Proof.
  unfold GeneratedSumSequenceSource.statement_leq_sum_sub_uniq,
    ss_target_leq_sum_sub_uniq_statement.
  apply prop_sprop_rel_intro.
  - intros Hsource T rL FL rsL.
    pose rR := ss_to_rocq rL.
    pose rsR := ss_to_rocq rsL.
    pose FR := ss_nat_fun_to_rocq FL.
    have Hr : SsListRel rR rL := ss_list_target_roundtrip rL.
    have Hrs : SsListRel rsR rsL := ss_list_target_roundtrip rsL.
    have HF : SsNatFunRel FR FL := ss_nat_fun_surjective FL.
    exact (prop_to_sprop _ _
      (ss_leq_sum_sub_uniq_instance_correspondence T rR rsR rL rsL
        FR FL Hr Hrs HF)
      (Hsource T rR FR rsR)).
  - intro Htarget. apply strictly_inhabits.
    intros T rR FR rsR.
    have Hr : SsListRel rR (ss_to_imported rR) := @Lean.eq_refl _ _.
    have Hrs : SsListRel rsR (ss_to_imported rsR) := @Lean.eq_refl _ _.
    have HF : SsNatFunRel FR (ss_nat_fun_to_imported FR) :=
      ss_nat_fun_canonical FR.
    exact (sprop_to_prop _ _
      (ss_leq_sum_sub_uniq_instance_correspondence T rR rsR
        (ss_to_imported rR) (ss_to_imported rsR)
        FR (ss_nat_fun_to_imported FR) Hr Hrs HF)
      (Htarget T (ss_to_imported rR) (ss_nat_fun_to_imported FR)
        (ss_to_imported rsR))).
Qed.

Theorem sum_split_exhaustive_mutually_exclusive_preds_statement_certificate :
  PropSPropRel
    GeneratedSumSequenceSource.statement_sum_split_exhaustive_mutually_exclusive_preds
    ss_target_sum_split_statement.
Proof.
  unfold
    GeneratedSumSequenceSource.statement_sum_split_exhaustive_mutually_exclusive_preds,
    ss_target_sum_split_statement.
  apply prop_sprop_rel_intro.
  - intros Hsource T rL PL FL QL RL.
    pose rR := ss_to_rocq rL.
    pose PR := ss_pred_to_rocq PL.
    pose QR := ss_pred_to_rocq QL.
    pose RR := ss_pred_to_rocq RL.
    pose FR := ss_nat_fun_to_rocq FL.
    have Hr : SsListRel rR rL := ss_list_target_roundtrip rL.
    have HP : SsPredRel PR PL := ss_pred_surjective PL.
    have HQ : SsPredRel QR QL := ss_pred_surjective QL.
    have HR : SsPredRel RR RL := ss_pred_surjective RL.
    have HF : SsNatFunRel FR FL := ss_nat_fun_surjective FL.
    exact (prop_to_sprop _ _
      (ss_sum_split_instance_correspondence T rR rL
        PR QR RR PL QL RL FR FL Hr HP HQ HR HF)
      (Hsource T rR PR FR QR RR)).
  - intro Htarget. apply strictly_inhabits.
    intros T rR PR FR QR RR.
    have Hr : SsListRel rR (ss_to_imported rR) := @Lean.eq_refl _ _.
    have HP : SsPredRel PR (ss_pred_to_imported PR) := ss_pred_canonical PR.
    have HQ : SsPredRel QR (ss_pred_to_imported QR) := ss_pred_canonical QR.
    have HR : SsPredRel RR (ss_pred_to_imported RR) := ss_pred_canonical RR.
    have HF : SsNatFunRel FR (ss_nat_fun_to_imported FR) :=
      ss_nat_fun_canonical FR.
    exact (sprop_to_prop _ _
      (ss_sum_split_instance_correspondence T rR (ss_to_imported rR)
        PR QR RR (ss_pred_to_imported PR) (ss_pred_to_imported QR)
        (ss_pred_to_imported RR) FR (ss_nat_fun_to_imported FR)
        Hr HP HQ HR HF)
      (Htarget T (ss_to_imported rR) (ss_pred_to_imported PR)
        (ss_nat_fun_to_imported FR) (ss_pred_to_imported QR)
        (ss_pred_to_imported RR))).
Qed.

Theorem sum_over_partitions_le_statement_certificate :
  PropSPropRel GeneratedSumSequenceSource.statement_sum_over_partitions_le
    ss_target_sum_over_partitions_le_statement.
Proof.
  unfold GeneratedSumSequenceSource.statement_sum_over_partitions_le,
    ss_target_sum_over_partitions_le_statement.
  apply prop_sprop_rel_intro.
  - intros Hsource X Y xToY fL PL xsL ysL.
    pose fR := ss_nat_fun_to_rocq fL.
    pose PR := ss_pred_to_rocq PL.
    pose xsR := ss_to_rocq xsL.
    pose ysR := ss_to_rocq ysL.
    have Hf : SsNatFunRel fR fL := ss_nat_fun_surjective fL.
    have HP : SsPredRel PR PL := ss_pred_surjective PL.
    have Hxs : SsListRel xsR xsL := ss_list_target_roundtrip xsL.
    have Hys : SsListRel ysR ysL := ss_list_target_roundtrip ysL.
    exact (prop_to_sprop _ _
      (ss_sum_over_partitions_le_instance_correspondence X Y xToY
        fR fL PR PL xsR xsL ysR ysL Hf HP Hxs Hys)
      (Hsource X Y xToY fR PR xsR ysR)).
  - intro Htarget. apply strictly_inhabits.
    intros X Y xToY fR PR xsR ysR.
    have Hf : SsNatFunRel fR (ss_nat_fun_to_imported fR) :=
      ss_nat_fun_canonical fR.
    have HP : SsPredRel PR (ss_pred_to_imported PR) :=
      ss_pred_canonical PR.
    have Hxs : SsListRel xsR (ss_to_imported xsR) := @Lean.eq_refl _ _.
    have Hys : SsListRel ysR (ss_to_imported ysR) := @Lean.eq_refl _ _.
    exact (sprop_to_prop _ _
      (ss_sum_over_partitions_le_instance_correspondence X Y xToY
        fR (ss_nat_fun_to_imported fR) PR (ss_pred_to_imported PR)
        xsR (ss_to_imported xsR) ysR (ss_to_imported ysR)
        Hf HP Hxs Hys)
      (Htarget X Y xToY (ss_nat_fun_to_imported fR)
        (ss_pred_to_imported PR) (ss_to_imported xsR)
        (ss_to_imported ysR))).
Qed.

Theorem reorder_summation_statement_certificate :
  PropSPropRel GeneratedSumSequenceSource.statement_reorder_summation
    ss_target_reorder_summation_statement.
Proof.
  unfold GeneratedSumSequenceSource.statement_reorder_summation,
    ss_target_reorder_summation_statement.
  apply prop_sprop_rel_intro.
  - intros Hsource X Y xToY fL PL xsL ysL.
    pose fR := ss_nat_fun_to_rocq fL.
    pose PR := ss_pred_to_rocq PL.
    pose xsR := ss_to_rocq xsL.
    pose ysR := ss_to_rocq ysL.
    have Hf : SsNatFunRel fR fL := ss_nat_fun_surjective fL.
    have HP : SsPredRel PR PL := ss_pred_surjective PL.
    have Hxs : SsListRel xsR xsL := ss_list_target_roundtrip xsL.
    have Hys : SsListRel ysR ysL := ss_list_target_roundtrip ysL.
    exact (prop_to_sprop _ _
      (ss_reorder_summation_instance_correspondence X Y xToY
        fR fL PR PL xsR xsL ysR ysL Hf HP Hxs Hys)
      (Hsource X Y xToY fR PR xsR ysR)).
  - intro Htarget. apply strictly_inhabits.
    intros X Y xToY fR PR xsR ysR.
    have Hf : SsNatFunRel fR (ss_nat_fun_to_imported fR) :=
      ss_nat_fun_canonical fR.
    have HP : SsPredRel PR (ss_pred_to_imported PR) :=
      ss_pred_canonical PR.
    have Hxs : SsListRel xsR (ss_to_imported xsR) := @Lean.eq_refl _ _.
    have Hys : SsListRel ysR (ss_to_imported ysR) := @Lean.eq_refl _ _.
    exact (sprop_to_prop _ _
      (ss_reorder_summation_instance_correspondence X Y xToY
        fR (ss_nat_fun_to_imported fR) PR (ss_pred_to_imported PR)
        xsR (ss_to_imported xsR) ysR (ss_to_imported ysR)
        Hf HP Hxs Hys)
      (Htarget X Y xToY (ss_nat_fun_to_imported fR)
        (ss_pred_to_imported PR) (ss_to_imported xsR)
        (ss_to_imported ysR))).
Qed.

Theorem sum_over_partitions_eq_statement_certificate :
  PropSPropRel GeneratedSumSequenceSource.statement_sum_over_partitions_eq
    ss_target_sum_over_partitions_eq_statement.
Proof.
  unfold GeneratedSumSequenceSource.statement_sum_over_partitions_eq,
    ss_target_sum_over_partitions_eq_statement.
  apply prop_sprop_rel_intro.
  - intros Hsource X Y xToY fL PL xsL ysL.
    pose fR := ss_nat_fun_to_rocq fL.
    pose PR := ss_pred_to_rocq PL.
    pose xsR := ss_to_rocq xsL.
    pose ysR := ss_to_rocq ysL.
    have Hf : SsNatFunRel fR fL := ss_nat_fun_surjective fL.
    have HP : SsPredRel PR PL := ss_pred_surjective PL.
    have Hxs : SsListRel xsR xsL := ss_list_target_roundtrip xsL.
    have Hys : SsListRel ysR ysL := ss_list_target_roundtrip ysL.
    exact (prop_to_sprop _ _
      (ss_sum_over_partitions_eq_instance_correspondence X Y xToY
        fR fL PR PL xsR xsL ysR ysL Hf HP Hxs Hys)
      (Hsource X Y xToY fR PR xsR ysR)).
  - intro Htarget. apply strictly_inhabits.
    intros X Y xToY fR PR xsR ysR.
    have Hf : SsNatFunRel fR (ss_nat_fun_to_imported fR) :=
      ss_nat_fun_canonical fR.
    have HP : SsPredRel PR (ss_pred_to_imported PR) :=
      ss_pred_canonical PR.
    have Hxs : SsListRel xsR (ss_to_imported xsR) := @Lean.eq_refl _ _.
    have Hys : SsListRel ysR (ss_to_imported ysR) := @Lean.eq_refl _ _.
    exact (sprop_to_prop _ _
      (ss_sum_over_partitions_eq_instance_correspondence X Y xToY
        fR (ss_nat_fun_to_imported fR) PR (ss_pred_to_imported PR)
        xsR (ss_to_imported xsR) ysR (ss_to_imported ysR)
        Hf HP Hxs Hys)
      (Htarget X Y xToY (ss_nat_fun_to_imported fR)
        (ss_pred_to_imported PR) (ss_to_imported xsR)
        (ss_to_imported ysR))).
Qed.

Theorem sum_leq_mono_statement_certificate :
  PropSPropRel GeneratedSumSequenceSource.statement_sum_leq_mono
    ss_target_sum_leq_mono_statement.
Proof.
  unfold GeneratedSumSequenceSource.statement_sum_leq_mono,
    prosa.util.rel.monotone, ss_target_sum_leq_mono_statement.
  apply prop_sprop_rel_intro.
  - intros Hsource I PL FL rL.
    pose PR := ss_pred_to_rocq PL.
    pose FR := ss_nat_family_to_rocq FL.
    pose rR := ss_to_rocq rL.
    have HP : SsPredRel PR PL := ss_pred_surjective PL.
    have HF : SsNatFamilyRel FR FL := ss_nat_family_surjective FL.
    have Hr : SsListRel rR rL := ss_list_target_roundtrip rL.
    exact (prop_to_sprop _ _
      (ss_sum_leq_mono_instance_correspondence I PR PL FR FL
        rR rL HP HF Hr)
      (Hsource I PR FR rR)).
  - intro Htarget. apply strictly_inhabits.
    intros I PR FR rR.
    have HP : SsPredRel PR (ss_pred_to_imported PR) :=
      ss_pred_canonical PR.
    have HF : SsNatFamilyRel FR (ss_nat_family_to_imported FR) :=
      ss_nat_family_canonical FR.
    have Hr : SsListRel rR (ss_to_imported rR) := @Lean.eq_refl _ _.
    exact (sprop_to_prop _ _
      (ss_sum_leq_mono_instance_correspondence I PR
        (ss_pred_to_imported PR) FR (ss_nat_family_to_imported FR)
        rR (ss_to_imported rR) HP HF Hr)
      (Htarget I (ss_pred_to_imported PR)
        (ss_nat_family_to_imported FR) (ss_to_imported rR))).
Qed.

Theorem sum_unit1_statement_certificate :
  PropSPropRel GeneratedSumSequenceSource.statement_sum_unit1
    ss_target_sum_unit1_statement.
Proof.
  unfold GeneratedSumSequenceSource.statement_sum_unit1,
    ss_target_sum_unit1_statement.
  apply prop_sprop_rel_intro.
  - intros Hsource FL.
    pose FR := ss_unit_nat_fun_to_rocq FL.
    have HF : SsUnitNatFunRel FR FL := ss_unit_nat_fun_surjective FL.
    exact (prop_to_sprop _ _
      (ss_sum_unit1_instance_correspondence FR FL HF)
      (Hsource FR)).
  - intro Htarget. apply strictly_inhabits. intro FR.
    have HF : SsUnitNatFunRel FR (ss_unit_nat_fun_to_imported FR) :=
      ss_unit_nat_fun_canonical FR.
    exact (sprop_to_prop _ _
      (ss_sum_unit1_instance_correspondence FR
        (ss_unit_nat_fun_to_imported FR) HF)
      (Htarget (ss_unit_nat_fun_to_imported FR))).
Qed.

Theorem sum_ge_2_seq_statement_certificate :
  PropSPropRel GeneratedSumSequenceSource.statement_sum_ge_2_seq
    ss_target_sum_ge_2_seq_statement.
Proof.
  unfold GeneratedSumSequenceSource.statement_sum_ge_2_seq,
    ss_target_sum_ge_2_seq_statement.
  apply prop_sprop_rel_intro.
  - intros Hsource T xsL pL.
    pose xsR := ss_to_rocq xsL.
    pose pR := ss_nat_fun_to_rocq pL.
    have Hxs : SsListRel xsR xsL := ss_list_target_roundtrip xsL.
    have Hp : SsNatFunRel pR pL := ss_nat_fun_surjective pL.
    exact (prop_to_sprop _ _
      (ss_sum_ge_2_seq_instance_correspondence T xsR xsL pR pL Hxs Hp)
      (Hsource T xsR pR)).
  - intro Htarget. apply strictly_inhabits. intros T xsR pR.
    have Hxs : SsListRel xsR (ss_to_imported xsR) := @Lean.eq_refl _ _.
    have Hp : SsNatFunRel pR (ss_nat_fun_to_imported pR) :=
      ss_nat_fun_canonical pR.
    exact (sprop_to_prop _ _
      (ss_sum_ge_2_seq_instance_correspondence T xsR
        (ss_to_imported xsR) pR (ss_nat_fun_to_imported pR) Hxs Hp)
      (Htarget T (ss_to_imported xsR) (ss_nat_fun_to_imported pR))).
Qed.

Print Assumptions sum_nat_eq0_nat_statement_certificate.
Print Assumptions sum_nat_gt0_statement_certificate.
Print Assumptions sum_majorant_constant_statement_certificate.
Print Assumptions bigmax_leq_sum_statement_certificate.
Print Assumptions sum_le_subseq_statement_certificate.
Print Assumptions leq_sum_subseq_statement_certificate.
Print Assumptions leq_sum_seq_statement_certificate.
Print Assumptions eq_sum_seq_statement_certificate.
Print Assumptions leq_sum_seq_pred_statement_certificate.
Print Assumptions ltn_sum_leq_seq_statement_certificate.
Print Assumptions eq_sum_leq_seq_statement_certificate.
Print Assumptions leq_sum_sub_uniq_statement_certificate.
Print Assumptions sum_split_exhaustive_mutually_exclusive_preds_statement_certificate.
Print Assumptions sum_over_partitions_le_statement_certificate.
Print Assumptions reorder_summation_statement_certificate.
Print Assumptions sum_over_partitions_eq_statement_certificate.
Print Assumptions sum_leq_mono_statement_certificate.
Print Assumptions sum_unit1_statement_certificate.
Print Assumptions sum_ge_2_seq_statement_certificate.
