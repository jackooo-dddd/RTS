From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From prosa Require Import behavior.arrival_sequence.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedSporadic ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation
  LogicalRelation SubadditivityNatCorrespondence.
From SporadicCertificates Require Import SporadicBaseAdapter.

(** Sporadic target-local operation slice adapted from accepted ConceptOperations.
    Target-local, small operation slice.  Each proof is kernel rechecked against
    the exact Concept import; no unused Arrival/Bigcat operation is asserted. *)

Definition ct_target_false_elim (Q : SProp)
    (H : ImportedSporadic.False) : Q :=
  match H return Q with end.

Lemma ar_bool_eq_correspondence aR aL bR bL :
  ArBoolRel aR aL -> ArBoolRel bR bL ->
  PropSPropRel (Logic.eq aR bR) (Lean.eq aL bL).
Proof.
  intros Ha Hb. apply prop_sprop_rel_intro.
  - intro Heq. destruct Heq.
    exact (sub_imported_eq_trans _ _ _
      (sub_imported_eq_sym _ _ Ha) Hb).
  - intro Heq. apply strictly_inhabits.
    have Hcanonical : Lean.eq (ar_bool_to_imported aR)
        (ar_bool_to_imported bR) :=
      sub_imported_eq_trans _ _ _ Ha
        (sub_imported_eq_trans _ _ _ Heq
          (sub_imported_eq_sym _ _ Hb)).
    have Hdecoded := f_equal ar_bool_to_rocq
      (imported_eq_to_coq_eq _ _ Hcanonical).
    rewrite (ar_bool_source_roundtrip aR) in Hdecoded.
    rewrite (ar_bool_source_roundtrip bR) in Hdecoded.
    exact Hdecoded.
Qed.

Lemma ct_bool_false_correspondence bR bL :
  ArBoolRel bR bL ->
  PropSPropRel (is_true (~~ bR))
    (Lean.eq bL ImportedSporadic.Bool_false).
Proof.
  intro Hb.
  have Hfalse := ar_bool_eq_correspondence bR bL false
    ImportedSporadic.Bool_false Hb (@Lean.eq_refl _ _).
  apply prop_sprop_rel_intro.
  - intro Hnot. destruct bR; cbn in Hnot.
    + discriminate Hnot.
    + exact (prop_to_sprop _ _ Hfalse (Logic.eq_refl false)).
  - intro HL. have Heq := sprop_to_prop _ _ Hfalse HL.
    apply strictly_inhabits.
    destruct bR; cbn in *.
    + discriminate Heq.
    + reflexivity.
Qed.

Lemma ar_decide_bool_correspondence (b : bool) (Q : SProp)
    (d : ImportedSporadic.Decidable Q) :
  PropSPropRel (is_true b) Q ->
  ArBoolRel b (ImportedSporadic.Decidable_decide Q d).
Proof.
  intro Hrel. unfold ArBoolRel.
  destruct d as [Hfalse | Htrue]; destruct b; cbn.
  - exact (ct_target_false_elim _
      (Hfalse (prop_to_sprop _ _ Hrel (Logic.eq_refl true)))).
  - exact (@Lean.eq_refl _ _).
  - exact (@Lean.eq_refl _ _).
  - exact (ct_target_false_elim _ (ar_coq_false_to_target
      (match sprop_to_prop _ _ Hrel Htrue with end))).
Qed.

Definition ct_target_decide_eq (T : eqType) (x y : T) :
    ImportedSporadic.Bool :=
  ImportedSporadic.Decidable_decide (Lean.eq x y)
    (ar_decidable_eq T x y).

Lemma ct_decide_eq_related (T : eqType) (x y : T) :
  ArBoolRel (x == y) (ct_target_decide_eq T x y).
Proof.
  apply ar_decide_bool_correspondence.
  apply prop_sprop_rel_intro.
  - move/eqP => Heq. exact (coq_eq_to_imported_eq _ _ Heq).
  - intro Heq. apply strictly_inhabits. apply/eqP.
    exact (imported_eq_to_coq_eq _ _ Heq).
Qed.

Definition ar_target_decide_mem (T : eqType) (x : T)
    (xs : ImportedSporadic.List T) : ImportedSporadic.Bool :=
  ImportedSporadic.Decidable_decide (ar_target_mem x xs)
    (ImportedSporadic.List_instDecidableMemOfLawfulBEq T
      (ImportedSporadic.instBEqOfDecidableEq T (ar_decidable_eq T))
      (ImportedSporadic.instLawfulBEq T (ar_decidable_eq T)) x xs).

Lemma ar_decide_mem_related (T : eqType) (x : T)
    (xsR : seq T) (xsL : ImportedSporadic.List T) :
  ArListRel xsR xsL ->
  ArBoolRel (x \in xsR) (ar_target_decide_mem T x xsL).
Proof.
  intro Hxs. apply ar_decide_bool_correspondence.
  exact (ar_membership_correspondence T x xsR xsL Hxs).
Qed.

Definition ar_target_le (a b : Lean.Nat) : SProp :=
  ImportedSporadic.LE_le_inst1 Lean.Nat ImportedSporadic.instLENat a b.

Definition ar_target_lt (a b : Lean.Nat) : SProp :=
  ImportedSporadic.LT_lt_inst1 Lean.Nat ImportedSporadic.instLTNat a b.

Definition ar_target_decide_le (a b : Lean.Nat) : ImportedSporadic.Bool :=
  ImportedSporadic.Decidable_decide (ar_target_le a b)
    (ImportedSporadic.Nat_decLe a b).

Definition ar_target_decide_lt (a b : Lean.Nat) : ImportedSporadic.Bool :=
  ImportedSporadic.Decidable_decide (ar_target_lt a b)
    (ImportedSporadic.Nat_decLt a b).

Lemma ar_decide_le_related aR aL bR bL :
  SubNatRel aR aL -> SubNatRel bR bL ->
  ArBoolRel (leq aR bR) (ar_target_decide_le aL bL).
Proof.
  intros Ha Hb. apply ar_decide_bool_correspondence.
  unfold ar_target_le.
  exact (sub_nat_le_correspondence aR aL bR bL Ha Hb).
Qed.

Lemma ar_decide_lt_related aR aL bR bL :
  SubNatRel aR aL -> SubNatRel bR bL ->
  ArBoolRel (ltn aR bR) (ar_target_decide_lt aL bL).
Proof.
  intros Ha Hb. apply ar_decide_bool_correspondence.
  unfold ar_target_lt.
  exact (sub_nat_lt_correspondence aR aL bR bL Ha Hb).
Qed.

Definition ArArrivalSequenceRel (T : eqType)
    (arrR : prosa.behavior.arrival_sequence.arrival_sequence T)
    (arrL :
      ImportedSporadic.Prosa_Behavior_Arrival_sequence_arrival_sequence T
        (ar_decidable_eq T)) : SProp :=
  forall tR tL, SubNatRel tR tL -> ArListRel (arrR tR) (arrL tL).

Definition ar_arrival_sequence_to_imported (T : eqType)
    (arrR : prosa.behavior.arrival_sequence.arrival_sequence T) :
    ImportedSporadic.Prosa_Behavior_Arrival_sequence_arrival_sequence T
      (ar_decidable_eq T) :=
  fun tL => ar_list_to_imported (arrR (sub_nat_to_rocq tL)).

Lemma ar_arrival_sequence_canonical (T : eqType)
    (arrR : prosa.behavior.arrival_sequence.arrival_sequence T) :
  ArArrivalSequenceRel T arrR (ar_arrival_sequence_to_imported T arrR).
Proof.
  intros tR tL Ht. unfold ArListRel, ar_arrival_sequence_to_imported.
  have Hdecoded := f_equal sub_nat_to_rocq
    (imported_eq_to_coq_eq _ _ Ht).
  rewrite (sub_nat_rocq_roundtrip tR) in Hdecoded.
  rewrite <- Hdecoded. exact (@Lean.eq_refl _ _).
Qed.

Lemma ar_exists_nat_correspondence
    (PR : nat -> Prop) (PL : Lean.Nat -> SProp) :
  (forall nR nL, SubNatRel nR nL ->
    PropSPropRel (PR nR) (PL nL)) ->
  PropSPropRel (exists nR, PR nR)
    (ImportedSporadic.Exists Lean.Nat PL).
Proof.
  intro HP. apply prop_sprop_rel_intro.
  - intros [nR Hn].
    exact (ImportedSporadic.Exists_intro Lean.Nat PL
      (sub_nat_to_imported nR)
      (prop_to_sprop _ _
        (HP nR (sub_nat_to_imported nR) (sub_nat_rel_canonical nR)) Hn)).
  - intros [nL Hn]. apply strictly_inhabits.
    exists (sub_nat_to_rocq nL).
    exact (sprop_to_prop _ _
      (HP (sub_nat_to_rocq nL) nL (sub_nat_rel_surjective nL)) Hn).
Qed.

Lemma ar_imp_correspondence (P Q : Prop) (PL QL : SProp) :
  PropSPropRel P PL -> PropSPropRel Q QL ->
  PropSPropRel (P -> Q) (PL -> QL).
Proof.
  intros HP HQ. apply prop_sprop_rel_intro.
  - intros H p. apply (prop_to_sprop _ _ HQ).
    exact (H (sprop_to_prop _ _ HP p)).
  - intro H. apply strictly_inhabits. intro p.
    apply (sprop_to_prop _ _ HQ).
    exact (H (prop_to_sprop _ _ HP p)).
Qed.

Lemma ar_forall_identity_correspondence (T : Type)
    (PR : T -> Prop) (PL : T -> SProp) :
  (forall x, PropSPropRel (PR x) (PL x)) ->
  PropSPropRel (forall x, PR x) (forall x, PL x).
Proof.
  intro HP. apply prop_sprop_rel_intro.
  - intros HR x. exact (prop_to_sprop _ _ (HP x) (HR x)).
  - intro HL. apply strictly_inhabits. intro x.
    exact (sprop_to_prop _ _ (HP x) (HL x)).
Qed.

Print Assumptions ct_decide_eq_related.
Print Assumptions ar_decide_mem_related.
Print Assumptions ar_decide_le_related.
Print Assumptions ar_decide_lt_related.
Print Assumptions ar_exists_nat_correspondence.

Lemma sp_arrives_at_correspondence (T : eqType)
    (arrR : prosa.behavior.arrival_sequence.arrival_sequence T)
    (arrL :
      ImportedSporadic.Prosa_Behavior_Arrival_sequence_arrival_sequence T
        (ar_decidable_eq T)) (j : T) :
  ArArrivalSequenceRel T arrR arrL ->
  forall tR tL, SubNatRel tR tL ->
  ArBoolRel
    (prosa.behavior.arrival_sequence.arrives_at arrR j tR)
    (ImportedSporadic.Prosa_Behavior_Arrival_sequence_arrives_at T
      (ar_decidable_eq T) arrL j tL).
Proof.
  intros Harr tR tL Ht. cbn.
  apply ar_decide_mem_related.
  exact (Harr tR tL Ht).
Qed.

Lemma sp_arrives_in_correspondence (T : eqType)
    (arrR : prosa.behavior.arrival_sequence.arrival_sequence T)
    (arrL :
      ImportedSporadic.Prosa_Behavior_Arrival_sequence_arrival_sequence T
        (ar_decidable_eq T)) (j : T) :
  ArArrivalSequenceRel T arrR arrL ->
  PropSPropRel
    (prosa.behavior.arrival_sequence.arrives_in arrR j)
    (ImportedSporadic.Prosa_Behavior_Arrival_sequence_arrives_in T
      (ar_decidable_eq T) arrL j).
Proof.
  intro Harr. cbn.
  apply ar_exists_nat_correspondence.
  intros tR tL Ht. apply ar_bool_truth_correspondence.
  exact (sp_arrives_at_correspondence T arrR arrL j
    Harr tR tL Ht).
Qed.

Print Assumptions sp_arrives_at_correspondence.
Print Assumptions sp_arrives_in_correspondence.
