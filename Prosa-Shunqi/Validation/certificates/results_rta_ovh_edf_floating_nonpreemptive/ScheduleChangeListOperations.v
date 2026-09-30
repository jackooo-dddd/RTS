From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq
  fintype bigop.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedRtaOvhEdfFloatingNonpreemptive ImportedSubadditivity.
From FoundationCertificates Require Import
  PropSPropFoundation LogicalRelation SubadditivityNatCorrespondence
  ScheduleChangeBaseAdapter ScheduleChangeIntervalOperations.

Definition ScNatPredRel (PR : nat -> bool)
    (PL : Lean.Nat -> ImportedRtaOvhEdfFloatingNonpreemptive.Bool) : SProp :=
  forall nR nL, SubNatRel nR nL -> ScBoolRel (PR nR) (PL nL).

Definition sc_target_countP
    (P : Lean.Nat -> ImportedRtaOvhEdfFloatingNonpreemptive.Bool)
    (xs : ImportedRtaOvhEdfFloatingNonpreemptive.List_inst1 Lean.Nat) : Lean.Nat :=
  ImportedRtaOvhEdfFloatingNonpreemptive.List_countP_inst1 Lean.Nat P xs.

Definition sc_target_all
    (P : Lean.Nat -> ImportedRtaOvhEdfFloatingNonpreemptive.Bool)
    (xs : ImportedRtaOvhEdfFloatingNonpreemptive.List_inst1 Lean.Nat) :
    ImportedRtaOvhEdfFloatingNonpreemptive.Bool :=
  ImportedRtaOvhEdfFloatingNonpreemptive.List_all_inst1 Lean.Nat xs P.

Definition sc_list_target_false_elim (Q : SProp)
    (H : ImportedRtaOvhEdfFloatingNonpreemptive.False) : Q := match H return Q with end.

Definition sc_imported_ite_true {A : Type} (p : SProp)
    (d : ImportedRtaOvhEdfFloatingNonpreemptive.Decidable p) (hp : p) (x y : A) :
    Lean.eq (ImportedRtaOvhEdfFloatingNonpreemptive.ite A p d x y) x :=
  match d as d0 return Lean.eq (ImportedRtaOvhEdfFloatingNonpreemptive.ite A p d0 x y) x with
  | ImportedRtaOvhEdfFloatingNonpreemptive.Decidable_isFalse hn => sc_list_target_false_elim _ (hn hp)
  | ImportedRtaOvhEdfFloatingNonpreemptive.Decidable_isTrue _ => @Lean.eq_refl A x
  end.

Definition sc_imported_ite_false {A : Type} (p : SProp)
    (d : ImportedRtaOvhEdfFloatingNonpreemptive.Decidable p)
    (hn : ImportedRtaOvhEdfFloatingNonpreemptive.Not p) (x y : A) :
    Lean.eq (ImportedRtaOvhEdfFloatingNonpreemptive.ite A p d x y) y :=
  match d as d0 return Lean.eq (ImportedRtaOvhEdfFloatingNonpreemptive.ite A p d0 x y) y with
  | ImportedRtaOvhEdfFloatingNonpreemptive.Decidable_isFalse _ => @Lean.eq_refl A y
  | ImportedRtaOvhEdfFloatingNonpreemptive.Decidable_isTrue hp => sc_list_target_false_elim _ (hn hp)
  end.

Definition sc_target_bool_true_ne_false :
    ImportedRtaOvhEdfFloatingNonpreemptive.Not
      (Lean.eq ImportedRtaOvhEdfFloatingNonpreemptive.Bool_false
        ImportedRtaOvhEdfFloatingNonpreemptive.Bool_true) :=
  fun H => ImportedRtaOvhEdfFloatingNonpreemptive.Bool_noConfusion_inst1
    ImportedRtaOvhEdfFloatingNonpreemptive.False ImportedRtaOvhEdfFloatingNonpreemptive.Bool_false
    ImportedRtaOvhEdfFloatingNonpreemptive.Bool_true H.

Definition sc_target_bool_ne_true_of_eq_false
    (b : ImportedRtaOvhEdfFloatingNonpreemptive.Bool) :
    Lean.eq ImportedRtaOvhEdfFloatingNonpreemptive.Bool_false b ->
    ImportedRtaOvhEdfFloatingNonpreemptive.Not
      (Lean.eq b ImportedRtaOvhEdfFloatingNonpreemptive.Bool_true) :=
  fun Hb Htrue => sc_target_bool_true_ne_false
    (sub_imported_eq_trans _ _ _ Hb Htrue).

Lemma sc_countP_canonical (PR : nat -> bool)
    (PL : Lean.Nat -> ImportedRtaOvhEdfFloatingNonpreemptive.Bool) :
  ScNatPredRel PR PL ->
  forall xs : seq nat,
    SubNatRel (count PR xs)
      (sc_target_countP PL (sc_nat_list_to_imported xs)).
Proof.
  intro HP. induction xs as [|a xs IH].
  - unfold SubNatRel, sc_target_countP.
    exact (sub_imported_eq_sym _ _
      (ImportedRtaOvhEdfFloatingNonpreemptive.Prosa_Validation_ScheduleChangeInterface_production_countP_nil
        PL)).
  - have Hstep :=
      ImportedRtaOvhEdfFloatingNonpreemptive.Prosa_Validation_ScheduleChangeInterface_production_countP_cons
        PL (sub_nat_to_imported a) (sc_nat_list_to_imported xs).
    have Hb := HP a (sub_nat_to_imported a) (sub_nat_rel_canonical a).
    destruct (PR a) eqn:Hpa.
    + cbn [sc_bool_to_imported] in Hb.
      have Hite := sc_imported_ite_true
        (Lean.eq (PL (sub_nat_to_imported a)) ImportedRtaOvhEdfFloatingNonpreemptive.Bool_true)
        (ImportedRtaOvhEdfFloatingNonpreemptive.instDecidableEqBool
          (PL (sub_nat_to_imported a)) ImportedRtaOvhEdfFloatingNonpreemptive.Bool_true)
        (sub_imported_eq_sym _ _ Hb) sc_target_one sc_target_zero.
      have Hadd := sc_target_add_related (count PR xs)
        (sc_target_countP PL (sc_nat_list_to_imported xs)) 1 sc_target_one
        IH (sub_nat_rel_canonical 1).
      rewrite /= Hpa.
      unfold SubNatRel in Hadd |- *.
      have Hsource : Lean.eq
          (sub_nat_to_imported (S (count PR xs)))
          (sub_nat_to_imported (count PR xs + 1)) :=
        coq_eq_to_imported_eq _ _
          (f_equal sub_nat_to_imported
            (Logic.eq_sym (addn1 (count PR xs)))).
      exact (sub_imported_eq_trans _ _ _ Hsource
        (sub_imported_eq_trans _ _ _ Hadd
          (sub_imported_eq_sym _ _
            (sub_imported_eq_trans _ _ _ Hstep
              (sub_imported_eq_congr
                (sc_target_add (sc_target_countP PL
                  (sc_nat_list_to_imported xs))) _ _ Hite))))).
    + cbn [sc_bool_to_imported] in Hb.
      have Hite := sc_imported_ite_false
        (Lean.eq (PL (sub_nat_to_imported a)) ImportedRtaOvhEdfFloatingNonpreemptive.Bool_true)
        (ImportedRtaOvhEdfFloatingNonpreemptive.instDecidableEqBool
          (PL (sub_nat_to_imported a)) ImportedRtaOvhEdfFloatingNonpreemptive.Bool_true)
        (sc_target_bool_ne_true_of_eq_false
          (PL (sub_nat_to_imported a)) Hb)
        sc_target_one sc_target_zero.
      rewrite /= Hpa.
      unfold SubNatRel in IH |- *.
      exact (sub_imported_eq_trans _ _ _ IH
        (sub_imported_eq_sym _ _
          (sub_imported_eq_trans _ _ _ Hstep
            (sub_imported_eq_congr
              (sc_target_add (sc_target_countP PL
                (sc_nat_list_to_imported xs))) _ _ Hite)))).
Qed.

Lemma sc_countP_related PR PL xsR xsL :
  ScNatPredRel PR PL -> ScNatListRel xsR xsL ->
  SubNatRel (count PR xsR) (sc_target_countP PL xsL).
Proof.
  intros HP Hxs. unfold SubNatRel.
  have Hcanon := sc_countP_canonical PR PL HP xsR.
  unfold SubNatRel in Hcanon.
  exact (sub_imported_eq_trans _ _ _ Hcanon
    (sub_imported_eq_congr (sc_target_countP PL) _ _ Hxs)).
Qed.

Lemma sc_bool_and_related aR aL bR bL :
  ScBoolRel aR aL -> ScBoolRel bR bL ->
  ScBoolRel (aR && bR) (ImportedRtaOvhEdfFloatingNonpreemptive.Bool_and aL bL).
Proof.
  intros Ha Hb. unfold ScBoolRel in Ha, Hb |- *.
  have Ha' := imported_eq_to_coq_eq _ _ Ha.
  have Hb' := imported_eq_to_coq_eq _ _ Hb.
  rewrite <- Ha', <- Hb'.
  destruct aR, bR; cbn; exact (@Lean.eq_refl _ _).
Qed.

Lemma sc_all_canonical (PR : nat -> bool)
    (PL : Lean.Nat -> ImportedRtaOvhEdfFloatingNonpreemptive.Bool) :
  ScNatPredRel PR PL ->
  forall xs : seq nat,
    ScBoolRel (all PR xs) (sc_target_all PL (sc_nat_list_to_imported xs)).
Proof.
  intro HP. induction xs as [|a xs IH].
  - unfold ScBoolRel, sc_target_all.
    exact (sub_imported_eq_sym _ _
      (ImportedRtaOvhEdfFloatingNonpreemptive.Prosa_Validation_ScheduleChangeInterface_production_all_nil
        PL)).
  - have Hhead := HP a (sub_nat_to_imported a) (sub_nat_rel_canonical a).
    have Hstep :=
      ImportedRtaOvhEdfFloatingNonpreemptive.Prosa_Validation_ScheduleChangeInterface_production_all_cons
        PL (sub_nat_to_imported a) (sc_nat_list_to_imported xs).
    unfold ScBoolRel in Hhead, IH |- *.
    exact (sub_imported_eq_trans _ _ _
      (sc_bool_and_related _ _ _ _ Hhead IH)
      (sub_imported_eq_sym _ _ Hstep)).
Qed.

Lemma sc_all_related PR PL xsR xsL :
  ScNatPredRel PR PL -> ScNatListRel xsR xsL ->
  ScBoolRel (all PR xsR) (sc_target_all PL xsL).
Proof.
  intros HP Hxs. unfold ScBoolRel.
  have Hcanon := sc_all_canonical PR PL HP xsR.
  unfold ScBoolRel in Hcanon.
  exact (sub_imported_eq_trans _ _ _ Hcanon
    (sub_imported_eq_congr (sc_target_all PL) _ _ Hxs)).
Qed.
