From mathcomp Require Import ssreflect ssrbool ssrnat seq.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedExtrapolatedArrivalCurveBase.
From FoundationCertificates Require Import
  PropSPropFoundation LogicalRelation SubadditivityNatCorrespondence.
Require Import OfficialExtrapolatedArrivalCurveBase.

(** An operation-level representation relation for the actual imported
    Lean product/list constructors. Source sequence order and multiplicity
    are retained. *)
Definition eac_imported_step (p : nat * nat) :
    ImportedExtrapolatedArrivalCurveBase.Prod_inst3 Lean.Nat Lean.Nat :=
  match p with
  | (t, n) => ImportedExtrapolatedArrivalCurveBase.Prod_mk_inst3
      Lean.Nat Lean.Nat (sub_nat_to_imported t) (sub_nat_to_imported n)
  end.

Fixpoint eac_imported_steps (xs : seq (nat * nat)) :
    ImportedExtrapolatedArrivalCurveBase.List_inst1
      (ImportedExtrapolatedArrivalCurveBase.Prod_inst3 Lean.Nat Lean.Nat) :=
  match xs with
  | [::] => ImportedExtrapolatedArrivalCurveBase.List_nil_inst1 _
  | x :: tail => ImportedExtrapolatedArrivalCurveBase.List_cons_inst1 _
      (eac_imported_step x) (eac_imported_steps tail)
  end.

Fixpoint eac_imported_times (xs : seq nat) :
    ImportedExtrapolatedArrivalCurveBase.List_inst1 Lean.Nat :=
  match xs with
  | [::] => ImportedExtrapolatedArrivalCurveBase.List_nil_inst1 _
  | x :: tail => ImportedExtrapolatedArrivalCurveBase.List_cons_inst1 _
      (sub_nat_to_imported x) (eac_imported_times tail)
  end.

Definition eac_imported_prefix
    (p : OfficialExtrapolatedArrivalCurveBase.ArrivalCurvePrefix) :
    ImportedExtrapolatedArrivalCurveBase.Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_ArrivalCurvePrefix :=
  match p with
  | (h, steps) => ImportedExtrapolatedArrivalCurveBase.Prod_mk_inst3
      Lean.Nat _ (sub_nat_to_imported h) (eac_imported_steps steps)
  end.

Definition EacPrefixRel (pR : OfficialExtrapolatedArrivalCurveBase.ArrivalCurvePrefix)
    (pL : ImportedExtrapolatedArrivalCurveBase.Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_ArrivalCurvePrefix) : SProp :=
  Lean.eq (eac_imported_prefix pR) pL.

Definition eac_bool_to_imported (b : bool) :
    ImportedExtrapolatedArrivalCurveBase.Bool :=
  match b with
  | true => ImportedExtrapolatedArrivalCurveBase.Bool_true
  | false => ImportedExtrapolatedArrivalCurveBase.Bool_false
  end.

Definition EacBoolRel (bR : bool)
    (bL : ImportedExtrapolatedArrivalCurveBase.Bool) : SProp :=
  Lean.eq (eac_bool_to_imported bR) bL.

Definition eac_imported_false_elim (Q : SProp)
    (H : ImportedExtrapolatedArrivalCurveBase.False) : Q :=
  match H return Q with end.

Definition eac_rocq_false_to_imported (H : Logic.False) :
    ImportedExtrapolatedArrivalCurveBase.False :=
  match H return ImportedExtrapolatedArrivalCurveBase.False with end.

Lemma eac_decide_bool_correspondence (bR : bool) (Q : SProp)
    (d : ImportedExtrapolatedArrivalCurveBase.Decidable Q) :
  PropSPropRel (is_true bR) Q ->
  EacBoolRel bR
    (ImportedExtrapolatedArrivalCurveBase.Decidable_decide Q d).
Proof.
  intro Hrel. unfold EacBoolRel.
  destruct d as [Hfalse | Htrue]; destruct bR; cbn.
  - exact (eac_imported_false_elim _
      (Hfalse (prop_to_sprop _ _ Hrel (Logic.eq_refl true)))).
  - exact (@Lean.eq_refl _ _).
  - exact (@Lean.eq_refl _ _).
  - exact (eac_imported_false_elim _ (eac_rocq_false_to_imported
      (match sprop_to_prop _ _ Hrel Htrue with end))).
Qed.

Definition eac_target_decide_le (a b : Lean.Nat) :
    ImportedExtrapolatedArrivalCurveBase.Bool :=
  ImportedExtrapolatedArrivalCurveBase.Decidable_decide
    (ImportedExtrapolatedArrivalCurveBase.LE_le_inst1 Lean.Nat
      ImportedExtrapolatedArrivalCurveBase.instLENat a b)
    (ImportedExtrapolatedArrivalCurveBase.Nat_decLe a b).

Lemma eac_nat_le_bool_correspondence aR aL bR bL :
  SubNatRel aR aL -> SubNatRel bR bL ->
  EacBoolRel (leq aR bR) (eac_target_decide_le aL bL).
Proof.
  intros Ha Hb. apply eac_decide_bool_correspondence.
  exact (sub_nat_le_correspondence aR aL bR bL Ha Hb).
Qed.

Definition eac_target_filter {A : Type}
    (P : A -> ImportedExtrapolatedArrivalCurveBase.Bool)
    (xs : ImportedExtrapolatedArrivalCurveBase.List_inst1 A) :=
  ImportedExtrapolatedArrivalCurveBase.List_filter_inst1 A P xs.

Lemma eac_target_filter_nil {A : Type}
    (P : A -> ImportedExtrapolatedArrivalCurveBase.Bool) :
    Lean.eq
      (eac_target_filter P
        (ImportedExtrapolatedArrivalCurveBase.List_nil_inst1 A))
      (ImportedExtrapolatedArrivalCurveBase.List_nil_inst1 A).
Proof. exact (@Lean.eq_refl _ _). Qed.

Lemma eac_target_filter_cons {A : Type}
    (P : A -> ImportedExtrapolatedArrivalCurveBase.Bool) (x : A)
    (xs : ImportedExtrapolatedArrivalCurveBase.List_inst1 A) :
    Lean.eq
      (eac_target_filter P
        (ImportedExtrapolatedArrivalCurveBase.List_cons_inst1 A x xs))
      (match P x with
       | ImportedExtrapolatedArrivalCurveBase.Bool_true =>
           ImportedExtrapolatedArrivalCurveBase.List_cons_inst1 A x
             (eac_target_filter P xs)
       | ImportedExtrapolatedArrivalCurveBase.Bool_false =>
           eac_target_filter P xs
       end).
Proof. exact (@Lean.eq_refl _ _). Qed.

Lemma eac_target_last_nil {A : Type} (fallback : A) :
  Lean.eq
    (ImportedExtrapolatedArrivalCurveBase.List_getLastD_inst1 A
      (ImportedExtrapolatedArrivalCurveBase.List_nil_inst1 A) fallback)
    fallback.
Proof. exact (@Lean.eq_refl _ _). Qed.

Lemma eac_target_last_singleton {A : Type} (x fallback : A) :
  Lean.eq
    (ImportedExtrapolatedArrivalCurveBase.List_getLastD_inst1 A
      (ImportedExtrapolatedArrivalCurveBase.List_cons_inst1 A x
        (ImportedExtrapolatedArrivalCurveBase.List_nil_inst1 A)) fallback)
    x.
Proof. exact (@Lean.eq_refl _ _). Qed.

Lemma eac_target_last_cons_cons {A : Type} (x y : A)
    (xs : ImportedExtrapolatedArrivalCurveBase.List_inst1 A)
    (fallback : A) :
  Lean.eq
    (ImportedExtrapolatedArrivalCurveBase.List_getLastD_inst1 A
      (ImportedExtrapolatedArrivalCurveBase.List_cons_inst1 A x
        (ImportedExtrapolatedArrivalCurveBase.List_cons_inst1 A y xs)) fallback)
    (ImportedExtrapolatedArrivalCurveBase.List_getLastD_inst1 A
      (ImportedExtrapolatedArrivalCurveBase.List_cons_inst1 A y xs) fallback).
Proof. exact (@Lean.eq_refl _ _). Qed.

Definition eac_target_step_pred (t : Lean.Nat)
    (p : ImportedExtrapolatedArrivalCurveBase.Prod_inst3 Lean.Nat Lean.Nat) :
    ImportedExtrapolatedArrivalCurveBase.Bool :=
  eac_target_decide_le
    (ImportedExtrapolatedArrivalCurveBase.Prod_fst_inst3 Lean.Nat Lean.Nat p) t.

Lemma eac_filter_branch_canonical (b : bool) (x : nat * nat)
    (filtered : seq (nat * nat))
    (tail : ImportedExtrapolatedArrivalCurveBase.List_inst1
      (ImportedExtrapolatedArrivalCurveBase.Prod_inst3 Lean.Nat Lean.Nat)) :
  Lean.eq tail (eac_imported_steps filtered) ->
  Lean.eq
    (match eac_bool_to_imported b with
     | ImportedExtrapolatedArrivalCurveBase.Bool_true =>
         ImportedExtrapolatedArrivalCurveBase.List_cons_inst1 _
           (eac_imported_step x) tail
     | ImportedExtrapolatedArrivalCurveBase.Bool_false => tail
     end)
    (eac_imported_steps
      (if b then x :: filtered else filtered)).
Proof.
  intro Htail. destruct b; cbn.
  - exact (sub_imported_eq_congr
      (ImportedExtrapolatedArrivalCurveBase.List_cons_inst1 _
        (eac_imported_step x)) _ _ Htail).
  - exact Htail.
Qed.

Lemma eac_filter_steps_generic (PR : nat * nat -> bool)
    (PL : ImportedExtrapolatedArrivalCurveBase.Prod_inst3 Lean.Nat Lean.Nat ->
      ImportedExtrapolatedArrivalCurveBase.Bool)
    (HP : forall p, EacBoolRel (PR p) (PL (eac_imported_step p)))
    (xs : seq (nat * nat)) :
  Lean.eq (eac_target_filter PL (eac_imported_steps xs))
    (eac_imported_steps (filter PR xs)).
Proof.
  induction xs as [|x tail IH].
  - exact (eac_target_filter_nil _).
  - have Hpred := HP x.
    unfold EacBoolRel in Hpred.
    refine (sub_imported_eq_trans _ _ _
      (eac_target_filter_cons _ _ _) _).
    refine (sub_imported_eq_trans _ _ _
      (sub_imported_eq_congr
        (fun z : ImportedExtrapolatedArrivalCurveBase.Bool =>
          match z with
          | ImportedExtrapolatedArrivalCurveBase.Bool_true =>
              ImportedExtrapolatedArrivalCurveBase.List_cons_inst1 _
                (eac_imported_step x)
                (eac_target_filter PL (eac_imported_steps tail))
          | ImportedExtrapolatedArrivalCurveBase.Bool_false =>
              eac_target_filter PL (eac_imported_steps tail)
          end) _ _ (sub_imported_eq_sym _ _ Hpred)) _).
    exact (eac_filter_branch_canonical (PR x) x (filter PR tail)
      (eac_target_filter PL (eac_imported_steps tail)) IH).
Qed.

Lemma eac_filter_steps_canonical (tR : nat) (tL : Lean.Nat)
    (Ht : SubNatRel tR tL) (xs : seq (nat * nat)) :
  Lean.eq
    (eac_target_filter (eac_target_step_pred tL)
      (eac_imported_steps xs))
    (eac_imported_steps
      (filter (fun p : nat * nat => leq (Datatypes.fst p) tR) xs)).
Proof.
  apply eac_filter_steps_generic.
  intros [a b].
  exact (eac_nat_le_bool_correspondence a (sub_nat_to_imported a)
    tR tL (sub_nat_rel_canonical a) Ht).
Qed.

Lemma eac_last_steps_canonical (dR : nat * nat)
    (dL : ImportedExtrapolatedArrivalCurveBase.Prod_inst3 Lean.Nat Lean.Nat)
    (Hd : Lean.eq (eac_imported_step dR) dL)
    (xs : seq (nat * nat)) :
  Lean.eq (eac_imported_step (last dR xs))
    (ImportedExtrapolatedArrivalCurveBase.List_getLastD_inst1 _
      (eac_imported_steps xs) dL).
Proof.
  induction xs as [|x xs IH].
  - exact (sub_imported_eq_trans _ _ _ Hd
      (sub_imported_eq_sym _ _ (eac_target_last_nil dL))).
  - destruct xs as [|y ys].
    + exact (sub_imported_eq_sym _ _
        (eac_target_last_singleton (eac_imported_step x) dL)).
    + exact (sub_imported_eq_trans _ _ _ IH
        (sub_imported_eq_sym _ _
          (eac_target_last_cons_cons (eac_imported_step x)
            (eac_imported_step y) (eac_imported_steps ys) dL))).
Qed.

Lemma eac_inter_arrival_to_prefix_correspondence :
  forall pR pL, SubNatRel pR pL ->
    EacPrefixRel
      (OfficialExtrapolatedArrivalCurveBase.inter_arrival_to_prefix pR)
      (ImportedExtrapolatedArrivalCurveBase.Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_inter_arrival_to_prefix pL).
Proof.
  intros pR pL Hp.
  destruct Hp.
  exact (@Lean.eq_refl _ _).
Qed.

Lemma eac_horizon_of_correspondence :
  forall pR pL, EacPrefixRel pR pL ->
    SubNatRel
      (OfficialExtrapolatedArrivalCurveBase.horizon_of pR)
      (ImportedExtrapolatedArrivalCurveBase.Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_horizon_of pL).
Proof.
  intros [h steps] pL Hp.
  destruct Hp.
  exact (@Lean.eq_refl _ _).
Qed.

Lemma eac_steps_of_correspondence :
  forall pR pL, EacPrefixRel pR pL ->
    Lean.eq
      (eac_imported_steps
        (OfficialExtrapolatedArrivalCurveBase.steps_of pR))
      (ImportedExtrapolatedArrivalCurveBase.Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_steps_of pL).
Proof.
  intros [h steps] pL Hp.
  destruct Hp.
  exact (@Lean.eq_refl _ _).
Qed.

Lemma eac_time_steps_of_correspondence :
  forall pR pL, EacPrefixRel pR pL ->
    Lean.eq
      (eac_imported_times
        (OfficialExtrapolatedArrivalCurveBase.time_steps_of pR))
      (ImportedExtrapolatedArrivalCurveBase.Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_time_steps_of pL).
Proof.
  intros [h steps] pL Hp.
  destruct Hp.
  induction steps as [|[t n] tail IH]; cbn.
  - exact (@Lean.eq_refl _ _).
  - exact (sub_imported_eq_congr
      (ImportedExtrapolatedArrivalCurveBase.List_cons_inst1 Lean.Nat
        (sub_nat_to_imported t)) _ _ IH).
Qed.

Lemma eac_step_at_correspondence :
  forall pR pL tR tL,
    EacPrefixRel pR pL -> SubNatRel tR tL ->
    Lean.eq
      (eac_imported_step
        (OfficialExtrapolatedArrivalCurveBase.step_at pR tR))
      (ImportedExtrapolatedArrivalCurveBase.Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_step_at pL tL).
Proof.
  intros [h steps] pL tR tL Hp Ht.
  destruct Hp.
  set (defaultL := ImportedExtrapolatedArrivalCurveBase.Prod_mk_inst3
    Lean.Nat Lean.Nat Lean.Nat_zero Lean.Nat_zero).
  have Hdefault : Lean.eq (eac_imported_step (O, O)) defaultL :=
    @Lean.eq_refl _ _.
  have Hfilter := eac_filter_steps_canonical tR tL Ht steps.
  have Hlast := eac_last_steps_canonical (O, O) defaultL Hdefault
    (filter (fun p : nat * nat => leq (Datatypes.fst p) tR) steps).
  exact (sub_imported_eq_trans _ _ _ Hlast
    (sub_imported_eq_congr
      (fun xs => ImportedExtrapolatedArrivalCurveBase.List_getLastD_inst1 _
        xs defaultL) _ _ (sub_imported_eq_sym _ _ Hfilter))).
Qed.

Lemma eac_step_snd_correspondence (pR : nat * nat)
    (pL : ImportedExtrapolatedArrivalCurveBase.Prod_inst3 Lean.Nat Lean.Nat) :
  Lean.eq (eac_imported_step pR) pL ->
  SubNatRel (Datatypes.snd pR)
    (ImportedExtrapolatedArrivalCurveBase.Prod_snd_inst3 Lean.Nat Lean.Nat pL).
Proof.
  destruct pR as [a b]. intro Hp.
  exact (sub_imported_eq_congr
    (ImportedExtrapolatedArrivalCurveBase.Prod_snd_inst3 Lean.Nat Lean.Nat)
    _ _ Hp).
Qed.

Lemma eac_value_at_correspondence :
  forall pR pL tR tL,
    EacPrefixRel pR pL -> SubNatRel tR tL ->
    SubNatRel
      (OfficialExtrapolatedArrivalCurveBase.value_at pR tR)
      (ImportedExtrapolatedArrivalCurveBase.Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_value_at pL tL).
Proof.
  intros pR pL tR tL Hp Ht.
  exact (eac_step_snd_correspondence _ _
    (eac_step_at_correspondence pR pL tR tL Hp Ht)).
Qed.

Print Assumptions eac_inter_arrival_to_prefix_correspondence.
Print Assumptions eac_horizon_of_correspondence.
Print Assumptions eac_steps_of_correspondence.
Print Assumptions eac_time_steps_of_correspondence.
Print Assumptions eac_step_at_correspondence.
Print Assumptions eac_value_at_correspondence.
