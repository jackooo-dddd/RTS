(* Re-bound copy of the accepted certificates/implementation_facts_job_constructor/EacFullCorrespondence.v: modules renamed (ImportedFactsJobConstructor=ImportedRefFPPSched,EacFullCorrespondence=PsEac,AbCorrespondence=PsAb,ImplTaskCorrespondence=PsImplTask,JcListOps=PsListOps), its statement
   correspondences dropped (their statement-only targets are not part of this export), and the commands that mention
   constants absent from this export dropped (the file's report lists them).  Every kept command is unchanged. *)
(* Copy of the accepted certificates/implementation_definitions_task/PsEac.v, re-bound to this export; only the
   imported module name differs, and the four reflection-view blocks are dropped (the Lean BoolReflect family and the
   eqn_task/eqn_job statements are not targets of this export); every kept block is unchanged. *)
(* Copy of the accepted certificates/implementation/ExtrapolatedArrivalCurveFullCorrespondence.v, re-bound to this
   export: the imported module is this file's, and the source side is the pinned extrapolated_arrival_curve.v
   (compiled under its Rocq 9.3 import-compatibility patch) instead of the accepted definition-extracted
   OfficialExtrapolatedArrivalCurve signature; its Print Assumptions commands are dropped, and so are the 34
   blocks about the validity predicates, sortedness, membership and time steps (their Lean definitions are not
   reachable from this file's targets and are absent from this export); every kept block is unchanged. *)
From mathcomp Require Import ssreflect ssrbool ssrnat seq div.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedRefFPPSched.
From FoundationCertificates Require Import
  PropSPropFoundation LogicalRelation SubadditivityNatCorrespondence.
From prosa Require Import implementation.definitions.extrapolated_arrival_curve.

(** An operation-level representation relation for the actual imported
    Lean product/list constructors. Source sequence order and multiplicity
    are retained. *)
Definition eac_imported_step (p : nat * nat) :
    ImportedRefFPPSched.Prod_inst3 Lean.Nat Lean.Nat :=
  match p with
  | (t, n) => ImportedRefFPPSched.Prod_mk_inst3
      Lean.Nat Lean.Nat (sub_nat_to_imported t) (sub_nat_to_imported n)
  end.

Fixpoint eac_imported_steps (xs : seq (nat * nat)) :
    ImportedRefFPPSched.List_inst1
      (ImportedRefFPPSched.Prod_inst3 Lean.Nat Lean.Nat) :=
  match xs with
  | [::] => ImportedRefFPPSched.List_nil_inst1 _
  | x :: tail => ImportedRefFPPSched.List_cons_inst1 _
      (eac_imported_step x) (eac_imported_steps tail)
  end.

Fixpoint eac_imported_times (xs : seq nat) :
    ImportedRefFPPSched.List_inst1 Lean.Nat :=
  match xs with
  | [::] => ImportedRefFPPSched.List_nil_inst1 _
  | x :: tail => ImportedRefFPPSched.List_cons_inst1 _
      (sub_nat_to_imported x) (eac_imported_times tail)
  end.

Definition eac_imported_prefix
    (p : prosa.implementation.definitions.extrapolated_arrival_curve.ArrivalCurvePrefix) :
    ImportedRefFPPSched.Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_ArrivalCurvePrefix :=
  match p with
  | (h, steps) => ImportedRefFPPSched.Prod_mk_inst3
      Lean.Nat _ (sub_nat_to_imported h) (eac_imported_steps steps)
  end.

Definition EacPrefixRel (pR : prosa.implementation.definitions.extrapolated_arrival_curve.ArrivalCurvePrefix)
    (pL : ImportedRefFPPSched.Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_ArrivalCurvePrefix) : SProp :=
  Lean.eq (eac_imported_prefix pR) pL.

(** The public prefix alias is represented by a product of a Nat and an
    ordered list of Nat pairs on both sides.  These decoders show that the
    representation relation covers every imported value, not merely values
    produced by one source constructor. *)
Definition eac_rocq_step
    (p : ImportedRefFPPSched.Prod_inst3 Lean.Nat Lean.Nat) :
    nat * nat :=
  match p with
  | ImportedRefFPPSched.Prod_mk_inst3 t n =>
      (sub_nat_to_rocq t, sub_nat_to_rocq n)
  end.

Fixpoint eac_rocq_steps
    (xs : ImportedRefFPPSched.List_inst1
      (ImportedRefFPPSched.Prod_inst3 Lean.Nat Lean.Nat)) :
    seq (nat * nat) :=
  match xs with
  | ImportedRefFPPSched.List_nil_inst1 => [::]
  | ImportedRefFPPSched.List_cons_inst1 x tail =>
      eac_rocq_step x :: eac_rocq_steps tail
  end.

Definition eac_rocq_prefix
    (p : ImportedRefFPPSched.Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_ArrivalCurvePrefix) :
    prosa.implementation.definitions.extrapolated_arrival_curve.ArrivalCurvePrefix :=
  match p with
  | ImportedRefFPPSched.Prod_mk_inst3 h steps =>
      (sub_nat_to_rocq h, eac_rocq_steps steps)
  end.

Lemma eac_step_rocq_roundtrip p :
  Logic.eq (eac_rocq_step (eac_imported_step p)) p.
Proof.
  destruct p as [t n]. unfold eac_rocq_step, eac_imported_step. cbn.
  rewrite (sub_nat_rocq_roundtrip t) (sub_nat_rocq_roundtrip n).
  reflexivity.
Qed.

Lemma eac_step_imported_roundtrip p :
  Lean.eq (eac_imported_step (eac_rocq_step p)) p.
Proof.
  destruct p as [t n]. cbn.
  exact (sub_imported_eq_congr2
    (ImportedRefFPPSched.Prod_mk_inst3 Lean.Nat Lean.Nat)
    _ _ _ _ (sub_nat_imported_roundtrip t)
    (sub_nat_imported_roundtrip n)).
Qed.

Lemma eac_steps_rocq_roundtrip xs :
  Logic.eq (eac_rocq_steps (eac_imported_steps xs)) xs.
Proof.
  induction xs as [|x tail IH]; cbn.
  - reflexivity.
  - rewrite (eac_step_rocq_roundtrip x) IH. reflexivity.
Qed.

Lemma eac_steps_imported_roundtrip xs :
  Lean.eq (eac_imported_steps (eac_rocq_steps xs)) xs.
Proof.
  induction xs as [|x tail IH]; cbn.
  - exact (@Lean.eq_refl _ _).
  - exact (sub_imported_eq_congr2
      (ImportedRefFPPSched.List_cons_inst1 _)
      _ _ _ _ (eac_step_imported_roundtrip x) IH).
Qed.

Lemma eac_prefix_rocq_roundtrip p :
  Logic.eq (eac_rocq_prefix (eac_imported_prefix p)) p.
Proof.
  destruct p as [h steps]. unfold eac_rocq_prefix, eac_imported_prefix. cbn.
  rewrite (sub_nat_rocq_roundtrip h) (eac_steps_rocq_roundtrip steps).
  reflexivity.
Qed.

Lemma eac_prefix_imported_roundtrip p :
  EacPrefixRel (eac_rocq_prefix p) p.
Proof.
  destruct p as [h steps]. cbn.
  exact (sub_imported_eq_congr2
    (ImportedRefFPPSched.Prod_mk_inst3 Lean.Nat _)
    _ _ _ _ (sub_nat_imported_roundtrip h)
    (eac_steps_imported_roundtrip steps)).
Qed.

Fixpoint eac_rocq_times
    (xs : ImportedRefFPPSched.List_inst1 Lean.Nat) : seq nat :=
  match xs with
  | ImportedRefFPPSched.List_nil_inst1 => [::]
  | ImportedRefFPPSched.List_cons_inst1 x tail =>
      sub_nat_to_rocq x :: eac_rocq_times tail
  end.

Lemma eac_times_rocq_roundtrip xs :
  Logic.eq (eac_rocq_times (eac_imported_times xs)) xs.
Proof.
  induction xs as [|x tail IH]; cbn.
  - reflexivity.
  - rewrite (sub_nat_rocq_roundtrip x) IH. reflexivity.
Qed.

Definition eac_mem_head_truth (a b : bool) :
  SubNatTruth a -> SubNatTruth (a || b) :=
  match a, b return SubNatTruth a -> SubNatTruth (a || b) with
  | true, _ => fun _ => sub_nat_truth_intro
  | false, _ => sub_nat_false_elim _
  end.

Definition eac_mem_tail_truth (a b : bool) :
  SubNatTruth b -> SubNatTruth (a || b) :=
  match a, b return SubNatTruth b -> SubNatTruth (a || b) with
  | true, _ => fun _ => sub_nat_truth_intro
  | false, true => fun _ => sub_nat_truth_intro
  | false, false => fun H => H
  end.

Definition eac_mem_refl_truth (x : nat) ys :
  SubNatTruth (x \in sub_nat_to_rocq (sub_nat_to_imported x) :: ys).
Proof.
  rewrite (sub_nat_rocq_roundtrip x) in_cons eqxx.
  exact sub_nat_truth_intro.
Defined.

Definition eac_mem_truth_transport (x : nat) (xs ys : seq nat) :
  Logic.eq xs ys -> SubNatTruth (x \in xs) -> SubNatTruth (x \in ys) :=
  fun H Htruth =>
    match H in Logic.eq _ zs return
      SubNatTruth (x \in xs) -> SubNatTruth (x \in zs) with
    | Logic.eq_refl => fun Ht => Ht
    end Htruth.

Definition eac_bool_to_imported (b : bool) :
    ImportedRefFPPSched.Bool :=
  match b with
  | true => ImportedRefFPPSched.Bool_true
  | false => ImportedRefFPPSched.Bool_false
  end.

Definition EacBoolRel (bR : bool)
    (bL : ImportedRefFPPSched.Bool) : SProp :=
  Lean.eq (eac_bool_to_imported bR) bL.

Definition eac_imported_false_elim (Q : SProp)
    (H : ImportedRefFPPSched.False) : Q :=
  match H return Q with end.

Definition eac_rocq_false_to_imported (H : Logic.False) :
    ImportedRefFPPSched.False :=
  match H return ImportedRefFPPSched.False with end.

Lemma eac_decide_bool_correspondence (bR : bool) (Q : SProp)
    (d : ImportedRefFPPSched.Decidable Q) :
  PropSPropRel (is_true bR) Q ->
  EacBoolRel bR
    (ImportedRefFPPSched.Decidable_decide Q d).
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
    ImportedRefFPPSched.Bool :=
  ImportedRefFPPSched.Decidable_decide
    (ImportedRefFPPSched.LE_le_inst1 Lean.Nat
      ImportedRefFPPSched.instLENat a b)
    (ImportedRefFPPSched.Nat_decLe a b).

Lemma eac_nat_le_bool_correspondence aR aL bR bL :
  SubNatRel aR aL -> SubNatRel bR bL ->
  EacBoolRel (leq aR bR) (eac_target_decide_le aL bL).
Proof.
  intros Ha Hb. apply eac_decide_bool_correspondence.
  exact (sub_nat_le_correspondence aR aL bR bL Ha Hb).
Qed.

Definition eac_target_decide_lt (a b : Lean.Nat) :
    ImportedRefFPPSched.Bool :=
  ImportedRefFPPSched.Decidable_decide
    (ImportedRefFPPSched.LT_lt_inst1 Lean.Nat
      ImportedRefFPPSched.instLTNat a b)
    (ImportedRefFPPSched.Nat_decLt a b).

Lemma eac_nat_lt_bool_correspondence aR aL bR bL :
  SubNatRel aR aL -> SubNatRel bR bL ->
  EacBoolRel (ltn aR bR) (eac_target_decide_lt aL bL).
Proof.
  intros Ha Hb. apply eac_decide_bool_correspondence.
  exact (sub_nat_lt_correspondence aR aL bR bL Ha Hb).
Qed.

Definition eac_target_decide_eq (a b : Lean.Nat) :
    ImportedRefFPPSched.Bool :=
  ImportedRefFPPSched.Decidable_decide
    (Lean.eq a b)
    (ImportedRefFPPSched.instDecidableEqNat a b).

Lemma eac_nat_eq_bool_correspondence aR aL bR bL :
  SubNatRel aR aL -> SubNatRel bR bL ->
  EacBoolRel (aR == bR) (eac_target_decide_eq aL bL).
Proof.
  intros Ha Hb. apply eac_decide_bool_correspondence.
  have Heq := sub_nat_eq_correspondence aR aL bR bL Ha Hb.
  constructor.
  - intro H. apply (prop_to_sprop _ _ Heq). by move/eqP: H.
  - intro H. apply/eqP. exact (sprop_to_prop _ _ Heq H).
Qed.

Lemma eac_bool_and_correspondence xR xL yR yL :
  EacBoolRel xR xL -> EacBoolRel yR yL ->
  EacBoolRel (andb xR yR)
    (ImportedRefFPPSched.Bool_and xL yL).
Proof.
  intros Hx Hy. destruct Hx. destruct Hy.
  destruct xR, yR; exact (@Lean.eq_refl _ _).
Qed.

Definition eac_imported_false_ne_true
    (H : Lean.eq ImportedRefFPPSched.Bool_false
      ImportedRefFPPSched.Bool_true) :
    ImportedRefFPPSched.False :=
  match H in Lean.eq _ b return
      match b with
      | ImportedRefFPPSched.Bool_false =>
          ImportedRefFPPSched.True
      | ImportedRefFPPSched.Bool_true =>
          ImportedRefFPPSched.False
      end with
  | Lean.eq_refl => ImportedRefFPPSched.True_intro
  end.

Lemma eac_bool_truth_correspondence bR bL :
  EacBoolRel bR bL ->
  PropSPropRel (is_true bR)
    (Lean.eq bL ImportedRefFPPSched.Bool_true).
Proof.
  intro Hb. destruct Hb. destruct bR; cbn.
  - apply prop_sprop_rel_intro.
    + intro Htruth. exact (@Lean.eq_refl _ _).
    + intro Htruth. exact (strictly_inhabits (Logic.eq_refl true)).
  - apply prop_sprop_rel_intro.
    + intro H. discriminate H.
    + intro H. exact (eac_imported_false_elim _
        (eac_imported_false_ne_true H)).
Qed.

Lemma eac_and_correspondence P Q P' Q' :
  PropSPropRel P Q -> PropSPropRel P' Q' ->
  PropSPropRel (P /\ P') (Lean.And Q Q').
Proof.
  intros H1 H2. apply prop_sprop_rel_intro.
  - intros [HP HP']. exact (Lean.And_intro Q Q'
      (prop_to_sprop _ _ H1 HP) (prop_to_sprop _ _ H2 HP')).
  - intro H. apply strictly_inhabits. split.
    + exact (sprop_to_prop _ _ H1 (Lean.left Q Q' H)).
    + exact (sprop_to_prop _ _ H2 (Lean.right Q Q' H)).
Qed.

(** These maps preserve the informative constructor of MathComp [reflect]
    and the compiled Lean [BoolReflect].  They do not use either public proof
    term being validated. *)
Definition eac_bool_from_imported
    (b : ImportedRefFPPSched.Bool) : bool :=
  match b with
  | ImportedRefFPPSched.Bool_true => true
  | ImportedRefFPPSched.Bool_false => false
  end.

Definition eac_target_filter {A : Type}
    (P : A -> ImportedRefFPPSched.Bool)
    (xs : ImportedRefFPPSched.List_inst1 A) :=
  ImportedRefFPPSched.List_filter_inst1 A P xs.

Lemma eac_target_filter_nil {A : Type}
    (P : A -> ImportedRefFPPSched.Bool) :
    Lean.eq
      (eac_target_filter P
        (ImportedRefFPPSched.List_nil_inst1 A))
      (ImportedRefFPPSched.List_nil_inst1 A).
Proof. exact (@Lean.eq_refl _ _). Qed.

Lemma eac_target_filter_cons {A : Type}
    (P : A -> ImportedRefFPPSched.Bool) (x : A)
    (xs : ImportedRefFPPSched.List_inst1 A) :
    Lean.eq
      (eac_target_filter P
        (ImportedRefFPPSched.List_cons_inst1 A x xs))
      (match P x with
       | ImportedRefFPPSched.Bool_true =>
           ImportedRefFPPSched.List_cons_inst1 A x
             (eac_target_filter P xs)
       | ImportedRefFPPSched.Bool_false =>
           eac_target_filter P xs
       end).
Proof. exact (@Lean.eq_refl _ _). Qed.

Lemma eac_target_last_nil {A : Type} (fallback : A) :
  Lean.eq
    (ImportedRefFPPSched.List_getLastD_inst1 A
      (ImportedRefFPPSched.List_nil_inst1 A) fallback)
    fallback.
Proof. exact (@Lean.eq_refl _ _). Qed.

Lemma eac_target_last_singleton {A : Type} (x fallback : A) :
  Lean.eq
    (ImportedRefFPPSched.List_getLastD_inst1 A
      (ImportedRefFPPSched.List_cons_inst1 A x
        (ImportedRefFPPSched.List_nil_inst1 A)) fallback)
    x.
Proof. exact (@Lean.eq_refl _ _). Qed.

Lemma eac_target_last_cons_cons {A : Type} (x y : A)
    (xs : ImportedRefFPPSched.List_inst1 A)
    (fallback : A) :
  Lean.eq
    (ImportedRefFPPSched.List_getLastD_inst1 A
      (ImportedRefFPPSched.List_cons_inst1 A x
        (ImportedRefFPPSched.List_cons_inst1 A y xs)) fallback)
    (ImportedRefFPPSched.List_getLastD_inst1 A
      (ImportedRefFPPSched.List_cons_inst1 A y xs) fallback).
Proof. exact (@Lean.eq_refl _ _). Qed.

Definition eac_target_step_pred (t : Lean.Nat)
    (p : ImportedRefFPPSched.Prod_inst3 Lean.Nat Lean.Nat) :
    ImportedRefFPPSched.Bool :=
  eac_target_decide_le
    (ImportedRefFPPSched.Prod_fst_inst3 Lean.Nat Lean.Nat p) t.

Lemma eac_filter_branch_canonical (b : bool) (x : nat * nat)
    (filtered : seq (nat * nat))
    (tail : ImportedRefFPPSched.List_inst1
      (ImportedRefFPPSched.Prod_inst3 Lean.Nat Lean.Nat)) :
  Lean.eq tail (eac_imported_steps filtered) ->
  Lean.eq
    (match eac_bool_to_imported b with
     | ImportedRefFPPSched.Bool_true =>
         ImportedRefFPPSched.List_cons_inst1 _
           (eac_imported_step x) tail
     | ImportedRefFPPSched.Bool_false => tail
     end)
    (eac_imported_steps
      (if b then x :: filtered else filtered)).
Proof.
  intro Htail. destruct b; cbn.
  - exact (sub_imported_eq_congr
      (ImportedRefFPPSched.List_cons_inst1 _
        (eac_imported_step x)) _ _ Htail).
  - exact Htail.
Qed.

Lemma eac_filter_steps_generic (PR : nat * nat -> bool)
    (PL : ImportedRefFPPSched.Prod_inst3 Lean.Nat Lean.Nat ->
      ImportedRefFPPSched.Bool)
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
        (fun z : ImportedRefFPPSched.Bool =>
          match z with
          | ImportedRefFPPSched.Bool_true =>
              ImportedRefFPPSched.List_cons_inst1 _
                (eac_imported_step x)
                (eac_target_filter PL (eac_imported_steps tail))
          | ImportedRefFPPSched.Bool_false =>
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
    (dL : ImportedRefFPPSched.Prod_inst3 Lean.Nat Lean.Nat)
    (Hd : Lean.eq (eac_imported_step dR) dL)
    (xs : seq (nat * nat)) :
  Lean.eq (eac_imported_step (last dR xs))
    (ImportedRefFPPSched.List_getLastD_inst1 _
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
      (prosa.implementation.definitions.extrapolated_arrival_curve.inter_arrival_to_prefix pR)
      (ImportedRefFPPSched.Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_inter_arrival_to_prefix pL).
Proof.
  intros pR pL Hp.
  destruct Hp.
  exact (@Lean.eq_refl _ _).
Qed.

Lemma eac_horizon_of_correspondence :
  forall pR pL, EacPrefixRel pR pL ->
    SubNatRel
      (prosa.implementation.definitions.extrapolated_arrival_curve.horizon_of pR)
      (ImportedRefFPPSched.Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_horizon_of pL).
Proof.
  intros [h steps] pL Hp.
  destruct Hp.
  exact (@Lean.eq_refl _ _).
Qed.

Lemma eac_steps_of_correspondence :
  forall pR pL, EacPrefixRel pR pL ->
    Lean.eq
      (eac_imported_steps
        (prosa.implementation.definitions.extrapolated_arrival_curve.steps_of pR))
      (ImportedRefFPPSched.Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_steps_of pL).
Proof.
  intros [h steps] pL Hp.
  destruct Hp.
  exact (@Lean.eq_refl _ _).
Qed.

Lemma eac_step_at_correspondence :
  forall pR pL tR tL,
    EacPrefixRel pR pL -> SubNatRel tR tL ->
    Lean.eq
      (eac_imported_step
        (prosa.implementation.definitions.extrapolated_arrival_curve.step_at pR tR))
      (ImportedRefFPPSched.Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_step_at pL tL).
Proof.
  intros [h steps] pL tR tL Hp Ht.
  destruct Hp.
  set (defaultL := ImportedRefFPPSched.Prod_mk_inst3
    Lean.Nat Lean.Nat Lean.Nat_zero Lean.Nat_zero).
  have Hdefault : Lean.eq (eac_imported_step (O, O)) defaultL :=
    @Lean.eq_refl _ _.
  have Hfilter := eac_filter_steps_canonical tR tL Ht steps.
  have Hlast := eac_last_steps_canonical (O, O) defaultL Hdefault
    (filter (fun p : nat * nat => leq (Datatypes.fst p) tR) steps).
  exact (sub_imported_eq_trans _ _ _ Hlast
    (sub_imported_eq_congr
      (fun xs => ImportedRefFPPSched.List_getLastD_inst1 _
        xs defaultL) _ _ (sub_imported_eq_sym _ _ Hfilter))).
Qed.

Lemma eac_step_snd_correspondence (pR : nat * nat)
    (pL : ImportedRefFPPSched.Prod_inst3 Lean.Nat Lean.Nat) :
  Lean.eq (eac_imported_step pR) pL ->
  SubNatRel (Datatypes.snd pR)
    (ImportedRefFPPSched.Prod_snd_inst3 Lean.Nat Lean.Nat pL).
Proof.
  destruct pR as [a b]. intro Hp.
  exact (sub_imported_eq_congr
    (ImportedRefFPPSched.Prod_snd_inst3 Lean.Nat Lean.Nat)
    _ _ Hp).
Qed.

Lemma eac_value_at_correspondence :
  forall pR pL tR tL,
    EacPrefixRel pR pL -> SubNatRel tR tL ->
    SubNatRel
      (prosa.implementation.definitions.extrapolated_arrival_curve.value_at pR tR)
      (ImportedRefFPPSched.Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_value_at pL tL).
Proof.
  intros pR pL tR tL Hp Ht.
  exact (eac_step_snd_correspondence _ _
    (eac_step_at_correspondence pR pL tR tL Hp Ht)).
Qed.

Definition eac_imported_add (a b : Lean.Nat) : Lean.Nat :=
  ImportedRefFPPSched.HAdd_hAdd_inst7 Lean.Nat Lean.Nat Lean.Nat
    (ImportedRefFPPSched.instHAdd_inst1 Lean.Nat
      ImportedRefFPPSched.instAddNat) a b.

Definition eac_imported_mul (a b : Lean.Nat) : Lean.Nat :=
  ImportedRefFPPSched.HMul_hMul_inst7 Lean.Nat Lean.Nat Lean.Nat
    (ImportedRefFPPSched.instHMul_inst1 Lean.Nat
      ImportedRefFPPSched.instMulNat) a b.

Definition eac_imported_div (a b : Lean.Nat) : Lean.Nat :=
  ImportedRefFPPSched.HDiv_hDiv_inst7 Lean.Nat Lean.Nat Lean.Nat
    (ImportedRefFPPSched.instHDiv_inst1 Lean.Nat
      ImportedRefFPPSched.Nat_instDiv) a b.

Definition eac_imported_mod (a b : Lean.Nat) : Lean.Nat :=
  ImportedRefFPPSched.HMod_hMod_inst7 Lean.Nat Lean.Nat Lean.Nat
    (ImportedRefFPPSched.instHMod_inst1 Lean.Nat
      ImportedRefFPPSched.Nat_instMod) a b.

Definition eac_imported_zero : Lean.Nat :=
  ImportedRefFPPSched.OfNat_ofNat_inst1 Lean.Nat Lean.Nat_zero
    (ImportedRefFPPSched.instOfNatNat Lean.Nat_zero).

Lemma eac_add_correspondence aR aL bR bL :
  SubNatRel aR aL -> SubNatRel bR bL ->
  SubNatRel (aR + bR) (eac_imported_add aL bL).
Proof.
  change (SubNatRel aR aL -> SubNatRel bR bL ->
    SubNatRel (aR + bR) (sub_imported_add aL bL)).
  exact (sub_add_correspondence aR aL bR bL).
Qed.

Lemma eac_mul_correspondence aR aL bR bL :
  SubNatRel aR aL -> SubNatRel bR bL ->
  SubNatRel (aR * bR) (eac_imported_mul aL bL).
Proof.
  change (SubNatRel aR aL -> SubNatRel bR bL ->
    SubNatRel (aR * bR) (sub_imported_mul aL bL)).
  exact (sub_mul_correspondence aR aL bR bL).
Qed.

Lemma eac_lt_correspondence aR aL bR bL :
  SubNatRel aR aL -> SubNatRel bR bL ->
  PropSPropRel (is_true (ltn aR bR))
    (ImportedRefFPPSched.LT_lt_inst1 Lean.Nat
      ImportedRefFPPSched.instLTNat aL bL).
Proof.
  change (SubNatRel aR aL -> SubNatRel bR bL ->
    PropSPropRel (is_true (ltn aR bR)) (sub_imported_lt aL bL)).
  exact (sub_nat_lt_correspondence aR aL bR bL).
Qed.

Lemma eac_eq_correspondence aR aL bR bL :
  SubNatRel aR aL -> SubNatRel bR bL ->
  PropSPropRel (Logic.eq aR bR) (Lean.eq aL bL).
Proof. exact (sub_nat_eq_correspondence aR aL bR bL). Qed.

Lemma eac_div_mod_decoded_canonical (x y : nat) :
  Logic.eq
    (sub_nat_to_rocq
      (eac_imported_div (sub_nat_to_imported x) (sub_nat_to_imported y)))
    (x %/ y) /\
  Logic.eq
    (sub_nat_to_rocq
      (eac_imported_mod (sub_nat_to_imported x) (sub_nat_to_imported y)))
    (x %% y).
Proof.
  case Hy: y => [|y'].
  - subst y. split.
    + rewrite divn0.
      have H :=
        ImportedRefFPPSched.Prosa_Validation_ExtrapolatedArrivalCurveArithmeticInterface_production_div_zero
          (sub_nat_to_imported x).
      exact (f_equal sub_nat_to_rocq
        (imported_eq_to_coq_eq _ _ H)).
    + rewrite modn0.
      have H :=
        ImportedRefFPPSched.Prosa_Validation_ExtrapolatedArrivalCurveArithmeticInterface_production_mod_zero
          (sub_nat_to_imported x).
      transitivity
        (sub_nat_to_rocq (sub_nat_to_imported x)).
      * exact (f_equal sub_nat_to_rocq
          (imported_eq_to_coq_eq _ _ H)).
      * exact (sub_nat_rocq_roundtrip x).
  - have Hypos : is_true (ltn O y'.+1) by done.
    set xL := sub_nat_to_imported x.
    set yL := sub_nat_to_imported y'.+1.
    set qL := eac_imported_div xL yL.
    set rL := eac_imported_mod xL yL.
    have HrLtR : is_true (ltn (sub_nat_to_rocq rL) y'.+1).
    { exact (sprop_to_prop _ _
        (eac_lt_correspondence (sub_nat_to_rocq rL) rL y'.+1 yL
          (sub_nat_rel_surjective rL) (sub_nat_rel_canonical y'.+1))
        (ImportedRefFPPSched.Prosa_Validation_ExtrapolatedArrivalCurveArithmeticInterface_production_mod_lt
          xL yL
          (prop_to_sprop _ _
            (eac_lt_correspondence O eac_imported_zero y'.+1 yL
              (sub_nat_rel_canonical O) (sub_nat_rel_canonical y'.+1))
            Hypos))). }
    have HdecompR : Logic.eq
        (y'.+1 * sub_nat_to_rocq qL + sub_nat_to_rocq rL) x.
    { exact (sprop_to_prop _ _
        (eac_eq_correspondence
          (y'.+1 * sub_nat_to_rocq qL + sub_nat_to_rocq rL)
          (eac_imported_add (eac_imported_mul yL qL) rL)
          x xL
          (eac_add_correspondence _ _ _ _
            (eac_mul_correspondence y'.+1 yL
              (sub_nat_to_rocq qL) qL
              (sub_nat_rel_canonical y'.+1)
              (sub_nat_rel_surjective qL))
            (sub_nat_rel_surjective rL))
          (sub_nat_rel_canonical x))
        (ImportedRefFPPSched.Prosa_Validation_ExtrapolatedArrivalCurveArithmeticInterface_production_div_add_mod
          xL yL)). }
    have Hx : Logic.eq x
        (sub_nat_to_rocq qL * y'.+1 + sub_nat_to_rocq rL).
    { rewrite mulnC. exact (Logic.eq_sym HdecompR). }
    have Hedge : Logic.eq (edivn x y'.+1)
        (sub_nat_to_rocq qL, sub_nat_to_rocq rL).
    { rewrite Hx. exact (@edivn_eq y'.+1 (sub_nat_to_rocq qL)
        (sub_nat_to_rocq rL) HrLtR). }
    have Hq := f_equal (@Datatypes.fst nat nat) Hedge.
    change (Logic.eq (divn x (S y')) (sub_nat_to_rocq qL)) in Hq.
    have Hr := f_equal (@Datatypes.snd nat nat) Hedge.
    change (Logic.eq (Datatypes.snd (edivn x (S y')))
      (sub_nat_to_rocq rL)) in Hr.
    rewrite <- (modn_def x y'.+1) in Hr.
    split; exact (Logic.eq_sym Hq) || exact (Logic.eq_sym Hr).
Qed.

Lemma eac_div_canonical (x y : nat) :
  Lean.eq
    (eac_imported_div (sub_nat_to_imported x) (sub_nat_to_imported y))
    (sub_nat_to_imported (x %/ y)).
Proof.
  have Hdecoded := proj1 (eac_div_mod_decoded_canonical x y).
  exact (sub_imported_eq_trans _ _ _
    (sub_imported_eq_sym _ _
      (sub_nat_imported_roundtrip
        (eac_imported_div (sub_nat_to_imported x) (sub_nat_to_imported y))))
    (coq_eq_to_imported_eq _ _ (f_equal sub_nat_to_imported Hdecoded))).
Qed.

Lemma eac_mod_canonical (x y : nat) :
  Lean.eq
    (eac_imported_mod (sub_nat_to_imported x) (sub_nat_to_imported y))
    (sub_nat_to_imported (x %% y)).
Proof.
  have Hdecoded := proj2 (eac_div_mod_decoded_canonical x y).
  exact (sub_imported_eq_trans _ _ _
    (sub_imported_eq_sym _ _
      (sub_nat_imported_roundtrip
        (eac_imported_mod (sub_nat_to_imported x) (sub_nat_to_imported y))))
    (coq_eq_to_imported_eq _ _ (f_equal sub_nat_to_imported Hdecoded))).
Qed.

Lemma eac_div_correspondence xR xL yR yL :
  SubNatRel xR xL -> SubNatRel yR yL ->
  SubNatRel (xR %/ yR) (eac_imported_div xL yL).
Proof.
  intros Hx Hy. unfold SubNatRel.
  exact (sub_imported_eq_trans _ _ _
    (sub_imported_eq_sym _ _ (eac_div_canonical xR yR))
    (sub_imported_eq_congr2 eac_imported_div _ _ _ _ Hx Hy)).
Qed.

Lemma eac_mod_correspondence xR xL yR yL :
  SubNatRel xR xL -> SubNatRel yR yL ->
  SubNatRel (xR %% yR) (eac_imported_mod xL yL).
Proof.
  intros Hx Hy. unfold SubNatRel.
  exact (sub_imported_eq_trans _ _ _
    (sub_imported_eq_sym _ _ (eac_mod_canonical xR yR))
    (sub_imported_eq_congr2 eac_imported_mod _ _ _ _ Hx Hy)).
Qed.

Lemma eac_extrapolated_arrival_curve_correspondence :
  forall pR pL tR tL,
    EacPrefixRel pR pL -> SubNatRel tR tL ->
    SubNatRel
      (prosa.implementation.definitions.extrapolated_arrival_curve.extrapolated_arrival_curve pR tR)
      (ImportedRefFPPSched.Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_extrapolated_arrival_curve pL tL).
Proof.
  intros pR pL tR tL Hp Ht.
  have Hh := eac_horizon_of_correspondence pR pL Hp.
  have Hdiv := eac_div_correspondence tR tL
    (prosa.implementation.definitions.extrapolated_arrival_curve.horizon_of pR)
    (ImportedRefFPPSched.Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_horizon_of pL)
    Ht Hh.
  have Hmod := eac_mod_correspondence tR tL
    (prosa.implementation.definitions.extrapolated_arrival_curve.horizon_of pR)
    (ImportedRefFPPSched.Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_horizon_of pL)
    Ht Hh.
  have Hv := eac_value_at_correspondence pR pL _ _ Hp Hh.
  have Hvm := eac_value_at_correspondence pR pL _ _ Hp Hmod.
  unfold prosa.implementation.definitions.extrapolated_arrival_curve.extrapolated_arrival_curve,
    ImportedRefFPPSched.Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_extrapolated_arrival_curve.
  exact (eac_add_correspondence _ _ _ _
    (eac_mul_correspondence _ _ _ _ Hdiv Hv) Hvm).
Qed.
