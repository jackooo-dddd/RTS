From mathcomp Require Import ssreflect ssrbool ssrnat seq div.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedExtrapolatedArrivalCurve.
From FoundationCertificates Require Import
  PropSPropFoundation LogicalRelation SubadditivityNatCorrespondence.
Require Import OfficialExtrapolatedArrivalCurve.

(** An operation-level representation relation for the actual imported
    Lean product/list constructors. Source sequence order and multiplicity
    are retained. *)
Definition eac_imported_step (p : nat * nat) :
    ImportedExtrapolatedArrivalCurve.Prod_inst3 Lean.Nat Lean.Nat :=
  match p with
  | (t, n) => ImportedExtrapolatedArrivalCurve.Prod_mk_inst3
      Lean.Nat Lean.Nat (sub_nat_to_imported t) (sub_nat_to_imported n)
  end.

Fixpoint eac_imported_steps (xs : seq (nat * nat)) :
    ImportedExtrapolatedArrivalCurve.List_inst1
      (ImportedExtrapolatedArrivalCurve.Prod_inst3 Lean.Nat Lean.Nat) :=
  match xs with
  | [::] => ImportedExtrapolatedArrivalCurve.List_nil_inst1 _
  | x :: tail => ImportedExtrapolatedArrivalCurve.List_cons_inst1 _
      (eac_imported_step x) (eac_imported_steps tail)
  end.

Fixpoint eac_imported_times (xs : seq nat) :
    ImportedExtrapolatedArrivalCurve.List_inst1 Lean.Nat :=
  match xs with
  | [::] => ImportedExtrapolatedArrivalCurve.List_nil_inst1 _
  | x :: tail => ImportedExtrapolatedArrivalCurve.List_cons_inst1 _
      (sub_nat_to_imported x) (eac_imported_times tail)
  end.

Definition eac_imported_prefix
    (p : OfficialExtrapolatedArrivalCurve.ArrivalCurvePrefix) :
    ImportedExtrapolatedArrivalCurve.Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_ArrivalCurvePrefix :=
  match p with
  | (h, steps) => ImportedExtrapolatedArrivalCurve.Prod_mk_inst3
      Lean.Nat _ (sub_nat_to_imported h) (eac_imported_steps steps)
  end.

Definition EacPrefixRel (pR : OfficialExtrapolatedArrivalCurve.ArrivalCurvePrefix)
    (pL : ImportedExtrapolatedArrivalCurve.Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_ArrivalCurvePrefix) : SProp :=
  Lean.eq (eac_imported_prefix pR) pL.

(** The public prefix alias is represented by a product of a Nat and an
    ordered list of Nat pairs on both sides.  These decoders show that the
    representation relation covers every imported value, not merely values
    produced by one source constructor. *)
Definition eac_rocq_step
    (p : ImportedExtrapolatedArrivalCurve.Prod_inst3 Lean.Nat Lean.Nat) :
    nat * nat :=
  match p with
  | ImportedExtrapolatedArrivalCurve.Prod_mk_inst3 t n =>
      (sub_nat_to_rocq t, sub_nat_to_rocq n)
  end.

Fixpoint eac_rocq_steps
    (xs : ImportedExtrapolatedArrivalCurve.List_inst1
      (ImportedExtrapolatedArrivalCurve.Prod_inst3 Lean.Nat Lean.Nat)) :
    seq (nat * nat) :=
  match xs with
  | ImportedExtrapolatedArrivalCurve.List_nil_inst1 => [::]
  | ImportedExtrapolatedArrivalCurve.List_cons_inst1 x tail =>
      eac_rocq_step x :: eac_rocq_steps tail
  end.

Definition eac_rocq_prefix
    (p : ImportedExtrapolatedArrivalCurve.Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_ArrivalCurvePrefix) :
    OfficialExtrapolatedArrivalCurve.ArrivalCurvePrefix :=
  match p with
  | ImportedExtrapolatedArrivalCurve.Prod_mk_inst3 h steps =>
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
    (ImportedExtrapolatedArrivalCurve.Prod_mk_inst3 Lean.Nat Lean.Nat)
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
      (ImportedExtrapolatedArrivalCurve.List_cons_inst1 _)
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
    (ImportedExtrapolatedArrivalCurve.Prod_mk_inst3 Lean.Nat _)
    _ _ _ _ (sub_nat_imported_roundtrip h)
    (eac_steps_imported_roundtrip steps)).
Qed.

Fixpoint eac_rocq_times
    (xs : ImportedExtrapolatedArrivalCurve.List_inst1 Lean.Nat) : seq nat :=
  match xs with
  | ImportedExtrapolatedArrivalCurve.List_nil_inst1 => [::]
  | ImportedExtrapolatedArrivalCurve.List_cons_inst1 x tail =>
      sub_nat_to_rocq x :: eac_rocq_times tail
  end.

Lemma eac_times_rocq_roundtrip xs :
  Logic.eq (eac_rocq_times (eac_imported_times xs)) xs.
Proof.
  induction xs as [|x tail IH]; cbn.
  - reflexivity.
  - rewrite (sub_nat_rocq_roundtrip x) IH. reflexivity.
Qed.

Definition eac_target_mem (x : Lean.Nat)
    (xs : ImportedExtrapolatedArrivalCurve.List_inst1 Lean.Nat) : SProp :=
  ImportedExtrapolatedArrivalCurve.Membership_mem_inst3 Lean.Nat
    (ImportedExtrapolatedArrivalCurve.List_inst1 Lean.Nat)
    (ImportedExtrapolatedArrivalCurve.List_instMembership_inst1 Lean.Nat)
    xs x.

Definition eac_list_mem_transport (x : Lean.Nat) xs ys :
  Lean.eq xs ys ->
  ImportedExtrapolatedArrivalCurve.List_Mem_inst1 Lean.Nat x xs ->
  ImportedExtrapolatedArrivalCurve.List_Mem_inst1 Lean.Nat x ys :=
  fun Hxy Hmem =>
    match Hxy in Lean.eq _ zs return
        ImportedExtrapolatedArrivalCurve.List_Mem_inst1 Lean.Nat x zs with
    | Lean.eq_refl => Hmem
    end.

Definition eac_mem_element_transport (x y : Lean.Nat) xs :
  Lean.eq x y ->
  ImportedExtrapolatedArrivalCurve.List_Mem_inst1 Lean.Nat x xs ->
  ImportedExtrapolatedArrivalCurve.List_Mem_inst1 Lean.Nat y xs :=
  fun Hxy Hmem =>
    match Hxy in Lean.eq _ z return
        ImportedExtrapolatedArrivalCurve.List_Mem_inst1 Lean.Nat z xs with
    | Lean.eq_refl => Hmem
    end.

Definition eac_mem_head_of_nat_eq (x y : nat) ys :
  Logic.eq x y ->
  ImportedExtrapolatedArrivalCurve.List_Mem_inst1 Lean.Nat
    (sub_nat_to_imported x)
    (ImportedExtrapolatedArrivalCurve.List_cons_inst1 Lean.Nat
      (sub_nat_to_imported y) ys) :=
  fun Hxy => match Hxy in Logic.eq _ z return
      ImportedExtrapolatedArrivalCurve.List_Mem_inst1 Lean.Nat
        (sub_nat_to_imported x)
        (ImportedExtrapolatedArrivalCurve.List_cons_inst1 Lean.Nat
          (sub_nat_to_imported z) ys) with
    | Logic.eq_refl =>
        ImportedExtrapolatedArrivalCurve.List_Mem_head_inst1 Lean.Nat
          (sub_nat_to_imported x) ys
    end.

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

Fixpoint eac_seq_mem_forward (x : nat) (xs : seq nat) :
  SubNatTruth (x \in xs) ->
  ImportedExtrapolatedArrivalCurve.List_Mem_inst1 Lean.Nat
    (sub_nat_to_imported x) (eac_imported_times xs) :=
  match xs as zs return SubNatTruth (x \in zs) ->
      ImportedExtrapolatedArrivalCurve.List_Mem_inst1 Lean.Nat
        (sub_nat_to_imported x) (eac_imported_times zs) with
  | [::] => sub_nat_false_elim _
  | y :: ys =>
      match @eqP _ x y as r in reflect _ b return
        SubNatTruth (b || (x \in ys)) ->
        ImportedExtrapolatedArrivalCurve.List_Mem_inst1 Lean.Nat
          (sub_nat_to_imported x)
          (ImportedExtrapolatedArrivalCurve.List_cons_inst1 Lean.Nat
            (sub_nat_to_imported y) (eac_imported_times ys)) with
      | ReflectT Hxy => fun _ =>
          eac_mem_head_of_nat_eq x y (eac_imported_times ys) Hxy
      | ReflectF _ => fun H =>
          ImportedExtrapolatedArrivalCurve.List_Mem_tail_inst1 Lean.Nat
            (sub_nat_to_imported x) (sub_nat_to_imported y)
            (eac_imported_times ys) (eac_seq_mem_forward x ys H)
      end
  end.

Definition eac_mem_refl_truth (x : nat) ys :
  SubNatTruth (x \in sub_nat_to_rocq (sub_nat_to_imported x) :: ys).
Proof.
  rewrite (sub_nat_rocq_roundtrip x) in_cons eqxx.
  exact sub_nat_truth_intro.
Defined.

Fixpoint eac_imported_mem_decoded (x : nat)
    (xs : ImportedExtrapolatedArrivalCurve.List_inst1 Lean.Nat)
    (H : ImportedExtrapolatedArrivalCurve.List_Mem_inst1 Lean.Nat
      (sub_nat_to_imported x) xs) :
    SubNatTruth (x \in eac_rocq_times xs) :=
  match H with
  | ImportedExtrapolatedArrivalCurve.List_Mem_head_inst1 ys =>
      eac_mem_refl_truth x (eac_rocq_times ys)
  | ImportedExtrapolatedArrivalCurve.List_Mem_tail_inst1 y ys Htail =>
      eac_mem_tail_truth _ _ (eac_imported_mem_decoded x ys Htail)
  end.

Definition eac_mem_truth_transport (x : nat) (xs ys : seq nat) :
  Logic.eq xs ys -> SubNatTruth (x \in xs) -> SubNatTruth (x \in ys) :=
  fun H Htruth =>
    match H in Logic.eq _ zs return
      SubNatTruth (x \in xs) -> SubNatTruth (x \in zs) with
    | Logic.eq_refl => fun Ht => Ht
    end Htruth.

Lemma eac_nat_membership_correspondence (x : nat) (xsR : seq nat)
    (xsL : ImportedExtrapolatedArrivalCurve.List_inst1 Lean.Nat) :
  Lean.eq (eac_imported_times xsR) xsL ->
  PropSPropRel (x \in xsR)
    (eac_target_mem (sub_nat_to_imported x) xsL).
Proof.
  intro Hxs. constructor.
  - intro Hmem. unfold eac_target_mem.
    apply (eac_list_mem_transport (sub_nat_to_imported x) _ _ Hxs).
    apply eac_seq_mem_forward. exact (sub_nat_prop_to_truth _ Hmem).
  - intro Hmem. apply interpret_strict. apply sub_nat_truth_to_strict_prop.
    apply (eac_mem_truth_transport x _ _ (eac_times_rocq_roundtrip xsR)).
    apply eac_imported_mem_decoded. unfold eac_target_mem in Hmem.
    exact (eac_list_mem_transport (sub_nat_to_imported x) _ _
      (sub_imported_eq_sym _ _ Hxs) Hmem).
Qed.

Definition eac_target_decide_mem_nat (x : Lean.Nat)
    (xs : ImportedExtrapolatedArrivalCurve.List_inst1 Lean.Nat) :
    ImportedExtrapolatedArrivalCurve.Bool :=
  ImportedExtrapolatedArrivalCurve.Decidable_decide
    (eac_target_mem x xs)
    (ImportedExtrapolatedArrivalCurve.List_instDecidableMemOfLawfulBEq_inst1
      Lean.Nat
      (ImportedExtrapolatedArrivalCurve.instBEqOfDecidableEq_inst1
        Lean.Nat ImportedExtrapolatedArrivalCurve.instDecidableEqNat)
      ImportedExtrapolatedArrivalCurve.Nat_instLawfulBEq x xs).

Definition eac_bool_to_imported (b : bool) :
    ImportedExtrapolatedArrivalCurve.Bool :=
  match b with
  | true => ImportedExtrapolatedArrivalCurve.Bool_true
  | false => ImportedExtrapolatedArrivalCurve.Bool_false
  end.

Definition EacBoolRel (bR : bool)
    (bL : ImportedExtrapolatedArrivalCurve.Bool) : SProp :=
  Lean.eq (eac_bool_to_imported bR) bL.

Definition eac_imported_false_elim (Q : SProp)
    (H : ImportedExtrapolatedArrivalCurve.False) : Q :=
  match H return Q with end.

Definition eac_rocq_false_to_imported (H : Logic.False) :
    ImportedExtrapolatedArrivalCurve.False :=
  match H return ImportedExtrapolatedArrivalCurve.False with end.

Lemma eac_decide_bool_correspondence (bR : bool) (Q : SProp)
    (d : ImportedExtrapolatedArrivalCurve.Decidable Q) :
  PropSPropRel (is_true bR) Q ->
  EacBoolRel bR
    (ImportedExtrapolatedArrivalCurve.Decidable_decide Q d).
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
    ImportedExtrapolatedArrivalCurve.Bool :=
  ImportedExtrapolatedArrivalCurve.Decidable_decide
    (ImportedExtrapolatedArrivalCurve.LE_le_inst1 Lean.Nat
      ImportedExtrapolatedArrivalCurve.instLENat a b)
    (ImportedExtrapolatedArrivalCurve.Nat_decLe a b).

Lemma eac_nat_le_bool_correspondence aR aL bR bL :
  SubNatRel aR aL -> SubNatRel bR bL ->
  EacBoolRel (leq aR bR) (eac_target_decide_le aL bL).
Proof.
  intros Ha Hb. apply eac_decide_bool_correspondence.
  exact (sub_nat_le_correspondence aR aL bR bL Ha Hb).
Qed.

Definition eac_target_decide_lt (a b : Lean.Nat) :
    ImportedExtrapolatedArrivalCurve.Bool :=
  ImportedExtrapolatedArrivalCurve.Decidable_decide
    (ImportedExtrapolatedArrivalCurve.LT_lt_inst1 Lean.Nat
      ImportedExtrapolatedArrivalCurve.instLTNat a b)
    (ImportedExtrapolatedArrivalCurve.Nat_decLt a b).

Lemma eac_nat_lt_bool_correspondence aR aL bR bL :
  SubNatRel aR aL -> SubNatRel bR bL ->
  EacBoolRel (ltn aR bR) (eac_target_decide_lt aL bL).
Proof.
  intros Ha Hb. apply eac_decide_bool_correspondence.
  exact (sub_nat_lt_correspondence aR aL bR bL Ha Hb).
Qed.

Definition eac_target_decide_eq (a b : Lean.Nat) :
    ImportedExtrapolatedArrivalCurve.Bool :=
  ImportedExtrapolatedArrivalCurve.Decidable_decide
    (Lean.eq a b)
    (ImportedExtrapolatedArrivalCurve.instDecidableEqNat a b).

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
    (ImportedExtrapolatedArrivalCurve.Bool_and xL yL).
Proof.
  intros Hx Hy. destruct Hx. destruct Hy.
  destruct xR, yR; exact (@Lean.eq_refl _ _).
Qed.

Definition eac_imported_false_ne_true
    (H : Lean.eq ImportedExtrapolatedArrivalCurve.Bool_false
      ImportedExtrapolatedArrivalCurve.Bool_true) :
    ImportedExtrapolatedArrivalCurve.False :=
  match H in Lean.eq _ b return
      match b with
      | ImportedExtrapolatedArrivalCurve.Bool_false =>
          ImportedExtrapolatedArrivalCurve.True
      | ImportedExtrapolatedArrivalCurve.Bool_true =>
          ImportedExtrapolatedArrivalCurve.False
      end with
  | Lean.eq_refl => ImportedExtrapolatedArrivalCurve.True_intro
  end.

Lemma eac_bool_truth_correspondence bR bL :
  EacBoolRel bR bL ->
  PropSPropRel (is_true bR)
    (Lean.eq bL ImportedExtrapolatedArrivalCurve.Bool_true).
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
Definition eac_reflect_forward (PR : Prop) (PL : SProp)
    (bR : bool) (bL : ImportedExtrapolatedArrivalCurve.Bool)
    (HP : PropSPropRel PR PL) (Hb : EacBoolRel bR bL) :
    reflect PR bR ->
    ImportedExtrapolatedArrivalCurve.Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_BoolReflect PL bL.
Proof.
  destruct Hb. intro HR. destruct HR as [Htrue | Hfalse].
  - exact (ImportedExtrapolatedArrivalCurve.Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_BoolReflect_isTrue
      PL (prop_to_sprop _ _ HP Htrue)).
  - exact (ImportedExtrapolatedArrivalCurve.Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_BoolReflect_isFalse
      PL (fun HL => eac_rocq_false_to_imported
        (Hfalse (sprop_to_prop _ _ HP HL)))).
Defined.

Definition eac_bool_from_imported
    (b : ImportedExtrapolatedArrivalCurve.Bool) : bool :=
  match b with
  | ImportedExtrapolatedArrivalCurve.Bool_true => true
  | ImportedExtrapolatedArrivalCurve.Bool_false => false
  end.

Definition eac_reflect_backward_at_bool (PR : Prop) (PL : SProp)
    (HP : PropSPropRel PR PL) (bL : ImportedExtrapolatedArrivalCurve.Bool) :
    ImportedExtrapolatedArrivalCurve.Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_BoolReflect PL bL ->
    reflect PR (eac_bool_from_imported bL) :=
  fun HL =>
    match HL in
      ImportedExtrapolatedArrivalCurve.Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_BoolReflect _ b
      return reflect PR (eac_bool_from_imported b) with
    | ImportedExtrapolatedArrivalCurve.Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_BoolReflect_isTrue Htrue =>
        ReflectT PR (sprop_to_prop _ _ HP Htrue)
    | ImportedExtrapolatedArrivalCurve.Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_BoolReflect_isFalse Hfalse =>
        ReflectF PR (fun HR =>
          interpret_strict Logic.False
            (eac_imported_false_elim _
              (Hfalse (prop_to_sprop _ _ HP HR))))
    end.

Definition eac_reflect_backward (PR : Prop) (PL : SProp)
    (bR : bool) (bL : ImportedExtrapolatedArrivalCurve.Bool)
    (HP : PropSPropRel PR PL) (Hb : EacBoolRel bR bL) :
    ImportedExtrapolatedArrivalCurve.Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_BoolReflect PL bL ->
    reflect PR bR.
Proof.
  destruct Hb. destruct bR; cbn;
    exact (eac_reflect_backward_at_bool PR PL HP _).
Defined.

Definition EacReflectTypeRel (PR : Prop) (PL : SProp)
    (bR : bool) (bL : ImportedExtrapolatedArrivalCurve.Bool) : Type :=
  Datatypes.prod
    (reflect PR bR ->
      ImportedExtrapolatedArrivalCurve.Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_BoolReflect PL bL)
    (ImportedExtrapolatedArrivalCurve.Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_BoolReflect PL bL ->
      reflect PR bR).

Definition eac_target_all {A : Type}
    (P : A -> ImportedExtrapolatedArrivalCurve.Bool)
    (xs : ImportedExtrapolatedArrivalCurve.List_inst1 A) :=
  ImportedExtrapolatedArrivalCurve.List_all_inst1 A xs P.

Lemma eac_target_all_nil {A : Type}
    (P : A -> ImportedExtrapolatedArrivalCurve.Bool) :
  Lean.eq (eac_target_all P (ImportedExtrapolatedArrivalCurve.List_nil_inst1 A))
    ImportedExtrapolatedArrivalCurve.Bool_true.
Proof. exact (@Lean.eq_refl _ _). Qed.

Lemma eac_target_all_cons {A : Type}
    (P : A -> ImportedExtrapolatedArrivalCurve.Bool) (x : A)
    (xs : ImportedExtrapolatedArrivalCurve.List_inst1 A) :
  Lean.eq
    (eac_target_all P (ImportedExtrapolatedArrivalCurve.List_cons_inst1 A x xs))
    (ImportedExtrapolatedArrivalCurve.Bool_and (P x) (eac_target_all P xs)).
Proof. exact (@Lean.eq_refl _ _). Qed.

Lemma eac_all_times_generic (PR : nat -> bool)
    (PL : Lean.Nat -> ImportedExtrapolatedArrivalCurve.Bool)
    (HP : forall t, EacBoolRel (PR t) (PL (sub_nat_to_imported t)))
    (xs : seq nat) :
  EacBoolRel (all PR xs) (eac_target_all PL (eac_imported_times xs)).
Proof.
  induction xs as [|x tail IH].
  - exact (@Lean.eq_refl _ _).
  - change (EacBoolRel (andb (PR x) (all PR tail))
      (eac_target_all PL
        (ImportedExtrapolatedArrivalCurve.List_cons_inst1 Lean.Nat
          (sub_nat_to_imported x) (eac_imported_times tail)))).
    have Heq := eac_target_all_cons PL (sub_nat_to_imported x)
      (eac_imported_times tail).
    exact (sub_imported_eq_trans _ _ _
      (eac_bool_and_correspondence _ _ _ _ (HP x) IH)
      (sub_imported_eq_sym _ _ Heq)).
Qed.

Definition eac_target_filter {A : Type}
    (P : A -> ImportedExtrapolatedArrivalCurve.Bool)
    (xs : ImportedExtrapolatedArrivalCurve.List_inst1 A) :=
  ImportedExtrapolatedArrivalCurve.List_filter_inst1 A P xs.

Lemma eac_target_filter_nil {A : Type}
    (P : A -> ImportedExtrapolatedArrivalCurve.Bool) :
    Lean.eq
      (eac_target_filter P
        (ImportedExtrapolatedArrivalCurve.List_nil_inst1 A))
      (ImportedExtrapolatedArrivalCurve.List_nil_inst1 A).
Proof. exact (@Lean.eq_refl _ _). Qed.

Lemma eac_target_filter_cons {A : Type}
    (P : A -> ImportedExtrapolatedArrivalCurve.Bool) (x : A)
    (xs : ImportedExtrapolatedArrivalCurve.List_inst1 A) :
    Lean.eq
      (eac_target_filter P
        (ImportedExtrapolatedArrivalCurve.List_cons_inst1 A x xs))
      (match P x with
       | ImportedExtrapolatedArrivalCurve.Bool_true =>
           ImportedExtrapolatedArrivalCurve.List_cons_inst1 A x
             (eac_target_filter P xs)
       | ImportedExtrapolatedArrivalCurve.Bool_false =>
           eac_target_filter P xs
       end).
Proof. exact (@Lean.eq_refl _ _). Qed.

Lemma eac_target_last_nil {A : Type} (fallback : A) :
  Lean.eq
    (ImportedExtrapolatedArrivalCurve.List_getLastD_inst1 A
      (ImportedExtrapolatedArrivalCurve.List_nil_inst1 A) fallback)
    fallback.
Proof. exact (@Lean.eq_refl _ _). Qed.

Lemma eac_target_last_singleton {A : Type} (x fallback : A) :
  Lean.eq
    (ImportedExtrapolatedArrivalCurve.List_getLastD_inst1 A
      (ImportedExtrapolatedArrivalCurve.List_cons_inst1 A x
        (ImportedExtrapolatedArrivalCurve.List_nil_inst1 A)) fallback)
    x.
Proof. exact (@Lean.eq_refl _ _). Qed.

Lemma eac_target_last_cons_cons {A : Type} (x y : A)
    (xs : ImportedExtrapolatedArrivalCurve.List_inst1 A)
    (fallback : A) :
  Lean.eq
    (ImportedExtrapolatedArrivalCurve.List_getLastD_inst1 A
      (ImportedExtrapolatedArrivalCurve.List_cons_inst1 A x
        (ImportedExtrapolatedArrivalCurve.List_cons_inst1 A y xs)) fallback)
    (ImportedExtrapolatedArrivalCurve.List_getLastD_inst1 A
      (ImportedExtrapolatedArrivalCurve.List_cons_inst1 A y xs) fallback).
Proof. exact (@Lean.eq_refl _ _). Qed.

Definition eac_target_step_pred (t : Lean.Nat)
    (p : ImportedExtrapolatedArrivalCurve.Prod_inst3 Lean.Nat Lean.Nat) :
    ImportedExtrapolatedArrivalCurve.Bool :=
  eac_target_decide_le
    (ImportedExtrapolatedArrivalCurve.Prod_fst_inst3 Lean.Nat Lean.Nat p) t.

Lemma eac_filter_branch_canonical (b : bool) (x : nat * nat)
    (filtered : seq (nat * nat))
    (tail : ImportedExtrapolatedArrivalCurve.List_inst1
      (ImportedExtrapolatedArrivalCurve.Prod_inst3 Lean.Nat Lean.Nat)) :
  Lean.eq tail (eac_imported_steps filtered) ->
  Lean.eq
    (match eac_bool_to_imported b with
     | ImportedExtrapolatedArrivalCurve.Bool_true =>
         ImportedExtrapolatedArrivalCurve.List_cons_inst1 _
           (eac_imported_step x) tail
     | ImportedExtrapolatedArrivalCurve.Bool_false => tail
     end)
    (eac_imported_steps
      (if b then x :: filtered else filtered)).
Proof.
  intro Htail. destruct b; cbn.
  - exact (sub_imported_eq_congr
      (ImportedExtrapolatedArrivalCurve.List_cons_inst1 _
        (eac_imported_step x)) _ _ Htail).
  - exact Htail.
Qed.

Lemma eac_filter_steps_generic (PR : nat * nat -> bool)
    (PL : ImportedExtrapolatedArrivalCurve.Prod_inst3 Lean.Nat Lean.Nat ->
      ImportedExtrapolatedArrivalCurve.Bool)
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
        (fun z : ImportedExtrapolatedArrivalCurve.Bool =>
          match z with
          | ImportedExtrapolatedArrivalCurve.Bool_true =>
              ImportedExtrapolatedArrivalCurve.List_cons_inst1 _
                (eac_imported_step x)
                (eac_target_filter PL (eac_imported_steps tail))
          | ImportedExtrapolatedArrivalCurve.Bool_false =>
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
    (dL : ImportedExtrapolatedArrivalCurve.Prod_inst3 Lean.Nat Lean.Nat)
    (Hd : Lean.eq (eac_imported_step dR) dL)
    (xs : seq (nat * nat)) :
  Lean.eq (eac_imported_step (last dR xs))
    (ImportedExtrapolatedArrivalCurve.List_getLastD_inst1 _
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
      (OfficialExtrapolatedArrivalCurve.inter_arrival_to_prefix pR)
      (ImportedExtrapolatedArrivalCurve.Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_inter_arrival_to_prefix pL).
Proof.
  intros pR pL Hp.
  destruct Hp.
  exact (@Lean.eq_refl _ _).
Qed.

Lemma eac_horizon_of_correspondence :
  forall pR pL, EacPrefixRel pR pL ->
    SubNatRel
      (OfficialExtrapolatedArrivalCurve.horizon_of pR)
      (ImportedExtrapolatedArrivalCurve.Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_horizon_of pL).
Proof.
  intros [h steps] pL Hp.
  destruct Hp.
  exact (@Lean.eq_refl _ _).
Qed.

Lemma eac_steps_of_correspondence :
  forall pR pL, EacPrefixRel pR pL ->
    Lean.eq
      (eac_imported_steps
        (OfficialExtrapolatedArrivalCurve.steps_of pR))
      (ImportedExtrapolatedArrivalCurve.Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_steps_of pL).
Proof.
  intros [h steps] pL Hp.
  destruct Hp.
  exact (@Lean.eq_refl _ _).
Qed.

Lemma eac_time_steps_of_correspondence :
  forall pR pL, EacPrefixRel pR pL ->
    Lean.eq
      (eac_imported_times
        (OfficialExtrapolatedArrivalCurve.time_steps_of pR))
      (ImportedExtrapolatedArrivalCurve.Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_time_steps_of pL).
Proof.
  intros [h steps] pL Hp.
  destruct Hp.
  induction steps as [|[t n] tail IH]; cbn.
  - exact (@Lean.eq_refl _ _).
  - exact (sub_imported_eq_congr
      (ImportedExtrapolatedArrivalCurve.List_cons_inst1 Lean.Nat
        (sub_nat_to_imported t)) _ _ IH).
Qed.

Lemma eac_step_at_correspondence :
  forall pR pL tR tL,
    EacPrefixRel pR pL -> SubNatRel tR tL ->
    Lean.eq
      (eac_imported_step
        (OfficialExtrapolatedArrivalCurve.step_at pR tR))
      (ImportedExtrapolatedArrivalCurve.Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_step_at pL tL).
Proof.
  intros [h steps] pL tR tL Hp Ht.
  destruct Hp.
  set (defaultL := ImportedExtrapolatedArrivalCurve.Prod_mk_inst3
    Lean.Nat Lean.Nat Lean.Nat_zero Lean.Nat_zero).
  have Hdefault : Lean.eq (eac_imported_step (O, O)) defaultL :=
    @Lean.eq_refl _ _.
  have Hfilter := eac_filter_steps_canonical tR tL Ht steps.
  have Hlast := eac_last_steps_canonical (O, O) defaultL Hdefault
    (filter (fun p : nat * nat => leq (Datatypes.fst p) tR) steps).
  exact (sub_imported_eq_trans _ _ _ Hlast
    (sub_imported_eq_congr
      (fun xs => ImportedExtrapolatedArrivalCurve.List_getLastD_inst1 _
        xs defaultL) _ _ (sub_imported_eq_sym _ _ Hfilter))).
Qed.

Lemma eac_step_snd_correspondence (pR : nat * nat)
    (pL : ImportedExtrapolatedArrivalCurve.Prod_inst3 Lean.Nat Lean.Nat) :
  Lean.eq (eac_imported_step pR) pL ->
  SubNatRel (Datatypes.snd pR)
    (ImportedExtrapolatedArrivalCurve.Prod_snd_inst3 Lean.Nat Lean.Nat pL).
Proof.
  destruct pR as [a b]. intro Hp.
  exact (sub_imported_eq_congr
    (ImportedExtrapolatedArrivalCurve.Prod_snd_inst3 Lean.Nat Lean.Nat)
    _ _ Hp).
Qed.

Lemma eac_value_at_correspondence :
  forall pR pL tR tL,
    EacPrefixRel pR pL -> SubNatRel tR tL ->
    SubNatRel
      (OfficialExtrapolatedArrivalCurve.value_at pR tR)
      (ImportedExtrapolatedArrivalCurve.Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_value_at pL tL).
Proof.
  intros pR pL tR tL Hp Ht.
  exact (eac_step_snd_correspondence _ _
    (eac_step_at_correspondence pR pL tR tL Hp Ht)).
Qed.

Lemma eac_large_horizon_dec_correspondence :
  forall pR pL,
    EacPrefixRel pR pL ->
    EacBoolRel
      (OfficialExtrapolatedArrivalCurve.large_horizon_dec pR)
      (ImportedExtrapolatedArrivalCurve.Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_large_horizon_dec pL).
Proof.
  intros pR pL Hp.
  have Hh := eac_horizon_of_correspondence pR pL Hp.
  have Htimes := eac_time_steps_of_correspondence pR pL Hp.
  change (EacBoolRel
    (all (fun s => leq s (OfficialExtrapolatedArrivalCurve.horizon_of pR))
      (OfficialExtrapolatedArrivalCurve.time_steps_of pR))
    (eac_target_all
      (fun s => eac_target_decide_le s
        (ImportedExtrapolatedArrivalCurve.Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_horizon_of pL))
      (ImportedExtrapolatedArrivalCurve.Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_time_steps_of pL))).
  destruct Htimes.
  apply eac_all_times_generic. intro t.
  apply eac_nat_le_bool_correspondence.
  - exact (@Lean.eq_refl _ _).
  - exact Hh.
Qed.

Lemma eac_large_horizon_correspondence :
  forall pR pL,
    EacPrefixRel pR pL ->
    PropSPropRel
      (OfficialExtrapolatedArrivalCurve.large_horizon pR)
      (ImportedExtrapolatedArrivalCurve.Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_large_horizon pL).
Proof.
  intros pR pL Hp.
  have Htimes := eac_time_steps_of_correspondence pR pL Hp.
  have Hh := eac_horizon_of_correspondence pR pL Hp.
  apply prop_sprop_rel_intro.
  - intro HR. intros sL HmemL.
    set sR := sub_nat_to_rocq sL.
    have Hs : SubNatRel sR sL := sub_nat_rel_surjective sL.
    have Hmemrel := eac_nat_membership_correspondence sR
      (OfficialExtrapolatedArrivalCurve.time_steps_of pR)
      (ImportedExtrapolatedArrivalCurve.Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_time_steps_of pL)
      Htimes.
    have HmemCanonical : eac_target_mem (sub_nat_to_imported sR)
      (ImportedExtrapolatedArrivalCurve.Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_time_steps_of pL) :=
      eac_mem_element_transport sL (sub_nat_to_imported sR) _
        (sub_imported_eq_sym _ _ Hs) HmemL.
    have HmemR := sprop_to_prop _ _ Hmemrel HmemCanonical.
    have HleRel := sub_nat_le_correspondence sR sL
      (OfficialExtrapolatedArrivalCurve.horizon_of pR)
      (ImportedExtrapolatedArrivalCurve.Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_horizon_of pL)
      Hs Hh.
    exact (prop_to_sprop _ _ HleRel (HR sR HmemR)).
  - intro HL. apply strictly_inhabits. intros sR HmemR.
    have Hmemrel := eac_nat_membership_correspondence sR
      (OfficialExtrapolatedArrivalCurve.time_steps_of pR)
      (ImportedExtrapolatedArrivalCurve.Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_time_steps_of pL)
      Htimes.
    have HmemL := prop_to_sprop _ _ Hmemrel HmemR.
    have HleRel := sub_nat_le_correspondence sR
      (sub_nat_to_imported sR)
      (OfficialExtrapolatedArrivalCurve.horizon_of pR)
      (ImportedExtrapolatedArrivalCurve.Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_horizon_of pL)
      (@Lean.eq_refl _ _) Hh.
    exact (sprop_to_prop _ _ HleRel
      (HL (sub_nat_to_imported sR) HmemL)).
Qed.

Lemma eac_positive_horizon_correspondence :
  forall pR pL,
    EacPrefixRel pR pL ->
    EacBoolRel
      (OfficialExtrapolatedArrivalCurve.positive_horizon pR)
      (ImportedExtrapolatedArrivalCurve.Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_positive_horizon pL).
Proof.
  intros pR pL Hp.
  change (EacBoolRel
    (ltn O (OfficialExtrapolatedArrivalCurve.horizon_of pR))
    (eac_target_decide_lt Lean.Nat_zero
      (ImportedExtrapolatedArrivalCurve.Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_horizon_of pL))).
  apply eac_nat_lt_bool_correspondence.
  - exact (@Lean.eq_refl _ _).
  - exact (eac_horizon_of_correspondence pR pL Hp).
Qed.

Lemma eac_no_inf_arrivals_correspondence :
  forall pR pL,
    EacPrefixRel pR pL ->
    EacBoolRel
      (OfficialExtrapolatedArrivalCurve.no_inf_arrivals pR)
      (ImportedExtrapolatedArrivalCurve.Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_no_inf_arrivals pL).
Proof.
  intros pR pL Hp.
  change (EacBoolRel
    (OfficialExtrapolatedArrivalCurve.value_at pR O == O)
    (eac_target_decide_eq
      (ImportedExtrapolatedArrivalCurve.Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_value_at pL Lean.Nat_zero)
      Lean.Nat_zero)).
  apply eac_nat_eq_bool_correspondence.
  - exact (eac_value_at_correspondence pR pL O Lean.Nat_zero Hp
      (@Lean.eq_refl _ _)).
  - exact (@Lean.eq_refl _ _).
Qed.

Lemma eac_specified_bursts_correspondence :
  forall pR pL,
    EacPrefixRel pR pL ->
    EacBoolRel
      (OfficialExtrapolatedArrivalCurve.specified_bursts pR)
      (ImportedExtrapolatedArrivalCurve.Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_specified_bursts pL).
Proof.
  intros pR pL Hp.
  change (EacBoolRel
    (prosa.util.epsilon.ε \in OfficialExtrapolatedArrivalCurve.time_steps_of pR)
    (eac_target_decide_mem_nat (Lean.Nat_succ Lean.Nat_zero)
      (ImportedExtrapolatedArrivalCurve.Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_time_steps_of pL))).
  apply eac_decide_bool_correspondence.
  exact (eac_nat_membership_correspondence 1
    (OfficialExtrapolatedArrivalCurve.time_steps_of pR)
    (ImportedExtrapolatedArrivalCurve.Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_time_steps_of pL)
    (eac_time_steps_of_correspondence pR pL Hp)).
Qed.

Lemma eac_ltn_steps_correspondence :
  forall aR bR aL bL,
    Lean.eq (eac_imported_step aR) aL ->
    Lean.eq (eac_imported_step bR) bL ->
    EacBoolRel
      (OfficialExtrapolatedArrivalCurve.ltn_steps aR bR)
      (ImportedExtrapolatedArrivalCurve.Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_ltn_steps aL bL).
Proof.
  intros [ta va] [tb vb] aL bL Ha Hb.
  destruct Ha. destruct Hb.
  change (EacBoolRel (andb (ltn ta tb) (ltn va vb))
    (ImportedExtrapolatedArrivalCurve.Bool_and
      (eac_target_decide_lt (sub_nat_to_imported ta) (sub_nat_to_imported tb))
      (eac_target_decide_lt (sub_nat_to_imported va) (sub_nat_to_imported vb)))).
  apply eac_bool_and_correspondence;
    apply eac_nat_lt_bool_correspondence;
    exact (@Lean.eq_refl _ _).
Qed.

Lemma eac_leq_steps_correspondence :
  forall aR bR aL bL,
    Lean.eq (eac_imported_step aR) aL ->
    Lean.eq (eac_imported_step bR) bL ->
    EacBoolRel
      (OfficialExtrapolatedArrivalCurve.leq_steps aR bR)
      (ImportedExtrapolatedArrivalCurve.Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_leq_steps aL bL).
Proof.
  intros [ta va] [tb vb] aL bL Ha Hb.
  destruct Ha. destruct Hb.
  change (EacBoolRel (andb (leq ta tb) (leq va vb))
    (ImportedExtrapolatedArrivalCurve.Bool_and
      (eac_target_decide_le (sub_nat_to_imported ta) (sub_nat_to_imported tb))
      (eac_target_decide_le (sub_nat_to_imported va) (sub_nat_to_imported vb)))).
  apply eac_bool_and_correspondence;
    apply eac_nat_le_bool_correspondence;
    exact (@Lean.eq_refl _ _).
Qed.

Definition eac_target_sorted_from
    (R : ImportedExtrapolatedArrivalCurve.Prod_inst3 Lean.Nat Lean.Nat ->
      ImportedExtrapolatedArrivalCurve.Prod_inst3 Lean.Nat Lean.Nat ->
      ImportedExtrapolatedArrivalCurve.Bool)
    (previous : ImportedExtrapolatedArrivalCurve.Prod_inst3 Lean.Nat Lean.Nat)
    (xs : ImportedExtrapolatedArrivalCurve.List_inst1
      (ImportedExtrapolatedArrivalCurve.Prod_inst3 Lean.Nat Lean.Nat)) :=
  ImportedExtrapolatedArrivalCurve.Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_sortedBoolFrom_inst1
    _ R previous xs.

Definition eac_target_sorted
    (R : ImportedExtrapolatedArrivalCurve.Prod_inst3 Lean.Nat Lean.Nat ->
      ImportedExtrapolatedArrivalCurve.Prod_inst3 Lean.Nat Lean.Nat ->
      ImportedExtrapolatedArrivalCurve.Bool)
    (xs : ImportedExtrapolatedArrivalCurve.List_inst1
      (ImportedExtrapolatedArrivalCurve.Prod_inst3 Lean.Nat Lean.Nat)) :=
  ImportedExtrapolatedArrivalCurve.Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_sortedBool_inst1
    _ R xs.

Lemma eac_target_sorted_from_nil R previous :
  Lean.eq
    (eac_target_sorted_from R previous
      (ImportedExtrapolatedArrivalCurve.List_nil_inst1 _))
    ImportedExtrapolatedArrivalCurve.Bool_true.
Proof. exact (@Lean.eq_refl _ _). Qed.

Lemma eac_target_sorted_from_cons R previous x xs :
  Lean.eq
    (eac_target_sorted_from R previous
      (ImportedExtrapolatedArrivalCurve.List_cons_inst1 _ x xs))
    (ImportedExtrapolatedArrivalCurve.Bool_and (R previous x)
      (eac_target_sorted_from R x xs)).
Proof. exact (@Lean.eq_refl _ _). Qed.

Lemma eac_target_sorted_nil R :
  Lean.eq
    (eac_target_sorted R (ImportedExtrapolatedArrivalCurve.List_nil_inst1 _))
    ImportedExtrapolatedArrivalCurve.Bool_true.
Proof. exact (@Lean.eq_refl _ _). Qed.

Lemma eac_target_sorted_cons R x xs :
  Lean.eq
    (eac_target_sorted R
      (ImportedExtrapolatedArrivalCurve.List_cons_inst1 _ x xs))
    (eac_target_sorted_from R x xs).
Proof. exact (@Lean.eq_refl _ _). Qed.

Lemma eac_path_steps_generic
    (PR : nat * nat -> nat * nat -> bool)
    (PL : ImportedExtrapolatedArrivalCurve.Prod_inst3 Lean.Nat Lean.Nat ->
      ImportedExtrapolatedArrivalCurve.Prod_inst3 Lean.Nat Lean.Nat ->
      ImportedExtrapolatedArrivalCurve.Bool)
    (HP : forall a b,
      EacBoolRel (PR a b) (PL (eac_imported_step a) (eac_imported_step b))) :
  forall previous xs,
    EacBoolRel (path PR previous xs)
      (eac_target_sorted_from PL (eac_imported_step previous)
        (eac_imported_steps xs)).
Proof.
  intros previous xs. revert previous.
  induction xs as [|x tail IH]; intro previous.
  - exact (@Lean.eq_refl _ _).
  - change (EacBoolRel (andb (PR previous x) (path PR x tail))
      (eac_target_sorted_from PL (eac_imported_step previous)
        (ImportedExtrapolatedArrivalCurve.List_cons_inst1 _
          (eac_imported_step x) (eac_imported_steps tail)))).
    exact (sub_imported_eq_trans _ _ _
      (eac_bool_and_correspondence _ _ _ _ (HP previous x) (IH x))
      (sub_imported_eq_sym _ _
        (eac_target_sorted_from_cons PL (eac_imported_step previous)
          (eac_imported_step x) (eac_imported_steps tail)))).
Qed.

Lemma eac_sorted_steps_generic
    (PR : nat * nat -> nat * nat -> bool)
    (PL : ImportedExtrapolatedArrivalCurve.Prod_inst3 Lean.Nat Lean.Nat ->
      ImportedExtrapolatedArrivalCurve.Prod_inst3 Lean.Nat Lean.Nat ->
      ImportedExtrapolatedArrivalCurve.Bool)
    (HP : forall a b,
      EacBoolRel (PR a b) (PL (eac_imported_step a) (eac_imported_step b)))
    (xs : seq (nat * nat)) :
  EacBoolRel (sorted PR xs) (eac_target_sorted PL (eac_imported_steps xs)).
Proof.
  destruct xs as [|x tail].
  - exact (@Lean.eq_refl _ _).
  - change (EacBoolRel (path PR x tail)
      (eac_target_sorted PL
        (ImportedExtrapolatedArrivalCurve.List_cons_inst1 _
          (eac_imported_step x) (eac_imported_steps tail)))).
    exact (sub_imported_eq_trans _ _ _
      (eac_path_steps_generic PR PL HP x tail)
      (sub_imported_eq_sym _ _
        (eac_target_sorted_cons PL (eac_imported_step x)
          (eac_imported_steps tail)))).
Qed.

Lemma eac_sorted_ltn_steps_correspondence :
  forall pR pL,
    EacPrefixRel pR pL ->
    EacBoolRel
      (OfficialExtrapolatedArrivalCurve.sorted_ltn_steps pR)
      (ImportedExtrapolatedArrivalCurve.Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_sorted_ltn_steps pL).
Proof.
  intros pR pL Hp.
  have Hsteps := eac_steps_of_correspondence pR pL Hp.
  change (EacBoolRel
    (sorted OfficialExtrapolatedArrivalCurve.ltn_steps
      (OfficialExtrapolatedArrivalCurve.steps_of pR))
    (eac_target_sorted
      ImportedExtrapolatedArrivalCurve.Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_ltn_steps
      (ImportedExtrapolatedArrivalCurve.Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_steps_of pL))).
  destruct Hsteps.
  apply eac_sorted_steps_generic. intros a b.
  apply eac_ltn_steps_correspondence;
    exact (@Lean.eq_refl _ _).
Qed.

Lemma eac_sorted_leq_steps_correspondence :
  forall pR pL,
    EacPrefixRel pR pL ->
    EacBoolRel
      (OfficialExtrapolatedArrivalCurve.sorted_leq_steps pR)
      (ImportedExtrapolatedArrivalCurve.Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_sorted_leq_steps pL).
Proof.
  intros pR pL Hp.
  have Hsteps := eac_steps_of_correspondence pR pL Hp.
  change (EacBoolRel
    (sorted OfficialExtrapolatedArrivalCurve.leq_steps
      (OfficialExtrapolatedArrivalCurve.steps_of pR))
    (eac_target_sorted
      ImportedExtrapolatedArrivalCurve.Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_leq_steps
      (ImportedExtrapolatedArrivalCurve.Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_steps_of pL))).
  destruct Hsteps.
  apply eac_sorted_steps_generic. intros a b.
  apply eac_leq_steps_correspondence;
    exact (@Lean.eq_refl _ _).
Qed.

Lemma eac_valid_arrival_curve_prefix_correspondence :
  forall pR pL,
    EacPrefixRel pR pL ->
    PropSPropRel
      (OfficialExtrapolatedArrivalCurve.valid_arrival_curve_prefix pR)
      (ImportedExtrapolatedArrivalCurve.Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_valid_arrival_curve_prefix pL).
Proof.
  intros pR pL Hp.
  change (PropSPropRel
    (is_true (OfficialExtrapolatedArrivalCurve.positive_horizon pR) /\
     OfficialExtrapolatedArrivalCurve.large_horizon pR /\
     is_true (OfficialExtrapolatedArrivalCurve.no_inf_arrivals pR) /\
     is_true (OfficialExtrapolatedArrivalCurve.specified_bursts pR) /\
     is_true (OfficialExtrapolatedArrivalCurve.sorted_ltn_steps pR))
    (Lean.And
      (Lean.eq
        (ImportedExtrapolatedArrivalCurve.Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_positive_horizon pL)
        ImportedExtrapolatedArrivalCurve.Bool_true)
      (Lean.And
        (ImportedExtrapolatedArrivalCurve.Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_large_horizon pL)
        (Lean.And
          (Lean.eq
            (ImportedExtrapolatedArrivalCurve.Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_no_inf_arrivals pL)
            ImportedExtrapolatedArrivalCurve.Bool_true)
          (Lean.And
            (Lean.eq
              (ImportedExtrapolatedArrivalCurve.Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_specified_bursts pL)
              ImportedExtrapolatedArrivalCurve.Bool_true)
            (Lean.eq
              (ImportedExtrapolatedArrivalCurve.Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_sorted_ltn_steps pL)
              ImportedExtrapolatedArrivalCurve.Bool_true)))))).
  apply eac_and_correspondence.
  - apply eac_bool_truth_correspondence.
    exact (eac_positive_horizon_correspondence pR pL Hp).
  - apply eac_and_correspondence.
    + exact (eac_large_horizon_correspondence pR pL Hp).
    + apply eac_and_correspondence.
      * apply eac_bool_truth_correspondence.
        exact (eac_no_inf_arrivals_correspondence pR pL Hp).
      * apply eac_and_correspondence.
        -- apply eac_bool_truth_correspondence.
           exact (eac_specified_bursts_correspondence pR pL Hp).
        -- apply eac_bool_truth_correspondence.
           exact (eac_sorted_ltn_steps_correspondence pR pL Hp).
Qed.

Lemma eac_valid_arrival_curve_prefix_dec_correspondence :
  forall pR pL,
    EacPrefixRel pR pL ->
    EacBoolRel
      (OfficialExtrapolatedArrivalCurve.valid_arrival_curve_prefix_dec pR)
      (ImportedExtrapolatedArrivalCurve.Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_valid_arrival_curve_prefix_dec pL).
Proof.
  intros pR pL Hp.
  unfold OfficialExtrapolatedArrivalCurve.valid_arrival_curve_prefix_dec,
    ImportedExtrapolatedArrivalCurve.Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_valid_arrival_curve_prefix_dec.
  apply eac_bool_and_correspondence.
  - apply eac_bool_and_correspondence.
    + apply eac_bool_and_correspondence.
      * apply eac_bool_and_correspondence.
        -- exact (eac_positive_horizon_correspondence pR pL Hp).
        -- exact (eac_large_horizon_dec_correspondence pR pL Hp).
      * exact (eac_no_inf_arrivals_correspondence pR pL Hp).
    + exact (eac_specified_bursts_correspondence pR pL Hp).
  - exact (eac_sorted_ltn_steps_correspondence pR pL Hp).
Qed.

Definition eac_large_horizon_P_statement_correspondence :
  forall pR pL,
    EacPrefixRel pR pL ->
    EacReflectTypeRel
      (OfficialExtrapolatedArrivalCurve.large_horizon pR)
      (ImportedExtrapolatedArrivalCurve.Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_large_horizon pL)
      (OfficialExtrapolatedArrivalCurve.large_horizon_dec pR)
      (ImportedExtrapolatedArrivalCurve.Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_large_horizon_dec pL) :=
  fun pR pL Hp =>
    let Hprop := eac_large_horizon_correspondence pR pL Hp in
    let Hbool := eac_large_horizon_dec_correspondence pR pL Hp in
    Datatypes.pair
      (eac_reflect_forward _ _ _ _ Hprop Hbool)
      (eac_reflect_backward _ _ _ _ Hprop Hbool).

Definition eac_valid_arrival_curve_prefix_P_statement_correspondence :
  forall pR pL,
    EacPrefixRel pR pL ->
    EacReflectTypeRel
      (OfficialExtrapolatedArrivalCurve.valid_arrival_curve_prefix pR)
      (ImportedExtrapolatedArrivalCurve.Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_valid_arrival_curve_prefix pL)
      (OfficialExtrapolatedArrivalCurve.valid_arrival_curve_prefix_dec pR)
      (ImportedExtrapolatedArrivalCurve.Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_valid_arrival_curve_prefix_dec pL) :=
  fun pR pL Hp =>
    let Hprop := eac_valid_arrival_curve_prefix_correspondence pR pL Hp in
    let Hbool := eac_valid_arrival_curve_prefix_dec_correspondence pR pL Hp in
    Datatypes.pair
      (eac_reflect_forward _ _ _ _ Hprop Hbool)
      (eac_reflect_backward _ _ _ _ Hprop Hbool).

(** The following operations are the exact artifact-local operations in the
    compiled production definition.  The Euclidean facts used below have
    exported Lean proof bodies, rather than statement-only imports. *)
Definition eac_imported_add (a b : Lean.Nat) : Lean.Nat :=
  ImportedExtrapolatedArrivalCurve.HAdd_hAdd_inst7 Lean.Nat Lean.Nat Lean.Nat
    (ImportedExtrapolatedArrivalCurve.instHAdd_inst1 Lean.Nat
      ImportedExtrapolatedArrivalCurve.instAddNat) a b.

Definition eac_imported_mul (a b : Lean.Nat) : Lean.Nat :=
  ImportedExtrapolatedArrivalCurve.HMul_hMul_inst7 Lean.Nat Lean.Nat Lean.Nat
    (ImportedExtrapolatedArrivalCurve.instHMul_inst1 Lean.Nat
      ImportedExtrapolatedArrivalCurve.instMulNat) a b.

Definition eac_imported_div (a b : Lean.Nat) : Lean.Nat :=
  ImportedExtrapolatedArrivalCurve.HDiv_hDiv_inst7 Lean.Nat Lean.Nat Lean.Nat
    (ImportedExtrapolatedArrivalCurve.instHDiv_inst1 Lean.Nat
      ImportedExtrapolatedArrivalCurve.Nat_instDiv) a b.

Definition eac_imported_mod (a b : Lean.Nat) : Lean.Nat :=
  ImportedExtrapolatedArrivalCurve.HMod_hMod_inst7 Lean.Nat Lean.Nat Lean.Nat
    (ImportedExtrapolatedArrivalCurve.instHMod_inst1 Lean.Nat
      ImportedExtrapolatedArrivalCurve.Nat_instMod) a b.

Definition eac_imported_zero : Lean.Nat :=
  ImportedExtrapolatedArrivalCurve.OfNat_ofNat_inst1 Lean.Nat Lean.Nat_zero
    (ImportedExtrapolatedArrivalCurve.instOfNatNat Lean.Nat_zero).

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
    (ImportedExtrapolatedArrivalCurve.LT_lt_inst1 Lean.Nat
      ImportedExtrapolatedArrivalCurve.instLTNat aL bL).
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
        ImportedExtrapolatedArrivalCurve.Prosa_Validation_ExtrapolatedArrivalCurveArithmeticInterface_production_div_zero
          (sub_nat_to_imported x).
      exact (f_equal sub_nat_to_rocq
        (imported_eq_to_coq_eq _ _ H)).
    + rewrite modn0.
      have H :=
        ImportedExtrapolatedArrivalCurve.Prosa_Validation_ExtrapolatedArrivalCurveArithmeticInterface_production_mod_zero
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
        (ImportedExtrapolatedArrivalCurve.Prosa_Validation_ExtrapolatedArrivalCurveArithmeticInterface_production_mod_lt
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
        (ImportedExtrapolatedArrivalCurve.Prosa_Validation_ExtrapolatedArrivalCurveArithmeticInterface_production_div_add_mod
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
      (OfficialExtrapolatedArrivalCurve.extrapolated_arrival_curve pR tR)
      (ImportedExtrapolatedArrivalCurve.Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_extrapolated_arrival_curve pL tL).
Proof.
  intros pR pL tR tL Hp Ht.
  have Hh := eac_horizon_of_correspondence pR pL Hp.
  have Hdiv := eac_div_correspondence tR tL
    (OfficialExtrapolatedArrivalCurve.horizon_of pR)
    (ImportedExtrapolatedArrivalCurve.Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_horizon_of pL)
    Ht Hh.
  have Hmod := eac_mod_correspondence tR tL
    (OfficialExtrapolatedArrivalCurve.horizon_of pR)
    (ImportedExtrapolatedArrivalCurve.Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_horizon_of pL)
    Ht Hh.
  have Hv := eac_value_at_correspondence pR pL _ _ Hp Hh.
  have Hvm := eac_value_at_correspondence pR pL _ _ Hp Hmod.
  unfold OfficialExtrapolatedArrivalCurve.extrapolated_arrival_curve,
    ImportedExtrapolatedArrivalCurve.Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_extrapolated_arrival_curve.
  exact (eac_add_correspondence _ _ _ _
    (eac_mul_correspondence _ _ _ _ Hdiv Hv) Hvm).
Qed.

Print Assumptions eac_extrapolated_arrival_curve_correspondence.

Print Assumptions eac_inter_arrival_to_prefix_correspondence.
Print Assumptions eac_horizon_of_correspondence.
Print Assumptions eac_steps_of_correspondence.
Print Assumptions eac_time_steps_of_correspondence.
Print Assumptions eac_step_at_correspondence.
Print Assumptions eac_value_at_correspondence.
Print Assumptions eac_large_horizon_dec_correspondence.
Print Assumptions eac_positive_horizon_correspondence.
Print Assumptions eac_no_inf_arrivals_correspondence.
Print Assumptions eac_ltn_steps_correspondence.
Print Assumptions eac_leq_steps_correspondence.
Print Assumptions eac_sorted_ltn_steps_correspondence.
Print Assumptions eac_sorted_leq_steps_correspondence.
