From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq fintype bigop.
From prosa Require Import GeneratedMinmaxSource.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedMinmax.
From FoundationCertificates Require Import
  PropSPropFoundation LogicalRelation TypeSPropRelation
  SubadditivityNatCorrespondence
  MinmaxCorrespondence.

(** Reusable logical composition for the Minmax artifact. *)
Lemma mm_and_correspondence (P Q : Prop) (PL QL : SProp) :
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

Lemma mm_imp_correspondence (P Q : Prop) (PL QL : SProp) :
  PropSPropRel P PL -> PropSPropRel Q QL ->
  PropSPropRel (P -> Q) (PL -> QL).
Proof.
  intros HP HQ. apply prop_sprop_rel_intro.
  - intros H p. exact (prop_to_sprop _ _ HQ
      (H (sprop_to_prop _ _ HP p))).
  - intro H. apply strictly_inhabits. intro p.
    exact (sprop_to_prop _ _ HQ (H (prop_to_sprop _ _ HP p))).
Qed.

Lemma mm_iff_correspondence (P Q : Prop) (PL QL : SProp) :
  PropSPropRel P PL -> PropSPropRel Q QL ->
  PropSPropRel (P <-> Q) (ImportedMinmax.Iff PL QL).
Proof.
  intros HP HQ. apply prop_sprop_rel_intro.
  - intros [Hpq Hqp]. apply ImportedMinmax.Iff_intro.
    + intro p. exact (prop_to_sprop _ _ HQ
        (Hpq (sprop_to_prop _ _ HP p))).
    + intro q. exact (prop_to_sprop _ _ HP
        (Hqp (sprop_to_prop _ _ HQ q))).
  - intro H. apply strictly_inhabits. split.
    + intro p. exact (sprop_to_prop _ _ HQ
        (ImportedMinmax.mp PL QL H (prop_to_sprop _ _ HP p))).
    + intro q. exact (sprop_to_prop _ _ HP
        (ImportedMinmax.mpr PL QL H (prop_to_sprop _ _ HQ q))).
Qed.

Lemma mm_exists_identity_correspondence (T : Type)
    (PR : T -> Prop) (PL : T -> SProp) :
  (forall x, PropSPropRel (PR x) (PL x)) ->
  PropSPropRel (exists x, PR x) (ImportedMinmax.Exists T PL).
Proof.
  intro Hrel. apply prop_sprop_rel_intro.
  - intros [x Hx]. exact (ImportedMinmax.Exists_intro T PL x
      (prop_to_sprop _ _ (Hrel x) Hx)).
  - intros [x Hx]. apply strictly_inhabits. exists x.
    exact (sprop_to_prop _ _ (Hrel x) Hx).
Qed.

Lemma mm_forall_identity_correspondence (T : Type)
    (PR : T -> Prop) (PL : T -> SProp) :
  (forall x, PropSPropRel (PR x) (PL x)) ->
  PropSPropRel (forall x, PR x) (forall x, PL x).
Proof.
  intro Hrel. apply prop_sprop_rel_intro.
  - intros H x. exact (prop_to_sprop _ _ (Hrel x) (H x)).
  - intro H. apply strictly_inhabits. intro x.
    exact (sprop_to_prop _ _ (Hrel x) (H x)).
Qed.

Definition mm_target_leq_bigmax_cond_seq_statement : SProp :=
  forall (X : eqType) (F : X -> nat) (P : X -> bool)
    (xs : seq X) (x : X),
  mm_target_mem x (mm_to_imported xs) ->
  Lean.eq (mm_pred_to_imported P x) ImportedMinmax.Bool_true ->
  mm_target_le (sub_nat_to_imported (F x))
    (mm_target_bigMaxListCond (mm_to_imported xs)
      (mm_pred_to_imported P) (mm_nat_fun_to_imported F)).

Theorem leq_bigmax_cond_seq_statement_certificate :
  PropSPropRel GeneratedMinmaxSource.statement_leq_bigmax_cond_seq
    mm_target_leq_bigmax_cond_seq_statement.
Proof.
  unfold GeneratedMinmaxSource.statement_leq_bigmax_cond_seq,
    mm_target_leq_bigmax_cond_seq_statement.
  apply prop_sprop_rel_intro.
  - intros H X F P xs x HmemL HPxL.
    apply (prop_to_sprop _ _
      (mm_nat_le_correspondence (F x) (sub_nat_to_imported (F x))
        (\max_(i <- xs | P i) F i)
        (mm_target_bigMaxListCond (mm_to_imported xs)
          (mm_pred_to_imported P) (mm_nat_fun_to_imported F))
        (sub_nat_rel_canonical (F x))
        (mm_bigmax_list_canonical X xs P F))).
    apply H.
    + exact (sprop_to_prop _ _
        (mm_membership_correspondence X x xs (mm_to_imported xs)
          (@Lean.eq_refl _ _)) HmemL).
    + exact (sprop_to_prop _ _
        (mm_bool_truth_correspondence (P x) (mm_pred_to_imported P x)
          (mm_pred_canonical P x)) HPxL).
  - intro H. apply strictly_inhabits.
    intros X F P xs x HmemR HPxR.
    exact (sprop_to_prop _ _
      (mm_nat_le_correspondence (F x) (sub_nat_to_imported (F x))
        (\max_(i <- xs | P i) F i)
        (mm_target_bigMaxListCond (mm_to_imported xs)
          (mm_pred_to_imported P) (mm_nat_fun_to_imported F))
        (sub_nat_rel_canonical (F x))
        (mm_bigmax_list_canonical X xs P F))
      (H X F P xs x
        (prop_to_sprop _ _
          (mm_membership_correspondence X x xs (mm_to_imported xs)
            (@Lean.eq_refl _ _)) HmemR)
        (prop_to_sprop _ _
          (mm_bool_truth_correspondence (P x) (mm_pred_to_imported P x)
            (mm_pred_canonical P x)) HPxR))).
Qed.

Definition mm_target_leq_bigmax_sup_statement : SProp :=
  forall (X : eqType) (P : X -> bool) (F : X -> nat)
    (xs : seq X) (n : nat),
  ImportedMinmax.Exists X (fun x =>
    Lean.And (mm_target_mem x (mm_to_imported xs))
      (Lean.And
        (Lean.eq (mm_pred_to_imported P x) ImportedMinmax.Bool_true)
        (mm_target_le (sub_nat_to_imported n)
          (sub_nat_to_imported (F x))))) ->
  mm_target_le (sub_nat_to_imported n)
    (mm_target_bigMaxListCond (mm_to_imported xs)
      (mm_pred_to_imported P) (mm_nat_fun_to_imported F)).

Lemma mm_bigmax_sup_premise_correspondence (X : eqType)
    (P : X -> bool) (F : X -> nat) (xs : seq X) (n : nat) :
  PropSPropRel
    (exists x, x \in xs /\ P x /\ is_true (leq n (F x)))
    (ImportedMinmax.Exists X (fun x =>
      Lean.And (mm_target_mem x (mm_to_imported xs))
        (Lean.And
          (Lean.eq (mm_pred_to_imported P x) ImportedMinmax.Bool_true)
          (mm_target_le (sub_nat_to_imported n)
            (sub_nat_to_imported (F x)))))).
Proof.
  apply mm_exists_identity_correspondence. intro x.
  apply mm_and_correspondence.
  - exact (mm_membership_correspondence X x xs (mm_to_imported xs)
      (@Lean.eq_refl _ _)).
  - apply mm_and_correspondence.
    + exact (mm_bool_truth_correspondence (P x) (mm_pred_to_imported P x)
        (mm_pred_canonical P x)).
    + exact (mm_nat_le_correspondence n (sub_nat_to_imported n)
        (F x) (sub_nat_to_imported (F x))
        (sub_nat_rel_canonical n) (sub_nat_rel_canonical (F x))).
Qed.

Theorem leq_bigmax_sup_statement_certificate :
  PropSPropRel GeneratedMinmaxSource.statement_leq_bigmax_sup
    mm_target_leq_bigmax_sup_statement.
Proof.
  unfold GeneratedMinmaxSource.statement_leq_bigmax_sup,
    mm_target_leq_bigmax_sup_statement.
  apply prop_sprop_rel_intro.
  - intros H X P F xs n Hprem.
    exact (prop_to_sprop _ _
      (mm_nat_le_correspondence n (sub_nat_to_imported n)
        (\max_(x <- xs | P x) F x)
        (mm_target_bigMaxListCond (mm_to_imported xs)
          (mm_pred_to_imported P) (mm_nat_fun_to_imported F))
        (sub_nat_rel_canonical n) (mm_bigmax_list_canonical X xs P F))
      (H X P F xs n
        (sprop_to_prop _ _
          (mm_bigmax_sup_premise_correspondence X P F xs n) Hprem))).
  - intro H. apply strictly_inhabits. intros X P F xs n Hprem.
    exact (sprop_to_prop _ _
      (mm_nat_le_correspondence n (sub_nat_to_imported n)
        (\max_(x <- xs | P x) F x)
        (mm_target_bigMaxListCond (mm_to_imported xs)
          (mm_pred_to_imported P) (mm_nat_fun_to_imported F))
        (sub_nat_rel_canonical n) (mm_bigmax_list_canonical X xs P F))
      (H X P F xs n
        (prop_to_sprop _ _
          (mm_bigmax_sup_premise_correspondence X P F xs n) Hprem))).
Qed.

(** The MathComp source intentionally exposes an informative [reflect] view,
    while the Lean translation exposes its proposition-level [Iff]. *)
Definition mm_target_bigmax_leq_seqP_statement : SProp :=
  forall (X : eqType) (F : X -> nat) (P : X -> bool)
    (xs : seq X) (m : nat),
  ImportedMinmax.Iff
    (mm_target_le
      (mm_target_bigMaxListCond (mm_to_imported xs)
        (mm_pred_to_imported P) (mm_nat_fun_to_imported F))
      (sub_nat_to_imported m))
    (forall x : X,
      mm_target_mem x (mm_to_imported xs) ->
      Lean.eq (mm_pred_to_imported P x) ImportedMinmax.Bool_true ->
      mm_target_le (sub_nat_to_imported (F x)) (sub_nat_to_imported m)).

Lemma mm_bigmax_leq_seqP_instance_relation (X : eqType)
    (F : X -> nat) (P : X -> bool) (xs : seq X) (m : nat) :
  TypeSPropRel
    (reflect (forall x, x \in xs -> P x -> is_true (leq (F x) m))
      (leq (\max_(x <- xs | P x) F x) m))
    (ImportedMinmax.Iff
      (mm_target_le
        (mm_target_bigMaxListCond (mm_to_imported xs)
          (mm_pred_to_imported P) (mm_nat_fun_to_imported F))
        (sub_nat_to_imported m))
      (forall x : X,
        mm_target_mem x (mm_to_imported xs) ->
        Lean.eq (mm_pred_to_imported P x) ImportedMinmax.Bool_true ->
        mm_target_le (sub_nat_to_imported (F x)) (sub_nat_to_imported m))).
Proof.
  set (A := forall x, x \in xs -> P x -> is_true (leq (F x) m)).
  set (b := leq (\max_(x <- xs | P x) F x) m).
  set (BL := mm_target_le
    (mm_target_bigMaxListCond (mm_to_imported xs)
      (mm_pred_to_imported P) (mm_nat_fun_to_imported F))
    (sub_nat_to_imported m)).
  set (CL := forall x : X,
    mm_target_mem x (mm_to_imported xs) ->
    Lean.eq (mm_pred_to_imported P x) ImportedMinmax.Bool_true ->
    mm_target_le (sub_nat_to_imported (F x)) (sub_nat_to_imported m)).
  have Hb : PropSPropRel (is_true b) BL.
  { unfold b, BL. exact (mm_nat_le_correspondence
      (\max_(x <- xs | P x) F x)
      (mm_target_bigMaxListCond (mm_to_imported xs)
        (mm_pred_to_imported P) (mm_nat_fun_to_imported F))
      m (sub_nat_to_imported m)
      (mm_bigmax_list_canonical X xs P F) (sub_nat_rel_canonical m)). }
  have HA : PropSPropRel A CL.
  { unfold A, CL. apply prop_sprop_rel_intro.
    - intros H x Hmem HPx. exact (prop_to_sprop _ _
        (mm_nat_le_correspondence (F x) (sub_nat_to_imported (F x))
          m (sub_nat_to_imported m) (sub_nat_rel_canonical (F x))
          (sub_nat_rel_canonical m))
        (H x
          (sprop_to_prop _ _
            (mm_membership_correspondence X x xs (mm_to_imported xs)
              (@Lean.eq_refl _ _)) Hmem)
          (sprop_to_prop _ _
            (mm_bool_truth_correspondence (P x) (mm_pred_to_imported P x)
              (mm_pred_canonical P x)) HPx))).
    - intro H. apply strictly_inhabits. intros x Hmem HPx.
      exact (sprop_to_prop _ _
        (mm_nat_le_correspondence (F x) (sub_nat_to_imported (F x))
          m (sub_nat_to_imported m) (sub_nat_rel_canonical (F x))
          (sub_nat_rel_canonical m))
        (H x
          (prop_to_sprop _ _
            (mm_membership_correspondence X x xs (mm_to_imported xs)
              (@Lean.eq_refl _ _)) Hmem)
          (prop_to_sprop _ _
            (mm_bool_truth_correspondence (P x) (mm_pred_to_imported P x)
              (mm_pred_canonical P x)) HPx))). }
  have Hiff := mm_iff_correspondence (is_true b) A BL CL Hb HA.
  refine {| type_to_sprop := _; sprop_to_type := _ |}.
  - intro Hr. apply (prop_to_sprop _ _ Hiff).
    destruct Hr as [HAtrue | HAfalse].
    + split.
      * intro Hignored. exact HAtrue.
      * intro Hignored. reflexivity.
    + split.
      * intro Hbtrue. discriminate Hbtrue.
      * intro Ha. exfalso. exact (HAfalse Ha).
  - intro Htarget.
    have Hsource := sprop_to_prop _ _ Hiff Htarget.
    unfold b, A in Hsource |- *.
    case Hbval: (leq (\max_(x <- xs | P x) F x) m).
    + apply ReflectT. exact (proj1 Hsource Hbval).
    + apply ReflectF. intro Hall.
      have Hfalse := proj2 Hsource Hall.
      rewrite Hbval in Hfalse. discriminate Hfalse.
Defined.

Theorem bigmax_leq_seqP_statement_certificate :
  TypeSPropRel GeneratedMinmaxSource.statement_bigmax_leq_seqP
    mm_target_bigmax_leq_seqP_statement.
Proof.
  unfold GeneratedMinmaxSource.statement_bigmax_leq_seqP,
    mm_target_bigmax_leq_seqP_statement.
  refine {| type_to_sprop := _; sprop_to_type := _ |}.
  - intros H X F P xs m. exact (type_to_sprop _ _
      (mm_bigmax_leq_seqP_instance_relation X F P xs m)
      (H X F P xs m)).
  - intros H X F P xs m. exact (sprop_to_type _ _
      (mm_bigmax_leq_seqP_instance_relation X F P xs m)
      (H X F P xs m)).
Defined.

Definition mm_target_leq_big_max_statement : SProp :=
  forall (X : eqType) (F1 F2 : X -> nat) (P : X -> bool)
    (xs : seq X),
  (forall x : X,
    mm_target_mem x (mm_to_imported xs) ->
    Lean.eq (mm_pred_to_imported P x) ImportedMinmax.Bool_true ->
    mm_target_le (sub_nat_to_imported (F1 x))
      (sub_nat_to_imported (F2 x))) ->
  mm_target_le
    (mm_target_bigMaxListCond (mm_to_imported xs)
      (mm_pred_to_imported P) (mm_nat_fun_to_imported F1))
    (mm_target_bigMaxListCond (mm_to_imported xs)
      (mm_pred_to_imported P) (mm_nat_fun_to_imported F2)).

Theorem leq_big_max_statement_certificate :
  PropSPropRel GeneratedMinmaxSource.statement_leq_big_max
    mm_target_leq_big_max_statement.
Proof.
  unfold GeneratedMinmaxSource.statement_leq_big_max,
    mm_target_leq_big_max_statement.
  apply prop_sprop_rel_intro.
  - intros H X F1 F2 P xs Hpoint.
    apply (prop_to_sprop _ _
      (mm_nat_le_correspondence
        (\max_(x <- xs | P x) F1 x)
        (mm_target_bigMaxListCond (mm_to_imported xs)
          (mm_pred_to_imported P) (mm_nat_fun_to_imported F1))
        (\max_(x <- xs | P x) F2 x)
        (mm_target_bigMaxListCond (mm_to_imported xs)
          (mm_pred_to_imported P) (mm_nat_fun_to_imported F2))
        (mm_bigmax_list_canonical X xs P F1)
        (mm_bigmax_list_canonical X xs P F2))).
    apply H. intros x Hmem HPx.
    exact (sprop_to_prop _ _
      (mm_nat_le_correspondence (F1 x) (sub_nat_to_imported (F1 x))
        (F2 x) (sub_nat_to_imported (F2 x))
        (sub_nat_rel_canonical (F1 x)) (sub_nat_rel_canonical (F2 x)))
      (Hpoint x
        (prop_to_sprop _ _
          (mm_membership_correspondence X x xs (mm_to_imported xs)
            (@Lean.eq_refl _ _)) Hmem)
        (prop_to_sprop _ _
          (mm_bool_truth_correspondence (P x) (mm_pred_to_imported P x)
            (mm_pred_canonical P x)) HPx))).
  - intro H. apply strictly_inhabits. intros X F1 F2 P xs Hpoint.
    exact (sprop_to_prop _ _
      (mm_nat_le_correspondence
        (\max_(x <- xs | P x) F1 x)
        (mm_target_bigMaxListCond (mm_to_imported xs)
          (mm_pred_to_imported P) (mm_nat_fun_to_imported F1))
        (\max_(x <- xs | P x) F2 x)
        (mm_target_bigMaxListCond (mm_to_imported xs)
          (mm_pred_to_imported P) (mm_nat_fun_to_imported F2))
        (mm_bigmax_list_canonical X xs P F1)
        (mm_bigmax_list_canonical X xs P F2))
      (H X F1 F2 P xs (fun x Hmem HPx => prop_to_sprop _ _
        (mm_nat_le_correspondence (F1 x) (sub_nat_to_imported (F1 x))
          (F2 x) (sub_nat_to_imported (F2 x))
          (sub_nat_rel_canonical (F1 x)) (sub_nat_rel_canonical (F2 x)))
        (Hpoint x
          (sprop_to_prop _ _
            (mm_membership_correspondence X x xs (mm_to_imported xs)
              (@Lean.eq_refl _ _)) Hmem)
          (sprop_to_prop _ _
            (mm_bool_truth_correspondence (P x) (mm_pred_to_imported P x)
              (mm_pred_canonical P x)) HPx))))).
Qed.

Definition mm_target_bigmax_ord_ltn_identity_statement : SProp :=
  forall n : nat,
  mm_target_lt Lean.Nat_zero (sub_nat_to_imported n) ->
  mm_target_lt
    (mm_target_bigMaxNatRange (sub_nat_to_imported n)
      (fun _ => ImportedMinmax.Bool_true))
    (sub_nat_to_imported n).

Theorem bigmax_ord_ltn_identity_statement_certificate :
  PropSPropRel GeneratedMinmaxSource.statement_bigmax_ord_ltn_identity
    mm_target_bigmax_ord_ltn_identity_statement.
Proof.
  unfold GeneratedMinmaxSource.statement_bigmax_ord_ltn_identity,
    mm_target_bigmax_ord_ltn_identity_statement.
  apply prop_sprop_rel_intro.
  - intros H n Hpos. exact (prop_to_sprop _ _
      (mm_nat_lt_correspondence (\max_(i < n) i)
        (mm_target_bigMaxNatRange (sub_nat_to_imported n)
          (fun _ => ImportedMinmax.Bool_true))
        n (sub_nat_to_imported n) (mm_bigmax_range_true_canonical n)
        (sub_nat_rel_canonical n))
      (H n (sprop_to_prop _ _
        (mm_nat_lt_correspondence O Lean.Nat_zero n
          (sub_nat_to_imported n) (sub_nat_rel_canonical O)
          (sub_nat_rel_canonical n)) Hpos))).
  - intro H. apply strictly_inhabits. intros n Hpos.
    exact (sprop_to_prop _ _
      (mm_nat_lt_correspondence (\max_(i < n) i)
        (mm_target_bigMaxNatRange (sub_nat_to_imported n)
          (fun _ => ImportedMinmax.Bool_true))
        n (sub_nat_to_imported n) (mm_bigmax_range_true_canonical n)
        (sub_nat_rel_canonical n))
      (H n (prop_to_sprop _ _
        (mm_nat_lt_correspondence O Lean.Nat_zero n
          (sub_nat_to_imported n) (sub_nat_rel_canonical O)
          (sub_nat_rel_canonical n)) Hpos))).
Qed.

Definition mm_target_bigmax_ltn_ord_statement : SProp :=
  forall (n : nat) (P : nat -> bool) (i0 : 'I_n),
  Lean.eq
    (mm_nat_pred_to_imported P
      (ImportedMinmax.Fin_val (sub_nat_to_imported n)
        (mm_ord_to_fin n i0))) ImportedMinmax.Bool_true ->
  mm_target_lt
    (mm_target_bigMaxNatRange (sub_nat_to_imported n)
      (mm_nat_pred_to_imported P))
    (sub_nat_to_imported n).

Theorem bigmax_ltn_ord_statement_certificate :
  PropSPropRel GeneratedMinmaxSource.statement_bigmax_ltn_ord
    mm_target_bigmax_ltn_ord_statement.
Proof.
  unfold GeneratedMinmaxSource.statement_bigmax_ltn_ord,
    mm_target_bigmax_ltn_ord_statement.
  apply prop_sprop_rel_intro.
  - intros H n P i0 HP. exact (prop_to_sprop _ _
      (mm_nat_lt_correspondence (\max_(i < n | P i) i)
        (mm_target_bigMaxNatRange (sub_nat_to_imported n)
          (mm_nat_pred_to_imported P)) n (sub_nat_to_imported n)
        (mm_bigmax_range_canonical n P) (sub_nat_rel_canonical n))
      (H n P i0 (sprop_to_prop _ _
        (mm_bool_truth_correspondence (P i0)
          (mm_nat_pred_to_imported P
            (ImportedMinmax.Fin_val (sub_nat_to_imported n)
              (mm_ord_to_fin n i0)))
          (mm_nat_pred_canonical P (nat_of_ord i0))) HP))).
  - intro H. apply strictly_inhabits. intros n P i0 HP.
    exact (sprop_to_prop _ _
      (mm_nat_lt_correspondence (\max_(i < n | P i) i)
        (mm_target_bigMaxNatRange (sub_nat_to_imported n)
          (mm_nat_pred_to_imported P)) n (sub_nat_to_imported n)
        (mm_bigmax_range_canonical n P) (sub_nat_rel_canonical n))
      (H n P i0 (prop_to_sprop _ _
        (mm_bool_truth_correspondence (P i0)
          (mm_nat_pred_to_imported P
            (ImportedMinmax.Fin_val (sub_nat_to_imported n)
              (mm_ord_to_fin n i0)))
          (mm_nat_pred_canonical P (nat_of_ord i0))) HP))).
Qed.

Definition mm_target_bigmax_pred_statement : SProp :=
  forall (n : nat) (P : nat -> bool) (i0 : 'I_n),
  Lean.eq
    (mm_nat_pred_to_imported P
      (ImportedMinmax.Fin_val (sub_nat_to_imported n)
        (mm_ord_to_fin n i0))) ImportedMinmax.Bool_true ->
  Lean.eq
    (mm_nat_pred_to_imported P
      (mm_target_bigMaxNatRange (sub_nat_to_imported n)
        (mm_nat_pred_to_imported P))) ImportedMinmax.Bool_true.

Lemma mm_nat_pred_result_correspondence (P : nat -> bool)
    (r : nat) (l : Lean.Nat) : SubNatRel r l ->
  PropSPropRel (is_true (P r))
    (Lean.eq (mm_nat_pred_to_imported P l) ImportedMinmax.Bool_true).
Proof.
  intro Hr. unfold SubNatRel in Hr.
  have Hdecoded := f_equal sub_nat_to_rocq
    (imported_eq_to_coq_eq _ _ Hr).
  rewrite (sub_nat_rocq_roundtrip r) in Hdecoded.
  unfold mm_nat_pred_to_imported.
  rewrite -Hdecoded.
  exact (mm_bool_truth_correspondence (P r) (mm_bool_to_imported (P r))
    (@Lean.eq_refl _ _)).
Qed.

Theorem bigmax_pred_statement_certificate :
  PropSPropRel GeneratedMinmaxSource.statement_bigmax_pred
    mm_target_bigmax_pred_statement.
Proof.
  unfold GeneratedMinmaxSource.statement_bigmax_pred,
    mm_target_bigmax_pred_statement.
  apply prop_sprop_rel_intro.
  - intros H n P i0 HP. exact (prop_to_sprop _ _
      (mm_nat_pred_result_correspondence P
        (\max_(i < n | P i) i)
        (mm_target_bigMaxNatRange (sub_nat_to_imported n)
          (mm_nat_pred_to_imported P))
        (mm_bigmax_range_canonical n P))
      (H n P i0 (sprop_to_prop _ _
        (mm_bool_truth_correspondence (P i0)
          (mm_nat_pred_to_imported P
            (ImportedMinmax.Fin_val (sub_nat_to_imported n)
              (mm_ord_to_fin n i0)))
          (mm_nat_pred_canonical P (nat_of_ord i0))) HP))).
  - intro H. apply strictly_inhabits. intros n P i0 HP.
    exact (sprop_to_prop _ _
      (mm_nat_pred_result_correspondence P
        (\max_(i < n | P i) i)
        (mm_target_bigMaxNatRange (sub_nat_to_imported n)
          (mm_nat_pred_to_imported P))
        (mm_bigmax_range_canonical n P))
      (H n P i0 (prop_to_sprop _ _
        (mm_bool_truth_correspondence (P i0)
          (mm_nat_pred_to_imported P
            (ImportedMinmax.Fin_val (sub_nat_to_imported n)
              (mm_ord_to_fin n i0)))
          (mm_nat_pred_canonical P (nat_of_ord i0))) HP))).
Qed.

Definition mm_target_bigmax_witness_statement : SProp :=
  forall (T : eqType) (xs : seq T) (P : T -> bool) (F : T -> nat),
  Lean.eq (mm_target_any (mm_to_imported xs) (mm_pred_to_imported P))
    ImportedMinmax.Bool_true ->
  ImportedMinmax.Exists T (fun x =>
    Lean.And (mm_target_mem x (mm_to_imported xs))
      (Lean.And
        (Lean.eq (mm_pred_to_imported P x) ImportedMinmax.Bool_true)
        (Lean.eq (sub_nat_to_imported (F x))
          (mm_target_bigMaxListCond (mm_to_imported xs)
            (mm_pred_to_imported P) (mm_nat_fun_to_imported F))))).

Lemma mm_bigmax_witness_result_correspondence (T : eqType)
    (xs : seq T) (P : T -> bool) (F : T -> nat) :
  PropSPropRel
    (exists x, x \in xs /\ P x /\
      F x = \max_(y <- xs | P y) F y)
    (ImportedMinmax.Exists T (fun x =>
      Lean.And (mm_target_mem x (mm_to_imported xs))
        (Lean.And
          (Lean.eq (mm_pred_to_imported P x) ImportedMinmax.Bool_true)
          (Lean.eq (sub_nat_to_imported (F x))
            (mm_target_bigMaxListCond (mm_to_imported xs)
              (mm_pred_to_imported P) (mm_nat_fun_to_imported F)))))).
Proof.
  apply mm_exists_identity_correspondence. intro x.
  apply mm_and_correspondence.
  - exact (mm_membership_correspondence T x xs (mm_to_imported xs)
      (@Lean.eq_refl _ _)).
  - apply mm_and_correspondence.
    + exact (mm_bool_truth_correspondence (P x) (mm_pred_to_imported P x)
        (mm_pred_canonical P x)).
    + exact (mm_nat_value_eq_correspondence
        (F x) (sub_nat_to_imported (F x))
        (\max_(y <- xs | P y) F y)
        (mm_target_bigMaxListCond (mm_to_imported xs)
          (mm_pred_to_imported P) (mm_nat_fun_to_imported F))
        (sub_nat_rel_canonical (F x)) (mm_bigmax_list_canonical T xs P F)).
Qed.

Theorem bigmax_witness_statement_certificate :
  PropSPropRel GeneratedMinmaxSource.statement_bigmax_witness
    mm_target_bigmax_witness_statement.
Proof.
  unfold GeneratedMinmaxSource.statement_bigmax_witness,
    mm_target_bigmax_witness_statement.
  apply prop_sprop_rel_intro.
  - intros H T xs P F Hhas. exact (prop_to_sprop _ _
      (mm_bigmax_witness_result_correspondence T xs P F)
      (H T xs P F (sprop_to_prop _ _
        (mm_bool_truth_correspondence (has P xs)
          (mm_target_any (mm_to_imported xs) (mm_pred_to_imported P))
          (mm_any_canonical T xs P)) Hhas))).
  - intro H. apply strictly_inhabits. intros T xs P F Hhas.
    exact (sprop_to_prop _ _
      (mm_bigmax_witness_result_correspondence T xs P F)
      (H T xs P F (prop_to_sprop _ _
        (mm_bool_truth_correspondence (has P xs)
          (mm_target_any (mm_to_imported xs) (mm_pred_to_imported P))
          (mm_any_canonical T xs P)) Hhas))).
Qed.

Definition mm_target_bigmax_witness_diff_statement : SProp :=
  forall (T : eqType) (xs : seq T) (P1 P2 : T -> bool) (F : T -> nat),
  mm_target_lt
    (mm_target_bigMaxListCond (mm_to_imported xs)
      (mm_pred_to_imported P1) (mm_nat_fun_to_imported F))
    (mm_target_bigMaxListCond (mm_to_imported xs)
      (mm_pred_to_imported P2) (mm_nat_fun_to_imported F)) ->
  ImportedMinmax.Exists T (fun x =>
    Lean.And (mm_target_mem x (mm_to_imported xs))
      (Lean.And
        (Lean.eq (mm_pred_to_imported P1 x) ImportedMinmax.Bool_false)
        (Lean.eq (mm_pred_to_imported P2 x) ImportedMinmax.Bool_true))).

Lemma mm_bigmax_witness_diff_result_correspondence (T : eqType)
    (xs : seq T) (P1 P2 : T -> bool) :
  PropSPropRel
    (exists x, x \in xs /\ ~~ P1 x /\ P2 x)
    (ImportedMinmax.Exists T (fun x =>
      Lean.And (mm_target_mem x (mm_to_imported xs))
        (Lean.And
          (Lean.eq (mm_pred_to_imported P1 x) ImportedMinmax.Bool_false)
          (Lean.eq (mm_pred_to_imported P2 x) ImportedMinmax.Bool_true)))).
Proof.
  apply mm_exists_identity_correspondence. intro x.
  apply mm_and_correspondence.
  - exact (mm_membership_correspondence T x xs (mm_to_imported xs)
      (@Lean.eq_refl _ _)).
  - apply mm_and_correspondence.
    + exact (mm_bool_false_correspondence (P1 x) (mm_pred_to_imported P1 x)
        (mm_pred_canonical P1 x)).
    + exact (mm_bool_truth_correspondence (P2 x) (mm_pred_to_imported P2 x)
        (mm_pred_canonical P2 x)).
Qed.

Theorem bigmax_witness_diff_statement_certificate :
  PropSPropRel GeneratedMinmaxSource.statement_bigmax_witness_diff
    mm_target_bigmax_witness_diff_statement.
Proof.
  unfold GeneratedMinmaxSource.statement_bigmax_witness_diff,
    mm_target_bigmax_witness_diff_statement.
  apply prop_sprop_rel_intro.
  - intros H T xs P1 P2 F Hlt. exact (prop_to_sprop _ _
      (mm_bigmax_witness_diff_result_correspondence T xs P1 P2)
      (H T xs P1 P2 F (sprop_to_prop _ _
        (mm_nat_lt_correspondence
          (\max_(x <- xs | P1 x) F x)
          (mm_target_bigMaxListCond (mm_to_imported xs)
            (mm_pred_to_imported P1) (mm_nat_fun_to_imported F))
          (\max_(x <- xs | P2 x) F x)
          (mm_target_bigMaxListCond (mm_to_imported xs)
            (mm_pred_to_imported P2) (mm_nat_fun_to_imported F))
          (mm_bigmax_list_canonical T xs P1 F)
          (mm_bigmax_list_canonical T xs P2 F)) Hlt))).
  - intro H. apply strictly_inhabits. intros T xs P1 P2 F Hlt.
    exact (sprop_to_prop _ _
      (mm_bigmax_witness_diff_result_correspondence T xs P1 P2)
      (H T xs P1 P2 F (prop_to_sprop _ _
        (mm_nat_lt_correspondence
          (\max_(x <- xs | P1 x) F x)
          (mm_target_bigMaxListCond (mm_to_imported xs)
            (mm_pred_to_imported P1) (mm_nat_fun_to_imported F))
          (\max_(x <- xs | P2 x) F x)
          (mm_target_bigMaxListCond (mm_to_imported xs)
            (mm_pred_to_imported P2) (mm_nat_fun_to_imported F))
          (mm_bigmax_list_canonical T xs P1 F)
          (mm_bigmax_list_canonical T xs P2 F)) Hlt))).
Qed.

Definition mm_target_bigmax_subset_statement : SProp :=
  forall (T : eqType) (xs : seq T) (P1 P2 : T -> bool) (F : T -> nat),
  (forall x : T,
    mm_target_mem x (mm_to_imported xs) ->
    Lean.eq (mm_pred_to_imported P1 x) ImportedMinmax.Bool_true ->
    Lean.eq (mm_pred_to_imported P2 x) ImportedMinmax.Bool_true) ->
  mm_target_le
    (mm_target_bigMaxListCond (mm_to_imported xs)
      (mm_pred_to_imported P1) (mm_nat_fun_to_imported F))
    (mm_target_bigMaxListCond (mm_to_imported xs)
      (mm_pred_to_imported P2) (mm_nat_fun_to_imported F)).

Theorem bigmax_subset_statement_certificate :
  PropSPropRel GeneratedMinmaxSource.statement_bigmax_subset
    mm_target_bigmax_subset_statement.
Proof.
  unfold GeneratedMinmaxSource.statement_bigmax_subset,
    mm_target_bigmax_subset_statement.
  apply prop_sprop_rel_intro.
  - intros H T xs P1 P2 F Himpl.
    apply (prop_to_sprop _ _
      (mm_nat_le_correspondence
        (\max_(x <- xs | P1 x) F x)
        (mm_target_bigMaxListCond (mm_to_imported xs)
          (mm_pred_to_imported P1) (mm_nat_fun_to_imported F))
        (\max_(x <- xs | P2 x) F x)
        (mm_target_bigMaxListCond (mm_to_imported xs)
          (mm_pred_to_imported P2) (mm_nat_fun_to_imported F))
        (mm_bigmax_list_canonical T xs P1 F)
        (mm_bigmax_list_canonical T xs P2 F))).
    apply H. intros x Hmem HP1.
    exact (sprop_to_prop _ _
      (mm_bool_truth_correspondence (P2 x) (mm_pred_to_imported P2 x)
        (mm_pred_canonical P2 x))
      (Himpl x
        (prop_to_sprop _ _
          (mm_membership_correspondence T x xs (mm_to_imported xs)
            (@Lean.eq_refl _ _)) Hmem)
        (prop_to_sprop _ _
          (mm_bool_truth_correspondence (P1 x) (mm_pred_to_imported P1 x)
            (mm_pred_canonical P1 x)) HP1))).
  - intro H. apply strictly_inhabits. intros T xs P1 P2 F Himpl.
    exact (sprop_to_prop _ _
      (mm_nat_le_correspondence
        (\max_(x <- xs | P1 x) F x)
        (mm_target_bigMaxListCond (mm_to_imported xs)
          (mm_pred_to_imported P1) (mm_nat_fun_to_imported F))
        (\max_(x <- xs | P2 x) F x)
        (mm_target_bigMaxListCond (mm_to_imported xs)
          (mm_pred_to_imported P2) (mm_nat_fun_to_imported F))
        (mm_bigmax_list_canonical T xs P1 F)
        (mm_bigmax_list_canonical T xs P2 F))
      (H T xs P1 P2 F (fun x Hmem HP1 => prop_to_sprop _ _
        (mm_bool_truth_correspondence (P2 x) (mm_pred_to_imported P2 x)
          (mm_pred_canonical P2 x))
        (Himpl x
          (sprop_to_prop _ _
            (mm_membership_correspondence T x xs (mm_to_imported xs)
              (@Lean.eq_refl _ _)) Hmem)
          (sprop_to_prop _ _
            (mm_bool_truth_correspondence (P1 x) (mm_pred_to_imported P1 x)
              (mm_pred_canonical P1 x)) HP1))))).
Qed.
