From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq fintype bigop.
From prosa Require Import util.notation GeneratedBigcatSource.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedBigcat.
From FoundationCertificates Require Import
  PropSPropFoundation LogicalRelation SubadditivityNatCorrespondence
  BigcatCorrespondence.

(** Encoded target statements use the canonical representatives of the
    approved eqType/DecidableEq and ordered seq/List relations.  Separate
    exact-type guards bind these encodings to the actual imported theorem
    constants; the correspondence proofs below do not depend on those target
    constants or on the official source theorem proofs. *)

Lemma bc_nat_interval_related
    (mR jR nR : nat) (mL jL nL : Lean.Nat) :
  SubNatRel mR mL -> SubNatRel jR jL -> SubNatRel nR nL ->
  PropSPropRel (is_true (mR <= jR < nR))
    (And (bc_target_le mL jL) (bc_target_lt jL nL)).
Proof.
  intros Hm Hj Hn.
  have Hand := bc_and_correspondence
    (is_true (leq mR jR)) (is_true (ltn jR nR))
    (bc_target_le mL jL) (bc_target_lt jL nL)
    (bc_nat_le_correspondence mR mL jR jL Hm Hj)
    (bc_nat_lt_correspondence jR jL nR nL Hj Hn).
  apply prop_sprop_rel_intro.
  - intro Hrange. apply (prop_to_sprop _ _ Hand).
    move/andP: Hrange => [Hmj Hjn]. split; assumption.
  - intro Hrange. apply strictly_inhabits. apply/andP.
    exact (sprop_to_prop _ _ Hand Hrange).
Qed.

Lemma bc_nat_interval_correspondence (m j n : nat) :
  PropSPropRel (is_true (m <= j < n))
    (And
      (bc_target_le (sub_nat_to_imported m) (sub_nat_to_imported j))
      (bc_target_lt (sub_nat_to_imported j) (sub_nat_to_imported n))).
Proof.
  exact (bc_nat_interval_related m j n
    (sub_nat_to_imported m) (sub_nat_to_imported j)
    (sub_nat_to_imported n)
    (sub_nat_rel_canonical m) (sub_nat_rel_canonical j)
    (sub_nat_rel_canonical n)).
Qed.

Definition bc_target_mem_bigcat_nat_statement : SProp :=
  forall (T : eqType) (f : nat -> seq T) (x : T) (m n j : nat),
  And
    (bc_target_le (sub_nat_to_imported m) (sub_nat_to_imported j))
    (bc_target_lt (sub_nat_to_imported j) (sub_nat_to_imported n)) ->
  bc_target_mem x
    (bc_nat_family_to_imported f (sub_nat_to_imported j)) ->
  bc_target_mem x
    (bc_target_bigCat_nat (sub_nat_to_imported m)
      (sub_nat_to_imported n) (bc_nat_family_to_imported f)).

Theorem mem_bigcat_nat_statement_certificate :
  PropSPropRel GeneratedBigcatSource.statement_mem_bigcat_nat
    bc_target_mem_bigcat_nat_statement.
Proof.
  unfold GeneratedBigcatSource.statement_mem_bigcat_nat,
    bc_target_mem_bigcat_nat_statement.
  apply prop_sprop_rel_intro.
  - intros Hsource T f x m n j HrangeL HmemL.
    have HrangeR := sprop_to_prop _ _
      (bc_nat_interval_correspondence m j n) HrangeL.
    have HmemR := sprop_to_prop _ _
      (bc_membership_correspondence T x (f j)
        (bc_nat_family_to_imported f (sub_nat_to_imported j))
        (bc_nat_family_value_related T f j)) HmemL.
    exact (prop_to_sprop _ _
      (bc_membership_correspondence T x
        (\cat_(m <= i < n) f i)
        (bc_target_bigCat_nat (sub_nat_to_imported m)
          (sub_nat_to_imported n) (bc_nat_family_to_imported f))
        (bc_bigCatNat_related T f m n))
      (Hsource T f x m n j HrangeR HmemR)).
  - intro Htarget. apply strictly_inhabits.
    intros T f x m n j HrangeR HmemR.
    have HrangeL := prop_to_sprop _ _
      (bc_nat_interval_correspondence m j n) HrangeR.
    have HmemL := prop_to_sprop _ _
      (bc_membership_correspondence T x (f j)
        (bc_nat_family_to_imported f (sub_nat_to_imported j))
        (bc_nat_family_value_related T f j)) HmemR.
    exact (sprop_to_prop _ _
      (bc_membership_correspondence T x
        (\cat_(m <= i < n) f i)
        (bc_target_bigCat_nat (sub_nat_to_imported m)
          (sub_nat_to_imported n) (bc_nat_family_to_imported f))
        (bc_bigCatNat_related T f m n))
      (Htarget T f x m n j HrangeL HmemL)).
Qed.

Definition bc_target_mem_bigcat_nat_exists_statement : SProp :=
  forall (T : eqType) (f : nat -> seq T) (x : T) (m n : nat),
  bc_target_mem x
    (bc_target_bigCat_nat (sub_nat_to_imported m)
      (sub_nat_to_imported n) (bc_nat_family_to_imported f)) ->
  ImportedBigcat.Exists Lean.Nat (fun i =>
    And (bc_target_mem x (bc_nat_family_to_imported f i))
      (And
        (bc_target_le (sub_nat_to_imported m) i)
        (bc_target_lt i (sub_nat_to_imported n)))).

Lemma bc_mem_bigcat_nat_exists_result_correspondence
    (T : eqType) (f : nat -> seq T) (x : T) (m n : nat) :
  PropSPropRel
    (exists i : nat, x \in f i /\ m <= i < n)
    (ImportedBigcat.Exists Lean.Nat (fun i =>
      And (bc_target_mem x (bc_nat_family_to_imported f i))
        (And
          (bc_target_le (sub_nat_to_imported m) i)
          (bc_target_lt i (sub_nat_to_imported n))))).
Proof.
  apply bc_exists_nat_correspondence. intros iR iL Hi.
  apply bc_and_correspondence.
  - exact (bc_membership_correspondence T x (f iR)
      (bc_nat_family_to_imported f iL)
      (bc_nat_family_canonical T f iR iL Hi)).
  - exact (bc_nat_interval_related m iR n
      (sub_nat_to_imported m) iL (sub_nat_to_imported n)
      (sub_nat_rel_canonical m) Hi (sub_nat_rel_canonical n)).
Qed.

Theorem mem_bigcat_nat_exists_statement_certificate :
  PropSPropRel GeneratedBigcatSource.statement_mem_bigcat_nat_exists
    bc_target_mem_bigcat_nat_exists_statement.
Proof.
  unfold GeneratedBigcatSource.statement_mem_bigcat_nat_exists,
    bc_target_mem_bigcat_nat_exists_statement.
  apply prop_sprop_rel_intro.
  - intros Hsource T f x m n HmemL.
    have HmemR := sprop_to_prop _ _
      (bc_membership_correspondence T x
        (\cat_(m <= i < n) f i)
        (bc_target_bigCat_nat (sub_nat_to_imported m)
          (sub_nat_to_imported n) (bc_nat_family_to_imported f))
        (bc_bigCatNat_related T f m n)) HmemL.
    exact (prop_to_sprop _ _
      (bc_mem_bigcat_nat_exists_result_correspondence T f x m n)
      (Hsource T f x m n HmemR)).
  - intro Htarget. apply strictly_inhabits.
    intros T f x m n HmemR.
    have HmemL := prop_to_sprop _ _
      (bc_membership_correspondence T x
        (\cat_(m <= i < n) f i)
        (bc_target_bigCat_nat (sub_nat_to_imported m)
          (sub_nat_to_imported n) (bc_nat_family_to_imported f))
        (bc_bigCatNat_related T f m n)) HmemR.
    exact (sprop_to_prop _ _
      (bc_mem_bigcat_nat_exists_result_correspondence T f x m n)
      (Htarget T f x m n HmemL)).
Qed.

Definition bc_target_bigcat_nat_filter_statement : SProp :=
  forall (X : Type) (F : nat -> seq X) (P : X -> bool) (t1 t2 : nat),
  Lean.eq
    (bc_target_filter (bc_pred_to_imported P)
      (bc_target_bigCat_nat (sub_nat_to_imported t1)
        (sub_nat_to_imported t2) (bc_nat_family_to_imported F)))
    (bc_target_bigCat_nat (sub_nat_to_imported t1)
      (sub_nat_to_imported t2)
      (fun t => bc_target_filter (bc_pred_to_imported P)
        (bc_nat_family_to_imported F t))).

Lemma bc_bigcat_nat_filter_result_correspondence
    (X : Type) (F : nat -> seq X) (P : X -> bool) (t1 t2 : nat) :
  PropSPropRel
    ([seq x <- \cat_(t1 <= t < t2) F t | P x] =
      \cat_(t1 <= t < t2) [seq x <- F t | P x])
    (Lean.eq
      (bc_target_filter (bc_pred_to_imported P)
        (bc_target_bigCat_nat (sub_nat_to_imported t1)
          (sub_nat_to_imported t2) (bc_nat_family_to_imported F)))
      (bc_target_bigCat_nat (sub_nat_to_imported t1)
        (sub_nat_to_imported t2)
        (fun t => bc_target_filter (bc_pred_to_imported P)
          (bc_nat_family_to_imported F t)))).
Proof.
  have Hbig := bc_bigCatNat_related X F t1 t2.
  have Hleft := bc_filter_related X P (bc_pred_to_imported P)
    (\cat_(t1 <= t < t2) F t)
    (bc_target_bigCat_nat (sub_nat_to_imported t1)
      (sub_nat_to_imported t2) (bc_nat_family_to_imported F))
    (bc_pred_canonical P) Hbig.
  have Hright := bc_bigCatNat_related_rel X
    (fun t => [seq x <- F t | P x])
    (fun t => bc_target_filter (bc_pred_to_imported P)
      (bc_nat_family_to_imported F t)) t1 t2
    (bc_filtered_nat_family_related X F P).
  exact (bc_list_eq_correspondence X _ _ _ _ Hleft Hright).
Qed.

Theorem bigcat_nat_filter_eq_filter_bigcat_nat_statement_certificate :
  PropSPropRel
    GeneratedBigcatSource.statement_bigcat_nat_filter_eq_filter_bigcat_nat
    bc_target_bigcat_nat_filter_statement.
Proof.
  unfold GeneratedBigcatSource.statement_bigcat_nat_filter_eq_filter_bigcat_nat,
    bc_target_bigcat_nat_filter_statement.
  apply prop_sprop_rel_intro.
  - intros Hsource X F P t1 t2. exact (prop_to_sprop _ _
      (bc_bigcat_nat_filter_result_correspondence X F P t1 t2)
      (Hsource X F P t1 t2)).
  - intro Htarget. apply strictly_inhabits.
    intros X F P t1 t2. exact (sprop_to_prop _ _
      (bc_bigcat_nat_filter_result_correspondence X F P t1 t2)
      (Htarget X F P t1 t2)).
Qed.

Definition bc_source_bigcat_nat_uniq_instance
    (T : eqType) (f : nat -> seq T) : Prop :=
  (forall i : nat, uniq (f i)) ->
  (forall (x : T) (i1 i2 : nat),
    x \in f i1 -> x \in f i2 -> i1 = i2) ->
  forall n1 n2 : nat, uniq (\cat_(n1 <= i < n2) f i).

Definition bc_target_bigcat_nat_uniq_instance
    (T : eqType) (f : nat -> seq T) : SProp :=
  (forall i : Lean.Nat,
    ImportedBigcat.List_Nodup T (bc_nat_family_to_imported f i)) ->
  (forall (x : T) (i1 i2 : Lean.Nat),
    bc_target_mem x (bc_nat_family_to_imported f i1) ->
    bc_target_mem x (bc_nat_family_to_imported f i2) ->
    Lean.eq i1 i2) ->
  forall n1 n2 : Lean.Nat,
    ImportedBigcat.List_Nodup T
      (bc_target_bigCat_nat n1 n2 (bc_nat_family_to_imported f)).

Lemma bc_nat_family_uniq_correspondence
    (T : eqType) (f : nat -> seq T) :
  PropSPropRel (forall i : nat, uniq (f i))
    (forall i : Lean.Nat,
      ImportedBigcat.List_Nodup T (bc_nat_family_to_imported f i)).
Proof.
  apply bc_forall_nat_correspondence. intros iR iL Hi.
  exact (bc_uniq_correspondence T (f iR)
    (bc_nat_family_to_imported f iL)
    (bc_nat_family_canonical T f iR iL Hi)).
Qed.

Lemma bc_nat_family_disjoint_correspondence
    (T : eqType) (f : nat -> seq T) :
  PropSPropRel
    (forall (x : T) (i1 i2 : nat),
      x \in f i1 -> x \in f i2 -> i1 = i2)
    (forall (x : T) (i1 i2 : Lean.Nat),
      bc_target_mem x (bc_nat_family_to_imported f i1) ->
      bc_target_mem x (bc_nat_family_to_imported f i2) ->
      Lean.eq i1 i2).
Proof.
  apply prop_sprop_rel_intro.
  - intros Hsource x i1L i2L Hmem1L Hmem2L.
    set (i1R := sub_nat_to_rocq i1L).
    set (i2R := sub_nat_to_rocq i2L).
    have Hi1 : SubNatRel i1R i1L := sub_nat_rel_surjective i1L.
    have Hi2 : SubNatRel i2R i2L := sub_nat_rel_surjective i2L.
    have Hmem1R := sprop_to_prop _ _
      (bc_membership_correspondence T x (f i1R)
        (bc_nat_family_to_imported f i1L)
        (bc_nat_family_canonical T f i1R i1L Hi1)) Hmem1L.
    have Hmem2R := sprop_to_prop _ _
      (bc_membership_correspondence T x (f i2R)
        (bc_nat_family_to_imported f i2L)
        (bc_nat_family_canonical T f i2R i2L Hi2)) Hmem2L.
    exact (prop_to_sprop _ _
      (sub_nat_eq_correspondence i1R i1L i2R i2L Hi1 Hi2)
      (Hsource x i1R i2R Hmem1R Hmem2R)).
  - intro Htarget. apply strictly_inhabits.
    intros x i1R i2R Hmem1R Hmem2R.
    have Hi1 := sub_nat_rel_canonical i1R.
    have Hi2 := sub_nat_rel_canonical i2R.
    have Hmem1L := prop_to_sprop _ _
      (bc_membership_correspondence T x (f i1R)
        (bc_nat_family_to_imported f (sub_nat_to_imported i1R))
        (bc_nat_family_canonical T f i1R (sub_nat_to_imported i1R) Hi1))
      Hmem1R.
    have Hmem2L := prop_to_sprop _ _
      (bc_membership_correspondence T x (f i2R)
        (bc_nat_family_to_imported f (sub_nat_to_imported i2R))
        (bc_nat_family_canonical T f i2R (sub_nat_to_imported i2R) Hi2))
      Hmem2R.
    exact (sprop_to_prop _ _
      (sub_nat_eq_correspondence i1R (sub_nat_to_imported i1R)
        i2R (sub_nat_to_imported i2R) Hi1 Hi2)
      (Htarget x (sub_nat_to_imported i1R)
        (sub_nat_to_imported i2R) Hmem1L Hmem2L)).
Qed.

Lemma bc_bigcat_nat_uniq_conclusion_correspondence
    (T : eqType) (f : nat -> seq T) :
  PropSPropRel
    (forall n1 n2 : nat, uniq (\cat_(n1 <= i < n2) f i))
    (forall n1 n2 : Lean.Nat,
      ImportedBigcat.List_Nodup T
        (bc_target_bigCat_nat n1 n2 (bc_nat_family_to_imported f))).
Proof.
  apply bc_forall_nat_correspondence. intros n1R n1L Hn1.
  apply bc_forall_nat_correspondence. intros n2R n2L Hn2.
  exact (bc_uniq_correspondence T
    (\cat_(n1R <= i < n2R) f i)
    (bc_target_bigCat_nat n1L n2L (bc_nat_family_to_imported f))
    (bc_bigCatNat_related_any T f (bc_nat_family_to_imported f)
      n1R n2R n1L n2L (bc_nat_family_canonical T f) Hn1 Hn2)).
Qed.

Lemma bc_bigcat_nat_uniq_instance_correspondence
    (T : eqType) (f : nat -> seq T) :
  PropSPropRel (bc_source_bigcat_nat_uniq_instance T f)
    (bc_target_bigcat_nat_uniq_instance T f).
Proof.
  unfold bc_source_bigcat_nat_uniq_instance,
    bc_target_bigcat_nat_uniq_instance.
  apply bc_imp_correspondence.
  - exact (bc_nat_family_uniq_correspondence T f).
  - apply bc_imp_correspondence.
    + exact (bc_nat_family_disjoint_correspondence T f).
    + exact (bc_bigcat_nat_uniq_conclusion_correspondence T f).
Qed.

Definition bc_target_bigcat_nat_uniq_statement : SProp :=
  forall (T : eqType) (f : nat -> seq T),
  bc_target_bigcat_nat_uniq_instance T f.

Theorem bigcat_nat_uniq_statement_certificate :
  PropSPropRel GeneratedBigcatSource.statement_bigcat_nat_uniq
    bc_target_bigcat_nat_uniq_statement.
Proof.
  unfold GeneratedBigcatSource.statement_bigcat_nat_uniq,
    bc_target_bigcat_nat_uniq_statement.
  apply prop_sprop_rel_intro.
  - intros Hsource T f. exact (prop_to_sprop _ _
      (bc_bigcat_nat_uniq_instance_correspondence T f) (Hsource T f)).
  - intro Htarget. apply strictly_inhabits.
    intros T f. exact (sprop_to_prop _ _
      (bc_bigcat_nat_uniq_instance_correspondence T f) (Htarget T f)).
Qed.

Definition bc_target_size_big_nat_statement : SProp :=
  forall (X : Type) (F : nat -> seq X) (t1 t2 : nat),
  Lean.eq
    (bc_target_interval_sum (sub_nat_to_imported t1)
      (sub_nat_to_imported t2)
      (fun t => bc_target_length (bc_nat_family_to_imported F t)))
    (bc_target_length
      (bc_target_bigCat_nat (sub_nat_to_imported t1)
        (sub_nat_to_imported t2) (bc_nat_family_to_imported F))).

Lemma bc_size_big_nat_result_correspondence
    (X : Type) (F : nat -> seq X) (t1 t2 : nat) :
  PropSPropRel
    (\sum_(t1 <= t < t2) size (F t) =
      size (\cat_(t1 <= t < t2) F t))
    (Lean.eq
      (bc_target_interval_sum (sub_nat_to_imported t1)
        (sub_nat_to_imported t2)
        (fun t => bc_target_length (bc_nat_family_to_imported F t)))
      (bc_target_length
        (bc_target_bigCat_nat (sub_nat_to_imported t1)
          (sub_nat_to_imported t2) (bc_nat_family_to_imported F)))).
Proof.
  apply sub_nat_eq_correspondence.
  - exact (bc_interval_sum_related t1 t2 (fun t => size (F t))
      (fun t => bc_target_length (bc_nat_family_to_imported F t))
      (bc_nat_length_family_related X F)).
  - exact (bc_length_related X (\cat_(t1 <= t < t2) F t)
      (bc_target_bigCat_nat (sub_nat_to_imported t1)
        (sub_nat_to_imported t2) (bc_nat_family_to_imported F))
      (bc_bigCatNat_related X F t1 t2)).
Qed.

Theorem size_big_nat_statement_certificate :
  PropSPropRel GeneratedBigcatSource.statement_size_big_nat
    bc_target_size_big_nat_statement.
Proof.
  unfold GeneratedBigcatSource.statement_size_big_nat,
    bc_target_size_big_nat_statement.
  apply prop_sprop_rel_intro.
  - intros Hsource X F t1 t2. exact (prop_to_sprop _ _
      (bc_size_big_nat_result_correspondence X F t1 t2)
      (Hsource X F t1 t2)).
  - intro Htarget. apply strictly_inhabits.
    intros X F t1 t2. exact (sprop_to_prop _ _
      (bc_size_big_nat_result_correspondence X F t1 t2)
      (Htarget X F t1 t2)).
Qed.

Definition bc_target_mem_bigcat_ord_statement : SProp :=
  forall (T : eqType) (x : T) (n : nat)
    (j : 'I_n) (f : 'I_n -> seq T),
  bc_target_lt
    (ImportedBigcat.Fin_val (sub_nat_to_imported n) (bc_ord_to_fin n j))
    (sub_nat_to_imported n) ->
  bc_target_mem x
    (bc_ord_family_to_imported n f (bc_ord_to_fin n j)) ->
  bc_target_mem x
    (bc_target_bigCatFin (sub_nat_to_imported n)
      (bc_ord_family_to_imported n f)).

Theorem mem_bigcat_ord_statement_certificate :
  PropSPropRel GeneratedBigcatSource.statement_mem_bigcat_ord
    bc_target_mem_bigcat_ord_statement.
Proof.
  unfold GeneratedBigcatSource.statement_mem_bigcat_ord,
    bc_target_mem_bigcat_ord_statement.
  apply prop_sprop_rel_intro.
  - intros Hsource T x n j f HltL HmemL.
    have HltR := sprop_to_prop _ _
      (bc_nat_lt_correspondence (nat_of_ord j)
        (ImportedBigcat.Fin_val (sub_nat_to_imported n)
          (bc_ord_to_fin n j)) n (sub_nat_to_imported n)
        (bc_ord_rel_canonical n j) (sub_nat_rel_canonical n)) HltL.
    have HmemR := sprop_to_prop _ _
      (bc_membership_correspondence T x (f j)
        (bc_ord_family_to_imported n f (bc_ord_to_fin n j))
        (bc_ord_family_canonical T n f j (bc_ord_to_fin n j)
          (bc_ord_rel_canonical n j))) HmemL.
    exact (prop_to_sprop _ _
      (bc_membership_correspondence T x
        (\cat_(i < n) f i)
        (bc_target_bigCatFin (sub_nat_to_imported n)
          (bc_ord_family_to_imported n f))
        (bc_bigCatFin_related T n f))
      (Hsource T x n j f HltR HmemR)).
  - intro Htarget. apply strictly_inhabits.
    intros T x n j f HltR HmemR.
    have HltL := prop_to_sprop _ _
      (bc_nat_lt_correspondence (nat_of_ord j)
        (ImportedBigcat.Fin_val (sub_nat_to_imported n)
          (bc_ord_to_fin n j)) n (sub_nat_to_imported n)
        (bc_ord_rel_canonical n j) (sub_nat_rel_canonical n)) HltR.
    have HmemL := prop_to_sprop _ _
      (bc_membership_correspondence T x (f j)
        (bc_ord_family_to_imported n f (bc_ord_to_fin n j))
        (bc_ord_family_canonical T n f j (bc_ord_to_fin n j)
          (bc_ord_rel_canonical n j))) HmemR.
    exact (sprop_to_prop _ _
      (bc_membership_correspondence T x
        (\cat_(i < n) f i)
        (bc_target_bigCatFin (sub_nat_to_imported n)
          (bc_ord_family_to_imported n f))
        (bc_bigCatFin_related T n f))
      (Htarget T x n j f HltL HmemL)).
Qed.

Definition bc_target_mem_bigcat_statement : SProp :=
  forall (X Y : eqType) (f : X -> seq Y) (x : X) (y : Y) (s : seq X),
  bc_target_mem x (bc_to_imported s) ->
  bc_target_mem y (bc_to_imported (f x)) ->
  bc_target_mem y
    (bc_target_bigCatSeqAll X Y (bc_to_imported s)
      (bc_family_to_imported f)).

Theorem mem_bigcat_statement_certificate :
  PropSPropRel GeneratedBigcatSource.statement_mem_bigcat
    bc_target_mem_bigcat_statement.
Proof.
  unfold GeneratedBigcatSource.statement_mem_bigcat,
    bc_target_mem_bigcat_statement.
  apply prop_sprop_rel_intro.
  - intros Hsource X Y f x y s HxsL HyL.
    have HxsR := sprop_to_prop _ _
      (bc_membership_correspondence X x s (bc_to_imported s)
        (@Lean.eq_refl _ _)) HxsL.
    have HyR := sprop_to_prop _ _
      (bc_membership_correspondence Y y (f x) (bc_to_imported (f x))
        (@Lean.eq_refl _ _)) HyL.
    have HresultR := Hsource X Y f x y s HxsR HyR.
    exact (prop_to_sprop _ _
      (bc_membership_correspondence Y y
        (\cat_(z <- s) f z)
        (bc_target_bigCatSeqAll X Y (bc_to_imported s)
          (bc_family_to_imported f))
        (bc_bigCatSeqAll_related X Y f (bc_family_to_imported f)
          s (bc_to_imported s) (bc_family_canonical f)
          (@Lean.eq_refl _ _))) HresultR).
  - intro Htarget. apply strictly_inhabits.
    intros X Y f x y s HxsR HyR.
    have HxsL := prop_to_sprop _ _
      (bc_membership_correspondence X x s (bc_to_imported s)
        (@Lean.eq_refl _ _)) HxsR.
    have HyL := prop_to_sprop _ _
      (bc_membership_correspondence Y y (f x) (bc_to_imported (f x))
        (@Lean.eq_refl _ _)) HyR.
    have HresultL := Htarget X Y f x y s HxsL HyL.
    exact (sprop_to_prop _ _
      (bc_membership_correspondence Y y
        (\cat_(z <- s) f z)
        (bc_target_bigCatSeqAll X Y (bc_to_imported s)
          (bc_family_to_imported f))
        (bc_bigCatSeqAll_related X Y f (bc_family_to_imported f)
          s (bc_to_imported s) (bc_family_canonical f)
          (@Lean.eq_refl _ _))) HresultL).
Qed.

Definition bc_target_mem_bigcat_exists_statement : SProp :=
  forall (X Y : eqType) (f : X -> seq Y) (P : X -> bool)
    (s : seq X) (y : Y),
  bc_target_mem y
    (bc_target_bigCatSeq X Y (bc_to_imported s)
      (bc_pred_to_imported P) (bc_family_to_imported f)) ->
  ImportedBigcat.Exists X (fun x =>
    And (bc_target_mem x (bc_to_imported s))
      (bc_target_mem y (bc_to_imported (f x)))).

Theorem mem_bigcat_exists_statement_certificate :
  PropSPropRel GeneratedBigcatSource.statement_mem_bigcat_exists
    bc_target_mem_bigcat_exists_statement.
Proof.
  unfold GeneratedBigcatSource.statement_mem_bigcat_exists,
    bc_target_mem_bigcat_exists_statement.
  apply prop_sprop_rel_intro.
  - intros Hsource X Y f P s y HmemL.
    have Hbig := bc_bigCatSeq_related X Y f (bc_family_to_imported f)
      P (bc_pred_to_imported P) s (bc_to_imported s)
      (bc_family_canonical f) (bc_pred_canonical P) (@Lean.eq_refl _ _).
    have HmemR := sprop_to_prop _ _
      (bc_membership_correspondence Y y
        (\cat_(x <- s | P x) f x)
        (bc_target_bigCatSeq X Y (bc_to_imported s)
          (bc_pred_to_imported P) (bc_family_to_imported f)) Hbig) HmemL.
    destruct (Hsource X Y f P s y HmemR) as [x [Hxs Hy]].
    exact (ImportedBigcat.Exists_intro X _ x
      (And_intro _ _
        (prop_to_sprop _ _
          (bc_membership_correspondence X x s (bc_to_imported s)
            (@Lean.eq_refl _ _)) Hxs)
        (prop_to_sprop _ _
          (bc_membership_correspondence Y y (f x)
            (bc_to_imported (f x)) (@Lean.eq_refl _ _)) Hy))).
  - intro Htarget. apply strictly_inhabits.
    intros X Y f P s y HmemR.
    have Hbig := bc_bigCatSeq_related X Y f (bc_family_to_imported f)
      P (bc_pred_to_imported P) s (bc_to_imported s)
      (bc_family_canonical f) (bc_pred_canonical P) (@Lean.eq_refl _ _).
    have HmemL := prop_to_sprop _ _
      (bc_membership_correspondence Y y
        (\cat_(x <- s | P x) f x)
        (bc_target_bigCatSeq X Y (bc_to_imported s)
          (bc_pred_to_imported P) (bc_family_to_imported f)) Hbig) HmemR.
    have Hexists := bc_exists_identity_correspondence X
      (fun x => x \in s /\ y \in f x)
      (fun x => And
        (bc_target_mem x (bc_to_imported s))
        (bc_target_mem y (bc_to_imported (f x))))
      (fun x => bc_and_correspondence _ _ _ _
        (bc_membership_correspondence X x s (bc_to_imported s)
          (@Lean.eq_refl _ _))
        (bc_membership_correspondence Y y (f x)
          (bc_to_imported (f x)) (@Lean.eq_refl _ _))).
    exact (sprop_to_prop _ _ Hexists (Htarget X Y f P s y HmemL)).
Qed.

Definition bc_target_bigcat_filter_eq_statement : SProp :=
  forall (X Y : eqType) (f : X -> seq Y) (xss : seq X) (P : Y -> bool),
  Lean.eq
    (bc_target_filter (bc_pred_to_imported P)
      (bc_target_bigCatSeqAll X Y (bc_to_imported xss)
        (bc_family_to_imported f)))
    (bc_target_bigCatSeqAll X Y (bc_to_imported xss)
      (fun x => bc_target_filter (bc_pred_to_imported P)
        (bc_family_to_imported f x))).

Lemma bc_bigcat_filter_result_correspondence
    (X Y : eqType) (f : X -> seq Y) (xss : seq X) (P : Y -> bool) :
  PropSPropRel
    ([seq y <- \cat_(x <- xss) f x | P y]
      = \cat_(x <- xss) [seq y <- f x | P y])
    (Lean.eq
      (bc_target_filter (bc_pred_to_imported P)
        (bc_target_bigCatSeqAll X Y (bc_to_imported xss)
          (bc_family_to_imported f)))
      (bc_target_bigCatSeqAll X Y (bc_to_imported xss)
        (fun x => bc_target_filter (bc_pred_to_imported P)
          (bc_family_to_imported f x)))).
Proof.
  have Hall := bc_bigCatSeqAll_related X Y f (bc_family_to_imported f)
    xss (bc_to_imported xss) (bc_family_canonical f) (@Lean.eq_refl _ _).
  have Hleft := bc_filter_related Y P (bc_pred_to_imported P)
    (\cat_(x <- xss) f x)
    (bc_target_bigCatSeqAll X Y (bc_to_imported xss)
      (bc_family_to_imported f)) (bc_pred_canonical P) Hall.
  have Hright := bc_bigCatSeqAll_related X Y
    (fun x => [seq y <- f x | P y])
    (fun x => bc_target_filter (bc_pred_to_imported P)
      (bc_family_to_imported f x))
    xss (bc_to_imported xss)
    (fun x => bc_filter_related Y P (bc_pred_to_imported P)
      (f x) (bc_family_to_imported f x)
      (bc_pred_canonical P) (@Lean.eq_refl _ _))
    (@Lean.eq_refl _ _).
  exact (bc_list_eq_correspondence Y _ _ _ _ Hleft Hright).
Qed.

Theorem bigcat_filter_eq_filter_bigcat_statement_certificate :
  PropSPropRel
    GeneratedBigcatSource.statement_bigcat_filter_eq_filter_bigcat
    bc_target_bigcat_filter_eq_statement.
Proof.
  unfold GeneratedBigcatSource.statement_bigcat_filter_eq_filter_bigcat,
    bc_target_bigcat_filter_eq_statement.
  apply prop_sprop_rel_intro.
  - intros Hsource X Y f xss P.
    exact (prop_to_sprop _ _
      (bc_bigcat_filter_result_correspondence X Y f xss P)
      (Hsource X Y f xss P)).
  - intro Htarget. apply strictly_inhabits.
    intros X Y f xss P.
    exact (sprop_to_prop _ _
      (bc_bigcat_filter_result_correspondence X Y f xss P)
      (Htarget X Y f xss P)).
Qed.

Definition bc_target_cancels_statement (X Y : eqType)
    (f : X -> seq Y) (g : Y -> X) : SProp :=
  forall x y,
    bc_target_mem y (bc_to_imported (f x)) -> Lean.eq (g y) x.

Lemma bc_cancels_correspondence (X Y : eqType)
    (f : X -> seq Y) (g : Y -> X) :
  PropSPropRel
    (forall x y, y \in f x -> g y = x)
    (bc_target_cancels_statement X Y f g).
Proof.
  unfold bc_target_cancels_statement. apply prop_sprop_rel_intro.
  - intros Hsource x y HmemL.
    have HmemR := sprop_to_prop _ _
      (bc_membership_correspondence Y y (f x) (bc_to_imported (f x))
        (@Lean.eq_refl _ _)) HmemL.
    exact (coq_eq_to_imported_eq _ _ (Hsource x y HmemR)).
  - intro Htarget. apply strictly_inhabits.
    intros x y HmemR.
    have HmemL := prop_to_sprop _ _
      (bc_membership_correspondence Y y (f x) (bc_to_imported (f x))
        (@Lean.eq_refl _ _)) HmemR.
    exact (imported_eq_to_coq_eq _ _ (Htarget x y HmemL)).
Qed.

Definition bc_target_seq_different_elements_nil_statement : SProp :=
  forall (X Y : eqType) (f : X -> seq Y) (g : Y -> X),
  bc_target_cancels_statement X Y f g ->
  forall x1 x2,
  bc_target_ne X x1 x2 ->
  Lean.eq
    (bc_target_filter
      (fun y => bc_target_decide_eq X (g y) x2)
      (bc_to_imported (f x1)))
    (bc_to_imported [::]).

Lemma bc_seq_different_result_correspondence
    (X Y : eqType) (f : X -> seq Y) (g : Y -> X) (x1 x2 : X) :
  PropSPropRel
    ([seq y <- f x1 | g y == x2] = [::])
    (Lean.eq
      (bc_target_filter
        (fun y => bc_target_decide_eq X (g y) x2)
        (bc_to_imported (f x1)))
      (bc_to_imported [::])).
Proof.
  have HP : BcPredRel (fun y => g y == x2)
      (fun y => bc_target_decide_eq X (g y) x2) :=
    fun y => bc_decide_eq_related X (g y) x2.
  have Hfilter := bc_filter_related Y
    (fun y => g y == x2)
    (fun y => bc_target_decide_eq X (g y) x2)
    (f x1) (bc_to_imported (f x1)) HP (@Lean.eq_refl _ _).
  exact (bc_list_eq_correspondence Y _ _ _ _
    Hfilter (@Lean.eq_refl _ _)).
Qed.

Theorem seq_different_elements_nil_statement_certificate :
  PropSPropRel
    GeneratedBigcatSource.statement_seq_different_elements_nil
    bc_target_seq_different_elements_nil_statement.
Proof.
  unfold GeneratedBigcatSource.statement_seq_different_elements_nil,
    bc_target_seq_different_elements_nil_statement.
  apply prop_sprop_rel_intro.
  - intros Hsource X Y f g HcancelL x1 x2 HneL.
    have HcancelR := sprop_to_prop _ _
      (bc_cancels_correspondence X Y f g) HcancelL.
    have HneR := sprop_to_prop _ _
      (bc_bool_ne_correspondence X x1 x2) HneL.
    exact (prop_to_sprop _ _
      (bc_seq_different_result_correspondence X Y f g x1 x2)
      (Hsource X Y f g HcancelR x1 x2 HneR)).
  - intro Htarget. apply strictly_inhabits.
    intros X Y f g HcancelR x1 x2 HneR.
    have HcancelL := prop_to_sprop _ _
      (bc_cancels_correspondence X Y f g) HcancelR.
    have HneL := prop_to_sprop _ _
      (bc_bool_ne_correspondence X x1 x2) HneR.
    exact (sprop_to_prop _ _
      (bc_seq_different_result_correspondence X Y f g x1 x2)
      (Htarget X Y f g HcancelL x1 x2 HneL)).
Qed.

Definition bc_target_bigcat_seq_uniqK_statement : SProp :=
  forall (X Y : eqType) (f : X -> seq Y) (g : Y -> X),
  bc_target_cancels_statement X Y f g ->
  forall (y : X) (xs : seq X),
  bc_target_mem y (bc_to_imported xs) ->
  ImportedBigcat.List_Nodup X (bc_to_imported xs) ->
  Lean.eq
    (bc_target_bigCatSeqAll X Y (bc_to_imported xs)
      (fun x => bc_target_filter
        (fun z => bc_target_decide_eq X (g z) y)
        (bc_to_imported (f x))))
    (bc_to_imported (f y)).

Lemma bc_bigcat_seq_uniqK_result_correspondence
    (X Y : eqType) (f : X -> seq Y) (g : Y -> X)
    (y : X) (xs : seq X) :
  PropSPropRel
    (\cat_(x <- xs) [seq z <- f x | g z == y] = f y)
    (Lean.eq
      (bc_target_bigCatSeqAll X Y (bc_to_imported xs)
        (fun x => bc_target_filter
          (fun z => bc_target_decide_eq X (g z) y)
          (bc_to_imported (f x))))
      (bc_to_imported (f y))).
Proof.
  have Hbig := bc_bigCatSeqAll_related X Y
    (fun x => [seq z <- f x | g z == y])
    (fun x => bc_target_filter
      (fun z => bc_target_decide_eq X (g z) y)
      (bc_to_imported (f x)))
    xs (bc_to_imported xs)
    (bc_decide_eq_filter_family_related X Y f g y)
    (@Lean.eq_refl _ _).
  exact (bc_list_eq_correspondence Y _ _ _ _ Hbig (@Lean.eq_refl _ _)).
Qed.

Theorem bigcat_seq_uniqK_statement_certificate :
  PropSPropRel GeneratedBigcatSource.statement_bigcat_seq_uniqK
    bc_target_bigcat_seq_uniqK_statement.
Proof.
  unfold GeneratedBigcatSource.statement_bigcat_seq_uniqK,
    bc_target_bigcat_seq_uniqK_statement.
  apply prop_sprop_rel_intro.
  - intros Hsource X Y f g HcancelL y xs HyL HuniqL.
    have HcancelR := sprop_to_prop _ _
      (bc_cancels_correspondence X Y f g) HcancelL.
    have HyR := sprop_to_prop _ _
      (bc_membership_correspondence X y xs (bc_to_imported xs)
        (@Lean.eq_refl _ _)) HyL.
    have HuniqR := sprop_to_prop _ _
      (bc_uniq_correspondence X xs (bc_to_imported xs)
        (@Lean.eq_refl _ _)) HuniqL.
    exact (prop_to_sprop _ _
      (bc_bigcat_seq_uniqK_result_correspondence X Y f g y xs)
      (Hsource X Y f g HcancelR y xs HyR HuniqR)).
  - intro Htarget. apply strictly_inhabits.
    intros X Y f g HcancelR y xs HyR HuniqR.
    have HcancelL := prop_to_sprop _ _
      (bc_cancels_correspondence X Y f g) HcancelR.
    have HyL := prop_to_sprop _ _
      (bc_membership_correspondence X y xs (bc_to_imported xs)
        (@Lean.eq_refl _ _)) HyR.
    have HuniqL := prop_to_sprop _ _
      (bc_uniq_correspondence X xs (bc_to_imported xs)
        (@Lean.eq_refl _ _)) HuniqR.
    exact (sprop_to_prop _ _
      (bc_bigcat_seq_uniqK_result_correspondence X Y f g y xs)
      (Htarget X Y f g HcancelL y xs HyL HuniqL)).
Qed.

Definition bc_target_bigcat_uniq_statement : SProp :=
  forall (X Y : eqType) (f : X -> seq Y) (xs : seq X) (P : X -> bool),
  (forall x,
    Lean.eq (bc_bool_to_imported (P x)) ImportedBigcat.Bool_true ->
    ImportedBigcat.List_Nodup Y (bc_to_imported (f x))) ->
  (forall (item : Y) (y z : X),
    bc_target_mem item (bc_to_imported (f y)) ->
    bc_target_mem item (bc_to_imported (f z)) ->
    Lean.eq y z) ->
  ImportedBigcat.List_Nodup X (bc_to_imported xs) ->
  ImportedBigcat.List_Nodup Y
    (bc_target_bigCatSeq X Y (bc_to_imported xs)
      (bc_pred_to_imported P) (bc_family_to_imported f)).

Lemma bc_uniq_family_correspondence (X Y : eqType)
    (f : X -> seq Y) (P : X -> bool) :
  PropSPropRel
    (forall x, P x -> uniq (f x))
    (forall x,
      Lean.eq (bc_bool_to_imported (P x)) ImportedBigcat.Bool_true ->
      ImportedBigcat.List_Nodup Y (bc_to_imported (f x))).
Proof.
  apply prop_sprop_rel_intro.
  - intros Hsource x HP.
    have HPR := sprop_to_prop _ _
      (bc_bool_truth_correspondence (P x)
        (bc_bool_to_imported (P x)) (@Lean.eq_refl _ _)) HP.
    exact (prop_to_sprop _ _
      (bc_uniq_correspondence Y (f x) (bc_to_imported (f x))
        (@Lean.eq_refl _ _)) (Hsource x HPR)).
  - intro Htarget. apply strictly_inhabits. intros x HP.
    have HPL := prop_to_sprop _ _
      (bc_bool_truth_correspondence (P x)
        (bc_bool_to_imported (P x)) (@Lean.eq_refl _ _)) HP.
    exact (sprop_to_prop _ _
      (bc_uniq_correspondence Y (f x) (bc_to_imported (f x))
        (@Lean.eq_refl _ _)) (Htarget x HPL)).
Qed.

Lemma bc_no_common_correspondence (X Y : eqType) (f : X -> seq Y) :
  PropSPropRel
    (forall (item : Y) (y z : X),
      item \in f y -> item \in f z -> y = z)
    (forall (item : Y) (y z : X),
      bc_target_mem item (bc_to_imported (f y)) ->
      bc_target_mem item (bc_to_imported (f z)) -> Lean.eq y z).
Proof.
  apply prop_sprop_rel_intro.
  - intros Hsource item y z Hy Hz.
    have HyR := sprop_to_prop _ _
      (bc_membership_correspondence Y item (f y) (bc_to_imported (f y))
        (@Lean.eq_refl _ _)) Hy.
    have HzR := sprop_to_prop _ _
      (bc_membership_correspondence Y item (f z) (bc_to_imported (f z))
        (@Lean.eq_refl _ _)) Hz.
    exact (coq_eq_to_imported_eq _ _ (Hsource item y z HyR HzR)).
  - intro Htarget. apply strictly_inhabits.
    intros item y z Hy Hz.
    have HyL := prop_to_sprop _ _
      (bc_membership_correspondence Y item (f y) (bc_to_imported (f y))
        (@Lean.eq_refl _ _)) Hy.
    have HzL := prop_to_sprop _ _
      (bc_membership_correspondence Y item (f z) (bc_to_imported (f z))
        (@Lean.eq_refl _ _)) Hz.
    exact (imported_eq_to_coq_eq _ _ (Htarget item y z HyL HzL)).
Qed.

Theorem bigcat_uniq_statement_certificate :
  PropSPropRel GeneratedBigcatSource.statement_bigcat_uniq
    bc_target_bigcat_uniq_statement.
Proof.
  unfold GeneratedBigcatSource.statement_bigcat_uniq,
    bc_target_bigcat_uniq_statement.
  apply prop_sprop_rel_intro.
  - intros Hsource X Y f xs P HuniqL HcommonL HxsL.
    have HuniqR := sprop_to_prop _ _
      (bc_uniq_family_correspondence X Y f P) HuniqL.
    have HcommonR := sprop_to_prop _ _
      (bc_no_common_correspondence X Y f) HcommonL.
    have HxsR := sprop_to_prop _ _
      (bc_uniq_correspondence X xs (bc_to_imported xs)
        (@Lean.eq_refl _ _)) HxsL.
    have HresultR := Hsource X Y f xs P HuniqR HcommonR HxsR.
    have Hbig := bc_bigCatSeq_related X Y f (bc_family_to_imported f)
      P (bc_pred_to_imported P) xs (bc_to_imported xs)
      (bc_family_canonical f) (bc_pred_canonical P) (@Lean.eq_refl _ _).
    exact (prop_to_sprop _ _
      (bc_uniq_correspondence Y _ _ Hbig) HresultR).
  - intro Htarget. apply strictly_inhabits.
    intros X Y f xs P HuniqR HcommonR HxsR.
    have HuniqL := prop_to_sprop _ _
      (bc_uniq_family_correspondence X Y f P) HuniqR.
    have HcommonL := prop_to_sprop _ _
      (bc_no_common_correspondence X Y f) HcommonR.
    have HxsL := prop_to_sprop _ _
      (bc_uniq_correspondence X xs (bc_to_imported xs)
        (@Lean.eq_refl _ _)) HxsR.
    have HresultL := Htarget X Y f xs P HuniqL HcommonL HxsL.
    have Hbig := bc_bigCatSeq_related X Y f (bc_family_to_imported f)
      P (bc_pred_to_imported P) xs (bc_to_imported xs)
      (bc_family_canonical f) (bc_pred_canonical P) (@Lean.eq_refl _ _).
    exact (sprop_to_prop _ _
      (bc_uniq_correspondence Y _ _ Hbig) HresultL).
Qed.

Definition bc_target_partition_pred (X Y : eqType)
    (P : X -> bool) (xToY : X -> Y) (y : Y) :
    X -> ImportedBigcat.Bool :=
  fun x => ImportedBigcat.Bool_and (bc_bool_to_imported (P x))
    (bc_target_decide_eq Y (xToY x) y).

Definition bc_target_partition_family (X Y : eqType)
    (xs : seq X) (P : X -> bool) (xToY : X -> Y) :
    Y -> ImportedBigcat.List X :=
  fun y => bc_target_filter (bc_target_partition_pred X Y P xToY y)
    (bc_to_imported xs).

Lemma bc_partition_family_related (X Y : eqType)
    (xs : seq X) (P : X -> bool) (xToY : X -> Y) :
  BcListFamilyRel
    (fun y => [seq x <- xs | P x & xToY x == y])
    (bc_target_partition_family X Y xs P xToY).
Proof.
  intro y. apply bc_filter_related.
  - intro x. apply bc_bool_and_related.
    + exact (@Lean.eq_refl _ _).
    + exact (bc_decide_eq_related Y (xToY x) y).
  - exact (@Lean.eq_refl _ _).
Qed.

Definition bc_target_no_partition_missing (X Y : eqType)
    (xs : seq X) (ys : seq Y) (P : X -> bool) (xToY : X -> Y) : SProp :=
  forall x,
    bc_target_mem x (bc_to_imported xs) ->
    Lean.eq (bc_bool_to_imported (P x)) ImportedBigcat.Bool_true ->
    bc_target_mem (xToY x) (bc_to_imported ys).

Lemma bc_no_partition_missing_correspondence (X Y : eqType)
    (xs : seq X) (ys : seq Y) (P : X -> bool) (xToY : X -> Y) :
  PropSPropRel
    (forall x, x \in xs -> P x -> xToY x \in ys)
    (bc_target_no_partition_missing X Y xs ys P xToY).
Proof.
  unfold bc_target_no_partition_missing. apply prop_sprop_rel_intro.
  - intros Hsource x HxL HPL.
    have HxR := sprop_to_prop _ _
      (bc_membership_correspondence X x xs (bc_to_imported xs)
        (@Lean.eq_refl _ _)) HxL.
    have HPR := sprop_to_prop _ _
      (bc_bool_truth_correspondence (P x) (bc_bool_to_imported (P x))
        (@Lean.eq_refl _ _)) HPL.
    exact (prop_to_sprop _ _
      (bc_membership_correspondence Y (xToY x) ys (bc_to_imported ys)
        (@Lean.eq_refl _ _)) (Hsource x HxR HPR)).
  - intro Htarget. apply strictly_inhabits.
    intros x HxR HPR.
    have HxL := prop_to_sprop _ _
      (bc_membership_correspondence X x xs (bc_to_imported xs)
        (@Lean.eq_refl _ _)) HxR.
    have HPL := prop_to_sprop _ _
      (bc_bool_truth_correspondence (P x) (bc_bool_to_imported (P x))
        (@Lean.eq_refl _ _)) HPR.
    exact (sprop_to_prop _ _
      (bc_membership_correspondence Y (xToY x) ys (bc_to_imported ys)
        (@Lean.eq_refl _ _)) (Htarget x HxL HPL)).
Qed.

Definition bc_target_bigcat_partitions_statement : SProp :=
  forall (X Y : eqType) (xs : seq X) (ys : seq Y)
    (P : X -> bool) (xToY : X -> Y),
  bc_target_no_partition_missing X Y xs ys P xToY ->
  forall j,
  Lean.eq
    (bc_target_decide_mem X j
      (bc_target_filter (bc_pred_to_imported P) (bc_to_imported xs)))
    (bc_target_decide_mem X j
      (bc_target_bigCatSeqAll Y X (bc_to_imported ys)
        (bc_target_partition_family X Y xs P xToY))).

Lemma bc_bigcat_partitions_result_correspondence
    (X Y : eqType) (xs : seq X) (ys : seq Y)
    (P : X -> bool) (xToY : X -> Y) (j : X) :
  PropSPropRel
    ((j \in [seq x <- xs | P x]) =
      (j \in \cat_(y <- ys)[seq x <- xs | P x & xToY x == y]))
    (Lean.eq
      (bc_target_decide_mem X j
        (bc_target_filter (bc_pred_to_imported P) (bc_to_imported xs)))
      (bc_target_decide_mem X j
        (bc_target_bigCatSeqAll Y X (bc_to_imported ys)
          (bc_target_partition_family X Y xs P xToY)))).
Proof.
  have HleftList := bc_filter_related X P (bc_pred_to_imported P)
    xs (bc_to_imported xs) (bc_pred_canonical P) (@Lean.eq_refl _ _).
  have HrightList := bc_bigCatSeqAll_related Y X
    (fun y => [seq x <- xs | P x & xToY x == y])
    (bc_target_partition_family X Y xs P xToY)
    ys (bc_to_imported ys)
    (bc_partition_family_related X Y xs P xToY) (@Lean.eq_refl _ _).
  apply bc_bool_eq_correspondence.
  - exact (bc_decide_mem_related X j _ _ HleftList).
  - exact (bc_decide_mem_related X j _ _ HrightList).
Qed.

Theorem bigcat_partitions_statement_certificate :
  PropSPropRel GeneratedBigcatSource.statement_bigcat_partitions
    bc_target_bigcat_partitions_statement.
Proof.
  unfold GeneratedBigcatSource.statement_bigcat_partitions,
    bc_target_bigcat_partitions_statement.
  apply prop_sprop_rel_intro.
  - intros Hsource X Y xs ys P xToY HmissingL j.
    have HmissingR := sprop_to_prop _ _
      (bc_no_partition_missing_correspondence X Y xs ys P xToY)
      HmissingL.
    exact (prop_to_sprop _ _
      (bc_bigcat_partitions_result_correspondence X Y xs ys P xToY j)
      (Hsource X Y xs ys P xToY HmissingR j)).
  - intro Htarget. apply strictly_inhabits.
    intros X Y xs ys P xToY HmissingR j.
    have HmissingL := prop_to_sprop _ _
      (bc_no_partition_missing_correspondence X Y xs ys P xToY)
      HmissingR.
    exact (sprop_to_prop _ _
      (bc_bigcat_partitions_result_correspondence X Y xs ys P xToY j)
      (Htarget X Y xs ys P xToY HmissingL j)).
Qed.

Print Assumptions mem_bigcat_nat_statement_certificate.
Print Assumptions mem_bigcat_nat_exists_statement_certificate.
Print Assumptions mem_bigcat_ord_statement_certificate.
Print Assumptions bigcat_nat_uniq_statement_certificate.
Print Assumptions bigcat_nat_filter_eq_filter_bigcat_nat_statement_certificate.
Print Assumptions size_big_nat_statement_certificate.
Print Assumptions mem_bigcat_statement_certificate.
Print Assumptions mem_bigcat_exists_statement_certificate.
Print Assumptions bigcat_filter_eq_filter_bigcat_statement_certificate.
Print Assumptions bigcat_uniq_statement_certificate.
Print Assumptions seq_different_elements_nil_statement_certificate.
Print Assumptions bigcat_seq_uniqK_statement_certificate.
Print Assumptions bigcat_partitions_statement_certificate.
