From Coq Require Import Arith.Wf_nat.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat div seq.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedLcmseq ImportedSubadditivity.
From FoundationCertificates Require Import
  PropSPropFoundation LogicalRelation SubadditivityNatCorrespondence
  NatSubCorrespondence LcmseqBaseAdapter LcmseqDivModAdapter.

(** Operation-level correspondence for the exact [Nat.gcd], [Nat.lcm], and
    list-fold computation exported from the compiled Lcmseq artifact. *)

Definition lcmo_target_gcd (m n : Lean.Nat) : Lean.Nat :=
  ImportedLcmseq.Nat_gcd m n.

Definition lcmo_target_lcm (m n : Lean.Nat) : Lean.Nat :=
  ImportedLcmseq.Nat_lcm m n.

Definition lcmo_target_lcml
    (xs : ImportedLcmseq.List_inst1 Lean.Nat) : Lean.Nat :=
  ImportedLcmseq.Prosa_Util_Lcmseq_lcml xs.

Lemma lcmo_target_foldr_cons {A B : Type} (f : A -> B -> B)
    (z : B) (x : A) (xs : ImportedLcmseq.List_inst1 A) :
  Lean.eq
    (ImportedLcmseq.List_foldr_inst3 A B f z
      (ImportedLcmseq.List_cons_inst1 A x xs))
    (f x (ImportedLcmseq.List_foldr_inst3 A B f z xs)).
Proof. reflexivity. Qed.

Lemma lcmo_gcd_decoded_canonical (m : nat) : forall n : nat,
  Logic.eq
    (sub_nat_to_rocq
      (lcmo_target_gcd (sub_nat_to_imported m) (sub_nat_to_imported n)))
    (gcdn m n).
Proof.
  apply (lt_wf_ind m (fun k => forall n : nat,
    Logic.eq
      (sub_nat_to_rocq
        (lcmo_target_gcd (sub_nat_to_imported k) (sub_nat_to_imported n)))
      (gcdn k n))).
  intros k IH n. rewrite gcdnE.
  destruct k as [|k'].
  - have Hbody :=
      ImportedLcmseq.Prosa_Validation_LcmseqInterface_production_gcd_def
        Lean.Nat_zero (sub_nat_to_imported n).
    have Hdecoded := f_equal sub_nat_to_rocq
      (imported_eq_to_coq_eq _ _ Hbody).
    cbn [lcmo_target_gcd sub_nat_to_imported] in Hdecoded |- *.
    exact (Logic.eq_trans Hdecoded (sub_nat_rocq_roundtrip n)).
  - have Hmodbool : is_true (ltn (n %% k'.+1) k'.+1) :=
      @ltn_pmod n k'.+1 (ltn0Sn k').
    have Hmodlt : (n %% k'.+1 < k'.+1)%coq_nat :=
      elimT ltP Hmodbool.
    have Hrec := IH (n %% k'.+1) Hmodlt k'.+1.
    have Hmod := lcmseqdm_mod_correspondence
      n (sub_nat_to_imported n) k'.+1 (sub_nat_to_imported k'.+1)
      (sub_nat_rel_canonical n) (sub_nat_rel_canonical k'.+1).
    unfold SubNatRel in Hmod.
    have Hgmod := sub_imported_eq_congr
      (fun r => lcmo_target_gcd r (sub_nat_to_imported k'.+1))
      _ _ Hmod.
    have Hbody :=
      ImportedLcmseq.Prosa_Validation_LcmseqInterface_production_gcd_def
        (sub_nat_to_imported k'.+1) (sub_nat_to_imported n).
    have Hbodydecoded := f_equal sub_nat_to_rocq
      (imported_eq_to_coq_eq _ _ Hbody).
    have Hgmoddecoded := f_equal sub_nat_to_rocq
      (imported_eq_to_coq_eq _ _ Hgmod).
    cbn [lcmo_target_gcd sub_nat_to_imported] in Hbodydecoded |- *.
    exact (Logic.eq_trans Hbodydecoded
      (Logic.eq_trans (Logic.eq_sym Hgmoddecoded) Hrec)).
Qed.

Lemma lcmo_gcd_canonical (m n : nat) :
  Lean.eq
    (lcmo_target_gcd (sub_nat_to_imported m) (sub_nat_to_imported n))
    (sub_nat_to_imported (gcdn m n)).
Proof.
  have Hdecoded := lcmo_gcd_decoded_canonical m n.
  exact (sub_imported_eq_trans _ _ _
    (sub_imported_eq_sym _ _
      (sub_nat_imported_roundtrip
        (lcmo_target_gcd (sub_nat_to_imported m) (sub_nat_to_imported n))))
    (coq_eq_to_imported_eq _ _
      (f_equal sub_nat_to_imported Hdecoded))).
Qed.

Lemma lcmo_gcd_correspondence mR mL nR nL :
  SubNatRel mR mL -> SubNatRel nR nL ->
  SubNatRel (gcdn mR nR) (lcmo_target_gcd mL nL).
Proof.
  intros Hm Hn. unfold SubNatRel.
  exact (sub_imported_eq_trans _ _ _
    (sub_imported_eq_sym _ _ (lcmo_gcd_canonical mR nR))
    (sub_imported_eq_congr2 lcmo_target_gcd _ _ _ _ Hm Hn)).
Qed.

Lemma lcmo_lcm_canonical (m n : nat) :
  Lean.eq
    (lcmo_target_lcm (sub_nat_to_imported m) (sub_nat_to_imported n))
    (sub_nat_to_imported (lcmn m n)).
Proof.
  have Hbody :=
    ImportedLcmseq.Prosa_Validation_LcmseqInterface_production_lcm_eq_mul_div
      (sub_nat_to_imported m) (sub_nat_to_imported n).
  have Hmul := lcmseqdm_mul_correspondence
    m (sub_nat_to_imported m) n (sub_nat_to_imported n)
    (sub_nat_rel_canonical m) (sub_nat_rel_canonical n).
  have Hgcd := lcmo_gcd_correspondence
    m (sub_nat_to_imported m) n (sub_nat_to_imported n)
    (sub_nat_rel_canonical m) (sub_nat_rel_canonical n).
  have Hdiv := lcmseqdm_div_correspondence
    (m * n) (lcmseqdm_imported_mul
      (sub_nat_to_imported m) (sub_nat_to_imported n))
    (gcdn m n)
      (lcmo_target_gcd (sub_nat_to_imported m) (sub_nat_to_imported n))
    Hmul Hgcd.
  unfold SubNatRel in Hdiv.
  change (Lean.eq
    (lcmo_target_lcm (sub_nat_to_imported m) (sub_nat_to_imported n))
    (sub_nat_to_imported ((m * n) %/ gcdn m n))).
  exact (sub_imported_eq_trans _ _ _ Hbody
    (sub_imported_eq_sym _ _ Hdiv)).
Qed.

Lemma lcmo_lcm_correspondence mR mL nR nL :
  SubNatRel mR mL -> SubNatRel nR nL ->
  SubNatRel (lcmn mR nR) (lcmo_target_lcm mL nL).
Proof.
  intros Hm Hn. unfold SubNatRel.
  exact (sub_imported_eq_trans _ _ _
    (sub_imported_eq_sym _ _ (lcmo_lcm_canonical mR nR))
    (sub_imported_eq_congr2 lcmo_target_lcm _ _ _ _ Hm Hn)).
Qed.

Fixpoint lcmo_nat_list_to_imported (xs : seq nat) :
    ImportedLcmseq.List_inst1 Lean.Nat :=
  match xs with
  | [::] => ImportedLcmseq.List_nil_inst1 Lean.Nat
  | x :: xs' => ImportedLcmseq.List_cons_inst1 Lean.Nat
      (sub_nat_to_imported x) (lcmo_nat_list_to_imported xs')
  end.

Definition LcmoNatListRel (xsR : seq nat)
    (xsL : ImportedLcmseq.List_inst1 Lean.Nat) : SProp :=
  Lean.eq (lcmo_nat_list_to_imported xsR) xsL.

Fixpoint lcmo_nat_list_to_rocq
    (xs : ImportedLcmseq.List_inst1 Lean.Nat) : seq nat :=
  match xs with
  | ImportedLcmseq.List_nil_inst1 => [::]
  | ImportedLcmseq.List_cons_inst1 x xs' =>
      sub_nat_to_rocq x :: lcmo_nat_list_to_rocq xs'
  end.

Lemma lcmo_nat_list_source_roundtrip (xs : seq nat) :
  Logic.eq (lcmo_nat_list_to_rocq (lcmo_nat_list_to_imported xs)) xs.
Proof.
  induction xs as [|x xs IH]; cbn; first reflexivity.
  rw (sub_nat_rocq_roundtrip x) IH. reflexivity.
Qed.

Lemma lcmo_nat_list_target_roundtrip
    (xs : ImportedLcmseq.List_inst1 Lean.Nat) :
  Lean.eq (lcmo_nat_list_to_imported (lcmo_nat_list_to_rocq xs)) xs.
Proof.
  induction xs as [|x xs IH]; cbn.
  - exact (@Lean.eq_refl _ _).
  - exact (sub_imported_eq_congr2
      (ImportedLcmseq.List_cons_inst1 Lean.Nat) _ _ _ _
      (sub_nat_imported_roundtrip x) IH).
Qed.

Lemma lcmo_nat_list_rel_canonical (xs : seq nat) :
  LcmoNatListRel xs (lcmo_nat_list_to_imported xs).
Proof. exact (@Lean.eq_refl _ _). Qed.

Lemma lcmo_nat_list_rel_surjective
    (xs : ImportedLcmseq.List_inst1 Lean.Nat) :
  LcmoNatListRel (lcmo_nat_list_to_rocq xs) xs.
Proof. exact (lcmo_nat_list_target_roundtrip xs). Qed.

Lemma lcmo_nat_list_cons_related xR xL xsR xsL :
  SubNatRel xR xL -> LcmoNatListRel xsR xsL ->
  LcmoNatListRel (xR :: xsR)
    (ImportedLcmseq.List_cons_inst1 Lean.Nat xL xsL).
Proof.
  intros Hx Hxs. unfold LcmoNatListRel. cbn.
  exact (sub_imported_eq_congr2
    (ImportedLcmseq.List_cons_inst1 Lean.Nat) _ _ _ _ Hx Hxs).
Qed.

Definition lcmo_target_mem (x : Lean.Nat)
    (xs : ImportedLcmseq.List_inst1 Lean.Nat) : SProp :=
  ImportedLcmseq.Membership_mem_inst3 Lean.Nat
    (ImportedLcmseq.List_inst1 Lean.Nat)
    (ImportedLcmseq.List_instMembership_inst1 Lean.Nat) xs x.

Definition lcmo_target_mem_list_transport (x : Lean.Nat)
    (xs ys : ImportedLcmseq.List_inst1 Lean.Nat) :
  Lean.eq xs ys -> lcmo_target_mem x xs -> lcmo_target_mem x ys :=
  fun Hxy Hmem =>
    match Hxy in Lean.eq _ zs return
      lcmo_target_mem x xs -> lcmo_target_mem x zs
    with
    | Lean.eq_refl => fun H => H
    end Hmem.

Definition lcmo_target_mem_element_transport
    (x y : Lean.Nat) (xs : ImportedLcmseq.List_inst1 Lean.Nat) :
  Lean.eq x y -> lcmo_target_mem x xs -> lcmo_target_mem y xs :=
  fun Hxy Hmem =>
    match Hxy in Lean.eq _ z return
      lcmo_target_mem x xs -> lcmo_target_mem z xs
    with
    | Lean.eq_refl => fun H => H
    end Hmem.

Definition lcmo_mem_head_of_source_eq (x y : nat)
    (xs : ImportedLcmseq.List_inst1 Lean.Nat) :
  Logic.eq x y ->
  ImportedLcmseq.List_Mem_inst1 Lean.Nat (sub_nat_to_imported x)
    (ImportedLcmseq.List_cons_inst1 Lean.Nat
      (sub_nat_to_imported y) xs) :=
  fun H => match H in Logic.eq _ z return
      ImportedLcmseq.List_Mem_inst1 Lean.Nat (sub_nat_to_imported x)
        (ImportedLcmseq.List_cons_inst1 Lean.Nat
          (sub_nat_to_imported z) xs)
    with
    | Logic.eq_refl =>
        ImportedLcmseq.List_Mem_head_inst1 Lean.Nat
          (sub_nat_to_imported x) xs
    end.

Fixpoint lcmo_source_mem_forward (x : nat) (xs : seq nat) :
  SubNatTruth (x \in xs) ->
  ImportedLcmseq.List_Mem_inst1 Lean.Nat (sub_nat_to_imported x)
    (lcmo_nat_list_to_imported xs) :=
  match xs as zs return SubNatTruth (x \in zs) ->
      ImportedLcmseq.List_Mem_inst1 Lean.Nat (sub_nat_to_imported x)
        (lcmo_nat_list_to_imported zs)
  with
  | [::] => sub_nat_false_elim _
  | y :: ys =>
      match @eqP _ x y as r in reflect _ b return
        SubNatTruth (b || (x \in ys)) ->
        ImportedLcmseq.List_Mem_inst1 Lean.Nat (sub_nat_to_imported x)
          (ImportedLcmseq.List_cons_inst1 Lean.Nat
            (sub_nat_to_imported y) (lcmo_nat_list_to_imported ys))
      with
      | ReflectT Hxy => fun _ => lcmo_mem_head_of_source_eq x y _ Hxy
      | ReflectF _ => fun H =>
          ImportedLcmseq.List_Mem_tail_inst1 Lean.Nat
            (sub_nat_to_imported x) (sub_nat_to_imported y) _
            (lcmo_source_mem_forward x ys H)
      end
  end.

Fixpoint lcmo_target_mem_decoded (x : Lean.Nat)
    (xs : ImportedLcmseq.List_inst1 Lean.Nat)
    (H : ImportedLcmseq.List_Mem_inst1 Lean.Nat x xs) :
  SubNatTruth (sub_nat_to_rocq x \in lcmo_nat_list_to_rocq xs) :=
  match H with
  | ImportedLcmseq.List_Mem_head_inst1 ys =>
      lcmseq_mem_head_truth _ _
        (lcmseq_eq_refl_truth _ (sub_nat_to_rocq x))
  | ImportedLcmseq.List_Mem_tail_inst1 y ys Htail =>
      lcmseq_mem_tail_truth _ _ (lcmo_target_mem_decoded x ys Htail)
  end.

Definition lcmo_source_mem_truth_transport (x : nat) (xs ys : seq nat) :
  Logic.eq xs ys -> SubNatTruth (x \in xs) -> SubNatTruth (x \in ys) :=
  fun H Htruth =>
    match H in Logic.eq _ zs return
      SubNatTruth (x \in xs) -> SubNatTruth (x \in zs)
    with
    | Logic.eq_refl => fun Ht => Ht
    end Htruth.

Lemma lcmo_membership_correspondence xR xL xsR xsL :
  SubNatRel xR xL -> LcmoNatListRel xsR xsL ->
  PropSPropRel (xR \in xsR) (lcmo_target_mem xL xsL).
Proof.
  intros Hx Hxs. apply prop_sprop_rel_intro.
  - intro Hmem. unfold lcmo_target_mem.
    apply (lcmo_target_mem_element_transport
      (sub_nat_to_imported xR) xL xsL Hx).
    apply (lcmo_target_mem_list_transport
      (sub_nat_to_imported xR) (lcmo_nat_list_to_imported xsR) xsL Hxs).
    apply lcmo_source_mem_forward.
    exact (sub_nat_prop_to_truth _ Hmem).
  - intro Hmem. apply sub_nat_truth_to_strict_prop.
    apply (lcmo_source_mem_truth_transport xR _ _
      (lcmo_nat_list_source_roundtrip xsR)).
    rewrite -{1}(sub_nat_rocq_roundtrip xR).
    apply lcmo_target_mem_decoded.
    apply (lcmo_target_mem_element_transport xL
      (sub_nat_to_imported xR) (lcmo_nat_list_to_imported xsR)
      (sub_imported_eq_sym _ _ Hx)).
    apply (lcmo_target_mem_list_transport xL xsL
      (lcmo_nat_list_to_imported xsR)
      (sub_imported_eq_sym _ _ Hxs)).
    exact Hmem.
Qed.

Lemma lcmo_lcml_canonical (xs : seq nat) :
  Lean.eq (lcmo_target_lcml (lcmo_nat_list_to_imported xs))
    (sub_nat_to_imported (foldr lcmn (S O) xs)).
Proof.
  unfold lcmo_target_lcml.
  change (Lean.eq
    (ImportedLcmseq.List_foldr_inst3 Lean.Nat Lean.Nat
      ImportedLcmseq.Nat_lcm lcmseqdm_imported_one
      (lcmo_nat_list_to_imported xs))
    (sub_nat_to_imported (foldr lcmn (S O) xs))).
  induction xs as [|x xs IH].
  - reflexivity.
  - cbn [lcmo_nat_list_to_imported foldr].
    exact (sub_imported_eq_trans _ _ _
      (lcmo_target_foldr_cons ImportedLcmseq.Nat_lcm
        lcmseqdm_imported_one (sub_nat_to_imported x)
        (lcmo_nat_list_to_imported xs))
      (sub_imported_eq_trans _ _ _
        (sub_imported_eq_congr
          (ImportedLcmseq.Nat_lcm (sub_nat_to_imported x)) _ _ IH)
        (lcmo_lcm_canonical x (foldr lcmn (S O) xs)))).
Qed.

Lemma lcmo_lcml_correspondence xsR xsL :
  LcmoNatListRel xsR xsL ->
  SubNatRel (foldr lcmn (S O) xsR) (lcmo_target_lcml xsL).
Proof.
  intro Hxs. unfold SubNatRel, LcmoNatListRel in *.
  exact (sub_imported_eq_trans _ _ _
    (sub_imported_eq_sym _ _ (lcmo_lcml_canonical xsR))
    (sub_imported_eq_congr lcmo_target_lcml _ _ Hxs)).
Qed.
