From mathcomp Require Import ssreflect ssrbool eqtype ssrnat.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedFixpoint.
From FoundationCertificates Require Import SubadditivityNatCorrespondence.
From FoundationCertificates Require Import PropSPropFoundation.
From FoundationCertificates Require Import LogicalRelation.
Require Import GeneratedFixpointSource.

(** The option observation for the actual compiled Fixpoint artifact.  The
    payload map is the previously certified nat representation. *)
Definition FixpointOptionRel (oR : option nat)
    (oL : ImportedFixpoint.Option_inst1 Lean.Nat) : SProp :=
  match oR with
  | None => Lean.eq oL
      (ImportedFixpoint.Option_none_inst1 Lean.Nat)
  | Some n => Lean.eq oL
      (ImportedFixpoint.Option_some_inst1 Lean.Nat
        (sub_nat_to_imported n))
  end.

Definition fixpoint_option_to_imported (oR : option nat) :
    ImportedFixpoint.Option_inst1 Lean.Nat :=
  match oR with
  | None => ImportedFixpoint.Option_none_inst1 Lean.Nat
  | Some n => ImportedFixpoint.Option_some_inst1 Lean.Nat
      (sub_nat_to_imported n)
  end.

Definition fixpoint_option_to_rocq
    (oL : ImportedFixpoint.Option_inst1 Lean.Nat) : option nat :=
  match oL with
  | ImportedFixpoint.Option_none_inst1 => None
  | ImportedFixpoint.Option_some_inst1 n => Some (sub_nat_to_rocq n)
  end.

Lemma fixpoint_option_rocq_roundtrip (oR : option nat) :
    Logic.eq (fixpoint_option_to_rocq
      (fixpoint_option_to_imported oR)) oR.
Proof.
  destruct oR as [n|]; cbn; last reflexivity.
  f_equal. exact (sub_nat_rocq_roundtrip n).
Qed.

Lemma fixpoint_option_imported_roundtrip
    (oL : ImportedFixpoint.Option_inst1 Lean.Nat) :
    Lean.eq (fixpoint_option_to_imported
      (fixpoint_option_to_rocq oL)) oL.
Proof.
  destruct oL as [|n]; cbn.
  - exact (@Lean.eq_refl _ _).
  - exact (sub_imported_eq_congr
      (ImportedFixpoint.Option_some_inst1 Lean.Nat) _ _
      (sub_nat_imported_roundtrip n)).
Qed.

Lemma fixpoint_option_rel_eq (oR : option nat)
    (oL : ImportedFixpoint.Option_inst1 Lean.Nat) :
    FixpointOptionRel oR oL ->
    Lean.eq (fixpoint_option_to_imported oR) oL.
Proof.
  destruct oR; cbn [FixpointOptionRel fixpoint_option_to_imported];
    exact (fun H => sub_imported_eq_sym _ _ H).
Qed.

Lemma fixpoint_option_eq_correspondence oR oL pR pL :
  FixpointOptionRel oR oL -> FixpointOptionRel pR pL ->
  PropSPropRel (Logic.eq oR pR) (Lean.eq oL pL).
Proof.
  intros Ho Hp. apply prop_sprop_rel_intro.
  - intro Heq. subst pR.
    exact (sub_imported_eq_trans _ _ _
      (sub_imported_eq_sym _ _ (fixpoint_option_rel_eq oR oL Ho))
      (fixpoint_option_rel_eq oR pL Hp)).
  - intro Heq. apply strictly_inhabits.
    have HoP := imported_eq_to_coq_eq _ _ (fixpoint_option_rel_eq oR oL Ho).
    have HpP := imported_eq_to_coq_eq _ _ (fixpoint_option_rel_eq pR pL Hp).
    have HeqP := imported_eq_to_coq_eq _ _ Heq.
    apply (f_equal fixpoint_option_to_rocq) in HoP.
    apply (f_equal fixpoint_option_to_rocq) in HpP.
    apply (f_equal fixpoint_option_to_rocq) in HeqP.
    rewrite (fixpoint_option_rocq_roundtrip oR) in HoP.
    rewrite (fixpoint_option_rocq_roundtrip pR) in HpP.
    congruence.
Qed.

Print Assumptions fixpoint_option_eq_correspondence.

Definition FixpointBoolRel (bR : bool)
    (bL : ImportedFixpoint.Bool) : SProp :=
  match bR with
  | true => Lean.eq bL ImportedFixpoint.Bool_true
  | false => Lean.eq bL ImportedFixpoint.Bool_false
  end.

Definition fixpoint_imported_beq (a b : Lean.Nat) :
    ImportedFixpoint.Bool :=
  ImportedFixpoint.Nat_beq a b.

Definition fixpoint_imported_ble (a b : Lean.Nat) :
    ImportedFixpoint.Bool :=
  ImportedFixpoint.Nat_ble a b.

Lemma fixpoint_beq_canonical (a b : nat) :
  FixpointBoolRel (a == b)
    (fixpoint_imported_beq
      (sub_nat_to_imported a) (sub_nat_to_imported b)).
Proof.
  revert b. induction a as [|a IH]; intros [|b]; cbn
    [sub_nat_to_imported FixpointBoolRel fixpoint_imported_beq].
  - exact (@Lean.eq_refl ImportedFixpoint.Bool ImportedFixpoint.Bool_true).
  - exact (ImportedFixpoint.Prosa_Validation_FixpointInterface_natBeqZeroSucc
      (sub_nat_to_imported b)).
  - exact (ImportedFixpoint.Prosa_Validation_FixpointInterface_natBeqSuccZero
      (sub_nat_to_imported a)).
  - rewrite eqSS. destruct (a == b) eqn:Hab;
      pose proof (IH b) as HI; rewrite Hab in HI;
      cbn [FixpointBoolRel] in HI |- *;
      exact (sub_imported_eq_trans _ _ _
        (ImportedFixpoint.Prosa_Validation_FixpointInterface_natBeqSuccSucc
          (sub_nat_to_imported a) (sub_nat_to_imported b)) HI).
Qed.

Lemma fixpoint_ble_canonical (a b : nat) :
  FixpointBoolRel (leq a b)
    (fixpoint_imported_ble
      (sub_nat_to_imported a) (sub_nat_to_imported b)).
Proof.
  revert b. induction a as [|a IH]; intros [|b]; cbn
    [sub_nat_to_imported FixpointBoolRel fixpoint_imported_ble].
  - exact (ImportedFixpoint.Prosa_Validation_FixpointInterface_natBleZero
      Lean.Nat_zero).
  - exact (ImportedFixpoint.Prosa_Validation_FixpointInterface_natBleZero
      (Lean.Nat_succ (sub_nat_to_imported b))).
  - exact (ImportedFixpoint.Prosa_Validation_FixpointInterface_natBleSuccZero
      (sub_nat_to_imported a)).
  - change (FixpointBoolRel (leq a b)
      (ImportedFixpoint.Nat_ble
        (Lean.Nat_succ (sub_nat_to_imported a))
        (Lean.Nat_succ (sub_nat_to_imported b)))).
    destruct (leq a b) eqn:Hab;
      pose proof (IH b) as HI; rewrite Hab in HI;
      cbn [FixpointBoolRel] in HI |- *;
      exact (sub_imported_eq_trans _ _ _
        (ImportedFixpoint.Prosa_Validation_FixpointInterface_natBleSuccSucc
          (sub_nat_to_imported a) (sub_nat_to_imported b)) HI).
Qed.

Lemma fixpoint_beq_correspondence aR aL bR bL :
  SubNatRel aR aL -> SubNatRel bR bL ->
  FixpointBoolRel (aR == bR) (fixpoint_imported_beq aL bL).
Proof.
  intros Ha Hb. unfold SubNatRel in Ha, Hb.
  destruct (aR == bR) eqn:H; cbn [FixpointBoolRel];
    pose proof (fixpoint_beq_canonical aR bR) as Hcanon;
    rewrite H in Hcanon; cbn [FixpointBoolRel] in Hcanon;
  exact (sub_imported_eq_trans _ _ _
    (sub_imported_eq_sym _ _
      (sub_imported_eq_congr2 fixpoint_imported_beq _ _ _ _ Ha Hb))
    Hcanon).
Qed.

Lemma fixpoint_ble_correspondence aR aL bR bL :
  SubNatRel aR aL -> SubNatRel bR bL ->
  FixpointBoolRel (leq aR bR) (fixpoint_imported_ble aL bL).
Proof.
  intros Ha Hb. unfold SubNatRel in Ha, Hb.
  destruct (leq aR bR) eqn:H; cbn [FixpointBoolRel];
    pose proof (fixpoint_ble_canonical aR bR) as Hcanon;
    rewrite H in Hcanon; cbn [FixpointBoolRel] in Hcanon;
  exact (sub_imported_eq_trans _ _ _
    (sub_imported_eq_sym _ _
      (sub_imported_eq_congr2 fixpoint_imported_ble _ _ _ _ Ha Hb))
    Hcanon).
Qed.

Lemma fixpoint_from_canonical_correspondence (fuel : nat) :
  forall (fR : nat -> nat) (fL : Lean.Nat -> Lean.Nat),
    SubNatFunRel fR fL -> forall x h : nat,
  FixpointOptionRel
    (GeneratedFixpointSource.GeneratedFixpointSource.find_fixpoint_from
      fR x h fuel)
    (ImportedFixpoint.Prosa_Util_Fixpoint_find_fixpoint_from fL
      (sub_nat_to_imported x) (sub_nat_to_imported h)
      (sub_nat_to_imported fuel)).
Proof.
  induction fuel as [|fuel IH]; intros fR fL Hf x h.
  - cbn [GeneratedFixpointSource.GeneratedFixpointSource.find_fixpoint_from
      FixpointOptionRel].
    exact (ImportedFixpoint.Prosa_Validation_FixpointInterface_findFixpointFromZero
      fL (sub_nat_to_imported x) (sub_nat_to_imported h)).
  - cbn [GeneratedFixpointSource.GeneratedFixpointSource.find_fixpoint_from
      sub_nat_to_imported].
    pose proof (ImportedFixpoint.Prosa_Validation_FixpointInterface_findFixpointFromSucc
      fL (sub_nat_to_imported x) (sub_nat_to_imported h)
      (sub_nat_to_imported fuel)) as Hstep.
    rewrite (imported_eq_to_coq_eq _ _ Hstep).
    pose proof (Hf x (sub_nat_to_imported x)
      (sub_nat_rel_canonical x)) as Hfx.
    rewrite <- (imported_eq_to_coq_eq _ _ Hfx).
    destruct (fR x == x) eqn:Heq.
    + pose proof (fixpoint_beq_canonical (fR x) x) as Hbeq.
      rewrite Heq in Hbeq. cbn [FixpointBoolRel] in Hbeq.
      unfold fixpoint_imported_beq in Hbeq.
      rewrite (imported_eq_to_coq_eq _ _ Hbeq).
      cbn [ImportedFixpoint.ite ImportedFixpoint.instDecidableEqBool
        FixpointOptionRel].
      exact (@Lean.eq_refl _ _).
    + pose proof (fixpoint_beq_canonical (fR x) x) as Hbeq.
      rewrite Heq in Hbeq. cbn [FixpointBoolRel] in Hbeq.
      unfold fixpoint_imported_beq in Hbeq.
      rewrite (imported_eq_to_coq_eq _ _ Hbeq).
      destruct (leq (fR x) h) eqn:Hle.
      * pose proof (fixpoint_ble_canonical (fR x) h) as Hble.
        rewrite Hle in Hble. cbn [FixpointBoolRel] in Hble.
        unfold fixpoint_imported_ble in Hble.
        rewrite (imported_eq_to_coq_eq _ _ Hble).
        cbn [ImportedFixpoint.ite ImportedFixpoint.instDecidableEqBool].
        exact (IH fR fL Hf (fR x) h).
      * pose proof (fixpoint_ble_canonical (fR x) h) as Hble.
        rewrite Hle in Hble. cbn [FixpointBoolRel] in Hble.
        unfold fixpoint_imported_ble in Hble.
        rewrite (imported_eq_to_coq_eq _ _ Hble).
        cbn [ImportedFixpoint.ite ImportedFixpoint.instDecidableEqBool
          FixpointOptionRel].
        exact (@Lean.eq_refl _ _).
Qed.

Print Assumptions fixpoint_beq_canonical.
Print Assumptions fixpoint_ble_canonical.
Print Assumptions fixpoint_from_canonical_correspondence.

Lemma fixpoint_from_correspondence
    (fR : nat -> nat) (fL : Lean.Nat -> Lean.Nat)
    (xR hR fuelR : nat) (xL hL fuelL : Lean.Nat) :
  SubNatFunRel fR fL -> SubNatRel xR xL ->
  SubNatRel hR hL -> SubNatRel fuelR fuelL ->
  FixpointOptionRel
    (GeneratedFixpointSource.GeneratedFixpointSource.find_fixpoint_from
      fR xR hR fuelR)
    (ImportedFixpoint.Prosa_Util_Fixpoint_find_fixpoint_from
      fL xL hL fuelL).
Proof.
  intros Hf Hx Hh Hfuel.
  unfold SubNatRel in Hx, Hh, Hfuel.
  rewrite <- (imported_eq_to_coq_eq _ _ Hx).
  rewrite <- (imported_eq_to_coq_eq _ _ Hh).
  rewrite <- (imported_eq_to_coq_eq _ _ Hfuel).
  exact (fixpoint_from_canonical_correspondence fuelR fR fL Hf xR hR).
Qed.

Print Assumptions fixpoint_from_correspondence.

Lemma fixpoint_correspondence
    (fR : nat -> nat) (fL : Lean.Nat -> Lean.Nat)
    (hR : nat) (hL : Lean.Nat) :
  SubNatFunRel fR fL -> SubNatRel hR hL ->
  FixpointOptionRel
    (GeneratedFixpointSource.GeneratedFixpointSource.find_fixpoint fR hR)
    (ImportedFixpoint.Prosa_Util_Fixpoint_find_fixpoint fL hL).
Proof.
  intros Hf Hh.
  unfold GeneratedFixpointSource.GeneratedFixpointSource.find_fixpoint.
  pose proof (ImportedFixpoint.Prosa_Validation_FixpointInterface_findFixpointProjection
    fL hL) as Hproject.
  rewrite (imported_eq_to_coq_eq _ _ Hproject).
  apply fixpoint_from_correspondence.
  - exact Hf.
  - exact (sub_nat_rel_canonical 1).
  - exact Hh.
  - exact Hh.
Qed.

Print Assumptions fixpoint_correspondence.

Definition fixpoint_some_rel (nR : nat) (nL : Lean.Nat)
    (Hn : SubNatRel nR nL) :
    FixpointOptionRel (Some nR)
      (ImportedFixpoint.Option_some_inst1 Lean.Nat nL) :=
  sub_imported_eq_sym _ _
    (sub_imported_eq_congr
      (ImportedFixpoint.Option_some_inst1 Lean.Nat) _ _ Hn).

Lemma fixpoint_from_some_eq_correspondence
    (fR : nat -> nat) (fL : Lean.Nat -> Lean.Nat)
    (sR hR fuelR yR : nat) (sL hL fuelL yL : Lean.Nat) :
  SubNatFunRel fR fL -> SubNatRel sR sL -> SubNatRel hR hL ->
  SubNatRel fuelR fuelL -> SubNatRel yR yL ->
  PropSPropRel
    (Logic.eq
      (GeneratedFixpointSource.GeneratedFixpointSource.find_fixpoint_from
        fR sR hR fuelR) (Some yR))
    (Lean.eq
      (ImportedFixpoint.Prosa_Util_Fixpoint_find_fixpoint_from
        fL sL hL fuelL)
      (ImportedFixpoint.Option_some_inst1 Lean.Nat yL)).
Proof.
  intros Hf Hs Hh Hfuel Hy.
  exact (fixpoint_option_eq_correspondence _ _ _ _
    (fixpoint_from_correspondence fR fL
      sR hR fuelR sL hL fuelL Hf Hs Hh Hfuel)
    (fixpoint_some_rel yR yL Hy)).
Qed.

Lemma fixpoint_some_eq_correspondence
    (fR : nat -> nat) (fL : Lean.Nat -> Lean.Nat)
    (hR yR : nat) (hL yL : Lean.Nat) :
  SubNatFunRel fR fL -> SubNatRel hR hL -> SubNatRel yR yL ->
  PropSPropRel
    (Logic.eq
      (GeneratedFixpointSource.GeneratedFixpointSource.find_fixpoint
        fR hR) (Some yR))
    (Lean.eq (ImportedFixpoint.Prosa_Util_Fixpoint_find_fixpoint fL hL)
      (ImportedFixpoint.Option_some_inst1 Lean.Nat yL)).
Proof.
  intros Hf Hh Hy.
  exact (fixpoint_option_eq_correspondence _ _ _ _
    (fixpoint_correspondence fR fL hR hL Hf Hh)
    (fixpoint_some_rel yR yL Hy)).
Qed.

Print Assumptions fixpoint_from_some_eq_correspondence.
Print Assumptions fixpoint_some_eq_correspondence.

Lemma fixpoint_from_some_eq_reverse_correspondence
    (fR : nat -> nat) (fL : Lean.Nat -> Lean.Nat)
    (sR hR fuelR yR : nat) (sL hL fuelL yL : Lean.Nat) :
  SubNatFunRel fR fL -> SubNatRel sR sL -> SubNatRel hR hL ->
  SubNatRel fuelR fuelL -> SubNatRel yR yL ->
  PropSPropRel
    (Logic.eq (Some yR)
      (GeneratedFixpointSource.GeneratedFixpointSource.find_fixpoint_from
        fR sR hR fuelR))
    (Lean.eq (ImportedFixpoint.Option_some_inst1 Lean.Nat yL)
      (ImportedFixpoint.Prosa_Util_Fixpoint_find_fixpoint_from
        fL sL hL fuelL)).
Proof.
  intros Hf Hs Hh Hfuel Hy.
  exact (fixpoint_option_eq_correspondence _ _ _ _
    (fixpoint_some_rel yR yL Hy)
    (fixpoint_from_correspondence fR fL
      sR hR fuelR sL hL fuelL Hf Hs Hh Hfuel)).
Qed.

Lemma fixpoint_some_eq_reverse_correspondence
    (fR : nat -> nat) (fL : Lean.Nat -> Lean.Nat)
    (hR yR : nat) (hL yL : Lean.Nat) :
  SubNatFunRel fR fL -> SubNatRel hR hL -> SubNatRel yR yL ->
  PropSPropRel
    (Logic.eq (Some yR)
      (GeneratedFixpointSource.GeneratedFixpointSource.find_fixpoint
        fR hR))
    (Lean.eq (ImportedFixpoint.Option_some_inst1 Lean.Nat yL)
      (ImportedFixpoint.Prosa_Util_Fixpoint_find_fixpoint fL hL)).
Proof.
  intros Hf Hh Hy.
  exact (fixpoint_option_eq_correspondence _ _ _ _
    (fixpoint_some_rel yR yL Hy)
    (fixpoint_correspondence fR fL hR hL Hf Hh)).
Qed.

Definition fixpoint_none_rel :
    FixpointOptionRel None
      (ImportedFixpoint.Option_none_inst1 Lean.Nat) :=
  @Lean.eq_refl _ _.

Lemma fixpoint_from_none_eq_correspondence
    (fR : nat -> nat) (fL : Lean.Nat -> Lean.Nat)
    (sR hR fuelR : nat) (sL hL fuelL : Lean.Nat) :
  SubNatFunRel fR fL -> SubNatRel sR sL -> SubNatRel hR hL ->
  SubNatRel fuelR fuelL ->
  PropSPropRel
    (Logic.eq
      (GeneratedFixpointSource.GeneratedFixpointSource.find_fixpoint_from
        fR sR hR fuelR) None)
    (Lean.eq
      (ImportedFixpoint.Prosa_Util_Fixpoint_find_fixpoint_from
        fL sL hL fuelL)
      (ImportedFixpoint.Option_none_inst1 Lean.Nat)).
Proof.
  intros Hf Hs Hh Hfuel.
  exact (fixpoint_option_eq_correspondence _ _ _ _
    (fixpoint_from_correspondence fR fL
      sR hR fuelR sL hL fuelL Hf Hs Hh Hfuel)
    fixpoint_none_rel).
Qed.

Lemma fixpoint_none_eq_correspondence
    (fR : nat -> nat) (fL : Lean.Nat -> Lean.Nat)
    (hR : nat) (hL : Lean.Nat) :
  SubNatFunRel fR fL -> SubNatRel hR hL ->
  PropSPropRel
    (Logic.eq
      (GeneratedFixpointSource.GeneratedFixpointSource.find_fixpoint
        fR hR) None)
    (Lean.eq (ImportedFixpoint.Prosa_Util_Fixpoint_find_fixpoint fL hL)
      (ImportedFixpoint.Option_none_inst1 Lean.Nat)).
Proof.
  intros Hf Hh.
  exact (fixpoint_option_eq_correspondence _ _ _ _
    (fixpoint_correspondence fR fL hR hL Hf Hh)
    fixpoint_none_rel).
Qed.

Lemma fixpoint_ffpf_body_correspondence
    (fR : nat -> nat) (fL : Lean.Nat -> Lean.Nat)
    (sR hR fuelR yR : nat) (sL hL fuelL yL : Lean.Nat) :
  SubNatFunRel fR fL ->
  SubNatRel sR sL -> SubNatRel hR hL ->
  SubNatRel fuelR fuelL -> SubNatRel yR yL ->
  PropSPropRel
    (Logic.eq
       (GeneratedFixpointSource.GeneratedFixpointSource.find_fixpoint_from
         fR sR hR fuelR) (Some yR) ->
     Logic.eq yR (fR yR))
    (Lean.eq
       (ImportedFixpoint.Prosa_Util_Fixpoint_find_fixpoint_from
         fL sL hL fuelL)
       (ImportedFixpoint.Option_some_inst1 Lean.Nat yL) ->
     Lean.eq yL (fL yL)).
Proof.
  intros Hf Hs Hh Hfuel Hy.
  have Hrun := fixpoint_from_correspondence fR fL
    sR hR fuelR sL hL fuelL Hf Hs Hh Hfuel.
  have Hresult := fixpoint_option_eq_correspondence _ _ _ _
    Hrun (fixpoint_some_rel yR yL Hy).
  have Hyf := Hf yR yL Hy.
  have Heq := sub_nat_eq_correspondence yR yL (fR yR) (fL yL) Hy Hyf.
  apply prop_sprop_rel_intro.
  - intros HR HL. exact (prop_to_sprop _ _ Heq
      (HR (sprop_to_prop _ _ Hresult HL))).
  - intros HL. apply strictly_inhabits. intros HR.
    exact (sprop_to_prop _ _ Heq
      (HL (prop_to_sprop _ _ Hresult HR))).
Qed.

Print Assumptions fixpoint_ffpf_body_correspondence.

Lemma fixpoint_ffp_body_correspondence
    (fR : nat -> nat) (fL : Lean.Nat -> Lean.Nat)
    (hR yR : nat) (hL yL : Lean.Nat) :
  SubNatFunRel fR fL -> SubNatRel hR hL -> SubNatRel yR yL ->
  PropSPropRel
    (Logic.eq
       (GeneratedFixpointSource.GeneratedFixpointSource.find_fixpoint
         fR hR) (Some yR) -> Logic.eq yR (fR yR))
    (Lean.eq (ImportedFixpoint.Prosa_Util_Fixpoint_find_fixpoint fL hL)
      (ImportedFixpoint.Option_some_inst1 Lean.Nat yL) ->
     Lean.eq yL (fL yL)).
Proof.
  intros Hf Hh Hy.
  have Hrun := fixpoint_correspondence fR fL hR hL Hf Hh.
  have Hresult := fixpoint_option_eq_correspondence _ _ _ _
    Hrun (fixpoint_some_rel yR yL Hy).
  have Hyf := Hf yR yL Hy.
  have Heq := sub_nat_eq_correspondence yR yL (fR yR) (fL yL) Hy Hyf.
  apply prop_sprop_rel_intro.
  - intros HR HL. exact (prop_to_sprop _ _ Heq
      (HR (sprop_to_prop _ _ Hresult HL))).
  - intros HL. apply strictly_inhabits. intros HR.
    exact (sprop_to_prop _ _ Heq
      (HL (prop_to_sprop _ _ Hresult HR))).
Qed.

Print Assumptions fixpoint_ffp_body_correspondence.

(** Both directions for quantifying over all unary Nat functions in a
    theorem statement.  These are definitional representation maps, not
    semantic assumptions about an arbitrary pair of functions. *)
Definition fixpoint_fun_to_imported (fR : nat -> nat)
    (nL : Lean.Nat) : Lean.Nat :=
  sub_nat_to_imported (fR (sub_nat_to_rocq nL)).

Definition fixpoint_fun_to_rocq (fL : Lean.Nat -> Lean.Nat)
    (nR : nat) : nat :=
  sub_nat_to_rocq (fL (sub_nat_to_imported nR)).

Lemma fixpoint_fun_to_imported_rel (fR : nat -> nat) :
  SubNatFunRel fR (fixpoint_fun_to_imported fR).
Proof.
  intros nR nL Hn. unfold SubNatRel in Hn.
  rewrite <- (imported_eq_to_coq_eq _ _ Hn).
  unfold fixpoint_fun_to_imported.
  rewrite (sub_nat_rocq_roundtrip nR).
  exact (sub_nat_rel_canonical (fR nR)).
Qed.

Lemma fixpoint_fun_to_rocq_rel (fL : Lean.Nat -> Lean.Nat) :
  SubNatFunRel (fixpoint_fun_to_rocq fL) fL.
Proof.
  intros nR nL Hn. unfold SubNatRel in Hn.
  rewrite <- (imported_eq_to_coq_eq _ _ Hn).
  unfold fixpoint_fun_to_rocq.
  exact (sub_nat_imported_roundtrip
    (fL (sub_nat_to_imported nR))).
Qed.

(** A first closed computation slice.  It references the actual imported
    function and the actual exported [rfl] equation, not a Rocq rewrite of
    the Lean body.  The general fuel correspondence remains to be proved. *)
Lemma fixpoint_from_zero_correspondence
    (fR : nat -> nat) (fL : Lean.Nat -> Lean.Nat)
    (xR hR : nat) (xL hL : Lean.Nat) :
  FixpointOptionRel
    (GeneratedFixpointSource.GeneratedFixpointSource.find_fixpoint_from
      fR xR hR 0)
    (ImportedFixpoint.Prosa_Util_Fixpoint_find_fixpoint_from
      fL xL hL Lean.Nat_zero).
Proof.
  cbn [GeneratedFixpointSource.GeneratedFixpointSource.find_fixpoint_from
    FixpointOptionRel].
  exact (ImportedFixpoint.Prosa_Validation_FixpointInterface_findFixpointFromZero
    fL xL hL).
Qed.

Print Assumptions fixpoint_from_zero_correspondence.
