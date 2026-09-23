From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat div.
From LeanImport Require Import Lean.
From FoundationImported Require Import
  ImportedLcmseq ImportedSubadditivity.
From FoundationCertificates Require Import
  PropSPropFoundation LogicalRelation SubadditivityNatCorrespondence
  NatSubCorrespondence.

(** Operation-level bridge for the exact [Nat.div]/[Nat.mod] interface
    exported from the compiled [Prosa.Util.Div_mod] artifact.  The proof uses
    the two Euclidean characterizations on each side; it does not unfold the
    implementation-specific Lean [Nat.brecOn]/[Nat.below] recursion. *)

Definition lcmseqdm_imported_add (a b : Lean.Nat) : Lean.Nat :=
  ImportedLcmseq.HAdd_hAdd_inst7 Lean.Nat Lean.Nat Lean.Nat
    (ImportedLcmseq.instHAdd_inst1 Lean.Nat ImportedLcmseq.instAddNat) a b.

Definition lcmseqdm_imported_mul (a b : Lean.Nat) : Lean.Nat :=
  ImportedLcmseq.HMul_hMul_inst7 Lean.Nat Lean.Nat Lean.Nat
    (ImportedLcmseq.instHMul_inst1 Lean.Nat ImportedLcmseq.instMulNat) a b.

Definition lcmseqdm_imported_div (a b : Lean.Nat) : Lean.Nat :=
  ImportedLcmseq.HDiv_hDiv_inst7 Lean.Nat Lean.Nat Lean.Nat
    (ImportedLcmseq.instHDiv_inst1 Lean.Nat ImportedLcmseq.Nat_instDiv) a b.

Definition lcmseqdm_imported_sub (a b : Lean.Nat) : Lean.Nat :=
  ImportedLcmseq.HSub_hSub_inst7 Lean.Nat Lean.Nat Lean.Nat
    (ImportedLcmseq.instHSub_inst1 Lean.Nat ImportedLcmseq.instSubNat) a b.

Definition lcmseqdm_imported_mod (a b : Lean.Nat) : Lean.Nat :=
  ImportedLcmseq.HMod_hMod_inst7 Lean.Nat Lean.Nat Lean.Nat
    (ImportedLcmseq.instHMod_inst1 Lean.Nat ImportedLcmseq.Nat_instMod) a b.

Definition lcmseqdm_imported_lt (a b : Lean.Nat) : SProp :=
  ImportedLcmseq.LT_lt_inst1 Lean.Nat ImportedLcmseq.instLTNat a b.

Definition lcmseqdm_imported_le (a b : Lean.Nat) : SProp :=
  ImportedLcmseq.LE_le_inst1 Lean.Nat ImportedLcmseq.instLENat a b.

Definition lcmseqdm_imported_dvd (a b : Lean.Nat) : SProp :=
  ImportedLcmseq.Dvd_dvd_inst1 Lean.Nat ImportedLcmseq.Nat_instDvd a b.

Definition lcmseqdm_imported_zero : Lean.Nat :=
  ImportedLcmseq.OfNat_ofNat_inst1 Lean.Nat Lean.Nat_zero
    (ImportedLcmseq.instOfNatNat Lean.Nat_zero).

Definition lcmseqdm_imported_one : Lean.Nat :=
  ImportedLcmseq.OfNat_ofNat_inst1 Lean.Nat
    (Lean.Nat_succ Lean.Nat_zero)
    (ImportedLcmseq.instOfNatNat (Lean.Nat_succ Lean.Nat_zero)).

Definition lcmseqdm_coq_false_to_target (H : Logic.False) :
    ImportedLcmseq.False :=
  match H return ImportedLcmseq.False with end.

Lemma lcmseqdm_add_correspondence aR aL bR bL :
  SubNatRel aR aL -> SubNatRel bR bL ->
  SubNatRel (aR + bR) (lcmseqdm_imported_add aL bL).
Proof.
  change (SubNatRel aR aL -> SubNatRel bR bL ->
    SubNatRel (aR + bR) (sub_imported_add aL bL)).
  exact (sub_add_correspondence aR aL bR bL).
Qed.

Lemma lcmseqdm_mul_correspondence aR aL bR bL :
  SubNatRel aR aL -> SubNatRel bR bL ->
  SubNatRel (aR * bR) (lcmseqdm_imported_mul aL bL).
Proof.
  change (SubNatRel aR aL -> SubNatRel bR bL ->
    SubNatRel (aR * bR) (sub_imported_mul aL bL)).
  exact (sub_mul_correspondence aR aL bR bL).
Qed.

Lemma lcmseqdm_sub_zero (a : Lean.Nat) :
  Lean.eq (lcmseqdm_imported_sub a Lean.Nat_zero) a.
Proof. exact (@Lean.eq_refl Lean.Nat a). Qed.

Lemma lcmseqdm_sub_succ (a b : Lean.Nat) :
  Lean.eq (lcmseqdm_imported_sub a (Lean.Nat_succ b))
    (ImportedLcmseq.Nat_pred (lcmseqdm_imported_sub a b)).
Proof.
  exact (@Lean.eq_refl Lean.Nat
    (ImportedLcmseq.Nat_pred (lcmseqdm_imported_sub a b))).
Qed.

Definition lcmseqdm_pred_canonical (n : nat) :
  Lean.eq (ImportedLcmseq.Nat_pred (sub_nat_to_imported n))
    (sub_nat_to_imported (Nat.pred n)) :=
  match n return
    Lean.eq (ImportedLcmseq.Nat_pred (sub_nat_to_imported n))
      (sub_nat_to_imported (Nat.pred n))
  with
  | O => @Lean.eq_refl Lean.Nat Lean.Nat_zero
  | S n' => @Lean.eq_refl Lean.Nat (sub_nat_to_imported n')
  end.

Lemma lcmseqdm_sub_iterated_pred (a b : nat) :
  Lean.eq
    (lcmseqdm_imported_sub (sub_nat_to_imported a) (sub_nat_to_imported b))
    (sub_nat_to_imported (rocq_iterated_pred a b)).
Proof.
  revert a. induction b as [|b IH]; intro a.
  - exact (lcmseqdm_sub_zero (sub_nat_to_imported a)).
  - exact (sub_imported_eq_trans _ _ _
      (lcmseqdm_sub_succ _ _)
      (sub_imported_eq_trans _ _ _
        (sub_imported_eq_congr ImportedLcmseq.Nat_pred _ _ (IH a))
        (lcmseqdm_pred_canonical (rocq_iterated_pred a b)))).
Qed.

Lemma lcmseqdm_sub_canonical (a b : nat) :
  Lean.eq
    (lcmseqdm_imported_sub (sub_nat_to_imported a) (sub_nat_to_imported b))
    (sub_nat_to_imported (a - b)).
Proof.
  exact (sub_imported_eq_trans _ _ _
    (lcmseqdm_sub_iterated_pred a b)
    (coq_eq_to_imported_eq _ _
      (f_equal sub_nat_to_imported (rocq_iterated_pred_is_subn a b)))).
Qed.

Lemma lcmseqdm_sub_correspondence aR aL bR bL :
  SubNatRel aR aL -> SubNatRel bR bL ->
  SubNatRel (aR - bR) (lcmseqdm_imported_sub aL bL).
Proof.
  intros Ha Hb. unfold SubNatRel.
  exact (sub_imported_eq_trans _ _ _
    (sub_imported_eq_sym _ _ (lcmseqdm_sub_canonical aR bR))
    (sub_imported_eq_congr2 lcmseqdm_imported_sub _ _ _ _ Ha Hb)).
Qed.

Lemma lcmseqdm_le_correspondence aR aL bR bL :
  SubNatRel aR aL -> SubNatRel bR bL ->
  PropSPropRel (is_true (leq aR bR)) (lcmseqdm_imported_le aL bL).
Proof.
  change (SubNatRel aR aL -> SubNatRel bR bL ->
    PropSPropRel (is_true (leq aR bR)) (sub_imported_le aL bL)).
  exact (sub_nat_le_correspondence aR aL bR bL).
Qed.

Lemma lcmseqdm_lt_correspondence aR aL bR bL :
  SubNatRel aR aL -> SubNatRel bR bL ->
  PropSPropRel (is_true (ltn aR bR)) (lcmseqdm_imported_lt aL bL).
Proof.
  change (SubNatRel aR aL -> SubNatRel bR bL ->
    PropSPropRel (is_true (ltn aR bR)) (sub_imported_lt aL bL)).
  exact (sub_nat_lt_correspondence aR aL bR bL).
Qed.

Lemma lcmseqdm_eq_correspondence aR aL bR bL :
  SubNatRel aR aL -> SubNatRel bR bL ->
  PropSPropRel (Logic.eq aR bR) (Lean.eq aL bL).
Proof. exact (sub_nat_eq_correspondence aR aL bR bL). Qed.

Lemma lcmseqdm_succ_correspondence nR nL :
  SubNatRel nR nL ->
  SubNatRel nR.+1 (lcmseqdm_imported_add nL lcmseqdm_imported_one).
Proof.
  intro Hn. have H := lcmseqdm_add_correspondence nR nL 1 lcmseqdm_imported_one
    Hn (sub_nat_rel_canonical 1).
  rewrite addn1 in H. exact H.
Qed.

Lemma lcmseqdm_div_mod_decoded_canonical (x y : nat) :
  Logic.eq
    (sub_nat_to_rocq
      (lcmseqdm_imported_div (sub_nat_to_imported x) (sub_nat_to_imported y)))
    (x %/ y) /\
  Logic.eq
    (sub_nat_to_rocq
      (lcmseqdm_imported_mod (sub_nat_to_imported x) (sub_nat_to_imported y)))
    (x %% y).
Proof.
  case Hy: y => [|y'].
  - subst y. split.
    + rewrite divn0.
      have H :=
        ImportedLcmseq.Prosa_Validation_DivModInterface_production_div_zero
          (sub_nat_to_imported x).
      exact (f_equal sub_nat_to_rocq
        (imported_eq_to_coq_eq _ _ H)).
    + rewrite modn0.
      have H :=
        ImportedLcmseq.Prosa_Validation_DivModInterface_production_mod_zero
          (sub_nat_to_imported x).
      transitivity
        (sub_nat_to_rocq (sub_nat_to_imported x)).
      * exact (f_equal sub_nat_to_rocq
          (imported_eq_to_coq_eq _ _ H)).
      * exact (sub_nat_rocq_roundtrip x).
  - have Hypos : is_true (ltn O y'.+1) by done.
    set xL := sub_nat_to_imported x.
    set yL := sub_nat_to_imported y'.+1.
    set qL := lcmseqdm_imported_div xL yL.
    set rL := lcmseqdm_imported_mod xL yL.
    have HrLtR : is_true (ltn (sub_nat_to_rocq rL) y'.+1).
    { exact (sprop_to_prop _ _
        (lcmseqdm_lt_correspondence (sub_nat_to_rocq rL) rL y'.+1 yL
          (sub_nat_rel_surjective rL) (sub_nat_rel_canonical y'.+1))
        (ImportedLcmseq.Prosa_Validation_DivModInterface_production_mod_lt
          xL yL
          (prop_to_sprop _ _
            (lcmseqdm_lt_correspondence O lcmseqdm_imported_zero y'.+1 yL
              (sub_nat_rel_canonical O) (sub_nat_rel_canonical y'.+1))
            Hypos))). }
    have HdecompR : Logic.eq
        (y'.+1 * sub_nat_to_rocq qL + sub_nat_to_rocq rL) x.
    { exact (sprop_to_prop _ _
        (lcmseqdm_eq_correspondence
          (y'.+1 * sub_nat_to_rocq qL + sub_nat_to_rocq rL)
          (lcmseqdm_imported_add (lcmseqdm_imported_mul yL qL) rL)
          x xL
          (lcmseqdm_add_correspondence _ _ _ _
            (lcmseqdm_mul_correspondence y'.+1 yL
              (sub_nat_to_rocq qL) qL
              (sub_nat_rel_canonical y'.+1)
              (sub_nat_rel_surjective qL))
            (sub_nat_rel_surjective rL))
          (sub_nat_rel_canonical x))
        (ImportedLcmseq.Prosa_Validation_DivModInterface_production_div_add_mod
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

Lemma lcmseqdm_div_canonical (x y : nat) :
  Lean.eq
    (lcmseqdm_imported_div (sub_nat_to_imported x) (sub_nat_to_imported y))
    (sub_nat_to_imported (x %/ y)).
Proof.
  have Hdecoded := proj1 (lcmseqdm_div_mod_decoded_canonical x y).
  exact (sub_imported_eq_trans _ _ _
    (sub_imported_eq_sym _ _
      (sub_nat_imported_roundtrip
        (lcmseqdm_imported_div (sub_nat_to_imported x) (sub_nat_to_imported y))))
    (coq_eq_to_imported_eq _ _ (f_equal sub_nat_to_imported Hdecoded))).
Qed.

Lemma lcmseqdm_mod_canonical (x y : nat) :
  Lean.eq
    (lcmseqdm_imported_mod (sub_nat_to_imported x) (sub_nat_to_imported y))
    (sub_nat_to_imported (x %% y)).
Proof.
  have Hdecoded := proj2 (lcmseqdm_div_mod_decoded_canonical x y).
  exact (sub_imported_eq_trans _ _ _
    (sub_imported_eq_sym _ _
      (sub_nat_imported_roundtrip
        (lcmseqdm_imported_mod (sub_nat_to_imported x) (sub_nat_to_imported y))))
    (coq_eq_to_imported_eq _ _ (f_equal sub_nat_to_imported Hdecoded))).
Qed.

Lemma lcmseqdm_div_correspondence xR xL yR yL :
  SubNatRel xR xL -> SubNatRel yR yL ->
  SubNatRel (xR %/ yR) (lcmseqdm_imported_div xL yL).
Proof.
  intros Hx Hy. unfold SubNatRel.
  exact (sub_imported_eq_trans _ _ _
    (sub_imported_eq_sym _ _ (lcmseqdm_div_canonical xR yR))
    (sub_imported_eq_congr2 lcmseqdm_imported_div _ _ _ _ Hx Hy)).
Qed.

Lemma lcmseqdm_mod_correspondence xR xL yR yL :
  SubNatRel xR xL -> SubNatRel yR yL ->
  SubNatRel (xR %% yR) (lcmseqdm_imported_mod xL yL).
Proof.
  intros Hx Hy. unfold SubNatRel.
  exact (sub_imported_eq_trans _ _ _
    (sub_imported_eq_sym _ _ (lcmseqdm_mod_canonical xR yR))
    (sub_imported_eq_congr2 lcmseqdm_imported_mod _ _ _ _ Hx Hy)).
Qed.

Lemma lcmseqdm_dvd_correspondence xR xL yR yL :
  SubNatRel xR xL -> SubNatRel yR yL ->
  PropSPropRel (is_true (yR %| xR)) (lcmseqdm_imported_dvd yL xL).
Proof.
  intros Hx Hy. apply prop_sprop_rel_intro.
  - intro HdvdR.
    apply (ImportedLcmseq.mpr _ _
      (ImportedLcmseq.Prosa_Validation_DivModInterface_production_dvd_iff_mod_eq_zero
        xL yL)).
    apply (prop_to_sprop _ _
      (lcmseqdm_eq_correspondence (xR %% yR) (lcmseqdm_imported_mod xL yL)
        O lcmseqdm_imported_zero
        (lcmseqdm_mod_correspondence xR xL yR yL Hx Hy)
        (sub_nat_rel_canonical O))).
    move: HdvdR. rewrite /dvdn. by move/eqP.
  - intro HdvdL. apply strictly_inhabits.
    rewrite /dvdn. apply/eqP.
    apply (sprop_to_prop _ _
      (lcmseqdm_eq_correspondence (xR %% yR) (lcmseqdm_imported_mod xL yL)
        O lcmseqdm_imported_zero
        (lcmseqdm_mod_correspondence xR xL yR yL Hx Hy)
        (sub_nat_rel_canonical O))).
    exact (ImportedLcmseq.mp _ _
      (ImportedLcmseq.Prosa_Validation_DivModInterface_production_dvd_iff_mod_eq_zero
        xL yL) HdvdL).
Qed.

