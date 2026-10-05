From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat div.
From LeanImport Require Import Lean.
From FoundationImported Require Import
  ImportedDivMod ImportedNat ImportedSubadditivity.
From FoundationCertificates Require Import
  PropSPropFoundation LogicalRelation SubadditivityNatCorrespondence
  NatSubCorrespondence.

(** Operation-level bridge for the exact [Nat.div]/[Nat.mod] interface
    exported from the compiled [Prosa.Util.Div_mod] artifact.  The proof uses
    the two Euclidean characterizations on each side; it does not unfold the
    implementation-specific Lean [Nat.brecOn]/[Nat.below] recursion. *)

Definition dm_imported_add (a b : Lean.Nat) : Lean.Nat :=
  ImportedDivMod.HAdd_hAdd_inst7 Lean.Nat Lean.Nat Lean.Nat
    (ImportedDivMod.instHAdd_inst1 Lean.Nat ImportedDivMod.instAddNat) a b.

Definition dm_imported_mul (a b : Lean.Nat) : Lean.Nat :=
  ImportedDivMod.HMul_hMul_inst7 Lean.Nat Lean.Nat Lean.Nat
    (ImportedDivMod.instHMul_inst1 Lean.Nat ImportedDivMod.instMulNat) a b.

Definition dm_imported_div (a b : Lean.Nat) : Lean.Nat :=
  ImportedDivMod.HDiv_hDiv_inst7 Lean.Nat Lean.Nat Lean.Nat
    (ImportedDivMod.instHDiv_inst1 Lean.Nat ImportedDivMod.Nat_instDiv) a b.

Definition dm_imported_sub (a b : Lean.Nat) : Lean.Nat :=
  ImportedDivMod.HSub_hSub_inst7 Lean.Nat Lean.Nat Lean.Nat
    (ImportedDivMod.instHSub_inst1 Lean.Nat ImportedDivMod.instSubNat) a b.

Definition dm_imported_mod (a b : Lean.Nat) : Lean.Nat :=
  ImportedDivMod.HMod_hMod_inst7 Lean.Nat Lean.Nat Lean.Nat
    (ImportedDivMod.instHMod_inst1 Lean.Nat ImportedDivMod.Nat_instMod) a b.

Definition dm_imported_lt (a b : Lean.Nat) : SProp :=
  ImportedDivMod.LT_lt_inst1 Lean.Nat ImportedDivMod.instLTNat a b.

Definition dm_imported_le (a b : Lean.Nat) : SProp :=
  ImportedDivMod.LE_le_inst1 Lean.Nat ImportedDivMod.instLENat a b.

Definition dm_imported_dvd (a b : Lean.Nat) : SProp :=
  ImportedDivMod.Dvd_dvd_inst1 Lean.Nat ImportedDivMod.Nat_instDvd a b.

Definition dm_imported_zero : Lean.Nat :=
  ImportedDivMod.OfNat_ofNat_inst1 Lean.Nat Lean.Nat_zero
    (ImportedDivMod.instOfNatNat Lean.Nat_zero).

Definition dm_imported_one : Lean.Nat :=
  ImportedDivMod.OfNat_ofNat_inst1 Lean.Nat
    (Lean.Nat_succ Lean.Nat_zero)
    (ImportedDivMod.instOfNatNat (Lean.Nat_succ Lean.Nat_zero)).

Definition dm_imported_div_floor (a b : Lean.Nat) : Lean.Nat :=
  ImportedDivMod.Prosa_Util_Div_mod_div_floor a b.

Definition dm_imported_div_ceil (a b : Lean.Nat) : Lean.Nat :=
  ImportedDivMod.Prosa_Util_Div_mod_div_ceil a b.

Definition dm_coq_false_to_target (H : Logic.False) :
    ImportedDivMod.False :=
  match H return ImportedDivMod.False with end.

Lemma dm_add_correspondence aR aL bR bL :
  SubNatRel aR aL -> SubNatRel bR bL ->
  SubNatRel (aR + bR) (dm_imported_add aL bL).
Proof.
  change (SubNatRel aR aL -> SubNatRel bR bL ->
    SubNatRel (aR + bR) (sub_imported_add aL bL)).
  exact (sub_add_correspondence aR aL bR bL).
Qed.

Lemma dm_mul_correspondence aR aL bR bL :
  SubNatRel aR aL -> SubNatRel bR bL ->
  SubNatRel (aR * bR) (dm_imported_mul aL bL).
Proof.
  change (SubNatRel aR aL -> SubNatRel bR bL ->
    SubNatRel (aR * bR) (sub_imported_mul aL bL)).
  exact (sub_mul_correspondence aR aL bR bL).
Qed.

Lemma dm_sub_zero (a : Lean.Nat) :
  Lean.eq (dm_imported_sub a Lean.Nat_zero) a.
Proof. exact (@Lean.eq_refl Lean.Nat a). Qed.

Lemma dm_sub_succ (a b : Lean.Nat) :
  Lean.eq (dm_imported_sub a (Lean.Nat_succ b))
    (ImportedDivMod.Nat_pred (dm_imported_sub a b)).
Proof.
  exact (@Lean.eq_refl Lean.Nat
    (ImportedDivMod.Nat_pred (dm_imported_sub a b))).
Qed.

Definition dm_pred_canonical (n : nat) :
  Lean.eq (ImportedDivMod.Nat_pred (sub_nat_to_imported n))
    (sub_nat_to_imported (Nat.pred n)) :=
  match n return
    Lean.eq (ImportedDivMod.Nat_pred (sub_nat_to_imported n))
      (sub_nat_to_imported (Nat.pred n))
  with
  | O => @Lean.eq_refl Lean.Nat Lean.Nat_zero
  | S n' => @Lean.eq_refl Lean.Nat (sub_nat_to_imported n')
  end.

Lemma dm_sub_iterated_pred (a b : nat) :
  Lean.eq
    (dm_imported_sub (sub_nat_to_imported a) (sub_nat_to_imported b))
    (sub_nat_to_imported (rocq_iterated_pred a b)).
Proof.
  revert a. induction b as [|b IH]; intro a.
  - exact (dm_sub_zero (sub_nat_to_imported a)).
  - exact (sub_imported_eq_trans _ _ _
      (dm_sub_succ _ _)
      (sub_imported_eq_trans _ _ _
        (sub_imported_eq_congr ImportedDivMod.Nat_pred _ _ (IH a))
        (dm_pred_canonical (rocq_iterated_pred a b)))).
Qed.

Lemma dm_sub_canonical (a b : nat) :
  Lean.eq
    (dm_imported_sub (sub_nat_to_imported a) (sub_nat_to_imported b))
    (sub_nat_to_imported (a - b)).
Proof.
  exact (sub_imported_eq_trans _ _ _
    (dm_sub_iterated_pred a b)
    (coq_eq_to_imported_eq _ _
      (f_equal sub_nat_to_imported (rocq_iterated_pred_is_subn a b)))).
Qed.

Lemma dm_sub_correspondence aR aL bR bL :
  SubNatRel aR aL -> SubNatRel bR bL ->
  SubNatRel (aR - bR) (dm_imported_sub aL bL).
Proof.
  intros Ha Hb. unfold SubNatRel.
  exact (sub_imported_eq_trans _ _ _
    (sub_imported_eq_sym _ _ (dm_sub_canonical aR bR))
    (sub_imported_eq_congr2 dm_imported_sub _ _ _ _ Ha Hb)).
Qed.

Lemma dm_le_correspondence aR aL bR bL :
  SubNatRel aR aL -> SubNatRel bR bL ->
  PropSPropRel (is_true (leq aR bR)) (dm_imported_le aL bL).
Proof.
  change (SubNatRel aR aL -> SubNatRel bR bL ->
    PropSPropRel (is_true (leq aR bR)) (sub_imported_le aL bL)).
  exact (sub_nat_le_correspondence aR aL bR bL).
Qed.

Lemma dm_lt_correspondence aR aL bR bL :
  SubNatRel aR aL -> SubNatRel bR bL ->
  PropSPropRel (is_true (ltn aR bR)) (dm_imported_lt aL bL).
Proof.
  change (SubNatRel aR aL -> SubNatRel bR bL ->
    PropSPropRel (is_true (ltn aR bR)) (sub_imported_lt aL bL)).
  exact (sub_nat_lt_correspondence aR aL bR bL).
Qed.

Lemma dm_eq_correspondence aR aL bR bL :
  SubNatRel aR aL -> SubNatRel bR bL ->
  PropSPropRel (Logic.eq aR bR) (Lean.eq aL bL).
Proof. exact (sub_nat_eq_correspondence aR aL bR bL). Qed.

Lemma dm_succ_correspondence nR nL :
  SubNatRel nR nL ->
  SubNatRel nR.+1 (dm_imported_add nL dm_imported_one).
Proof.
  intro Hn. have H := dm_add_correspondence nR nL 1 dm_imported_one
    Hn (sub_nat_rel_canonical 1).
  rewrite addn1 in H. exact H.
Qed.

Lemma dm_div_mod_decoded_canonical (x y : nat) :
  Logic.eq
    (sub_nat_to_rocq
      (dm_imported_div (sub_nat_to_imported x) (sub_nat_to_imported y)))
    (x %/ y) /\
  Logic.eq
    (sub_nat_to_rocq
      (dm_imported_mod (sub_nat_to_imported x) (sub_nat_to_imported y)))
    (x %% y).
Proof.
  case Hy: y => [|y'].
  - subst y. split.
    + rewrite divn0.
      have H :=
        ImportedDivMod.Prosa_Validation_DivModInterface_production_div_zero
          (sub_nat_to_imported x).
      exact (f_equal sub_nat_to_rocq
        (imported_eq_to_coq_eq _ _ H)).
    + rewrite modn0.
      have H :=
        ImportedDivMod.Prosa_Validation_DivModInterface_production_mod_zero
          (sub_nat_to_imported x).
      transitivity
        (sub_nat_to_rocq (sub_nat_to_imported x)).
      * exact (f_equal sub_nat_to_rocq
          (imported_eq_to_coq_eq _ _ H)).
      * exact (sub_nat_rocq_roundtrip x).
  - have Hypos : is_true (ltn O y'.+1) by done.
    set xL := sub_nat_to_imported x.
    set yL := sub_nat_to_imported y'.+1.
    set qL := dm_imported_div xL yL.
    set rL := dm_imported_mod xL yL.
    have HrLtR : is_true (ltn (sub_nat_to_rocq rL) y'.+1).
    { exact (sprop_to_prop _ _
        (dm_lt_correspondence (sub_nat_to_rocq rL) rL y'.+1 yL
          (sub_nat_rel_surjective rL) (sub_nat_rel_canonical y'.+1))
        (ImportedDivMod.Prosa_Validation_DivModInterface_production_mod_lt
          xL yL
          (prop_to_sprop _ _
            (dm_lt_correspondence O dm_imported_zero y'.+1 yL
              (sub_nat_rel_canonical O) (sub_nat_rel_canonical y'.+1))
            Hypos))). }
    have HdecompR : Logic.eq
        (y'.+1 * sub_nat_to_rocq qL + sub_nat_to_rocq rL) x.
    { exact (sprop_to_prop _ _
        (dm_eq_correspondence
          (y'.+1 * sub_nat_to_rocq qL + sub_nat_to_rocq rL)
          (dm_imported_add (dm_imported_mul yL qL) rL)
          x xL
          (dm_add_correspondence _ _ _ _
            (dm_mul_correspondence y'.+1 yL
              (sub_nat_to_rocq qL) qL
              (sub_nat_rel_canonical y'.+1)
              (sub_nat_rel_surjective qL))
            (sub_nat_rel_surjective rL))
          (sub_nat_rel_canonical x))
        (ImportedDivMod.Prosa_Validation_DivModInterface_production_div_add_mod
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

Lemma dm_div_canonical (x y : nat) :
  Lean.eq
    (dm_imported_div (sub_nat_to_imported x) (sub_nat_to_imported y))
    (sub_nat_to_imported (x %/ y)).
Proof.
  have Hdecoded := proj1 (dm_div_mod_decoded_canonical x y).
  exact (sub_imported_eq_trans _ _ _
    (sub_imported_eq_sym _ _
      (sub_nat_imported_roundtrip
        (dm_imported_div (sub_nat_to_imported x) (sub_nat_to_imported y))))
    (coq_eq_to_imported_eq _ _ (f_equal sub_nat_to_imported Hdecoded))).
Qed.

Lemma dm_mod_canonical (x y : nat) :
  Lean.eq
    (dm_imported_mod (sub_nat_to_imported x) (sub_nat_to_imported y))
    (sub_nat_to_imported (x %% y)).
Proof.
  have Hdecoded := proj2 (dm_div_mod_decoded_canonical x y).
  exact (sub_imported_eq_trans _ _ _
    (sub_imported_eq_sym _ _
      (sub_nat_imported_roundtrip
        (dm_imported_mod (sub_nat_to_imported x) (sub_nat_to_imported y))))
    (coq_eq_to_imported_eq _ _ (f_equal sub_nat_to_imported Hdecoded))).
Qed.

Lemma dm_div_correspondence xR xL yR yL :
  SubNatRel xR xL -> SubNatRel yR yL ->
  SubNatRel (xR %/ yR) (dm_imported_div xL yL).
Proof.
  intros Hx Hy. unfold SubNatRel.
  exact (sub_imported_eq_trans _ _ _
    (sub_imported_eq_sym _ _ (dm_div_canonical xR yR))
    (sub_imported_eq_congr2 dm_imported_div _ _ _ _ Hx Hy)).
Qed.

Lemma dm_mod_correspondence xR xL yR yL :
  SubNatRel xR xL -> SubNatRel yR yL ->
  SubNatRel (xR %% yR) (dm_imported_mod xL yL).
Proof.
  intros Hx Hy. unfold SubNatRel.
  exact (sub_imported_eq_trans _ _ _
    (sub_imported_eq_sym _ _ (dm_mod_canonical xR yR))
    (sub_imported_eq_congr2 dm_imported_mod _ _ _ _ Hx Hy)).
Qed.

Lemma dm_dvd_correspondence xR xL yR yL :
  SubNatRel xR xL -> SubNatRel yR yL ->
  PropSPropRel (is_true (yR %| xR)) (dm_imported_dvd yL xL).
Proof.
  intros Hx Hy. apply prop_sprop_rel_intro.
  - intro HdvdR.
    apply (ImportedDivMod.Iff_mpr _ _
      (ImportedDivMod.Prosa_Validation_DivModInterface_production_dvd_iff_mod_eq_zero
        xL yL)).
    apply (prop_to_sprop _ _
      (dm_eq_correspondence (xR %% yR) (dm_imported_mod xL yL)
        O dm_imported_zero
        (dm_mod_correspondence xR xL yR yL Hx Hy)
        (sub_nat_rel_canonical O))).
    move: HdvdR. rewrite /dvdn. by move/eqP.
  - intro HdvdL. apply strictly_inhabits.
    rewrite /dvdn. apply/eqP.
    apply (sprop_to_prop _ _
      (dm_eq_correspondence (xR %% yR) (dm_imported_mod xL yL)
        O dm_imported_zero
        (dm_mod_correspondence xR xL yR yL Hx Hy)
        (sub_nat_rel_canonical O))).
    exact (ImportedDivMod.Iff_mp _ _
      (ImportedDivMod.Prosa_Validation_DivModInterface_production_dvd_iff_mod_eq_zero
        xL yL) HdvdL).
Qed.

Lemma dm_div_floor_correspondence xR xL yR yL :
  SubNatRel xR xL -> SubNatRel yR yL ->
  SubNatRel (xR %/ yR) (dm_imported_div_floor xL yL).
Proof.
  intros Hx Hy.
  change (SubNatRel (xR %/ yR) (dm_imported_div xL yL)).
  exact (dm_div_correspondence xR xL yR yL Hx Hy).
Qed.

Lemma dm_bool_false_no_truth (b : bool) :
  Logic.eq b false -> is_true b -> Logic.False.
Proof. destruct b; cbn; intros Hfalse Htruth; discriminate. Qed.

Definition dm_not_dvd_canonical (x y : nat)
    (Hfalse : Logic.eq (y %| x) false) :
    ImportedDivMod.Not
      (dm_imported_dvd (sub_nat_to_imported y) (sub_nat_to_imported x)) :=
  fun HdvdL =>
    dm_coq_false_to_target
      (dm_bool_false_no_truth (y %| x) Hfalse
        (sprop_to_prop _ _
        (dm_dvd_correspondence x (sub_nat_to_imported x)
          y (sub_nat_to_imported y)
          (sub_nat_rel_canonical x) (sub_nat_rel_canonical y)) HdvdL)).

Lemma dm_div_succ_canonical (x y : nat) :
  Lean.eq
    (dm_imported_add
      (dm_imported_div (sub_nat_to_imported x) (sub_nat_to_imported y))
      dm_imported_one)
    (sub_nat_to_imported ((x %/ y).+1)).
Proof.
  have Hrel := dm_add_correspondence
    (x %/ y) (dm_imported_div (sub_nat_to_imported x)
      (sub_nat_to_imported y))
    1 dm_imported_one
    (dm_div_correspondence x (sub_nat_to_imported x)
      y (sub_nat_to_imported y)
      (sub_nat_rel_canonical x) (sub_nat_rel_canonical y))
    (sub_nat_rel_canonical 1).
  unfold SubNatRel in Hrel.
  rewrite addn1 in Hrel.
  exact (sub_imported_eq_sym _ _ Hrel).
Qed.

Lemma dm_div_ceil_canonical (x y : nat) :
  Lean.eq
    (dm_imported_div_ceil (sub_nat_to_imported x) (sub_nat_to_imported y))
    (sub_nat_to_imported
      (if y %| x then x %/ y else (x %/ y).+1)).
Proof.
  have Hbody :=
    ImportedDivMod.Prosa_Validation_DivModInterface_production_div_ceil_eq
      (sub_nat_to_imported x) (sub_nat_to_imported y).
  destruct (y %| x) eqn:HdvdR.
  - have HdvdR' : is_true (y %| x) by rewrite HdvdR.
    have HdvdL := prop_to_sprop _ _
      (dm_dvd_correspondence x (sub_nat_to_imported x)
        y (sub_nat_to_imported y)
        (sub_nat_rel_canonical x) (sub_nat_rel_canonical y)) HdvdR'.
    have Hif := ImportedDivMod.if_pos
      (dm_imported_dvd (sub_nat_to_imported y) (sub_nat_to_imported x))
      (ImportedDivMod.Nat_decidable_dvd
        (sub_nat_to_imported y) (sub_nat_to_imported x)) HdvdL
      Lean.Nat
      (dm_imported_div (sub_nat_to_imported x) (sub_nat_to_imported y))
      (dm_imported_add
        (dm_imported_div (sub_nat_to_imported x) (sub_nat_to_imported y))
        dm_imported_one).
    exact (sub_imported_eq_trans _ _ _ Hbody
      (sub_imported_eq_trans _ _ _ Hif (dm_div_canonical x y))).
  - have Hif := ImportedDivMod.if_neg
      (dm_imported_dvd (sub_nat_to_imported y) (sub_nat_to_imported x))
      (ImportedDivMod.Nat_decidable_dvd
        (sub_nat_to_imported y) (sub_nat_to_imported x))
      (dm_not_dvd_canonical x y HdvdR)
      Lean.Nat
      (dm_imported_div (sub_nat_to_imported x) (sub_nat_to_imported y))
      (dm_imported_add
        (dm_imported_div (sub_nat_to_imported x) (sub_nat_to_imported y))
        dm_imported_one).
    exact (sub_imported_eq_trans _ _ _ Hbody
      (sub_imported_eq_trans _ _ _ Hif (dm_div_succ_canonical x y))).
Qed.

Lemma dm_div_ceil_correspondence xR xL yR yL :
  SubNatRel xR xL -> SubNatRel yR yL ->
  SubNatRel
    (if yR %| xR then xR %/ yR else (xR %/ yR).+1)
    (dm_imported_div_ceil xL yL).
Proof.
  intros Hx Hy. unfold SubNatRel.
  exact (sub_imported_eq_trans _ _ _
    (sub_imported_eq_sym _ _ (dm_div_ceil_canonical xR yR))
    (sub_imported_eq_congr2 dm_imported_div_ceil _ _ _ _ Hx Hy)).
Qed.

(** The imported target uses propositional [ite] for [Nat] order, whereas
    MathComp computes the corresponding branch with a Boolean test.  Keep
    the negative transport at top level: eliminating an imported [SProp]
    directly inside a local proof would violate Rocq's SProp restriction. *)
Definition dm_not_le_related (aR : nat) (aL : Lean.Nat)
    (bR : nat) (bL : Lean.Nat)
    (Ha : SubNatRel aR aL) (Hb : SubNatRel bR bL)
    (Hfalse : Logic.eq (leq aR bR) false) :
    ImportedDivMod.Not (dm_imported_le aL bL) :=
  fun HleL =>
    dm_coq_false_to_target
      (dm_bool_false_no_truth (leq aR bR) Hfalse
        (sprop_to_prop _ _
          (dm_le_correspondence aR aL bR bL Ha Hb) HleL)).

Lemma dm_mod_elim_rhs_canonical (a b c : nat) :
  Lean.eq
    (ImportedDivMod.ite Lean.Nat
      (dm_imported_le (sub_nat_to_imported b)
        (dm_imported_mod (sub_nat_to_imported a) (sub_nat_to_imported c)))
      (ImportedDivMod.Nat_decLe (sub_nat_to_imported b)
        (dm_imported_mod (sub_nat_to_imported a) (sub_nat_to_imported c)))
      (dm_imported_sub
        (dm_imported_mod (sub_nat_to_imported a) (sub_nat_to_imported c))
        (sub_nat_to_imported b))
      (dm_imported_sub
        (dm_imported_add
          (dm_imported_mod (sub_nat_to_imported a) (sub_nat_to_imported c))
          (sub_nat_to_imported c))
        (sub_nat_to_imported b)))
    (sub_nat_to_imported
      (if leq b (a %% c) then a %% c - b else a %% c + c - b)).
Proof.
  destruct (leq b (a %% c)) eqn:HleR.
  - have HleR' : is_true (leq b (a %% c)) by rewrite HleR.
    have HleL := prop_to_sprop _ _
      (dm_le_correspondence b (sub_nat_to_imported b)
        (a %% c)
        (dm_imported_mod (sub_nat_to_imported a) (sub_nat_to_imported c))
        (sub_nat_rel_canonical b)
        (dm_mod_correspondence a (sub_nat_to_imported a)
          c (sub_nat_to_imported c)
          (sub_nat_rel_canonical a) (sub_nat_rel_canonical c))) HleR'.
    have Hif := ImportedDivMod.if_pos
      (dm_imported_le (sub_nat_to_imported b)
        (dm_imported_mod (sub_nat_to_imported a) (sub_nat_to_imported c)))
      (ImportedDivMod.Nat_decLe (sub_nat_to_imported b)
        (dm_imported_mod (sub_nat_to_imported a) (sub_nat_to_imported c)))
      HleL Lean.Nat
      (dm_imported_sub
        (dm_imported_mod (sub_nat_to_imported a) (sub_nat_to_imported c))
        (sub_nat_to_imported b))
      (dm_imported_sub
        (dm_imported_add
          (dm_imported_mod (sub_nat_to_imported a) (sub_nat_to_imported c))
          (sub_nat_to_imported c))
        (sub_nat_to_imported b)).
    exact (sub_imported_eq_trans _ _ _ Hif
      (sub_imported_eq_sym _ _
        (dm_sub_correspondence (a %% c)
          (dm_imported_mod (sub_nat_to_imported a) (sub_nat_to_imported c))
          b (sub_nat_to_imported b)
          (dm_mod_correspondence a (sub_nat_to_imported a)
            c (sub_nat_to_imported c)
            (sub_nat_rel_canonical a) (sub_nat_rel_canonical c))
          (sub_nat_rel_canonical b)))).
  - have Hif := ImportedDivMod.if_neg
      (dm_imported_le (sub_nat_to_imported b)
        (dm_imported_mod (sub_nat_to_imported a) (sub_nat_to_imported c)))
      (ImportedDivMod.Nat_decLe (sub_nat_to_imported b)
        (dm_imported_mod (sub_nat_to_imported a) (sub_nat_to_imported c)))
      (dm_not_le_related b (sub_nat_to_imported b)
        (a %% c)
        (dm_imported_mod (sub_nat_to_imported a) (sub_nat_to_imported c))
        (sub_nat_rel_canonical b)
        (dm_mod_correspondence a (sub_nat_to_imported a)
          c (sub_nat_to_imported c)
          (sub_nat_rel_canonical a) (sub_nat_rel_canonical c)) HleR)
      Lean.Nat
      (dm_imported_sub
        (dm_imported_mod (sub_nat_to_imported a) (sub_nat_to_imported c))
        (sub_nat_to_imported b))
      (dm_imported_sub
        (dm_imported_add
          (dm_imported_mod (sub_nat_to_imported a) (sub_nat_to_imported c))
          (sub_nat_to_imported c))
        (sub_nat_to_imported b)).
    exact (sub_imported_eq_trans _ _ _ Hif
      (sub_imported_eq_sym _ _
        (dm_sub_correspondence (a %% c + c)
          (dm_imported_add
            (dm_imported_mod (sub_nat_to_imported a) (sub_nat_to_imported c))
            (sub_nat_to_imported c))
          b (sub_nat_to_imported b)
          (dm_add_correspondence (a %% c)
            (dm_imported_mod (sub_nat_to_imported a) (sub_nat_to_imported c))
            c (sub_nat_to_imported c)
            (dm_mod_correspondence a (sub_nat_to_imported a)
              c (sub_nat_to_imported c)
              (sub_nat_rel_canonical a) (sub_nat_rel_canonical c))
            (sub_nat_rel_canonical c))
          (sub_nat_rel_canonical b)))).
Qed.

Print Assumptions dm_div_mod_decoded_canonical.
Print Assumptions dm_div_canonical.
Print Assumptions dm_mod_canonical.
Print Assumptions dm_div_correspondence.
Print Assumptions dm_mod_correspondence.
Print Assumptions dm_dvd_correspondence.
Print Assumptions dm_div_floor_correspondence.
Print Assumptions dm_div_ceil_canonical.
Print Assumptions dm_div_ceil_correspondence.
Print Assumptions dm_sub_correspondence.
Print Assumptions dm_le_correspondence.
Print Assumptions dm_succ_correspondence.
Print Assumptions dm_mod_elim_rhs_canonical.
