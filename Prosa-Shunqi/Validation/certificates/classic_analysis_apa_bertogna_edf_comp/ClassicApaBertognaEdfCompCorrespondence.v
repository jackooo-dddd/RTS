From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq path fintype bigop div.
From prosa Require Import util.seqset util.div_mod classic.model.time classic.util.notation classic.model.arrival.basic.arrival_sequence classic.model.arrival.basic.task classic.model.arrival.basic.job classic.model.arrival.basic.task_arrival classic.model.priority classic.model.schedule.global.basic.schedule classic.model.schedule.global.response_time classic.model.schedule.apa.affinity classic.model.schedule.apa.interference classic.model.schedule.apa.platform classic.analysis.apa.workload_bound classic.analysis.apa.interference_bound classic.model.schedule.apa.interference_edf classic.analysis.apa.interference_bound_edf classic.analysis.apa.bertogna_edf_theory classic.model.schedule.global.schedulability classic.analysis.apa.bertogna_edf_comp.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedClassicApaBertognaEdfComp.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence ClassicApaBertognaEdfCompBase ClassicApaBertognaEdfCompList ClassicApaBertognaEdfCompOrd ClassicApaBertognaEdfCompList1.



Module I := ImportedClassicApaBertognaEdfComp.
Local Open Scope nat_scope.

(** Certificates for [classic/analysis/apa/bertogna_edf_comp.v] (ProsaBuddy classic, commit f692cb7).

    Inputs, relations and computation as in the accepted classic APA bertogna_fp_theory certificate (re-stated below for
    this export: affinities through the ordinal conversion, task affinities pointwise, APA interference and platform),
    with the stable-sort and EDF-priority sections of the accepted global basic interference_bound_edf certificate and the
    APA EDF definitions related below.  Each statement is proved by the relation search [crel]. *)

Ltac type_of_term t := let T := type of t in exact T.
Notation cid := (fun z => z).

(* ------------------------------------------------------------------ *)
(** * Helpers (re-bound to this export from the accepted classic certificates) *)

(* ------------------------------------------------------------------ *)
(** * Nat subtraction / Euclidean division bridge (re-bound copy of the accepted NatSubCorrespondence and
    DivModCorrespondence, through the exported [DivModInterface] equations) *)

(** Adapter for the operations that occur in the actual freshly imported
    [Prosa.Util.Nat] theorem types. *)
Definition nat_target_add (a b : Lean.Nat) : Lean.Nat :=
  I.HAdd_hAdd_inst7 Lean.Nat Lean.Nat Lean.Nat
    (I.instHAdd_inst1 Lean.Nat I.instAddNat) a b.

Definition nat_target_sub (a b : Lean.Nat) : Lean.Nat :=
  I.HSub_hSub_inst7 Lean.Nat Lean.Nat Lean.Nat
    (I.instHSub_inst1 Lean.Nat I.instSubNat) a b.

Definition nat_target_le (a b : Lean.Nat) : SProp :=
  I.LE_le_inst1 Lean.Nat I.instLENat a b.

Lemma nat_target_add_correspondence aR aL bR bL :
  SubNatRel aR aL -> SubNatRel bR bL ->
  SubNatRel (aR + bR) (nat_target_add aL bL).
Proof.
  intros Ha Hb. exact (sub_add_correspondence aR aL bR bL Ha Hb).
Qed.

Lemma nat_target_le_correspondence aR aL bR bL :
  SubNatRel aR aL -> SubNatRel bR bL ->
  PropSPropRel (is_true (leq aR bR)) (nat_target_le aL bL).
Proof.
  intros Ha Hb. exact (sub_nat_le_correspondence aR aL bR bL Ha Hb).
Qed.

(** The actual compiled Lean subtraction is a course-of-values recursion on
    the amount being subtracted.  Its two computation equations are
    definitionally true in the imported artifact. *)
Lemma nat_target_sub_zero (a : Lean.Nat) :
  Lean.eq (nat_target_sub a Lean.Nat_zero) a.
Proof. exact (@Lean.eq_refl Lean.Nat a). Qed.

Lemma nat_target_sub_succ (a b : Lean.Nat) :
  Lean.eq (nat_target_sub a (Lean.Nat_succ b))
    (I.Nat_pred (nat_target_sub a b)).
Proof.
  exact (@Lean.eq_refl Lean.Nat
    (I.Nat_pred (nat_target_sub a b))).
Qed.

Fixpoint rocq_iterated_pred (a b : nat) : nat :=
  match b with
  | O => a
  | S b' => Nat.pred (rocq_iterated_pred a b')
  end.

Lemma rocq_iterated_pred_is_subn (a b : nat) :
  Logic.eq (rocq_iterated_pred a b) (a - b).
Proof.
  revert a. induction b as [|b IH]; intro a; cbn [rocq_iterated_pred].
  - rewrite subn0. reflexivity.
  - rewrite (IH a). exact (Logic.eq_sym (subnS a b)).
Qed.

Definition nat_target_pred_canonical (n : nat) :
  Lean.eq (I.Nat_pred (sub_nat_to_imported n))
    (sub_nat_to_imported (Nat.pred n)) :=
  match n return
    Lean.eq (I.Nat_pred (sub_nat_to_imported n))
      (sub_nat_to_imported (Nat.pred n))
  with
  | O => @Lean.eq_refl Lean.Nat Lean.Nat_zero
  | S n' => @Lean.eq_refl Lean.Nat (sub_nat_to_imported n')
  end.

Lemma nat_target_sub_iterated_pred (a b : nat) :
  Lean.eq
    (nat_target_sub (sub_nat_to_imported a) (sub_nat_to_imported b))
    (sub_nat_to_imported (rocq_iterated_pred a b)).
Proof.
  induction b as [|b IH].
  - exact (nat_target_sub_zero (sub_nat_to_imported a)).
  - exact (sub_imported_eq_trans _ _ _
      (nat_target_sub_succ _ _)
      (sub_imported_eq_trans _ _ _
        (sub_imported_eq_congr I.Nat_pred _ _ IH)
        (nat_target_pred_canonical (rocq_iterated_pred a b)))).
Qed.

(** Direct computation proof for truncated subtraction.  This covers both
    branches: a positive residual and truncation to zero. *)
Lemma nat_target_sub_canonical (a b : nat) :
  Lean.eq
    (nat_target_sub (sub_nat_to_imported a) (sub_nat_to_imported b))
    (sub_nat_to_imported (a - b)).
Proof.
  exact (sub_imported_eq_trans _ _ _
    (nat_target_sub_iterated_pred a b)
    (coq_eq_to_imported_eq _ _
      (f_equal sub_nat_to_imported (rocq_iterated_pred_is_subn a b)))).
Qed.

Lemma nat_target_sub_correspondence aR aL bR bL :
  SubNatRel aR aL -> SubNatRel bR bL ->
  SubNatRel (aR - bR) (nat_target_sub aL bL).
Proof.
  intros Ha Hb. unfold SubNatRel.
  exact (sub_imported_eq_trans _ _ _
    (sub_imported_eq_sym _ _ (nat_target_sub_canonical aR bR))
    (sub_imported_eq_congr2 nat_target_sub _ _ _ _ Ha Hb)).
Qed.

(** Explicit branch witnesses requested by the translation policy. *)
Lemma nat_target_sub_nontruncated a b :
  is_true (leq b a) ->
  SubNatRel (a - b)
    (nat_target_sub (sub_nat_to_imported a) (sub_nat_to_imported b)).
Proof. intros _. apply nat_target_sub_correspondence; apply sub_nat_rel_canonical. Qed.

Lemma rocq_sub_truncates a b :
  is_true (ltn a b) -> Logic.eq (a - b) O.
Proof.
  move: a. elim: b => [|b IH] [|a] //= H. exact: IH.
Qed.

Lemma nat_target_sub_truncated a b :
  is_true (ltn a b) ->
  SubNatRel O
    (nat_target_sub (sub_nat_to_imported a) (sub_nat_to_imported b)).
Proof.
  intro Hlt. have Hz : Logic.eq (a - b) O := rocq_sub_truncates a b Hlt.
  rewrite <- Hz. apply nat_target_sub_correspondence; apply sub_nat_rel_canonical.
Qed.

(** Operation-level bridge for the exact [Nat.div]/[Nat.mod] interface
    exported from the compiled [Prosa.Util.Div_mod] artifact.  The proof uses
    the two Euclidean characterizations on each side; it does not unfold the
    implementation-specific Lean [Nat.brecOn]/[Nat.below] recursion. *)

Definition dm_imported_add (a b : Lean.Nat) : Lean.Nat :=
  I.HAdd_hAdd_inst7 Lean.Nat Lean.Nat Lean.Nat
    (I.instHAdd_inst1 Lean.Nat I.instAddNat) a b.

Definition dm_imported_mul (a b : Lean.Nat) : Lean.Nat :=
  I.HMul_hMul_inst7 Lean.Nat Lean.Nat Lean.Nat
    (I.instHMul_inst1 Lean.Nat I.instMulNat) a b.

Definition dm_imported_div (a b : Lean.Nat) : Lean.Nat :=
  I.HDiv_hDiv_inst7 Lean.Nat Lean.Nat Lean.Nat
    (I.instHDiv_inst1 Lean.Nat I.Nat_instDiv) a b.

Definition dm_imported_sub (a b : Lean.Nat) : Lean.Nat :=
  I.HSub_hSub_inst7 Lean.Nat Lean.Nat Lean.Nat
    (I.instHSub_inst1 Lean.Nat I.instSubNat) a b.

Definition dm_imported_mod (a b : Lean.Nat) : Lean.Nat :=
  I.HMod_hMod_inst7 Lean.Nat Lean.Nat Lean.Nat
    (I.instHMod_inst1 Lean.Nat I.Nat_instMod) a b.

Definition dm_imported_lt (a b : Lean.Nat) : SProp :=
  I.LT_lt_inst1 Lean.Nat I.instLTNat a b.

Definition dm_imported_le (a b : Lean.Nat) : SProp :=
  I.LE_le_inst1 Lean.Nat I.instLENat a b.

Definition dm_imported_dvd (a b : Lean.Nat) : SProp :=
  I.Dvd_dvd_inst1 Lean.Nat I.Nat_instDvd a b.

Definition dm_imported_zero : Lean.Nat :=
  I.OfNat_ofNat_inst1 Lean.Nat Lean.Nat_zero
    (I.instOfNatNat Lean.Nat_zero).

Definition dm_imported_one : Lean.Nat :=
  I.OfNat_ofNat_inst1 Lean.Nat
    (Lean.Nat_succ Lean.Nat_zero)
    (I.instOfNatNat (Lean.Nat_succ Lean.Nat_zero)).

Definition dm_imported_div_floor (a b : Lean.Nat) : Lean.Nat :=
  I.Prosa_Classic_Util_DivMod_div_floor a b.

Definition dm_imported_div_ceil (a b : Lean.Nat) : Lean.Nat :=
  I.Prosa_Classic_Util_DivMod_div_ceil a b.

Definition dm_coq_false_to_target (H : Logic.False) :
    I.False :=
  match H return I.False with end.

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
    (I.Nat_pred (dm_imported_sub a b)).
Proof.
  exact (@Lean.eq_refl Lean.Nat
    (I.Nat_pred (dm_imported_sub a b))).
Qed.

Definition dm_pred_canonical (n : nat) :
  Lean.eq (I.Nat_pred (sub_nat_to_imported n))
    (sub_nat_to_imported (Nat.pred n)) :=
  match n return
    Lean.eq (I.Nat_pred (sub_nat_to_imported n))
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
        (sub_imported_eq_congr I.Nat_pred _ _ (IH a))
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
        I.Prosa_Validation_DivModInterface_production_div_zero
          (sub_nat_to_imported x).
      exact (f_equal sub_nat_to_rocq
        (imported_eq_to_coq_eq _ _ H)).
    + rewrite modn0.
      have H :=
        I.Prosa_Validation_DivModInterface_production_mod_zero
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
        (I.Prosa_Validation_DivModInterface_production_mod_lt
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
        (I.Prosa_Validation_DivModInterface_production_div_add_mod
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
    apply (I.Iff_mpr _ _
      (I.Prosa_Validation_DivModInterface_production_dvd_iff_mod_eq_zero
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
    exact (I.Iff_mp _ _
      (I.Prosa_Validation_DivModInterface_production_dvd_iff_mod_eq_zero
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
    I.Not
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
    I.Prosa_Validation_DivModInterface_production_div_ceil_eq
      (sub_nat_to_imported x) (sub_nat_to_imported y).
  destruct (y %| x) eqn:HdvdR.
  - have HdvdR' : is_true (y %| x) by rewrite HdvdR.
    have HdvdL := prop_to_sprop _ _
      (dm_dvd_correspondence x (sub_nat_to_imported x)
        y (sub_nat_to_imported y)
        (sub_nat_rel_canonical x) (sub_nat_rel_canonical y)) HdvdR'.
    have Hif := I.if_pos
      (dm_imported_dvd (sub_nat_to_imported y) (sub_nat_to_imported x))
      (I.Nat_decidable_dvd
        (sub_nat_to_imported y) (sub_nat_to_imported x)) HdvdL
      Lean.Nat
      (dm_imported_div (sub_nat_to_imported x) (sub_nat_to_imported y))
      (dm_imported_add
        (dm_imported_div (sub_nat_to_imported x) (sub_nat_to_imported y))
        dm_imported_one).
    exact (sub_imported_eq_trans _ _ _ Hbody
      (sub_imported_eq_trans _ _ _ Hif (dm_div_canonical x y))).
  - have Hif := I.if_neg
      (dm_imported_dvd (sub_nat_to_imported y) (sub_nat_to_imported x))
      (I.Nat_decidable_dvd
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
    I.Not (dm_imported_le aL bL) :=
  fun HleL =>
    dm_coq_false_to_target
      (dm_bool_false_no_truth (leq aR bR) Hfalse
        (sprop_to_prop _ _
          (dm_le_correspondence aR aL bR bL Ha Hb) HleL)).

Lemma dm_mod_elim_rhs_canonical (a b c : nat) :
  Lean.eq
    (I.ite Lean.Nat
      (dm_imported_le (sub_nat_to_imported b)
        (dm_imported_mod (sub_nat_to_imported a) (sub_nat_to_imported c)))
      (I.Nat_decLe (sub_nat_to_imported b)
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
    have Hif := I.if_pos
      (dm_imported_le (sub_nat_to_imported b)
        (dm_imported_mod (sub_nat_to_imported a) (sub_nat_to_imported c)))
      (I.Nat_decLe (sub_nat_to_imported b)
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
  - have Hif := I.if_neg
      (dm_imported_le (sub_nat_to_imported b)
        (dm_imported_mod (sub_nat_to_imported a) (sub_nat_to_imported c)))
      (I.Nat_decLe (sub_nat_to_imported b)
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

(** [min] on [Nat] through [instMinNat] (this export elaborates [min] via the [Min] instance). *)
Lemma cib_min_canonical (a b : nat) :
  Logic.eq ((I.Min_min_inst1 Lean.Nat I.instMinNat) (sub_nat_to_imported a) (sub_nat_to_imported b)) (sub_nat_to_imported (minn a b)).
Proof.
  have Hle := sub_nat_le_correspondence _ _ _ _ (sub_nat_rel_canonical a) (sub_nat_rel_canonical b).
  have -> : Logic.eq ((I.Min_min_inst1 Lean.Nat I.instMinNat) (sub_nat_to_imported a) (sub_nat_to_imported b))
      (I.ite Lean.Nat (I.LE_le_inst1 Lean.Nat I.instLENat (sub_nat_to_imported a) (sub_nat_to_imported b))
         (I.Nat_decLe (sub_nat_to_imported a) (sub_nat_to_imported b)) (sub_nat_to_imported a) (sub_nat_to_imported b))
    by reflexivity.
  destruct (I.Nat_decLe (sub_nat_to_imported a) (sub_nat_to_imported b)) as [h|h].
  - have Hab : ~~ (a <= b)%nat.
    { apply/negP => Hs. exact (interpret_strict _ (ct_target_false_to_strict (h (prop_to_sprop _ _ Hle Hs)))). }
    rewrite -ltnNge in Hab. rewrite (minn_idPr (ltnW Hab)). reflexivity.
  - have Hab : (a <= b)%nat := sprop_to_prop _ _ Hle h. rewrite (minn_idPl Hab). reflexivity.
Qed.

Lemma cib_min_rel aR aL bR bL : SubNatRel aR aL -> SubNatRel bR bL -> SubNatRel (minn aR bR) ((I.Min_min_inst1 Lean.Nat I.instMinNat) aL bL).
Proof.
  intros Ha Hb. rewrite -(imported_eq_to_coq_eq _ _ Ha) -(imported_eq_to_coq_eq _ _ Hb).
  apply: coq_eq_to_imported_eq. exact (Logic.eq_sym (cib_min_canonical aR bR)).
Qed.

Lemma cs_forall_cover (A B : Type) (Rel : A -> B -> SProp) (toB : A -> B) (toA : B -> A)
    (HB : forall a, Rel a (toB a)) (HA : forall b, Rel (toA b) b) (PR : A -> Prop) (PL : B -> SProp) :
  (forall a b, Rel a b -> PropSPropRel (PR a) (PL b)) -> PropSPropRel (forall a, PR a) (forall b, PL b).
Proof.
  intro H. apply prop_sprop_rel_intro.
  - intros HR b. exact (prop_to_sprop _ _ (H _ _ (HA b)) (HR _)).
  - intro HL. apply strictly_inhabits. intro a. exact (sprop_to_prop _ _ (H _ _ (HB a)) (HL _)).
Qed.

Lemma cs_mem (T : eqType) x s sL : ClListRel cid s sL ->
  PropSPropRel (x \in s) (I.Membership_mem T (I.List T) (I.List_instMembership T) sL x).
Proof. exact (cl_mem_rel_list T T cid cid (fun _ => Logic.eq_refl _) x s sL). Qed.

Lemma cs_uniq (T : eqType) s sL : ClListRel cid s sL -> PropSPropRel (uniq s) (I.List_Nodup T sL).
Proof. exact (cl_uniq_rel_list T T cid cid (fun _ => Logic.eq_refl _) (fun _ => Logic.eq_refl _) s sL). Qed.

Lemma cs_list_size (T : Type) s sL : ClListRel (B := T) cid s sL -> SubNatRel (size s) (I.List_length T sL).
Proof. intro H. destruct H. exact (cl_size cid s). Qed.

Lemma cs_lean_eq_logic (A : Type) (x y : A) : Lean.eq x y -> Logic.eq x y.
Proof. exact (imported_eq_to_coq_eq x y). Qed.

Definition cs_tr {A : Type} {x y : A} (E : Lean.eq x y) (P : A -> Type) (h : P x) : P y :=
  match E in Lean.eq _ z return P z with Lean.eq_refl => h end.

Definition cs_trs {A : Type} {x y : A} (E : Lean.eq x y) (P : A -> SProp) (h : P x) : P y :=
  match E in Lean.eq _ z return P z with Lean.eq_refl => h end.

Lemma cs_opt_inj (A : Type) (o1 o2 : option A) : Logic.eq (cl_opt o1) (cl_opt o2) -> Logic.eq o1 o2.
Proof. intro E. by rewrite -(cl_unopt_opt o1) -(cl_unopt_opt o2) E. Qed.

Lemma cs_opt_eq_rel (A : Type) (o1 o2 : option A) :
  PropSPropRel (Logic.eq o1 o2) (Lean.eq (cl_opt o1) (cl_opt o2)).
Proof.
  apply prop_sprop_rel_intro.
  - intro E. rewrite E. exact (@Lean.eq_refl _ _).
  - intro E. apply strictly_inhabits. exact (cs_opt_inj A o1 o2 (imported_eq_to_coq_eq _ _ E)).
Qed.

Lemma cs_opt_eqb_rel (A : eqType) (o1 o2 : option A) :
  PropSPropRel (is_true (o1 == o2)) (Lean.eq (cl_opt o1) (cl_opt o2)).
Proof.
  apply prop_sprop_rel_intro.
  - move=> /eqP E. rewrite E. exact (@Lean.eq_refl _ _).
  - intro E. apply strictly_inhabits. apply/eqP. exact (cs_opt_inj A o1 o2 (imported_eq_to_coq_eq _ _ E)).
Qed.

Fixpoint cs_natl (s : seq nat) : I.List_inst1 Lean.Nat :=
  match s with [::] => I.List_nil_inst1 _ | x :: s' => I.List_cons_inst1 _ (sub_nat_to_imported x) (cs_natl s') end.

Lemma cs_iota_range : forall n s,
  Logic.eq (I.List_range' (sub_nat_to_imported s) (sub_nat_to_imported n) (Lean.Nat_succ Lean.Nat_zero)) (cs_natl (iota s n)).
Proof.
  elim => [|n IH] s; first reflexivity.
  change (Logic.eq (I.List_cons_inst1 _ (sub_nat_to_imported s)
      (I.List_range' (sub_nat_to_imported (S s)) (sub_nat_to_imported n) (Lean.Nat_succ Lean.Nat_zero)))
    (I.List_cons_inst1 _ (sub_nat_to_imported s) (cs_natl (iota (S s) n)))).
  by rewrite IH.
Qed.

Lemma cs_foldr_add (f : Lean.Nat -> Lean.Nat) (g : nat -> nat) (Hf : forall k, Logic.eq (f (sub_nat_to_imported k)) (sub_nat_to_imported (g k))) :
  forall s, Logic.eq (I.List_foldr_inst3 Lean.Nat Lean.Nat Lean.Nat_add Lean.Nat_zero (I.List_map_inst3 Lean.Nat Lean.Nat f (cs_natl s)))
                     (sub_nat_to_imported (foldr addn 0 (map g s))).
Proof.
  elim => [|k s IH] //=.
  change (Logic.eq (Lean.Nat_add (f (sub_nat_to_imported k))
            (I.List_foldr_inst3 Lean.Nat Lean.Nat Lean.Nat_add Lean.Nat_zero (I.List_map_inst3 Lean.Nat Lean.Nat f (cs_natl s))))
         (sub_nat_to_imported (g k + foldr addn 0 (map g s)))).
  rewrite IH Hf. exact (imported_eq_to_coq_eq _ _ (sub_add_canonical _ _)).
Qed.

Lemma cs_big_fold (xs : seq nat) (F : nat -> nat) : Logic.eq (\sum_(i <- xs) F i) (foldr addn 0 (map F xs)).
Proof. elim: xs => [|x xs IH]; first by rewrite big_nil. by rewrite big_cons IH. Qed.

Definition CsFunRel (FR : nat -> nat) (FL : Lean.Nat -> Lean.Nat) : SProp :=
  forall kR kL, SubNatRel kR kL -> SubNatRel (FR kR) (FL kL).

Lemma cs_fun_canonical FR FL (HF : CsFunRel FR FL) k : Logic.eq (FL (sub_nat_to_imported k)) (sub_nat_to_imported (FR k)).
Proof. exact (co_nat_logic _ _ (HF _ _ (sub_nat_rel_canonical k))). Qed.

Lemma cs_ico mR mL nR nL FR FL (Hm : SubNatRel mR mL) (Hn : SubNatRel nR nL) (HF : CsFunRel FR FL) :
  SubNatRel (\sum_(mR <= i < nR) FR i)
    (I.List_foldr_inst3 Lean.Nat Lean.Nat Lean.Nat_add Lean.Nat_zero
       (I.List_map_inst3 Lean.Nat Lean.Nat FL (I.List_range' mL (I.Nat_sub nL mL) (Lean.Nat_succ Lean.Nat_zero)))).
Proof.
  rewrite (co_nat_logic _ _ Hm) (co_nat_logic _ _ Hn).
  have -> : Logic.eq (I.Nat_sub (sub_nat_to_imported nR) (sub_nat_to_imported mR)) (sub_nat_to_imported (nR - mR))
    := ct_sub_canonical nR mR.
  rewrite cs_iota_range.
  apply: coq_eq_to_imported_eq. apply: Logic.eq_sym. rewrite (cs_foldr_add FL FR (cs_fun_canonical FR FL HF)).
  by rewrite cs_big_fold.
Qed.

Definition CsParRel (T : Type) (pR : T -> nat) (pL : T -> Lean.Nat) : SProp := forall x, SubNatRel (pR x) (pL x).

Lemma cs_forall_par (T : Type) (PR : (T -> nat) -> Prop) (PL : (T -> Lean.Nat) -> SProp) :
  (forall pR pL, CsParRel T pR pL -> PropSPropRel (PR pR) (PL pL)) -> PropSPropRel (forall p, PR p) (forall p, PL p).
Proof.
  exact (cs_forall_cover _ _ (CsParRel T) (fun pR j => sub_nat_to_imported (pR j)) (fun pL j => sub_nat_to_rocq (pL j))
           (fun pR j => sub_nat_rel_canonical (pR j)) (fun pL j => sub_nat_rel_surjective (pL j)) PR PL).
Qed.

Section Sched.
Variables (Job : eqType) (nR : nat) (nL : Lean.Nat).
Hypothesis Hn : SubNatRel nR nL.
Notation dJ := (ct_decidable_eq Job).
Notation LSched := (I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_schedule Job dJ nL).

Definition CsSchedRel (sR : Schedule.schedule Job nR) (sL : LSched) : SProp :=
  forall oR oL, CoOrdRel nR nL oR oL -> forall tR tL, SubNatRel tR tL -> Lean.eq (cl_opt (sR oR tR)) (sL oL tL).

Definition cs_sched_to_target (sR : Schedule.schedule Job nR) : LSched :=
  fun oL tL => cl_opt (sR (co_fin_to_ord nR nL Hn oL) (sub_nat_to_rocq tL)).

Definition cs_sched_to_source (sL : LSched) : Schedule.schedule Job nR :=
  fun oR tR => cl_unopt (sL (co_ord_to_fin nR nL Hn oR) (sub_nat_to_imported tR)).

Lemma cs_sched_canonical sR : CsSchedRel sR (cs_sched_to_target sR).
Proof.
  intros oR oL Ho tR tL Ht. apply: coq_eq_to_imported_eq. rewrite /cs_sched_to_target (co_nat_input _ _ Ht).
  by rewrite (co_ord_eq _ _ _ _ _ Ho (co_ord_surjective nR nL Hn oL)).
Qed.

Lemma cs_sched_surjective sL : CsSchedRel (cs_sched_to_source sL) sL.
Proof.
  intros oR oL Ho tR tL Ht. apply: coq_eq_to_imported_eq. rewrite /cs_sched_to_source cl_opt_unopt.
  rewrite (co_nat_logic _ _ Ht). by rewrite (co_fin_rel_eq _ _ _ _ _ (co_ord_canonical nR nL Hn oR) Ho).
Qed.

Lemma cs_forall_sched (PR : Schedule.schedule Job nR -> Prop) (PL : LSched -> SProp) :
  (forall sR sL, CsSchedRel sR sL -> PropSPropRel (PR sR) (PL sL)) -> PropSPropRel (forall s, PR s) (forall s, PL s).
Proof. exact (cs_forall_cover _ _ CsSchedRel cs_sched_to_target cs_sched_to_source cs_sched_canonical cs_sched_surjective PR PL). Qed.

End Sched.

Section Arr.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).
Notation LArr := (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrival_sequence Job dJ).

Definition CsArrRel (aR : ArrivalSequence.arrival_sequence Job) (aL : LArr) : SProp :=
  forall tR tL, SubNatRel tR tL -> ClListRel cid (aR tR) (aL tL).

Definition cs_arr_to_target (aR : ArrivalSequence.arrival_sequence Job) : LArr :=
  fun tL => cl_map cid (aR (sub_nat_to_rocq tL)).

Definition cs_arr_to_source (aL : LArr) : ArrivalSequence.arrival_sequence Job :=
  fun tR => cl_unmap cid (aL (sub_nat_to_imported tR)).

Lemma cs_arr_canonical aR : CsArrRel aR (cs_arr_to_target aR).
Proof.
  intros tR tL Ht. have E := co_nat_logic _ _ Ht. subst tL.
  apply: coq_eq_to_imported_eq. rewrite /cs_arr_to_target sub_nat_rocq_roundtrip. reflexivity.
Qed.

Lemma cs_arr_surjective aL : CsArrRel (cs_arr_to_source aL) aL.
Proof.
  intros tR tL Ht. have E := co_nat_logic _ _ Ht. subst tL.
  apply: coq_eq_to_imported_eq. exact (cl_map_unmap cid cid (fun _ => Logic.eq_refl _) _).
Qed.

Lemma cs_arrives_in aR aL (Ha : CsArrRel aR aL) j :
  PropSPropRel (ArrivalSequence.arrives_in aR j)
    (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrives_in Job dJ aL j).
Proof. apply: ct_exists_nat => tR tL Ht. exact (cs_mem Job j _ _ (Ha tR tL Ht)). Qed.

End Arr.

Lemma cs_map_natl {B : Type} (f : Lean.Nat -> B) : forall s,
  Logic.eq (I.List_map_inst1 Lean.Nat B f (cs_natl s)) (cl_map (fun k => f (sub_nat_to_imported k)) s).
Proof.
  elim => [|k s IH] //=.
  change (Logic.eq (I.List_cons B (f (sub_nat_to_imported k)) (I.List_map_inst1 Lean.Nat B f (cs_natl s)))
                   (I.List_cons B (f (sub_nat_to_imported k)) (cl_map (fun k => f (sub_nat_to_imported k)) s))).
  by rewrite IH.
Qed.

Lemma cs_big_seq {A : Type} (F : nat -> seq A) : forall s : seq nat,
  Logic.eq (\big[cat/[::]]_(i <- s) F i) (flatten (map F s)).
Proof. elim => [|x s IH]; first by rewrite big_nil. by rewrite big_cons IH. Qed.

Section Defs.
Variables (Job : eqType) (nR : nat) (nL : Lean.Nat).
Hypothesis Hn : SubNatRel nR nL.
Notation dJ := (ct_decidable_eq Job).
Variables (sR : Schedule.schedule Job nR)
  (sL : I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_schedule Job dJ nL).
Hypothesis Hs : CsSchedRel Job nR nL sR sL.

Lemma cf_Schedule_scheduled_on j oR oL (Ho : CoOrdRel nR nL oR oL) tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (Schedule.scheduled_on sR j oR tR)
    (I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_scheduled_on Job dJ nL sL j oL tL).
Proof.
  apply: ct_decide_bool.
  exact (cs_tr (Hs oR oL Ho tR tL Ht) (fun z => PropSPropRel (sR oR tR == Some j) (Lean.eq z (cl_opt (Some j))))
           (cs_opt_eqb_rel Job (sR oR tR) (Some j))).
Qed.

Lemma cf_Schedule_scheduled j tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (Schedule.scheduled sR j tR)
    (I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_scheduled Job dJ nL sL j tL).
Proof.
  apply: (co_exists_rel nR nL Hn). intros oR oL Ho. exact (cf_Schedule_scheduled_on j oR oL Ho tR tL Ht).
Qed.

Lemma cf_Schedule_service_at j tR tL (Ht : SubNatRel tR tL) :
  SubNatRel (Schedule.service_at sR j tR)
    (I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_service_at Job dJ nL sL j tL).
Proof.
  apply: coq_eq_to_imported_eq.
  rewrite (imported_eq_to_coq_eq _ _ (I.Prosa_Validation_ClassicApaBertognaEdfCompInterface_service_at_sum Job dJ nL sL j tL)).
  apply: imported_eq_to_coq_eq.
  rewrite /Schedule.service_at big_mkcond /=.
  apply: (co_sum_rel nR nL Hn). intros oR oL Ho.
  have H := cf_Schedule_scheduled_on j oR oL Ho tR tL Ht.
  rewrite (ct_bool_rel_logic _ _ H). destruct (Schedule.scheduled_on sR j oR tR).
  - exact (sub_nat_rel_canonical 1).
  - exact (sub_nat_rel_canonical 0).
Qed.

Lemma cs_service_at_fun j : CsFunRel (fun t => Schedule.service_at sR j t)
    (fun t => I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_service_at Job dJ nL sL j t).
Proof. intros kR kL Hk. exact (cf_Schedule_service_at j kR kL Hk). Qed.

Lemma cf_Schedule_service j tR tL (Ht : SubNatRel tR tL) :
  SubNatRel (Schedule.service sR j tR)
    (I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_service Job dJ nL sL j tL).
Proof. exact (cs_ico 0 _ tR tL _ _ (sub_nat_rel_canonical 0) Ht (cs_service_at_fun j)). Qed.

Lemma cf_Schedule_completed cR cL (Hc : CsParRel Job cR cL) j tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (Schedule.completed cR sR j tR)
    (I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_completed Job dJ cL nL sL j tL).
Proof. exact (ct_decide_le _ _ _ _ (Hc j) (cf_Schedule_service j tR tL Ht)). Qed.

Lemma cf_Schedule_pending aR aL (Ha : CsParRel Job aR aL) cR cL (Hc : CsParRel Job cR cL) j tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (Schedule.pending aR cR sR j tR)
    (I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_pending Job dJ aL cL nL sL j tL).
Proof.
  exact (ct_bool_and _ _ _ _ (ct_decide_le _ _ _ _ (Ha j) Ht)
           (ct_bool_not _ _ (cf_Schedule_completed cR cL Hc j tR tL Ht))).
Qed.

Lemma cf_Schedule_backlogged aR aL (Ha : CsParRel Job aR aL) cR cL (Hc : CsParRel Job cR cL) j tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (Schedule.backlogged aR cR sR j tR)
    (I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_backlogged Job dJ aL cL nL sL j tL).
Proof.
  exact (ct_bool_and _ _ _ _ (cf_Schedule_pending aR aL Ha cR cL Hc j tR tL Ht)
           (ct_bool_not _ _ (cf_Schedule_scheduled j tR tL Ht))).
Qed.

Lemma cf_Schedule_sequential_jobs :
  PropSPropRel (Schedule.sequential_jobs sR)
    (I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_sequential_jobs Job dJ nL sL).
Proof.
  apply: ct_forall_identity => j. apply: ct_forall_nat => tR tL Ht.
  apply: (co_forall_ord nR nL Hn) => o1R o1L H1. apply: (co_forall_ord nR nL Hn) => o2R o2L H2.
  apply: ct_imp.
  { exact (cs_tr (Hs o1R o1L H1 tR tL Ht) (fun z => PropSPropRel (sR o1R tR = Some j) (Lean.eq z (cl_opt (Some j))))
             (cs_opt_eq_rel Job (sR o1R tR) (Some j))). }
  apply: ct_imp.
  { exact (cs_tr (Hs o2R o2L H2 tR tL Ht) (fun z => PropSPropRel (sR o2R tR = Some j) (Lean.eq z (cl_opt (Some j))))
             (cs_opt_eq_rel Job (sR o2R tR) (Some j))). }
  exact (co_ord_eq_rel _ _ _ _ _ _ H1 H2).
Qed.

Lemma cf_Schedule_jobs_must_arrive_to_execute aR aL (Ha : CsParRel Job aR aL) :
  PropSPropRel (Schedule.jobs_must_arrive_to_execute aR sR)
    (I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_jobs_must_arrive_to_execute Job dJ aL nL sL).
Proof.
  apply: ct_forall_identity => j. apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (ct_bool_truth _ _ (cf_Schedule_scheduled j tR tL Ht)).
  exact (ct_bool_truth _ _ (ct_decide_le _ _ _ _ (Ha j) Ht)).
Qed.

Lemma cf_Schedule_completed_jobs_dont_execute cR cL (Hc : CsParRel Job cR cL) :
  PropSPropRel (Schedule.completed_jobs_dont_execute cR sR)
    (I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_completed_jobs_dont_execute Job dJ cL nL sL).
Proof.
  apply: ct_forall_identity => j. apply: ct_forall_nat => tR tL Ht.
  exact (sub_nat_le_correspondence _ _ _ _ (cf_Schedule_service j tR tL Ht) (Hc j)).
Qed.

Lemma cf_Schedule_jobs_come_from_arrival_sequence arrR arrL (Harr : CsArrRel Job arrR arrL) :
  PropSPropRel (Schedule.jobs_come_from_arrival_sequence sR arrR)
    (I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_jobs_come_from_arrival_sequence Job dJ nL sL arrL).
Proof.
  apply: ct_forall_identity => j. apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (ct_bool_truth _ _ (cf_Schedule_scheduled j tR tL Ht)).
  exact (cs_arrives_in Job arrR arrL Harr j).
Qed.

End Defs.

Section TaskDefs.
Variables (Task Job : eqType) (nR : nat) (nL : Lean.Nat).
Hypothesis Hn : SubNatRel nR nL.
Notation dT := (ct_decidable_eq Task).
Notation dJ := (ct_decidable_eq Job).
Variables (sR : Schedule.schedule Job nR)
  (sL : I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_schedule Job dJ nL).
Hypothesis Hs : CsSchedRel Job nR nL sR sL.
Variable job_task : Job -> Task.

End TaskDefs.

Lemma cs_forall_ncpus_sched (Job : eqType)
    (PR : forall n : nat, Schedule.schedule Job n -> Prop)
    (PL : forall n : Lean.Nat, I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_schedule Job (ct_decidable_eq Job) n -> SProp) :
  (forall nR nL (Hn : SubNatRel nR nL) sR sL, CsSchedRel Job nR nL sR sL -> PropSPropRel (PR nR sR) (PL nL sL)) ->
  PropSPropRel (forall n s, PR n s) (forall n s, PL n s).
Proof.
  intro H. apply: ct_forall_nat => nR nL Hn. exact (cs_forall_sched Job nR nL Hn _ _ (H nR nL Hn)).
Qed.

(* ------------------------------------------------------------------ *)
(** * Affinities (as in the accepted classic affinity certificate) *)

Section Aff.
Variables (nR : nat) (nL : Lean.Nat).
Hypothesis Hn : SubNatRel nR nL.
Notation c := (co_ord_to_fin nR nL Hn).
Notation d := (co_fin_to_ord nR nL Hn).
Notation LAff := (I.Prosa_Classic_Model_Schedule_Apa_Affinity_Affinity_affinity nL).

Lemma caf_cd (y : Fin nL) : Logic.eq (c (d y)) y.
Proof. exact (co_fin_rel_eq _ _ _ _ _ (co_ord_canonical nR nL Hn (d y)) (co_ord_surjective nR nL Hn y)). Qed.

Lemma caf_dc (x : 'I_nR) : Logic.eq (d (c x)) x.
Proof. exact (co_ord_eq _ _ _ _ _ (co_ord_surjective nR nL Hn (c x)) (co_ord_canonical nR nL Hn x)). Qed.

Lemma caf_c_rel (x : 'I_nR) (y : Fin nL) : CoOrdRel nR nL x y -> Logic.eq (c x) y.
Proof. intro H. exact (co_fin_rel_eq _ _ _ _ _ (co_ord_canonical nR nL Hn x) H). Qed.

(** Affinities are related through their underlying sequences, elementwise by the ordinal conversion
    (Lean lists of [Fin n] at the universe instance [List_inst1], [ClassicAffinityList1]). *)
Notation LVal := (I.Prosa_Util_Seqset_set_val_inst1 (Fin nL) (I.instDecidableEqFin nL)).

Definition CafRel (aR : Affinity.affinity nR) (aL : LAff) : SProp :=
  ClListRel1 c (@prosa.util.seqset._set_seq _ aR) (LVal aL).

Definition caf_to_target (aR : Affinity.affinity nR) : LAff :=
  I.Prosa_Util_Seqset_set_mk_inst1 (Fin nL) (I.instDecidableEqFin nL) (cl1_map c (@prosa.util.seqset._set_seq _ aR))
    (prop_to_sprop _ _ (cl1_uniq_rel _ _ c d caf_dc caf_cd _) (@prosa.util.seqset.set_uniq _ aR)).

Definition caf_to_source (aL : LAff) : Affinity.affinity nR :=
  @prosa.util.seqset.Build_set _ (cl1_unmap d (LVal aL))
    (interpret_strict _ (cl1_uniq_backward _ _ c d caf_cd _
                           (@I.nodup0 (Fin nL) (I.instDecidableEqFin nL) aL))).

Lemma caf_canonical aR : CafRel aR (caf_to_target aR).
Proof. exact (@Lean.eq_refl _ _). Qed.

Lemma caf_surjective aL : CafRel (caf_to_source aL) aL.
Proof. apply: coq_eq_to_imported_eq. exact (cl1_map_unmap c d caf_cd _). Qed.

Lemma caf_forall (PR : Affinity.affinity nR -> Prop) (PL : LAff -> SProp) :
  (forall aR aL, CafRel aR aL -> PropSPropRel (PR aR) (PL aL)) -> PropSPropRel (forall a, PR a) (forall a, PL a).
Proof. exact (cs_forall_cover _ _ CafRel caf_to_target caf_to_source caf_canonical caf_surjective PR PL). Qed.

Lemma caf_mem aR aL (Ha : CafRel aR aL) oR oL (Ho : CoOrdRel nR nL oR oL) :
  PropSPropRel (oR \in aR)
    (I.Membership_mem_inst3 (Fin nL) LAff (I.Prosa_Util_Seqset_instMembershipSet_inst1 (Fin nL) (I.instDecidableEqFin nL)) aL oL).
Proof.
  have E := caf_c_rel _ _ Ho. subst oL.
  exact (cl1_mem_rel_list _ _ c d caf_dc oR _ _ Ha).
Qed.

End Aff.

Section TaskAff.
Variables (Task : eqType) (nR : nat) (nL : Lean.Nat).
Hypothesis Hn : SubNatRel nR nL.
Notation LTAff := (I.Prosa_Classic_Model_Schedule_Apa_Affinity_Affinity_task_affinity Task (ct_decidable_eq Task) nL).

Definition CtafRel (aR : Affinity.task_affinity Task nR) (aL : LTAff) : SProp :=
  forall tsk, CafRel nR nL Hn (aR tsk) (aL tsk).

Lemma cai_forall_taff (PR : Affinity.task_affinity Task nR -> Prop) (PL : LTAff -> SProp) :
  (forall aR aL, CtafRel aR aL -> PropSPropRel (PR aR) (PL aL)) -> PropSPropRel (forall a, PR a) (forall a, PL a).
Proof.
  exact (cs_forall_cover _ _ CtafRel (fun a tsk => caf_to_target nR nL Hn (a tsk)) (fun a tsk => caf_to_source nR nL Hn (a tsk))
           (fun a tsk => caf_canonical nR nL Hn (a tsk)) (fun a tsk => caf_surjective nR nL Hn (a tsk)) PR PL).
Qed.

Lemma cai_can_execute_on aR aL (Ha : CtafRel aR aL) tsk oR oL (Ho : CoOrdRel nR nL oR oL) :
  CtBoolRel (Affinity.can_execute_on aR tsk oR)
    (I.Prosa_Classic_Model_Schedule_Apa_Affinity_Affinity_can_execute_on Task (ct_decidable_eq Task) nL aL tsk oL).
Proof. exact (ct_decide_bool _ _ _ (caf_mem nR nL Hn _ _ (Ha tsk) oR oL Ho)). Qed.

Lemma cai_affinity_intersects aR aL (Ha : CafRel nR nL Hn aR aL) a'R a'L (Ha' : CafRel nR nL Hn a'R a'L) :
  CtBoolRel (Affinity.affinity_intersects aR a'R)
    (I.Prosa_Classic_Model_Schedule_Apa_Affinity_Affinity_affinity_intersects nL aL a'L).
Proof.
  apply: (co_exists_rel nR nL Hn). intros oR oL Ho.
  exact (ct_bool_and _ _ _ _ (ct_decide_bool _ _ _ (caf_mem nR nL Hn _ _ Ha oR oL Ho))
           (ct_decide_bool _ _ _ (caf_mem nR nL Hn _ _ Ha' oR oL Ho))).
Qed.

End TaskAff.

(* ------------------------------------------------------------------ *)
(** * Workload (as in the accepted classic workload certificate) *)

(** [\sum_(i <- l | P i) F i] against the accepted v0.6 [sumFiltered] ([((l.filter P).map F).sum]), by induction. *)
Lemma cai_sum_map (T : Type) FR FL (HF : forall x, SubNatRel (FR x) (FL x)) : forall l,
  SubNatRel (\sum_(i <- l) FR i)
    (I.List_sum_inst1 Lean.Nat I.instAddNat (I.MulZeroClass_toZero_inst1 Lean.Nat I.Nat_instMulZeroClass)
       (I.List_map_inst2 T Lean.Nat FL (cl_map cid l))).
Proof.
  intro l. induction l as [|x l IH]; first by rewrite big_nil; exact (sub_nat_rel_canonical 0).
  rewrite big_cons. exact (sub_add_correspondence _ _ _ _ (HF x) IH).
Qed.

Lemma cai_sumFiltered (T : Type) (PR : T -> bool) PL (HP : forall x, CtBoolRel (PR x) (PL x)) FR FL
    (HF : forall x, SubNatRel (FR x) (FL x)) : forall l,
  SubNatRel (\sum_(i <- l | PR i) FR i) (I.Prosa_Util_Sum_sumFiltered T (cl_map cid l) PL FL).
Proof.
  intro l. rewrite -big_filter.
  refine (cs_trs (cl_lean_eq _ _ _ (cl_filter cid PR PL HP l))
            (fun z => SubNatRel (\sum_(i <- filter PR l) FR i)
                        (I.List_sum_inst1 Lean.Nat I.instAddNat (I.MulZeroClass_toZero_inst1 Lean.Nat I.Nat_instMulZeroClass)
                           (I.List_map_inst2 T Lean.Nat FL z))) _).
  exact (cai_sum_map T FR FL HF (filter PR l)).
Qed.

Lemma cai_sumFiltered_rel (T : Type) (PR : T -> bool) PL (HP : forall x, CtBoolRel (PR x) (PL x)) FR FL
    (HF : forall x, SubNatRel (FR x) (FL x)) l L : ClListRel (B := T) cid l L ->
  SubNatRel (\sum_(i <- l | PR i) FR i) (I.Prosa_Util_Sum_sumFiltered T L PL FL).
Proof.
  intro H. exact (cs_trs H (fun z => SubNatRel (\sum_(i <- l | PR i) FR i) (I.Prosa_Util_Sum_sumFiltered T z PL FL))
                    (cai_sumFiltered T PR PL HP FR FL HF l)).
Qed.

(* ------------------------------------------------------------------ *)
(** * Definitions *)

Section PolicyDefs.
Variables (Task : eqType) (nR : nat) (nL : Lean.Nat).
Hypothesis Hn : SubNatRel nR nL.
Notation dT := (ct_decidable_eq Task).

End PolicyDefs.

Section IntDefs.
Variables (Task Job : eqType) (nR : nat) (nL : Lean.Nat).
Hypothesis Hn : SubNatRel nR nL.
Notation dT := (ct_decidable_eq Task).
Notation dJ := (ct_decidable_eq Job).
Variables (sR : Schedule.schedule Job nR)
  (sL : I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_schedule Job dJ nL).
Hypothesis Hs : CsSchedRel Job nR nL sR sL.
Variables (jaR : Job -> nat) (jaL : Job -> Lean.Nat) (cR : Job -> nat) (cL : Job -> Lean.Nat).
Hypotheses (Hja : CsParRel Job jaR jaL) (Hc : CsParRel Job cR cL).
Variable job_task : Job -> Task.
Variables (aR : Affinity.task_affinity Task nR)
  (aL : I.Prosa_Classic_Model_Schedule_Apa_Affinity_Affinity_task_affinity Task dT nL).
Hypothesis Ha : CtafRel Task nR nL Hn aR aL.

Notation bl := (cf_Schedule_backlogged Job nR nL Hn sR sL Hs jaR jaL Hja cR cL Hc).

End IntDefs.

(* ------------------------------------------------------------------ *)
(** * Statements *)

(* ------------------------------------------------------------------ *)
(** * Affinity definitions (as in the accepted classic affinity certificate) *)

Section SchedDefs.
Variables (Task Job : eqType) (nR : nat) (nL : Lean.Nat).
Hypothesis Hn : SubNatRel nR nL.
Notation dT := (ct_decidable_eq Task).
Notation dJ := (ct_decidable_eq Job).
Variables (sR : Schedule.schedule Job nR)
  (sL : I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_schedule Job dJ nL).
Hypothesis Hs : CsSchedRel Job nR nL sR sL.
Variable job_task : Job -> Task.

End SchedDefs.

Section AffDefs.
Variables (nR : nat) (nL : Lean.Nat).
Hypothesis Hn : SubNatRel nR nL.

Theorem Affinity_is_subaffinity_correspondence a'R a'L (Ha' : CafRel nR nL Hn a'R a'L) aR aL (Ha : CafRel nR nL Hn aR aL) :
  PropSPropRel (Affinity.is_subaffinity a'R aR)
    (I.Prosa_Classic_Model_Schedule_Apa_Affinity_Affinity_is_subaffinity nL a'L aL).
Proof.
  apply: (co_forall_ord nR nL Hn) => oR oL Ho.
  exact (ct_imp _ _ _ _ (caf_mem nR nL Hn _ _ Ha' oR oL Ho) (caf_mem nR nL Hn _ _ Ha oR oL Ho)).
Qed.

Theorem Affinity_affinity_intersects_correspondence aR aL (Ha : CafRel nR nL Hn aR aL) a'R a'L (Ha' : CafRel nR nL Hn a'R a'L) :
  CtBoolRel (Affinity.affinity_intersects aR a'R)
    (I.Prosa_Classic_Model_Schedule_Apa_Affinity_Affinity_affinity_intersects nL aL a'L).
Proof.
  apply: (co_exists_rel nR nL Hn). intros oR oL Ho.
  exact (ct_bool_and _ _ _ _ (ct_decide_bool _ _ _ (caf_mem nR nL Hn _ _ Ha oR oL Ho))
           (ct_decide_bool _ _ _ (caf_mem nR nL Hn _ _ Ha' oR oL Ho))).
Qed.

(** [#|a|] against the cardinality of the filtered [Fin n] universe. *)
Lemma caf_card aR aL (Ha : CafRel nR nL Hn aR aL) :
  SubNatRel #|aR|
    (I.Finset_card_inst1 (Fin nL)
       (I.Finset_filter_inst1 (Fin nL)
          (fun x => I.Membership_mem_inst3 (Fin nL) (I.Prosa_Classic_Model_Schedule_Apa_Affinity_Affinity_affinity nL)
                      (I.Prosa_Util_Seqset_instMembershipSet_inst1 (Fin nL) (I.instDecidableEqFin nL)) aL x)
          (fun a => I.Prosa_Classic_Util_Seqset_memDecidable_inst1 (Fin nL) (I.instDecidableEqFin nL) a aL)
          (I.Finset_univ_inst1 (Fin nL) (I.Fin_fintype nL)))).
Proof.
  apply: coq_eq_to_imported_eq.
  rewrite (imported_eq_to_coq_eq _ _ (I.Prosa_Validation_ClassicApaBertognaEdfCompInterface_card_filter_sum nL
             (fun x => I.Membership_mem_inst3 (Fin nL) (I.Prosa_Classic_Model_Schedule_Apa_Affinity_Affinity_affinity nL)
                         (I.Prosa_Util_Seqset_instMembershipSet_inst1 (Fin nL) (I.instDecidableEqFin nL)) aL x)
             (fun a => I.Prosa_Classic_Util_Seqset_memDecidable_inst1 (Fin nL) (I.instDecidableEqFin nL) a aL))).
  have E : #|aR| = \sum_(i < nR) (if i \in aR then 1 else 0) by rewrite -sum1_card big_mkcond.
  rewrite E. apply: imported_eq_to_coq_eq.
  apply: (co_sum_rel nR nL Hn) => oR oL Ho.
  have H := ct_decide_bool _ _ (I.Prosa_Classic_Util_Seqset_memDecidable_inst1 (Fin nL) (I.instDecidableEqFin nL) oL aL)
              (caf_mem nR nL Hn _ _ Ha oR oL Ho).
  rewrite (ct_bool_rel_logic _ _ H). destruct (oR \in aR).
  - exact (sub_nat_rel_canonical 1).
  - exact (sub_nat_rel_canonical 0).
Qed.

End AffDefs.

(* ------------------------------------------------------------------ *)
(** * Policies and platform (as in the accepted classic priority and APA platform certificates) *)

Definition CpRelRel (T : Type) (rR : T -> T -> bool) (rL : T -> T -> I.Bool) : SProp :=
  forall a b, CtBoolRel (rR a b) (rL a b).

Lemma cp_forall_rel (T : Type) (PR : (T -> T -> bool) -> Prop) (PL : (T -> T -> I.Bool) -> SProp) :
  (forall rR rL, CpRelRel T rR rL -> PropSPropRel (PR rR) (PL rL)) -> PropSPropRel (forall r, PR r) (forall r, PL r).
Proof.
  exact (cs_forall_cover _ _ (CpRelRel T) (fun rR a b => ct_b2l (rR a b)) (fun rL a b => ct_l2b (rL a b))
           (fun rR a b => ct_bool_canonical _) (fun rL a b => ct_bool_surjective _) PR PL).
Qed.

Definition CpJldpRel (T : Type) (rR : nat -> T -> T -> bool) (rL : Lean.Nat -> T -> T -> I.Bool) : SProp :=
  forall tR tL, SubNatRel tR tL -> CpRelRel T (rR tR) (rL tL).

Section PlatDefs.
Variables (Task Job : eqType) (nR : nat) (nL : Lean.Nat).
Hypothesis Hn : SubNatRel nR nL.
Notation dT := (ct_decidable_eq Task).
Notation dJ := (ct_decidable_eq Job).
Variables (sR : Schedule.schedule Job nR) (sL : I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_schedule Job dJ nL).
Hypothesis Hs : CsSchedRel Job nR nL sR sL.
Variables (jaR : Job -> nat) (jaL : Job -> Lean.Nat) (cR : Job -> nat) (cL : Job -> Lean.Nat).
Hypotheses (Hja : CsParRel Job jaR jaL) (Hc : CsParRel Job cR cL).
Variable job_task : Job -> Task.
Variables (aR : ArrivalSequence.arrival_sequence Job) (aL : I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrival_sequence Job dJ).
Hypothesis Ha : CsArrRel Job aR aL.
Notation bl := (cf_Schedule_backlogged Job nR nL Hn sR sL Hs jaR jaL Hja cR cL Hc).
Notation son := (cf_Schedule_scheduled_on Job nR nL sR sL Hs).
Notation sch := (cf_Schedule_scheduled Job nR nL Hn sR sL Hs).
Variables (alR : Affinity.task_affinity Task nR)
  (alL : I.Prosa_Classic_Model_Schedule_Apa_Affinity_Affinity_task_affinity Task dT nL).
Hypothesis Hal : CtafRel Task nR nL Hn alR alL.
Notation cex := (cai_can_execute_on Task nR nL Hn alR alL Hal).

Theorem Platform_apa_work_conserving_correspondence :
  PropSPropRel (Platform.apa_work_conserving jaR cR job_task aR sR alR)
    (I.Prosa_Classic_Model_Schedule_Apa_Platform_Platform_apa_work_conserving Task Job dT dJ jaL cL job_task aL nL sL alL).
Proof.
  apply: ct_forall_identity => j. apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (cs_arrives_in Job aR aL Ha j).
  apply: ct_imp; first exact (ct_bool_truth _ _ (bl j tR tL Ht)).
  apply: (co_forall_ord nR nL Hn) => oR oL Ho.
  apply: ct_imp; first exact (ct_bool_truth _ _ (cex (job_task j) oR oL Ho)).
  apply: ct_exists_identity => j_other.
  exact (ct_bool_truth _ _ (son j_other oR oL Ho tR tL Ht)).
Qed.

Theorem Platform_respects_affinity_correspondence :
  PropSPropRel (Platform.respects_affinity job_task sR alR) (I.Prosa_Classic_Model_Schedule_Apa_Platform_Platform_respects_affinity Task Job dT dJ job_task nL sL alL).
Proof.
  apply: ct_forall_identity => j. apply: (co_forall_ord nR nL Hn) => oR oL Ho. apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (ct_bool_truth _ _ (son j oR oL Ho tR tL Ht)).
  exact (ct_bool_truth _ _ (cex (job_task j) oR oL Ho)).
Qed.

End PlatDefs.

(* ------------------------------------------------------------------ *)
(** * Response-time bounds (as in the accepted classic response_time certificate) *)

Theorem ResponseTime_is_response_time_bound_of_task_correspondence (Task Job : eqType) nR nL (Hn : SubNatRel nR nL)
    sR sL (Hs : CsSchedRel Job nR nL sR sL) jaR jaL (Hja : CsParRel Job jaR jaL) cR cL (Hc : CsParRel Job cR cL)
    (job_task : Job -> Task) aR aL (Ha : CsArrRel Job aR aL) tsk RR RL (HR : SubNatRel RR RL) :
  PropSPropRel (ResponseTime.is_response_time_bound_of_task jaR cR job_task aR sR tsk RR)
    (I.Prosa_Classic_Model_Schedule_Global_ResponseTime_ResponseTime_is_response_time_bound_of_task
       Task Job (ct_decidable_eq Task) (ct_decidable_eq Job) jaL cL job_task aL nL sL tsk RL).
Proof.
  apply: ct_forall_identity => j.
  apply: ct_imp; first exact (cs_arrives_in Job aR aL Ha j).
  apply: ct_imp; first exact (ct_eq_rel Task (job_task j) tsk).
  exact (ct_bool_truth _ _ (cf_Schedule_completed Job nR nL Hn sR sL Hs cR cL Hc j _ _ (sub_add_correspondence _ _ _ _ (Hja j) HR))).
Qed.

(* ------------------------------------------------------------------ *)
(** * Task model, job validity and sequence sums (as in the accepted classic task_arrival and workload_bound certificates) *)

Lemma cta_false_rel : PropSPropRel Logic.False I.False.
Proof.
  apply prop_sprop_rel_intro.
  - exact ct_coq_false_to_target.
  - exact ct_target_false_to_strict.
Qed.

Lemma cta_ne (T : Type) (x y : T) : PropSPropRel (x <> y) (I.Ne T x y).
Proof. exact (ct_imp _ _ _ _ (ct_eq_rel T x y) cta_false_rel). Qed.

Lemma cta_succ_rel nR nL : SubNatRel nR nL ->
  SubNatRel nR.+1 (I.HAdd_hAdd_inst7 Lean.Nat Lean.Nat Lean.Nat (I.instHAdd_inst1 Lean.Nat I.instAddNat) nL
                     (I.OfNat_ofNat_inst1 Lean.Nat 1 (I.instOfNatNat 1))).
Proof. intro Hn. exact (sub_imported_eq_congr Lean.Nat_succ _ _ Hn). Qed.

Lemma cwb_forall_arr (Job : eqType) PR PL :
  (forall aR aL, CsArrRel Job aR aL -> PropSPropRel (PR aR) (PL aL)) -> PropSPropRel (forall a, PR a) (forall a, PL a).
Proof. exact (cs_forall_cover _ _ (CsArrRel Job) (cs_arr_to_target Job) (cs_arr_to_source Job) (cs_arr_canonical Job) (cs_arr_surjective Job) PR PL). Qed.

Lemma cwb_valid_sporadic_job (Task Job : eqType) tcR tcL (Htc : CsParRel Task tcR tcL) tdR tdL (Htd : CsParRel Task tdR tdL)
    cR cL (Hc : CsParRel Job cR cL) dR dL (Hd : CsParRel Job dR dL) (job_task : Job -> Task) j :
  PropSPropRel (Job.valid_sporadic_job tcR tdR cR dR job_task j)
    (I.Prosa_Classic_Model_Arrival_Basic_Job_Job_valid_sporadic_job Task (ct_decidable_eq Task) tcL tdL Job (ct_decidable_eq Job) cL dL job_task j).
Proof.
  apply: ct_and.
  { apply: ct_and; first exact (ct_bool_truth _ _ (ct_decide_lt _ _ _ _ (sub_nat_rel_canonical 0) (Hc j))).
    apply: ct_and; first exact (ct_bool_truth _ _ (ct_decide_le _ _ _ _ (Hc j) (Hd j))).
    exact (ct_bool_truth _ _ (ct_decide_lt _ _ _ _ (sub_nat_rel_canonical 0) (Hd j))). }
  apply: ct_and; first exact (ct_bool_truth _ _ (ct_decide_le _ _ _ _ (Hc j) (Htc (job_task j)))).
  exact (sub_nat_eq_correspondence _ _ _ _ (Hd j) (Htd (job_task j))).
Qed.

Lemma cwb_sporadic_task_model (Task Job : eqType) tpR tpL (Htp : CsParRel Task tpR tpL) jaR jaL (Hja : CsParRel Job jaR jaL)
    (job_task : Job -> Task) aR aL (Ha : CsArrRel Job aR aL) :
  PropSPropRel (TaskArrival.sporadic_task_model tpR jaR job_task aR)
    (I.Prosa_Classic_Model_Arrival_Basic_TaskArrival_TaskArrival_sporadic_task_model Task (ct_decidable_eq Task) tpL Job (ct_decidable_eq Job) jaL job_task aL).
Proof.
  apply: ct_forall_identity => j. apply: ct_forall_identity => j'.
  apply: ct_imp; first exact (cta_ne Job j j').
  apply: ct_imp; first exact (cs_arrives_in Job aR aL Ha j).
  apply: ct_imp; first exact (cs_arrives_in Job aR aL Ha j').
  apply: ct_imp; first exact (ct_eq_rel Task (job_task j) (job_task j')).
  apply: ct_imp; first exact (sub_nat_le_correspondence _ _ _ _ (Hja j) (Hja j')).
  exact (sub_nat_le_correspondence _ _ _ _ (sub_add_correspondence _ _ _ _ (Hja j) (Htp (job_task j))) (Hja j')).
Qed.

Lemma cwb_valid_sporadic_task (Task : eqType) cR cL (Hc : CsParRel Task cR cL) pR pL (Hp : CsParRel Task pR pL)
    dR dL (Hd : CsParRel Task dR dL) tsk :
  PropSPropRel (SporadicTask.is_valid_sporadic_task cR pR dR tsk)
    (I.Prosa_Classic_Model_Arrival_Basic_Task_SporadicTask_is_valid_sporadic_task Task (ct_decidable_eq Task) cL pL dL tsk).
Proof.
  apply: ct_and; first exact (ct_bool_truth _ _ (ct_decide_lt _ _ _ _ (sub_nat_rel_canonical 0) (Hc tsk))).
  apply: ct_and; first exact (ct_bool_truth _ _ (ct_decide_lt _ _ _ _ (sub_nat_rel_canonical 0) (Hp tsk))).
  apply: ct_and; first exact (ct_bool_truth _ _ (ct_decide_lt _ _ _ _ (sub_nat_rel_canonical 0) (Hd tsk))).
  apply: ct_and; first exact (ct_bool_truth _ _ (ct_decide_le _ _ _ _ (Hc tsk) (Hd tsk))).
  exact (ct_bool_truth _ _ (ct_decide_le _ _ _ _ (Hc tsk) (Hp tsk))).
Qed.

Lemma cai_sumSeq (T : Type) (FR : T -> nat) (FL : T -> Lean.Nat) (HF : forall x, SubNatRel (FR x) (FL x)) : forall l,
  SubNatRel (\sum_(i <- l) FR i) (I.Prosa_Util_Sum_sumSeq T (cl_map cid l) FL).
Proof.
  intro l. induction l as [|x l IH]; first by rewrite big_nil; exact (sub_nat_rel_canonical 0).
  rewrite big_cons.
  change (SubNatRel (FR x + \sum_(j <- l) FR j) (Lean.Nat_add (FL x) (I.Prosa_Util_Sum_sumSeq T (cl_map cid l) FL))).
  exact (sub_add_correspondence _ _ _ _ (HF x) IH).
Qed.

Lemma cwb_sumSeq_rel (T : Type) FR FL (HF : forall x, SubNatRel (FR x) (FL x)) l L : ClListRel (B := T) cid l L ->
  SubNatRel (\sum_(i <- l) FR i) (I.Prosa_Util_Sum_sumSeq T L FL).
Proof. intro H. exact (cs_trs H (fun z => SubNatRel (\sum_(i <- l) FR i) (I.Prosa_Util_Sum_sumSeq T z FL)) (cai_sumSeq T FR FL HF l)). Qed.

(* ------------------------------------------------------------------ *)
(** * Workload and interference bounds (as in the accepted classic interference_bound_fp certificate) *)

Lemma cib_max_jobs (Task : eqType) cR cL (Hc : CsParRel Task cR cL) pR pL (Hp : CsParRel Task pR pL) tsk
    RR RL (HR : SubNatRel RR RL) dR dL (Hd : SubNatRel dR dL) :
  SubNatRel (WorkloadBound.max_jobs cR pR tsk RR dR) (I.Prosa_Classic_Analysis_Apa_WorkloadBound_WorkloadBound_max_jobs Task (ct_decidable_eq Task) cL pL tsk RL dL).
Proof.
  exact (dm_div_floor_correspondence _ _ _ _ (dm_sub_correspondence _ _ _ _ (dm_add_correspondence _ _ _ _ Hd HR) (Hc tsk)) (Hp tsk)).
Qed.

Lemma cib_W (Task : eqType) cR cL (Hc : CsParRel Task cR cL) pR pL (Hp : CsParRel Task pR pL) tsk
    RR RL (HR : SubNatRel RR RL) dR dL (Hd : SubNatRel dR dL) :
  SubNatRel (WorkloadBound.W cR pR tsk RR dR) (I.Prosa_Classic_Analysis_Apa_WorkloadBound_WorkloadBound_W Task (ct_decidable_eq Task) cL pL tsk RL dL).
Proof.
  have Hm := cib_max_jobs Task cR cL Hc pR pL Hp tsk RR RL HR dR dL Hd.
  exact (dm_add_correspondence _ _ _ _
           (cib_min_rel _ _ _ _ (Hc tsk)
              (dm_sub_correspondence _ _ _ _ (dm_sub_correspondence _ _ _ _ (dm_add_correspondence _ _ _ _ Hd HR) (Hc tsk))
                 (dm_mul_correspondence _ _ _ _ Hm (Hp tsk))))
           (dm_mul_correspondence _ _ _ _ Hm (Hc tsk))).
Qed.

Definition cibfp_pair (T : Type) (p : T * nat) : I.Prod_inst2 T Lean.Nat := I.Prod_mk_inst2 T Lean.Nat p.1 (sub_nat_to_imported p.2).

Lemma cib_generic (Task : eqType) cR cL (Hc : CsParRel Task cR cL) pR pL (Hp : CsParRel Task pR pL) tsk dR dL (Hd : SubNatRel dR dL)
    (p : Task * nat) :
  SubNatRel (InterferenceBoundGeneric.interference_bound_generic cR pR tsk dR p)
    (I.Prosa_Classic_Analysis_Apa_InterferenceBound_InterferenceBoundGeneric_interference_bound_generic Task (ct_decidable_eq Task) cL pL tsk dL (cibfp_pair Task p)).
Proof.
  exact (cib_min_rel _ _ _ _ (cib_W Task cR cL Hc pR pL Hp p.1 _ _ (sub_nat_rel_canonical p.2) _ _ Hd)
           (dm_add_correspondence _ _ _ _ (dm_sub_correspondence _ _ _ _ Hd (Hc tsk)) (sub_nat_rel_canonical 1))).
Qed.

Definition cibfp_trs {A : Type} {x y : A} (E : Lean.eq x y) (P : A -> SProp) (h : P x) : P y :=
  match E in Lean.eq _ z return P z with Lean.eq_refl => h end.

Lemma cibfp_sum_map (A B : Type) (c : A -> B) FR FL (HF : forall x, SubNatRel (FR x) (FL (c x))) : forall l,
  SubNatRel (\sum_(i <- l) FR i)
    (I.List_sum_inst1 Lean.Nat I.instAddNat (I.MulZeroClass_toZero_inst1 Lean.Nat I.Nat_instMulZeroClass)
       (I.List_map_inst2 B Lean.Nat FL (cl_map c l))).
Proof.
  intro l. induction l as [|x l IH]; first by rewrite big_nil; exact (sub_nat_rel_canonical 0).
  rewrite big_cons. exact (sub_add_correspondence _ _ _ _ (HF x) IH).
Qed.

Lemma cibfp_sumFiltered_rel (A B : Type) (PR : A -> bool) FR (c : A -> B) PL FL
    (HP : forall x, CtBoolRel (PR x) (PL (c x))) (HF : forall x, SubNatRel (FR x) (FL (c x))) l L :
  ClListRel c l L -> SubNatRel (\sum_(i <- l | PR i) FR i) (I.Prosa_Util_Sum_sumFiltered B L PL FL).
Proof.
  intro H.
  refine (cibfp_trs H (fun z => SubNatRel (\sum_(i <- l | PR i) FR i) (I.Prosa_Util_Sum_sumFiltered B z PL FL)) _).
  rewrite -big_filter.
  refine (cibfp_trs (cl_lean_eq _ _ _ (cl_filter c PR PL HP l))
            (fun z => SubNatRel (\sum_(i <- filter PR l) FR i)
                        (I.List_sum_inst1 Lean.Nat I.instAddNat (I.MulZeroClass_toZero_inst1 Lean.Nat I.Nat_instMulZeroClass)
                           (I.List_map_inst2 B Lean.Nat FL z))) _).
  exact (cibfp_sum_map A B c FR FL HF (filter PR l)).
Qed.

(* ------------------------------------------------------------------ *)
(** * Task sets, filters, counts and (task, time) pair sequences *)

(** [taskset_of Task] is the accepted sequence-set type; task sets are related through their
    underlying sequences, elementwise by identity, with two-way totals (as the accepted
    classic task certificate's [RocqSeqSetRel], here through the re-bound list library). *)
Section Ts.
Variable Task : eqType.
Notation dT := (ct_decidable_eq Task).
Notation LTs := (I.Prosa_Classic_Model_Arrival_Basic_Task_SporadicTaskset_taskset_of Task dT).
Notation LVal := (I.Prosa_Util_Seqset_set_val Task dT).

Definition CtsRel (tsR : SporadicTaskset.taskset_of Task) (tsL : LTs) : SProp :=
  ClListRel cid (@prosa.util.seqset._set_seq _ tsR) (LVal tsL).

Lemma cts_id (x : Task) : Logic.eq x x.
Proof. reflexivity. Qed.

Definition cts_to_target (tsR : SporadicTaskset.taskset_of Task) : LTs :=
  I.Prosa_Util_Seqset_set_mk Task dT (cl_map cid (@prosa.util.seqset._set_seq _ tsR))
    (prop_to_sprop _ _ (cl_uniq_rel _ _ cid cid cts_id cts_id _) (@prosa.util.seqset.set_uniq _ tsR)).

Definition cts_to_source (tsL : LTs) : SporadicTaskset.taskset_of Task :=
  @prosa.util.seqset.Build_set _ (cl_unmap cid (LVal tsL))
    (interpret_strict _ (cl_uniq_backward _ _ cid cid cts_id _ (@I.nodup Task dT tsL))).

Lemma cts_canonical tsR : CtsRel tsR (cts_to_target tsR).
Proof. exact (@Lean.eq_refl _ _). Qed.

Lemma cts_surjective tsL : CtsRel (cts_to_source tsL) tsL.
Proof. apply: coq_eq_to_imported_eq. exact (cl_map_unmap cid cid cts_id _). Qed.

Lemma cts_forall (PR : SporadicTaskset.taskset_of Task -> Prop) (PL : LTs -> SProp) :
  (forall tsR tsL, CtsRel tsR tsL -> PropSPropRel (PR tsR) (PL tsL)) -> PropSPropRel (forall ts, PR ts) (forall ts, PL ts).
Proof. exact (cs_forall_cover _ _ CtsRel cts_to_target cts_to_source cts_canonical cts_surjective PR PL). Qed.

Lemma cts_mem tsR tsL (Hts : CtsRel tsR tsL) x :
  PropSPropRel (x \in tsR)
    (I.Membership_mem Task LTs (I.Prosa_Util_Seqset_instMembershipSet Task dT) tsL x).
Proof. exact (cl_mem_rel_list _ _ cid cid cts_id x _ _ Hts). Qed.

End Ts.

(** [valid_sporadic_taskset] over related task sequences (as in the accepted classic task certificate). *)
Lemma cts_valid_taskset (Task : eqType) cR cL (Hc : CsParRel Task cR cL) pR pL (Hp : CsParRel Task pR pL)
    dR dL (Hd : CsParRel Task dR dL) (s : seq Task) sL (Hs : ClListRel cid s sL) :
  PropSPropRel (SporadicTaskset.valid_sporadic_taskset cR pR dR s)
    (I.Prosa_Classic_Model_Arrival_Basic_Task_SporadicTaskset_valid_sporadic_taskset Task (ct_decidable_eq Task) cL pL dL sL).
Proof.
  apply: ct_forall_identity => tsk.
  exact (ct_imp _ _ _ _ (cl_mem_rel_list Task Task cid cid (fun _ => Logic.eq_refl _) tsk s sL Hs)
           (cwb_valid_sporadic_task Task cR cL Hc pR pL Hp dR dL Hd tsk)).
Qed.

(** [[seq x <- s | P x]] against [List.filter]. *)
Lemma cts_filter (Task : eqType) (PR : Task -> bool) PL (Hp : forall x, CtBoolRel (PR x) (PL x)) s sL :
  ClListRel cid s sL -> ClListRel cid [seq x <- s | PR x] (I.List_filter Task PL sL).
Proof.
  intro H. refine (cs_trs H (fun z => ClListRel cid [seq x <- s | PR x] (I.List_filter Task PL z)) _).
  apply: coq_eq_to_imported_eq. exact (cl_filter cid PR PL Hp s).
Qed.

(** [count P s] against [List.countP P l] by structural induction through [countP.go] and its
    accumulator (as in the accepted classic counting certificate). *)
Lemma ccount_go (T : Type) (pR : T -> bool) (pL : T -> I.Bool) (Hp : forall x, CtBoolRel (pR x) (pL x)) :
  forall (s : seq T) n,
  Logic.eq (I.List_countP_go T pL (cl_map cid s) (sub_nat_to_imported n)) (sub_nat_to_imported (n + count pR s)).
Proof.
  elim => [|x s IH] n.
  - by rewrite addn0.
  - have -> : Logic.eq (I.List_countP_go T pL (cl_map cid (x :: s)) (sub_nat_to_imported n))
        (match pL x with
         | I.Bool_true => I.List_countP_go T pL (cl_map cid s) (sub_nat_to_imported n.+1)
         | I.Bool_false => I.List_countP_go T pL (cl_map cid s) (sub_nat_to_imported n) end).
    { cbn. destruct (pL x); reflexivity. }
    rewrite (ct_bool_rel_logic _ _ (Hp x)) (IH n.+1) (IH n).
    change (count pR (x :: s)) with (pR x + count pR s).
    case: (pR x).
    + by rewrite addSnnS add1n.
    + by rewrite add0n.
Qed.

Lemma ccount_rel (T : Type) pR pL (Hp : forall x, CtBoolRel (pR x) (pL x)) s sL : ClListRel (B := T) cid s sL ->
  SubNatRel (count pR s) (I.List_countP T pL sL).
Proof.
  intro H. refine (cs_trs H (fun z => SubNatRel (count pR s) (I.List_countP T pL z)) _).
  apply: coq_eq_to_imported_eq. apply: Logic.eq_sym. exact (ccount_go T pR pL Hp s 0).
Qed.

(** Sequences of (task, time) pairs: elementwise by [cibfp_pair], with two-way totals. *)
Definition cpair_unpair (T : Type) (p : I.Prod_inst2 T Lean.Nat) : T * nat :=
  match p with I.Prod_mk_inst2 a b => (a, sub_nat_to_rocq b) end.

Lemma cpair_dc (T : Type) (x : T * nat) : Logic.eq (cpair_unpair T (cibfp_pair T x)) x.
Proof.
  destruct x as [a b]. change (Logic.eq (a, sub_nat_to_rocq (sub_nat_to_imported b)) (a, b)).
  by rewrite sub_nat_rocq_roundtrip.
Qed.

Lemma cpair_cd (T : Type) (y : I.Prod_inst2 T Lean.Nat) : Logic.eq (cibfp_pair T (cpair_unpair T y)) y.
Proof.
  destruct y as [a b]. change (Logic.eq (I.Prod_mk_inst2 T Lean.Nat a (sub_nat_to_imported (sub_nat_to_rocq b))) (I.Prod_mk_inst2 T Lean.Nat a b)).
  by rewrite (imported_eq_to_coq_eq _ _ (sub_nat_imported_roundtrip b)).
Qed.

Lemma cpair_forall (T : Type) (PR : seq (T * nat) -> Prop) (PL : I.List (I.Prod_inst2 T Lean.Nat) -> SProp) :
  (forall lR lL, ClListRel (cibfp_pair T) lR lL -> PropSPropRel (PR lR) (PL lL)) -> PropSPropRel (forall l, PR l) (forall l, PL l).
Proof.
  exact (cs_forall_cover _ _ (ClListRel (cibfp_pair T)) (cl_map (cibfp_pair T)) (cl_unmap (cpair_unpair T))
           (fun l => @Lean.eq_refl _ _) (fun L => coq_eq_to_imported_eq _ _ (cl_map_unmap _ _ (cpair_cd T) L)) PR PL).
Qed.

Lemma cpair_mem (T : eqType) a bR bL (Hb : SubNatRel bR bL) (l : seq (T * nat)) L (Hl : ClListRel (cibfp_pair T) l L) :
  PropSPropRel ((a, bR) \in l)
    (I.Membership_mem (I.Prod_inst2 T Lean.Nat) (I.List (I.Prod_inst2 T Lean.Nat)) (I.List_instMembership (I.Prod_inst2 T Lean.Nat))
       L (I.Prod_mk_inst2 T Lean.Nat a bL)).
Proof.
  refine (cs_tr Hb (fun z => PropSPropRel ((a, bR) \in l)
                                (I.Membership_mem (I.Prod_inst2 T Lean.Nat) (I.List (I.Prod_inst2 T Lean.Nat))
                                   (I.List_instMembership (I.Prod_inst2 T Lean.Nat)) L (I.Prod_mk_inst2 T Lean.Nat a z))) _).
  exact (cl_mem_rel_list _ _ (cibfp_pair T) (cpair_unpair T) (cpair_dc T) (a, bR) l L Hl).
Qed.

Lemma cta_unmap_rel (T : Type) (l : I.List T) : ClListRel cid (cl_unmap cid l) l.
Proof. apply: coq_eq_to_imported_eq. exact (cl_map_unmap cid cid (fun _ => Logic.eq_refl _) l). Qed.

Lemma cta_cl_map_inj (T : Type) (s1 s2 : seq T) : Logic.eq (cl_map cid s1) (cl_map cid s2) -> Logic.eq s1 s2.
Proof.
  intro E. rewrite -(cl_unmap_map cid cid (fun _ => Logic.eq_refl _) s1) -(cl_unmap_map cid cid (fun _ => Logic.eq_refl _) s2).
  by rewrite E.
Qed.

Lemma cta_pred_rel nR nL : SubNatRel nR nL ->
  SubNatRel nR.-1 (ct_sub nL (I.OfNat_ofNat_inst1 Lean.Nat 1 (I.instOfNatNat 1))).
Proof.
  intro Hn. apply: coq_eq_to_imported_eq. rewrite -subn1.
  exact (imported_eq_to_coq_eq _ _ (ct_sub_rel _ _ _ _ Hn (sub_nat_rel_canonical 1))).
Qed.

Section SortUniq.
Variables (T : eqType) (f : T -> nat).
Notation leT := (fun a b : T => f a <= f b).
Notation cls x := (fun y : T => f y == f x).

Lemma cta_leT_trans : transitive leT.
Proof. move=> y x z. exact: leq_trans. Qed.

Lemma cta_leT_total : total leT.
Proof. move=> a b. exact: leq_total. Qed.

Lemma cta_class_sorted x : forall l : seq T, all (cls x) l -> sorted leT l.
Proof.
  case => [|a l] //= /andP [Ha Hl]. elim: l a Ha Hl => [|b l IH] a Ha //= /andP [Hb Hl].
  rewrite (eqP Ha) (eqP Hb) leqnn /=. exact: IH.
Qed.

Lemma cta_sort_filter_class s x : filter (cls x) (sort leT s) = filter (cls x) s.
Proof.
  rewrite (filter_sort cta_leT_total cta_leT_trans).
  apply: (sorted_sort cta_leT_trans). apply: cta_class_sorted. exact: filter_all.
Qed.

Lemma cta_sorted_class_uniq : forall u t : seq T, sorted leT u -> sorted leT t ->
  (forall x, filter (cls x) u = filter (cls x) t) -> u = t.
Proof.
  elim => [|a u IH] t Su St H.
  { case: t St H => [//|b t] St H. by have := H b; rewrite /= eqxx. }
  case: t St H => [|b t] St H; first by have := H a; rewrite /= eqxx.
  have Ma : all (leT a) u := order_path_min cta_leT_trans Su.
  have Mb : all (leT b) t := order_path_min cta_leT_trans St.
  have Hba : f b <= f a.
  { have : a \in filter (cls a) (b :: t) by rewrite -H /= eqxx mem_head.
    rewrite mem_filter => /andP [_]. rewrite in_cons => /orP [/eqP -> //|Ht].
    exact: (allP Mb). }
  have Hab : f a <= f b.
  { have : b \in filter (cls b) (a :: u) by rewrite H /= eqxx mem_head.
    rewrite mem_filter => /andP [_]. rewrite in_cons => /orP [/eqP -> //|Hu].
    exact: (allP Ma). }
  have Eab : f b == f a by rewrite eqn_leq Hab Hba.
  have Hhead := H a. rewrite /= eqxx Eab in Hhead. case: Hhead => Eh Et.
  subst b. congr cons. apply: IH.
  - exact: path_sorted Su.
  - exact: path_sorted St.
  - move=> x. have := H x. rewrite /=. by case: (f a == f x) => // [[]].
Qed.

Lemma cta_sort_unique (u s : seq T) : sorted leT u -> (forall x, filter (cls x) u = filter (cls x) s) -> u = sort leT s.
Proof.
  move=> Su H. apply: cta_sorted_class_uniq => //.
  - exact: (sort_sorted cta_leT_total).
  - move=> x. by rewrite cta_sort_filter_class H.
Qed.

End SortUniq.

Section Chain.
Variables (T : Type) (leR : T -> T -> bool) (leL : T -> T -> I.Bool).
Hypothesis HR : forall a b, CtBoolRel (leR a b) (leL a b).
Notation RL := (fun a b : T => Lean.eq (leL a b) I.Bool_true).

Inductive CtaTrue : SProp := cta_true_intro.

Definition cta_chain_head (x y : T) (l : I.List T) (H : I.List_IsChain T RL (I.List_cons T x (I.List_cons T y l))) : RL x y :=
  match H in I.List_IsChain _ _ L
    return (match L with I.List_cons a (I.List_cons b _) => RL a b | _ => CtaTrue end) with
  | I.List_IsChain_nil => cta_true_intro
  | I.List_IsChain_singleton _ => cta_true_intro
  | I.List_IsChain_cons_cons a b l h _ => h
  end.

Definition cta_chain_tail (x y : T) (l : I.List T) (H : I.List_IsChain T RL (I.List_cons T x (I.List_cons T y l))) :
    I.List_IsChain T RL (I.List_cons T y l) :=
  match H in I.List_IsChain _ _ L
    return (match L with I.List_cons _ (I.List_cons b l') => I.List_IsChain T RL (I.List_cons T b l') | _ => CtaTrue end) with
  | I.List_IsChain_nil => cta_true_intro
  | I.List_IsChain_singleton _ => cta_true_intro
  | I.List_IsChain_cons_cons a b l _ t => t
  end.

Fixpoint cta_path_backward (x : T) (s : seq T) : I.List_IsChain T RL (I.List_cons T x (cl_map cid s)) -> StrictlyInhabited (path leR x s) :=
  match s as s0 return I.List_IsChain T RL (I.List_cons T x (cl_map cid s0)) -> StrictlyInhabited (path leR x s0) with
  | [::] => fun _ => strictly_inhabits (Logic.eq_refl true)
  | y :: s' => fun H =>
      match cta_path_backward y s' (cta_chain_tail x y _ H) with
      | strictly_inhabits Hp =>
          strictly_inhabits (introT andP (conj (sprop_to_prop _ _ (ct_bool_truth _ _ (HR x y)) (cta_chain_head x y _ H)) Hp))
      end
  end.

Lemma cta_sorted_backward s : I.List_IsChain T RL (cl_map cid s) -> StrictlyInhabited (sorted leR s).
Proof.
  destruct s as [|x s].
  - intros _. exact (strictly_inhabits (Logic.eq_refl true)).
  - exact (cta_path_backward x s).
Qed.

End Chain.

Section Sort.
Variables (T : eqType) (f : T -> nat) (fL : T -> Lean.Nat).
Hypothesis Hf : forall x, SubNatRel (f x) (fL x).
Notation leL := (fun j j' : T => I.Decidable_decide (I.LE_le_inst1 Lean.Nat I.instLENat (fL j) (fL j')) (I.Nat_decLe (fL j) (fL j'))).
Notation clsL x := (fun y : T => I.Decidable_decide (Lean.eq (fL y) (fL x)) (I.instDecidableEqNat (fL y) (fL x))).

Lemma cta_sort_rel s sL : ClListRel cid s sL ->
  ClListRel cid (sort (fun j j' => f j <= f j') s) (I.List_mergeSort T sL leL).
Proof.
  intro Hs.
  pose m := I.List_mergeSort T sL leL. pose u := cl_unmap cid m.
  have Hu : ClListRel cid u m := cta_unmap_rel T m.
  have Su : sorted (fun a b => f a <= f b) u :=
    interpret_strict _
      (cta_sorted_backward T (fun a b => f a <= f b) leL (fun a b => ct_decide_le _ _ _ _ (Hf a) (Hf b)) u
         (match Hu in Lean.eq _ z
                return I.List_IsChain T (fun a b => Lean.eq (leL a b) I.Bool_true) z ->
                       I.List_IsChain T (fun a b => Lean.eq (leL a b) I.Bool_true) (cl_map cid u) with
          | Lean.eq_refl => fun h => h
          end (I.Prosa_Validation_ClassicApaBertognaEdfCompInterface_mergeSort_isChain T fL sL))).
  have Fu : forall x, filter (fun y => f y == f x) u = filter (fun y => f y == f x) s.
  { intro x. apply: cta_cl_map_inj.
    have Hp : forall y, CtBoolRel (f y == f x) (clsL x y) := fun y => ct_decide_eq_nat _ _ _ _ (Hf y) (Hf x).
    refine (Logic.eq_trans (cl_filter cid (fun y => f y == f x) (clsL x) Hp u)
              (Logic.eq_trans _ (Logic.eq_sym (cl_filter cid (fun y => f y == f x) (clsL x) Hp s)))).
    refine (Logic.eq_trans (f_equal (I.List_filter T (clsL x)) (Logic.eq_sym (cl_list_logic _ _ _ Hu)))
              (Logic.eq_trans _ (f_equal (I.List_filter T (clsL x)) (cl_list_logic _ _ _ Hs)))).
    exact (imported_eq_to_coq_eq _ _ (I.Prosa_Validation_ClassicApaBertognaEdfCompInterface_mergeSort_filter_class T fL x sL)). }
  have E := cta_sort_unique T f u s Su Fu.
  apply: coq_eq_to_imported_eq. rewrite -E. exact (Logic.eq_sym (cl_list_logic _ _ _ Hu)).
Qed.

End Sort.

Lemma cwb_add2 nR nL : SubNatRel nR nL ->
  SubNatRel nR.+2 (I.HAdd_hAdd_inst7 Lean.Nat Lean.Nat Lean.Nat (I.instHAdd_inst1 Lean.Nat I.instAddNat) nL
                     (I.OfNat_ofNat_inst1 Lean.Nat 2 (I.instOfNatNat 2))).
Proof.
  intro H. apply: coq_eq_to_imported_eq. rewrite -addn2.
  exact (imported_eq_to_coq_eq _ _ (sub_add_correspondence _ _ 2 _ H (sub_nat_rel_canonical 2))).
Qed.

(* ------------------------------------------------------------------ *)
(** * EDF priority and [different_task] (as in the accepted classic priority certificate) *)

Lemma cpe_edf (Job : eqType) jaR jaL (Hja : CsParRel Job jaR jaL) jdR jdL (Hjd : CsParRel Job jdR jdL) :
  CpRelRel Job (Priority.EDF jaR jdR) (I.Prosa_Classic_Model_Priority_Priority_EDF Job (ct_decidable_eq Job) jaL jdL).
Proof.
  intros a b. exact (ct_decide_le _ _ _ _ (sub_add_correspondence _ _ _ _ (Hja a) (Hjd a))
                                          (sub_add_correspondence _ _ _ _ (Hja b) (Hjd b))).
Qed.

Lemma cmem_list (T : eqType) x (s : seq T) sL : ClListRel cid s sL ->
  PropSPropRel (x \in s) (I.Membership_mem T (I.List T) (I.List_instMembership T) sL x).
Proof. exact (cl_mem_rel_list T T cid cid (fun _ => Logic.eq_refl _) x s sL). Qed.
Lemma cibfp_sumSeq_rel (A B : Type) FR (c : A -> B) FL (HF : forall x, SubNatRel (FR x) (FL (c x))) l L :
  ClListRel c l L -> SubNatRel (\sum_(i <- l) FR i) (I.Prosa_Util_Sum_sumSeq B L FL).
Proof.
  intro H. refine (cibfp_trs H (fun z => SubNatRel (\sum_(i <- l) FR i) (I.Prosa_Util_Sum_sumSeq B z FL)) _).
  exact (cibfp_sum_map A B c FR FL HF l).
Qed.

(* ------------------------------------------------------------------ *)
(** * [different_task_in] and the weak-APA JLFP policy (as the accepted FP versions above) *)

Section ApaEdfDefs.
Variables (Task : eqType) (nR : nat) (nL : Lean.Nat).
Hypothesis Hn : SubNatRel nR nL.
Notation dT := (ct_decidable_eq Task).

Theorem Interference_different_task_in_correspondence aR aL (Ha : CtafRel Task nR nL Hn aR aL) tsk a'R a'L (Ha' : CafRel nR nL Hn a'R a'L) tsk_other :
  CtBoolRel (Interference.different_task_in aR tsk a'R tsk_other)
    (I.Prosa_Classic_Model_Schedule_Apa_Interference_Interference_different_task_in Task dT nL aL tsk a'L tsk_other).
Proof.
  exact (ct_bool_and _ _ _ _ (ct_bool_not _ _ (ct_decide_eq Task tsk_other tsk))
           (cai_affinity_intersects nR nL Hn _ _ Ha' _ _ (Ha tsk_other))).
Qed.

End ApaEdfDefs.

Section ApaPlatJlfp.
Variables (Task Job : eqType) (nR : nat) (nL : Lean.Nat).
Hypothesis Hn : SubNatRel nR nL.
Notation dT := (ct_decidable_eq Task).
Notation dJ := (ct_decidable_eq Job).
Variables (sR : Schedule.schedule Job nR) (sL : I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_schedule Job dJ nL).
Hypothesis Hs : CsSchedRel Job nR nL sR sL.
Variables (jaR : Job -> nat) (jaL : Job -> Lean.Nat) (cR : Job -> nat) (cL : Job -> Lean.Nat).
Hypotheses (Hja : CsParRel Job jaR jaL) (Hc : CsParRel Job cR cL).
Variable job_task : Job -> Task.
Variables (aR : ArrivalSequence.arrival_sequence Job) (aL : I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrival_sequence Job dJ).
Hypothesis Ha : CsArrRel Job aR aL.
Variables (alR : Affinity.task_affinity Task nR)
  (alL : I.Prosa_Classic_Model_Schedule_Apa_Affinity_Affinity_task_affinity Task dT nL).
Hypothesis Hal : CtafRel Task nR nL Hn alR alL.

Theorem Platform_respects_JLFP_policy_under_weak_APA_correspondence hpR hpL (Hhp : CpRelRel Job hpR hpL) :
  PropSPropRel (Platform.respects_JLFP_policy_under_weak_APA jaR cR job_task aR sR alR hpR)
    (I.Prosa_Classic_Model_Schedule_Apa_Platform_Platform_respects_JLFP_policy_under_weak_APA Task Job dT dJ jaL cL job_task aL nL sL alL hpL).
Proof.
  apply: ct_forall_identity => j. apply: ct_forall_identity => j_hp. apply: (co_forall_ord nR nL Hn) => oR oL Ho.
  apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (cs_arrives_in Job aR aL Ha j).
  apply: ct_imp; first exact (ct_bool_truth _ _ (cf_Schedule_backlogged Job nR nL Hn sR sL Hs jaR jaL Hja cR cL Hc j tR tL Ht)).
  apply: ct_imp; first exact (ct_bool_truth _ _ (cf_Schedule_scheduled_on Job nR nL sR sL Hs j_hp oR oL Ho tR tL Ht)).
  apply: ct_imp; first exact (ct_bool_truth _ _ (cai_can_execute_on Task nR nL Hn alR alL Hal (job_task j) oR oL Ho)).
  exact (ct_bool_truth _ _ (Hhp j_hp j)).
Qed.

End ApaPlatJlfp.

(* ------------------------------------------------------------------ *)
(** * Definitions *)

Theorem InterferenceBoundEDF_edf_specific_interference_bound_correspondence (Task : eqType)
    cR cL (Hc : CsParRel Task cR cL) pR pL (Hp : CsParRel Task pR pL) dR dL (Hd : CsParRel Task dR dL)
    tsk tsk_other RR RL (HR : SubNatRel RR RL) :
  SubNatRel (InterferenceBoundEDF.edf_specific_interference_bound cR pR dR tsk tsk_other RR)
    (I.Prosa_Classic_Analysis_Apa_InterferenceBoundEdf_InterferenceBoundEDF_edf_specific_interference_bound Task (ct_decidable_eq Task) cL pL dL tsk tsk_other RL).
Proof.
  exact (dm_add_correspondence _ _ _ _
           (dm_mul_correspondence _ _ _ _ (dm_div_floor_correspondence _ _ _ _ (Hd tsk) (Hp tsk_other)) (Hc tsk_other))
           (cib_min_rel _ _ _ _ (Hc tsk_other)
              (dm_sub_correspondence _ _ _ _ (dm_mod_correspondence _ _ _ _ (Hd tsk) (Hp tsk_other))
                 (dm_sub_correspondence _ _ _ _ (Hd tsk_other) HR)))).
Qed.

Theorem InterferenceBoundEDF_interference_bound_edf_correspondence (Task : eqType)
    cR cL (Hc : CsParRel Task cR cL) pR pL (Hp : CsParRel Task pR pL) dR dL (Hd : CsParRel Task dR dL)
    tsk deltaR deltaL (Hdelta : SubNatRel deltaR deltaL) tsk_other RR RL (HR : SubNatRel RR RL) :
  SubNatRel (InterferenceBoundEDF.interference_bound_edf cR pR dR tsk deltaR (tsk_other, RR))
    (I.Prosa_Classic_Analysis_Apa_InterferenceBoundEdf_InterferenceBoundEDF_interference_bound_edf Task (ct_decidable_eq Task) cL pL dL tsk deltaL (I.Prod_mk_inst2 Task Lean.Nat tsk_other RL)).
Proof.
  refine (cs_trs HR (fun z => SubNatRel (InterferenceBoundEDF.interference_bound_edf cR pR dR tsk deltaR (tsk_other, RR))
                                (I.Prosa_Classic_Analysis_Apa_InterferenceBoundEdf_InterferenceBoundEDF_interference_bound_edf Task (ct_decidable_eq Task) cL pL dL tsk deltaL
                                   (I.Prod_mk_inst2 Task Lean.Nat tsk_other z))) _).
  exact (cib_min_rel _ _ _ _ (cib_generic Task cR cL Hc pR pL Hp tsk deltaR deltaL Hdelta (tsk_other, RR))
           (InterferenceBoundEDF_edf_specific_interference_bound_correspondence Task cR cL Hc pR pL Hp dR dL Hd
              tsk tsk_other RR _ (sub_nat_rel_canonical RR))).
Qed.

Theorem InterferenceBoundEDF_total_interference_bound_edf_correspondence (Task : eqType)
    cR cL (Hc : CsParRel Task cR cL) pR pL (Hp : CsParRel Task pR pL) dR dL (Hd : CsParRel Task dR dL)
    nR nL (Hn : SubNatRel nR nL) aR aL (Ha : CtafRel Task nR nL Hn aR aL) tsk a'R a'L (Ha' : CafRel nR nL Hn a'R a'L)
    (Rp : seq (Task * nat)) RpL (HRp : ClListRel (cibfp_pair Task) Rp RpL) deltaR deltaL (Hdelta : SubNatRel deltaR deltaL) :
  SubNatRel (InterferenceBoundEDF.total_interference_bound_edf cR pR dR aR tsk a'R Rp deltaR)
    (I.Prosa_Classic_Analysis_Apa_InterferenceBoundEdf_InterferenceBoundEDF_total_interference_bound_edf Task (ct_decidable_eq Task) cL pL dL nL aL tsk a'L RpL deltaL).
Proof.
  rewrite /InterferenceBoundEDF.total_interference_bound_edf.
  unfold I.Prosa_Classic_Analysis_Apa_InterferenceBoundEdf_InterferenceBoundEDF_total_interference_bound_edf.
  refine (cibfp_sumFiltered_rel (Task * nat) _ _ _ (cibfp_pair Task) _ _ _ _ _ _ HRp).
  - intros [a b]. exact (Interference_different_task_in_correspondence Task nR nL Hn aR aL Ha tsk a'R a'L Ha' a).
  - intros [a b]. exact (InterferenceBoundEDF_interference_bound_edf_correspondence Task cR cL Hc pR pL Hp dR dL Hd
                           tsk deltaR deltaL Hdelta a b _ (sub_nat_rel_canonical b)).
Qed.
(* ------------------------------------------------------------------ *)
(** * [unzip1] of a (task, time) pair sequence against [List.map Prod.fst] *)

Lemma cbe_map_fst (Task : Type) : forall (l : seq (Task * nat)),
  Logic.eq (I.List_map (I.Prod_inst2 Task Lean.Nat) Task (I.Prod_fst_inst2 Task Lean.Nat) (cl_map (cibfp_pair Task) l))
    (cl_map cid (unzip1 l)).
Proof.
  elim => [|[a b] l IH]; first reflexivity.
  cbn. exact (f_equal (I.List_cons Task a) IH).
Qed.

Lemma cbe_unzip1 (Task : eqType) (l : seq (Task * nat)) L (Hl : ClListRel (cibfp_pair Task) l L) (s : seq Task) sL
    (Hs : ClListRel cid s sL) :
  PropSPropRel (unzip1 l = s)
    (Lean.eq (I.List_map (I.Prod_inst2 Task Lean.Nat) Task (I.Prod_fst_inst2 Task Lean.Nat) L) sL).
Proof.
  rewrite (cl_list_logic _ _ _ Hl) (cl_list_logic _ _ _ Hs) cbe_map_fst.
  apply prop_sprop_rel_intro.
  - intro E. rewrite E. exact (@Lean.eq_refl _ _).
  - intro E. apply strictly_inhabits. exact (cta_cl_map_inj Task _ _ (imported_eq_to_coq_eq _ _ E)).
Qed.

(* ------------------------------------------------------------------ *)
(** * The fixed-point iteration: lists, options, [iter] and the left fold *)

Definition cs_succ_rel := cta_succ_rel.
Definition cs_ne := cta_ne.
Definition cs_false_rel := cta_false_rel.

Notation cfc_EQ H := (imported_eq_to_coq_eq _ _ H).

Lemma cfc_forall_list (T : Type) (PR : seq T -> Prop) (PL : I.List T -> SProp) :
  (forall sR sL, ClListRel (B := T) cid sR sL -> PropSPropRel (PR sR) (PL sL)) -> PropSPropRel (forall s, PR s) (forall s, PL s).
Proof. exact (cl_forall_list (B := T) cid cid (fun _ => Logic.eq_refl _) PR PL). Qed.

(** Sequences by identity: equality, [rcons], [take]. *)
Lemma cfc_list_eq (T : Type) aR aL (Ha : ClListRel (B := T) cid aR aL) bR bL (Hb : ClListRel (B := T) cid bR bL) :
  PropSPropRel (Logic.eq aR bR) (Lean.eq aL bL).
Proof.
  rewrite -(cfc_EQ Ha) -(cfc_EQ Hb). apply prop_sprop_rel_intro.
  - move=> ->. exact (@Lean.eq_refl _ _).
  - move=> E. apply strictly_inhabits. have E' := f_equal (cl_unmap (fun z : T => z)) (cfc_EQ E).
    by rewrite !(cl_unmap_map (fun z : T => z) (fun z : T => z) (fun _ => Logic.eq_refl _)) in E'.
Qed.

Lemma cfc_map_rcons (A B : Type) (c : A -> B) (l : seq A) (x : A) :
  Logic.eq (cl_map c (rcons l x))
    (I.HAppend_hAppend (I.List B) (I.List B) (I.List B) (I.instHAppendOfAppend (I.List B) (I.List_instAppend B))
       (cl_map c l) (I.List_cons B (c x) (I.List_nil B))).
Proof.
  elim: l => [|y l IH]; first reflexivity.
  change (Logic.eq (I.List_cons B (c y) (cl_map c (rcons l x)))
    (I.HAppend_hAppend (I.List B) (I.List B) (I.List B) (I.instHAppendOfAppend (I.List B) (I.List_instAppend B))
       (I.List_cons B (c y) (cl_map c l)) (I.List_cons B (c x) (I.List_nil B)))).
  rewrite IH. reflexivity.
Qed.

Lemma cfc_map_take (A B : Type) (c : A -> B) : forall (l : seq A) i,
  Logic.eq (cl_map c (take i l)) (I.List_take B (sub_nat_to_imported i) (cl_map c l)).
Proof.
  elim => [|x l IH] [|i]; try reflexivity.
  change (Logic.eq (I.List_cons B (c x) (cl_map c (take i l)))
                   (I.List_cons B (c x) (I.List_take B (sub_nat_to_imported i) (cl_map c l)))).
  by rewrite IH.
Qed.

Lemma cfc_rcons_id (T : Type) lR lL (Hl : ClListRel (B := T) cid lR lL) x :
  ClListRel (B := T) cid (rcons lR x)
    (I.HAppend_hAppend (I.List T) (I.List T) (I.List T) (I.instHAppendOfAppend (I.List T) (I.List_instAppend T))
       lL (I.List_cons T x (I.List_nil T))).
Proof. rewrite /ClListRel -(cfc_EQ Hl). apply: coq_eq_to_imported_eq. exact (cfc_map_rcons _ _ (fun z : T => z) lR x). Qed.

Lemma cfc_take_id (T : Type) lR lL (Hl : ClListRel (B := T) cid lR lL) iR iL (Hi : SubNatRel iR iL) :
  ClListRel (B := T) cid (take iR lR) (I.List_take T iL lL).
Proof.
  rewrite /ClListRel -(cfc_EQ Hl) (cl_nat_logic _ _ Hi). apply: coq_eq_to_imported_eq.
  exact (cfc_map_take _ _ (fun z : T => z) lR iR).
Qed.

(** Sequences of (task, time) pairs ([cibfp_pair]). *)
Lemma cfc_rcons_pair (T : Type) lR lL (Hl : ClListRel (cibfp_pair T) lR lL) a RR RL (HR : SubNatRel RR RL) :
  ClListRel (cibfp_pair T) (rcons lR (a, RR))
    (I.HAppend_hAppend (I.List (I.Prod_inst2 T Lean.Nat)) (I.List (I.Prod_inst2 T Lean.Nat)) (I.List (I.Prod_inst2 T Lean.Nat))
       (I.instHAppendOfAppend (I.List (I.Prod_inst2 T Lean.Nat)) (I.List_instAppend (I.Prod_inst2 T Lean.Nat)))
       lL (I.List_cons (I.Prod_inst2 T Lean.Nat) (I.Prod_mk_inst2 T Lean.Nat a RL) (I.List_nil (I.Prod_inst2 T Lean.Nat)))).
Proof.
  rewrite /ClListRel -(cfc_EQ Hl) (cl_nat_logic _ _ HR). apply: coq_eq_to_imported_eq.
  exact (cfc_map_rcons _ _ (cibfp_pair T) lR (a, RR)).
Qed.

Lemma cfc_take_pair (T : Type) lR lL (Hl : ClListRel (cibfp_pair T) lR lL) iR iL (Hi : SubNatRel iR iL) :
  ClListRel (cibfp_pair T) (take iR lR) (I.List_take (I.Prod_inst2 T Lean.Nat) iL lL).
Proof.
  rewrite /ClListRel -(cfc_EQ Hl) (cl_nat_logic _ _ Hi). apply: coq_eq_to_imported_eq.
  exact (cfc_map_take _ _ (cibfp_pair T) lR iR).
Qed.

Lemma cfc_size_pair (T : Type) lR lL (Hl : ClListRel (cibfp_pair T) lR lL) :
  SubNatRel (size lR) (I.List_length (I.Prod_inst2 T Lean.Nat) lL).
Proof.
  rewrite -(cfc_EQ Hl). clear Hl. apply: coq_eq_to_imported_eq.
  elim: lR => [|x l IH]; first reflexivity.
  exact (f_equal Lean.Nat_succ IH).
Qed.

Lemma cfc_unzip1 (T : Type) lR lL (Hl : ClListRel (cibfp_pair T) lR lL) :
  ClListRel (B := T) cid (unzip1 lR) (I.List_map (I.Prod_inst2 T Lean.Nat) T (I.Prod_fst_inst2 T Lean.Nat) lL).
Proof.
  rewrite /ClListRel -(cfc_EQ Hl). clear Hl. apply: coq_eq_to_imported_eq.
  elim: lR => [|[a b] l IH]; first reflexivity.
  change (Logic.eq (I.List_cons T a (cl_map (fun z : T => z) (unzip1 l)))
                   (I.List_cons T a (I.List_map (I.Prod_inst2 T Lean.Nat) T (I.Prod_fst_inst2 T Lean.Nat) (cl_map (cibfp_pair T) l)))).
  by rewrite IH.
Qed.

(** [sorted] against [List.IsChain] (as in the accepted classic sorting certificate). *)
Inductive CfcTrue : SProp := cfc_true_intro.

Section Chain.
Variables (T : Type) (leR : T -> T -> bool) (leL : T -> T -> I.Bool).
Hypothesis HR : forall a b, CtBoolRel (leR a b) (leL a b).
Notation RL := (fun a b : T => Lean.eq (leL a b) I.Bool_true).

Definition cfc_chain_head (x y : T) (l : I.List T) (H : I.List_IsChain T RL (I.List_cons T x (I.List_cons T y l))) : RL x y :=
  match H in I.List_IsChain _ _ L
    return (match L with I.List_cons a (I.List_cons b _) => RL a b | _ => CfcTrue end) with
  | I.List_IsChain_nil => cfc_true_intro
  | I.List_IsChain_singleton _ => cfc_true_intro
  | I.List_IsChain_cons_cons a b l h _ => h
  end.

Definition cfc_chain_tail (x y : T) (l : I.List T) (H : I.List_IsChain T RL (I.List_cons T x (I.List_cons T y l))) :
    I.List_IsChain T RL (I.List_cons T y l) :=
  match H in I.List_IsChain _ _ L
    return (match L with I.List_cons _ (I.List_cons b l') => I.List_IsChain T RL (I.List_cons T b l') | _ => CfcTrue end) with
  | I.List_IsChain_nil => cfc_true_intro
  | I.List_IsChain_singleton _ => cfc_true_intro
  | I.List_IsChain_cons_cons a b l _ t => t
  end.

Fixpoint cfc_path_forward (x : T) (s : seq T) : path leR x s -> I.List_IsChain T RL (I.List_cons T x (cl_map (fun z : T => z) s)) :=
  match s as s0 return path leR x s0 -> I.List_IsChain T RL (I.List_cons T x (cl_map (fun z : T => z) s0)) with
  | [::] => fun _ => I.List_IsChain_singleton T RL x
  | y :: s' => fun H =>
      I.List_IsChain_cons_cons T RL x y (cl_map (fun z : T => z) s')
        (prop_to_sprop _ _ (ct_bool_truth _ _ (HR x y)) (elimTF andP H).1)
        (cfc_path_forward y s' (elimTF andP H).2)
  end.

Fixpoint cfc_path_backward (x : T) (s : seq T) :
    I.List_IsChain T RL (I.List_cons T x (cl_map (fun z : T => z) s)) -> StrictlyInhabited (path leR x s) :=
  match s as s0 return I.List_IsChain T RL (I.List_cons T x (cl_map (fun z : T => z) s0)) -> StrictlyInhabited (path leR x s0) with
  | [::] => fun _ => strictly_inhabits (Logic.eq_refl true)
  | y :: s' => fun H =>
      match cfc_path_backward y s' (cfc_chain_tail x y _ H) with
      | strictly_inhabits Hp =>
          strictly_inhabits (introT andP (conj (sprop_to_prop _ _ (ct_bool_truth _ _ (HR x y)) (cfc_chain_head x y _ H)) Hp))
      end
  end.

Lemma cfc_sorted_canonical s : PropSPropRel (sorted leR s) (I.List_IsChain T RL (cl_map (fun z : T => z) s)).
Proof.
  apply prop_sprop_rel_intro; destruct s as [|x s].
  - intros _. exact (I.List_IsChain_nil T RL).
  - exact (cfc_path_forward x s).
  - intros _. exact (strictly_inhabits (Logic.eq_refl true)).
  - exact (cfc_path_backward x s).
Qed.

End Chain.

Lemma cfc_sorted (T : eqType) hR hL (Hh : CpRelRel T hR hL) s sL (Hs : ClListRel (B := T) cid s sL) :
  PropSPropRel (sorted hR s) (I.List_IsChain T (fun a b => Lean.eq (hL a b) I.Bool_true) sL).
Proof. rewrite -(cfc_EQ Hs). exact (cfc_sorted_canonical T hR hL Hh s). Qed.

(** FP policies (as in the accepted classic priority certificate). *)
Section Prio.
Variable Task : eqType.
Notation dT := (ct_decidable_eq Task).

End Prio.

(** Global schedulability (as in the accepted classic global schedulability definitions). *)
Lemma cfc_job_misses_no_deadline (Job : eqType) nR nL (Hn : SubNatRel nR nL) sR sL (Hs : CsSchedRel Job nR nL sR sL)
    aR aL (Ha : CsParRel Job aR aL) cR cL (Hc : CsParRel Job cR cL) dR dL (Hd : CsParRel Job dR dL) j :
  CtBoolRel (Schedulability.job_misses_no_deadline aR cR dR sR j)
    (I.Prosa_Classic_Model_Schedule_Global_Schedulability_Schedulability_job_misses_no_deadline Job (ct_decidable_eq Job) aL cL dL nL sL j).
Proof. exact (cf_Schedule_completed Job nR nL Hn sR sL Hs cR cL Hc j _ _ (sub_add_correspondence _ _ _ _ (Ha j) (Hd j))). Qed.

Lemma cfc_task_misses_no_deadline (Task Job : eqType) nR nL (Hn : SubNatRel nR nL) sR sL (Hs : CsSchedRel Job nR nL sR sL)
    aR aL (Ha : CsParRel Job aR aL) cR cL (Hc : CsParRel Job cR cL) dR dL (Hd : CsParRel Job dR dL)
    (job_task : Job -> Task) arrR arrL (Harr : CsArrRel Job arrR arrL) tsk :
  PropSPropRel (Schedulability.task_misses_no_deadline aR cR dR job_task arrR sR tsk)
    (I.Prosa_Classic_Model_Schedule_Global_Schedulability_Schedulability_task_misses_no_deadline Task Job
       (ct_decidable_eq Task) (ct_decidable_eq Job) aL cL dL job_task arrL nL sL tsk).
Proof.
  apply: ct_forall_identity => j.
  apply: ct_imp; first exact (cs_arrives_in Job arrR arrL Harr j).
  apply: ct_imp; first exact (ct_eq_rel Task (job_task j) tsk).
  exact (ct_bool_truth _ _ (cfc_job_misses_no_deadline Job nR nL Hn sR sL Hs aR aL Ha cR cL Hc dR dL Hd j)).
Qed.

Lemma cfc_ite_dec (A : Type) (P : SProp) (dec : I.Decidable P) bR (Hb : CtBoolRel bR (I.Decidable_decide P dec)) (a b : A) :
  Logic.eq (I.ite A P dec a b) (if bR then a else b).
Proof.
  have E := ct_bool_rel_logic _ _ Hb. clear Hb. move: E.
  case: dec => [h|h] E; destruct bR; try reflexivity; discriminate E.
Qed.

Section CfcOpt.
Variable Task : eqType.
Notation dT := (ct_decidable_eq Task).
Notation PT := (I.Prod_inst2 Task Lean.Nat).

Definition cfc_olist (o : option (seq (Task * nat))) : I.Option (I.List PT) :=
  match o with Some l => I.Option_some (I.List PT) (cl_map (cibfp_pair Task) l) | None => I.Option_none (I.List PT) end.
Definition CfcORel (oR : option (seq (Task * nat))) (oL : I.Option (I.List PT)) : SProp := Lean.eq (cfc_olist oR) oL.

Lemma cfc_olist_inj o1 o2 : Logic.eq (cfc_olist o1) (cfc_olist o2) -> Logic.eq o1 o2.
Proof.
  case: o1 => [l1|]; case: o2 => [l2|] //= E; try discriminate E.
  injection E => E'. have E'' := f_equal (cl_unmap (cpair_unpair Task)) E'.
  by rewrite !(cl_unmap_map (cibfp_pair Task) (cpair_unpair Task) (cpair_dc Task)) in E''; rewrite E''.
Qed.

Lemma cfc_oeq oR1 oL1 (H1 : CfcORel oR1 oL1) oR2 oL2 (H2 : CfcORel oR2 oL2) :
  PropSPropRel (Logic.eq oR1 oR2) (Lean.eq oL1 oL2).
Proof.
  rewrite -(cfc_EQ H1) -(cfc_EQ H2). apply prop_sprop_rel_intro.
  - move=> ->. exact (@Lean.eq_refl _ _).
  - move=> E. apply strictly_inhabits. exact (cfc_olist_inj _ _ (cfc_EQ E)).
Qed.

Lemma cfc_osome lR lL (Hl : ClListRel (cibfp_pair Task) lR lL) : CfcORel (Some lR) (I.Option_some (I.List PT) lL).
Proof. rewrite /CfcORel -(cfc_EQ Hl). exact (@Lean.eq_refl _ _). Qed.

Lemma cfc_none_rel oR oL (Ho : CfcORel oR oL) :
  PropSPropRel (is_true (oR == None)) (Lean.eq oL (I.Option_none (I.List PT))).
Proof.
  rewrite -(cfc_EQ Ho). clear Ho. case: oR => [l|]; apply prop_sprop_rel_intro.
  - move=> H. exact (cl_false_elim_s _ H).
  - move=> E. have := cfc_EQ E. discriminate.
  - move=> _. exact (@Lean.eq_refl _ _).
  - move=> _. exact (strictly_inhabits (Logic.eq_refl true)).
Qed.

End CfcOpt.

(** [x \In o] against [optIn x o]. *)
Lemma cfc_optIn (Task : eqType) tsk RR RL (HR : SubNatRel RR RL) oR oL (Ho : CfcORel Task oR oL) dP :
  CtBoolRel ((tsk, RR) \In oR)
    (I.Prosa_Classic_Util_Notation_optIn (I.Prod_inst2 Task Lean.Nat) dP (I.Prod_mk_inst2 Task Lean.Nat tsk RL) oL).
Proof.
  rewrite -(cfc_EQ Ho). clear Ho. destruct oR as [l|].
  - exact (ct_decide_bool _ _ _ (cpair_mem Task tsk RR RL HR l _ (@Lean.eq_refl _ _))).
  - exact (ct_bool_canonical false).
Qed.

(* ------------------------------------------------------------------ *)
(** * The EDF fixed-point iteration over (task, time) pair sequences *)

Lemma cfc_ite_bool (A : Type) bR bL (Hb : CtBoolRel bR bL) (a b : A) :
  Logic.eq (I.ite A (Lean.eq bL I.Bool_true) (I.instDecidableEqBool bL I.Bool_true) a b) (if bR then a else b).
Proof. rewrite (ct_bool_rel_logic _ _ Hb). clear Hb. by case: bR. Qed.

Lemma cfe_map_pair (T : Type) (fR : T * nat -> T * nat) (fL : I.Prod_inst2 T Lean.Nat -> I.Prod_inst2 T Lean.Nat)
    (Hf : forall x, Logic.eq (cibfp_pair T (fR x)) (fL (cibfp_pair T x))) : forall l,
  Logic.eq (cl_map (cibfp_pair T) (map fR l)) (I.List_map (I.Prod_inst2 T Lean.Nat) (I.Prod_inst2 T Lean.Nat) fL (cl_map (cibfp_pair T) l)).
Proof.
  elim => [|x l IH]; first reflexivity.
  change (Logic.eq (I.List_cons _ (cibfp_pair T (fR x)) (cl_map (cibfp_pair T) (map fR l)))
    (I.List_cons _ (fL (cibfp_pair T x)) (I.List_map (I.Prod_inst2 T Lean.Nat) (I.Prod_inst2 T Lean.Nat) fL (cl_map (cibfp_pair T) l)))).
  by rewrite Hf IH.
Qed.

(** Equality of pair sequences (the pair conversion is injective). *)
Lemma cfe_pairs_inj (T : Type) (l1 l2 : seq (T * nat)) :
  Logic.eq (cl_map (cibfp_pair T) l1) (cl_map (cibfp_pair T) l2) -> Logic.eq l1 l2.
Proof.
  move=> E. have E' := f_equal (cl_unmap (cpair_unpair T)) E.
  by rewrite !(cl_unmap_map (cibfp_pair T) (cpair_unpair T) (cpair_dc T)) in E'.
Qed.

Lemma cfe_pairs_eq (T : Type) aR aL (Ha : ClListRel (cibfp_pair T) aR aL) bR bL (Hb : ClListRel (cibfp_pair T) bR bL) :
  PropSPropRel (Logic.eq aR bR) (Lean.eq aL bL).
Proof.
  rewrite -(cfc_EQ Ha) -(cfc_EQ Hb). clear Ha Hb. apply prop_sprop_rel_intro.
  - move=> ->. exact (@Lean.eq_refl _ _).
  - move=> E. apply strictly_inhabits. exact (cfe_pairs_inj T _ _ (cfc_EQ E)).
Qed.

Lemma cfe_pairs_eqb (T : eqType) aR aL (Ha : ClListRel (cibfp_pair T) aR aL) bR bL (Hb : ClListRel (cibfp_pair T) bR bL) dP :
  CtBoolRel (aR == bR) (I.Decidable_decide (Lean.eq aL bL) dP).
Proof.
  apply: ct_decide_bool. have E := cfe_pairs_eq T aR aL Ha bR bL Hb. apply prop_sprop_rel_intro.
  - move=> /eqP H. exact (prop_to_sprop _ _ E H).
  - move=> H. apply strictly_inhabits. apply/eqP. exact (sprop_to_prop _ _ E H).
Qed.

Lemma cfe_ids_eqb (T : eqType) aR aL (Ha : ClListRel (B := T) cid aR aL) bR bL (Hb : ClListRel (B := T) cid bR bL) dP :
  CtBoolRel (aR == bR) (I.Decidable_decide (Lean.eq aL bL) dP).
Proof.
  apply: ct_decide_bool. have E := cfc_list_eq T aR aL Ha bR bL Hb. apply prop_sprop_rel_intro.
  - move=> /eqP H. exact (prop_to_sprop _ _ E H).
  - move=> H. apply strictly_inhabits. apply/eqP. exact (sprop_to_prop _ _ E H).
Qed.

(** MathComp's [iter] on pair sequences against the accepted Lean [Fixedpoint.iter] (fixture equations
    [xfe_iter_zero], [xfe_iter_succ]). *)
Lemma cfe_iter_canonical (T : Type) (fR : seq (T * nat) -> seq (T * nat))
    (fL : I.List (I.Prod_inst2 T Lean.Nat) -> I.List (I.Prod_inst2 T Lean.Nat))
    (Hf : forall l, Logic.eq (fL (cl_map (cibfp_pair T) l)) (cl_map (cibfp_pair T) (fR l))) :
  forall k x, Logic.eq (I.Prosa_Classic_Util_Fixedpoint_iter (I.List (I.Prod_inst2 T Lean.Nat)) (sub_nat_to_imported k) fL
                          (cl_map (cibfp_pair T) x))
                       (cl_map (cibfp_pair T) (iter k fR x)).
Proof.
  elim => [|k IH] x.
  - exact (cfc_EQ (I.Prosa_Validation_ClassicApaBertognaEdfCompInterface_xfe_iter_zero _ fL (cl_map (cibfp_pair T) x))).
  - refine (Logic.eq_trans (cfc_EQ (I.Prosa_Validation_ClassicApaBertognaEdfCompInterface_xfe_iter_succ _ fL (sub_nat_to_imported k) (cl_map (cibfp_pair T) x))) _).
    rewrite IH. exact (Hf (iter k fR x)).
Qed.

Section CfeDefs.
Variable Task : eqType.
Notation dT := (ct_decidable_eq Task).
Notation PT := (I.Prod_inst2 Task Lean.Nat).
Variables (tcR tpR tdR : Task -> nat) (tcL tpL tdL : Task -> Lean.Nat).
Hypotheses (Htc : CsParRel Task tcR tcL) (Htp : CsParRel Task tpR tpL) (Htd : CsParRel Task tdR tdL).
Variables (nR : nat) (nL : Lean.Nat).
Hypothesis Hn : SubNatRel nR nL.
Variables (aR a'R : Affinity.task_affinity Task nR) (aL a'L : I.Prosa_Classic_Model_Schedule_Apa_Affinity_Affinity_task_affinity Task dT nL).
Hypotheses (Ha : CtafRel Task nR nL Hn aR aL) (Ha' : CtafRel Task nR nL Hn a'R a'L).

Lemma cfe_rtb' rR rL (Hr : ClListRel (cibfp_pair Task) rR rL) tsk dR dL (Hd : SubNatRel dR dL) :
  SubNatRel (@ResponseTimeIterationEDF.edf_response_time_bound Task tcR tpR tdR nR aR a'R rR tsk dR)
            (I.Prosa_Classic_Analysis_Apa_BertognaEdfComp_ResponseTimeIterationEDF_edf_response_time_bound Task dT tcL tpL tdL nL aL a'L rL tsk dL).
Proof.
  exact (sub_add_correspondence _ _ _ _ (Htc tsk)
           (dm_div_floor_correspondence _ _ _ _
              (InterferenceBoundEDF_total_interference_bound_edf_correspondence Task tcR tcL Htc tpR tpL Htp tdR tdL Htd
                 nR nL Hn aR aL Ha tsk (a'R tsk) (a'L tsk) (Ha' tsk) rR rL Hr dR dL Hd)
              (caf_card nR nL Hn (a'R tsk) (a'L tsk) (Ha' tsk)))).
Qed.

Lemma cfe_update_bound_eq rR : forall x,
  Logic.eq (cibfp_pair Task (@ResponseTimeIterationEDF.update_bound Task tcR tpR tdR nR aR a'R rR x))
           (I.Prosa_Classic_Analysis_Apa_BertognaEdfComp_ResponseTimeIterationEDF_update_bound Task dT tcL tpL tdL nL aL a'L (cl_map (cibfp_pair Task) rR) (cibfp_pair Task x)).
Proof.
  move=> [tsk R].
  refine (Logic.eq_trans _ (Logic.eq_sym (cfc_EQ (I.Prosa_Validation_ClassicApaBertognaEdfCompInterface_xfe_update_bound Task dT tcL tpL tdL nL aL a'L
                                                    (cl_map (cibfp_pair Task) rR) tsk (sub_nat_to_imported R))))).
  have E := cl_nat_logic _ _ (cfe_rtb' rR _ (@Lean.eq_refl _ _) tsk R _ (sub_nat_rel_canonical R)).
  change (Logic.eq (I.Prod_mk_inst2 Task Lean.Nat tsk (sub_nat_to_imported (@ResponseTimeIterationEDF.edf_response_time_bound Task tcR tpR tdR nR aR a'R rR tsk R)))
    (I.Prod_mk_inst2 Task Lean.Nat tsk (I.Prosa_Classic_Analysis_Apa_BertognaEdfComp_ResponseTimeIterationEDF_edf_response_time_bound Task dT tcL tpL tdL nL aL a'L (cl_map (cibfp_pair Task) rR) tsk (sub_nat_to_imported R)))).
  by rewrite E.
Qed.

Lemma cfe_iteration_eq rR :
  Logic.eq (cl_map (cibfp_pair Task) (@ResponseTimeIterationEDF.edf_rta_iteration Task tcR tpR tdR nR aR a'R rR))
           (I.Prosa_Classic_Analysis_Apa_BertognaEdfComp_ResponseTimeIterationEDF_edf_rta_iteration Task dT tcL tpL tdL nL aL a'L (cl_map (cibfp_pair Task) rR)).
Proof. exact (cfe_map_pair Task _ _ (cfe_update_bound_eq rR) rR). Qed.

Lemma cfe_iteration' rR rL (Hr : ClListRel (cibfp_pair Task) rR rL) :
  ClListRel (cibfp_pair Task) (@ResponseTimeIterationEDF.edf_rta_iteration Task tcR tpR tdR nR aR a'R rR) (I.Prosa_Classic_Analysis_Apa_BertognaEdfComp_ResponseTimeIterationEDF_edf_rta_iteration Task dT tcL tpL tdL nL aL a'L rL).
Proof. rewrite -(cfc_EQ Hr). apply: coq_eq_to_imported_eq. exact (cfe_iteration_eq rR). Qed.

Lemma cfe_map_ub' rR rL (Hr : ClListRel (cibfp_pair Task) rR rL) l lL (Hl : ClListRel (cibfp_pair Task) l lL) :
  ClListRel (cibfp_pair Task) (map (@ResponseTimeIterationEDF.update_bound Task tcR tpR tdR nR aR a'R rR) l)
    (I.List_map PT PT (I.Prosa_Classic_Analysis_Apa_BertognaEdfComp_ResponseTimeIterationEDF_update_bound Task dT tcL tpL tdL nL aL a'L rL) lL).
Proof.
  rewrite -(cfc_EQ Hr) -(cfc_EQ Hl). clear Hr Hl. apply: coq_eq_to_imported_eq.
  exact (cfe_map_pair Task _ _ (cfe_update_bound_eq rR) l).
Qed.

Lemma cfe_init' tsR tsL (Hts : ClListRel (B := Task) cid tsR tsL) :
  ClListRel (cibfp_pair Task) (map (fun t => (t, tcR t)) tsR) (I.Prosa_Classic_Analysis_Apa_BertognaEdfComp_ResponseTimeIterationEDF_initial_state Task dT tcL tsL).
Proof.
  rewrite -(cfc_EQ Hts). clear Hts. apply: coq_eq_to_imported_eq.
  elim: tsR => [|t s IH]; first reflexivity.
  change (Logic.eq (I.List_cons PT (I.Prod_mk_inst2 Task Lean.Nat t (sub_nat_to_imported (tcR t))) (cl_map (cibfp_pair Task) (map (fun t => (t, tcR t)) s)))
    (I.List_cons PT (I.Prod_mk_inst2 Task Lean.Nat t (tcL t)) (I.Prosa_Classic_Analysis_Apa_BertognaEdfComp_ResponseTimeIterationEDF_initial_state Task dT tcL (cl_map (fun z : Task => z) s)))).
  by rewrite IH (cl_nat_logic _ _ (Htc t)).
Qed.

Lemma cfe_max_steps' tsR tsL (Hts : ClListRel (B := Task) cid tsR tsL) :
  SubNatRel (\sum_(tsk <- tsR) (tdR tsk - tcR tsk) + 1) (I.Prosa_Classic_Analysis_Apa_BertognaEdfComp_ResponseTimeIterationEDF_max_steps Task dT tcL tdL tsL).
Proof.
  exact (sub_add_correspondence _ _ _ _
           (cwb_sumSeq_rel Task (fun tsk => tdR tsk - tcR tsk) _ (fun x => ct_sub_rel _ _ _ _ (Htd x) (Htc x)) tsR tsL Hts)
           (sub_nat_rel_canonical 1)).
Qed.

Lemma cfe_f' kR kL (Hk : SubNatRel kR kL) tsR tsL (Hts : ClListRel (B := Task) cid tsR tsL) :
  ClListRel (cibfp_pair Task)
    (iter kR (@ResponseTimeIterationEDF.edf_rta_iteration Task tcR tpR tdR nR aR a'R) (map (fun t => (t, tcR t)) tsR))
    (I.Prosa_Classic_Util_Fixedpoint_iter (I.List PT) kL (I.Prosa_Classic_Analysis_Apa_BertognaEdfComp_ResponseTimeIterationEDF_edf_rta_iteration Task dT tcL tpL tdL nL aL a'L)
       (I.Prosa_Classic_Analysis_Apa_BertognaEdfComp_ResponseTimeIterationEDF_initial_state Task dT tcL tsL)).
Proof.
  have Hi := cfe_init' tsR tsL Hts. rewrite -(cfc_EQ Hi) (cl_nat_logic _ _ Hk). clear Hi.
  apply: coq_eq_to_imported_eq.
  exact (Logic.eq_sym (cfe_iter_canonical Task _ _ (fun l => Logic.eq_sym (cfe_iteration_eq l)) kR _)).
Qed.

Lemma cfe_all_le_deadline_eq : forall rR,
  Logic.eq (I.List_all PT (cl_map (cibfp_pair Task) rR) (I.Prosa_Classic_Analysis_Apa_BertognaEdfComp_ResponseTimeIterationEDF_R_le_deadline Task dT tdL))
           (ct_b2l (all (@ResponseTimeIterationEDF.R_le_deadline Task tdR) rR)).
Proof.
  elim => [|[tsk R] l IH]; first reflexivity.
  have E : Logic.eq (I.Prosa_Classic_Analysis_Apa_BertognaEdfComp_ResponseTimeIterationEDF_R_le_deadline Task dT tdL (I.Prod_mk_inst2 Task Lean.Nat tsk (sub_nat_to_imported R)))
             (I.Decidable_decide (I.LE_le_inst1 Lean.Nat I.instLENat (sub_nat_to_imported R) (tdL tsk))
                (I.Nat_decLe (sub_nat_to_imported R) (tdL tsk))) :=
    cfc_EQ (I.Prosa_Validation_ClassicApaBertognaEdfCompInterface_xfe_R_le_deadline Task dT tdL tsk (sub_nat_to_imported R)).
  change (Logic.eq (I.Bool_and (I.Prosa_Classic_Analysis_Apa_BertognaEdfComp_ResponseTimeIterationEDF_R_le_deadline Task dT tdL (I.Prod_mk_inst2 Task Lean.Nat tsk (sub_nat_to_imported R)))
       (I.List_all PT (cl_map (cibfp_pair Task) l) (I.Prosa_Classic_Analysis_Apa_BertognaEdfComp_ResponseTimeIterationEDF_R_le_deadline Task dT tdL)))
    (ct_b2l ((R <= tdR tsk) && all (@ResponseTimeIterationEDF.R_le_deadline Task tdR) l))).
  rewrite E IH (ct_bool_rel_logic _ _ (ct_decide_le _ _ _ _ (sub_nat_rel_canonical R) (Htd tsk))).
  by case: (R <= tdR tsk).
Qed.

Lemma cfe_all_le_deadline rR rL (Hr : ClListRel (cibfp_pair Task) rR rL) :
  CtBoolRel (all (@ResponseTimeIterationEDF.R_le_deadline Task tdR) rR) (I.List_all PT rL (I.Prosa_Classic_Analysis_Apa_BertognaEdfComp_ResponseTimeIterationEDF_R_le_deadline Task dT tdL)).
Proof.
  rewrite -(cfc_EQ Hr). clear Hr. apply: coq_eq_to_imported_eq. exact (Logic.eq_sym (cfe_all_le_deadline_eq rR)).
Qed.

Lemma cfe_ecb' tsR tsL (Hts : ClListRel (B := Task) cid tsR tsL) :
  CfcORel Task (@ResponseTimeIterationEDF.edf_claimed_bounds Task tcR tpR tdR nR aR a'R tsR) (I.Prosa_Classic_Analysis_Apa_BertognaEdfComp_ResponseTimeIterationEDF_edf_claimed_bounds Task dT tcL tpL tdL nL aL a'L tsL).
Proof.
  have HX := cfe_f' _ _ (cfe_max_steps' tsR tsL Hts) tsR tsL Hts.
  have Hall := cfe_all_le_deadline _ _ HX.
  apply: coq_eq_to_imported_eq.
  refine (Logic.eq_trans _ (Logic.eq_sym (cfc_EQ (I.Prosa_Validation_ClassicApaBertognaEdfCompInterface_xfe_edf_claimed_bounds Task dT tcL tpL tdL nL aL a'L tsL)))).
  rewrite (cfc_ite_bool _ _ _ Hall). rewrite /ResponseTimeIterationEDF.edf_claimed_bounds. cbv zeta.
  case: (all _ _); last reflexivity.
  rewrite /cfc_olist -(cfc_EQ HX). reflexivity.
Qed.

Lemma cfe_edf_schedulable' tsR tsL (Hts : ClListRel (B := Task) cid tsR tsL) :
  CtBoolRel (@ResponseTimeIterationEDF.edf_schedulable Task tcR tpR tdR nR aR a'R tsR) (I.Prosa_Classic_Analysis_Apa_BertognaEdfComp_ResponseTimeIterationEDF_edf_schedulable Task dT tcL tpL tdL nL aL a'L tsL).
Proof. exact (ct_bool_not _ _ (ct_decide_bool _ _ _ (cfc_none_rel Task _ _ (cfe_ecb' tsR tsL Hts)))). Qed.

End CfeDefs.

(** [all_le] and [one_lt] (section-local [Let]s of the source, LEAN_HELPER definitions of the translation). *)
Lemma cfe_zip_all (T : Type) (f : nat -> nat -> bool) (fL : I.Prod (I.Prod_inst2 T Lean.Nat) (I.Prod_inst2 T Lean.Nat) -> I.Bool)
    (Hf : forall a R b S, Logic.eq (fL (I.Prod_mk _ _ (cibfp_pair T (a, R)) (cibfp_pair T (b, S)))) (ct_b2l (f R S))) :
  forall l1 l2, Logic.eq
    (I.List_all _ (I.List_zip _ _ (cl_map (cibfp_pair T) l1) (cl_map (cibfp_pair T) l2)) fL)
    (ct_b2l (all (fun p : (T * nat) * (T * nat) => f p.1.2 p.2.2) (zip l1 l2))).
Proof.
  elim => [|[a R] l1 IH] [|[b S] l2]; try reflexivity.
  change (Logic.eq (I.Bool_and (fL (I.Prod_mk _ _ (cibfp_pair T (a, R)) (cibfp_pair T (b, S))))
                      (I.List_all _ (I.List_zip _ _ (cl_map (cibfp_pair T) l1) (cl_map (cibfp_pair T) l2)) fL))
                   (ct_b2l (f R S && all (fun p : (T * nat) * (T * nat) => f p.1.2 p.2.2) (zip l1 l2)))).
  rewrite Hf IH. by case: (f R S).
Qed.

Lemma cfe_zip_any (T : Type) (f : nat -> nat -> bool) (fL : I.Prod (I.Prod_inst2 T Lean.Nat) (I.Prod_inst2 T Lean.Nat) -> I.Bool)
    (Hf : forall a R b S, Logic.eq (fL (I.Prod_mk _ _ (cibfp_pair T (a, R)) (cibfp_pair T (b, S)))) (ct_b2l (f R S))) :
  forall l1 l2, Logic.eq
    (I.List_any _ (I.List_zip _ _ (cl_map (cibfp_pair T) l1) (cl_map (cibfp_pair T) l2)) fL)
    (ct_b2l (has (fun p : (T * nat) * (T * nat) => f p.1.2 p.2.2) (zip l1 l2))).
Proof.
  elim => [|[a R] l1 IH] [|[b S] l2]; try reflexivity.
  change (Logic.eq (I.Bool_or (fL (I.Prod_mk _ _ (cibfp_pair T (a, R)) (cibfp_pair T (b, S))))
                      (I.List_any _ (I.List_zip _ _ (cl_map (cibfp_pair T) l1) (cl_map (cibfp_pair T) l2)) fL))
                   (ct_b2l (f R S || has (fun p : (T * nat) * (T * nat) => f p.1.2 p.2.2) (zip l1 l2)))).
  rewrite Hf IH. by case: (f R S).
Qed.

Section AllLe.
Variable Task : eqType.
Notation dT := (ct_decidable_eq Task).

Lemma cfe_all_le l1 l1L (H1 : ClListRel (cibfp_pair Task) l1 l1L) l2 l2L (H2 : ClListRel (cibfp_pair Task) l2 l2L) :
  CtBoolRel ((unzip1 l1 == unzip1 l2) && all (fun p : (Task * nat) * (Task * nat) => p.1.2 <= p.2.2) (zip l1 l2))
            (I.Prosa_Classic_Analysis_Apa_BertognaEdfComp_ResponseTimeIterationEDF_all_le Task dT l1L l2L).
Proof.
  apply: ct_bool_and.
  - exact (cfe_ids_eqb Task _ _ (cfc_unzip1 Task _ _ H1) _ _ (cfc_unzip1 Task _ _ H2) _).
  - rewrite -(cfc_EQ H1) -(cfc_EQ H2). clear H1 H2. apply: coq_eq_to_imported_eq. apply: Logic.eq_sym.
    refine (cfe_zip_all Task (fun R S => R <= S) _ _ l1 l2).
    move=> a R b S. exact (ct_bool_rel_logic _ _ (ct_decide_le _ _ _ _ (sub_nat_rel_canonical R) (sub_nat_rel_canonical S))).
Qed.

Lemma cfe_one_lt l1 l1L (H1 : ClListRel (cibfp_pair Task) l1 l1L) l2 l2L (H2 : ClListRel (cibfp_pair Task) l2 l2L) :
  CtBoolRel ((unzip1 l1 == unzip1 l2) && has (fun p : (Task * nat) * (Task * nat) => p.1.2 < p.2.2) (zip l1 l2))
            (I.Prosa_Classic_Analysis_Apa_BertognaEdfComp_ResponseTimeIterationEDF_one_lt Task dT l1L l2L).
Proof.
  apply: ct_bool_and.
  - exact (cfe_ids_eqb Task _ _ (cfc_unzip1 Task _ _ H1) _ _ (cfc_unzip1 Task _ _ H2) _).
  - rewrite -(cfc_EQ H1) -(cfc_EQ H2). clear H1 H2. apply: coq_eq_to_imported_eq. apply: Logic.eq_sym.
    refine (cfe_zip_any Task (fun R S => R < S) _ _ l1 l2).
    move=> a R b S. exact (ct_bool_rel_logic _ _ (ct_decide_lt _ _ _ _ (sub_nat_rel_canonical R) (sub_nat_rel_canonical S))).
Qed.

(** The slack sum [\sum_((tsk, R) <- l) (R - task_cost tsk)] against [sumSeq l (fun (tsk, R) => R - task_cost tsk)]. *)
Lemma cfe_sum_slack (tcR : Task -> nat) l lL (Hl : ClListRel (cibfp_pair Task) l lL)
    (FL : I.Prod_inst2 Task Lean.Nat -> Lean.Nat)
    (HF : forall a R RL, SubNatRel R RL -> SubNatRel (R - tcR a) (FL (I.Prod_mk_inst2 Task Lean.Nat a RL))) :
  SubNatRel (\sum_((tsk, R) <- l) (R - tcR tsk)) (I.Prosa_Util_Sum_sumSeq (I.Prod_inst2 Task Lean.Nat) lL FL).
Proof.
  exact (cibfp_sumSeq_rel (Task * nat) _ (fun p : Task * nat => let (tsk, R) := p in R - tcR tsk) (cibfp_pair Task) FL
    (fun x : Task * nat =>
       match x as x0 return SubNatRel (let (tsk, R) := x0 in R - tcR tsk) (FL (cibfp_pair Task x0)) with
       | (a, R) => HF a R _ (sub_nat_rel_canonical R)
       end) l lL Hl).
Qed.

End AllLe.

(** The definitions of [bertogna_edf_comp], with all inputs as hypotheses. *)
Theorem ResponseTimeIterationEDF_edf_response_time_bound_correspondence (Task : eqType) tcR tcL (Htc : CsParRel Task tcR tcL)
    tpR tpL (Htp : CsParRel Task tpR tpL) tdR tdL (Htd : CsParRel Task tdR tdL) nR nL (Hn : SubNatRel nR nL) aR a'R aL a'L (Ha : CtafRel Task nR nL Hn aR aL) (Ha' : CtafRel Task nR nL Hn a'R a'L)
    rR rL (Hr : ClListRel (cibfp_pair Task) rR rL) tsk dR dL (Hd : SubNatRel dR dL) :
  SubNatRel (@ResponseTimeIterationEDF.edf_response_time_bound Task tcR tpR tdR nR aR a'R rR tsk dR)
            (I.Prosa_Classic_Analysis_Apa_BertognaEdfComp_ResponseTimeIterationEDF_edf_response_time_bound Task (ct_decidable_eq Task) tcL tpL tdL nL aL a'L rL tsk dL).
Proof. exact (cfe_rtb' Task tcR tpR tdR tcL tpL tdL Htc Htp Htd nR nL Hn aR a'R aL a'L Ha Ha' rR rL Hr tsk dR dL Hd). Qed.

Theorem ResponseTimeIterationEDF_R_le_deadline_correspondence (Task : eqType) tdR tdL (Htd : CsParRel Task tdR tdL) tsk RR RL (HR : SubNatRel RR RL) :
  CtBoolRel (@ResponseTimeIterationEDF.R_le_deadline Task tdR (tsk, RR)) (I.Prosa_Classic_Analysis_Apa_BertognaEdfComp_ResponseTimeIterationEDF_R_le_deadline Task (ct_decidable_eq Task) tdL (I.Prod_mk_inst2 Task Lean.Nat tsk RL)).
Proof.
  rewrite (cl_nat_logic _ _ HR) (cfc_EQ (I.Prosa_Validation_ClassicApaBertognaEdfCompInterface_xfe_R_le_deadline Task (ct_decidable_eq Task) tdL tsk (sub_nat_to_imported RR))).
  exact (ct_decide_le _ _ _ _ (sub_nat_rel_canonical RR) (Htd tsk)).
Qed.

Theorem ResponseTimeIterationEDF_update_bound_correspondence (Task : eqType) tcR tcL (Htc : CsParRel Task tcR tcL)
    tpR tpL (Htp : CsParRel Task tpR tpL) tdR tdL (Htd : CsParRel Task tdR tdL) nR nL (Hn : SubNatRel nR nL) aR a'R aL a'L (Ha : CtafRel Task nR nL Hn aR aL) (Ha' : CtafRel Task nR nL Hn a'R a'L)
    rR rL (Hr : ClListRel (cibfp_pair Task) rR rL) x :
  Lean.eq (cibfp_pair Task (@ResponseTimeIterationEDF.update_bound Task tcR tpR tdR nR aR a'R rR x))
          (I.Prosa_Classic_Analysis_Apa_BertognaEdfComp_ResponseTimeIterationEDF_update_bound Task (ct_decidable_eq Task) tcL tpL tdL nL aL a'L rL (cibfp_pair Task x)).
Proof.
  rewrite -(cfc_EQ Hr). apply: coq_eq_to_imported_eq.
  exact (cfe_update_bound_eq Task tcR tpR tdR tcL tpL tdL Htc Htp Htd nR nL Hn aR a'R aL a'L Ha Ha' rR x).
Qed.

Theorem ResponseTimeIterationEDF_edf_rta_iteration_correspondence (Task : eqType) tcR tcL (Htc : CsParRel Task tcR tcL)
    tpR tpL (Htp : CsParRel Task tpR tpL) tdR tdL (Htd : CsParRel Task tdR tdL) nR nL (Hn : SubNatRel nR nL) aR a'R aL a'L (Ha : CtafRel Task nR nL Hn aR aL) (Ha' : CtafRel Task nR nL Hn a'R a'L)
    rR rL (Hr : ClListRel (cibfp_pair Task) rR rL) :
  ClListRel (cibfp_pair Task) (@ResponseTimeIterationEDF.edf_rta_iteration Task tcR tpR tdR nR aR a'R rR) (I.Prosa_Classic_Analysis_Apa_BertognaEdfComp_ResponseTimeIterationEDF_edf_rta_iteration Task (ct_decidable_eq Task) tcL tpL tdL nL aL a'L rL).
Proof. exact (cfe_iteration' Task tcR tpR tdR tcL tpL tdL Htc Htp Htd nR nL Hn aR a'R aL a'L Ha Ha' rR rL Hr). Qed.

Theorem ResponseTimeIterationEDF_edf_claimed_bounds_correspondence (Task : eqType) tcR tcL (Htc : CsParRel Task tcR tcL)
    tpR tpL (Htp : CsParRel Task tpR tpL) tdR tdL (Htd : CsParRel Task tdR tdL) nR nL (Hn : SubNatRel nR nL) aR a'R aL a'L (Ha : CtafRel Task nR nL Hn aR aL) (Ha' : CtafRel Task nR nL Hn a'R a'L)
    tsR tsL (Hts : ClListRel (B := Task) cid tsR tsL) :
  CfcORel Task (@ResponseTimeIterationEDF.edf_claimed_bounds Task tcR tpR tdR nR aR a'R tsR) (I.Prosa_Classic_Analysis_Apa_BertognaEdfComp_ResponseTimeIterationEDF_edf_claimed_bounds Task (ct_decidable_eq Task) tcL tpL tdL nL aL a'L tsL).
Proof. exact (cfe_ecb' Task tcR tpR tdR tcL tpL tdL Htc Htp Htd nR nL Hn aR a'R aL a'L Ha Ha' tsR tsL Hts). Qed.

Theorem ResponseTimeIterationEDF_edf_schedulable_correspondence (Task : eqType) tcR tcL (Htc : CsParRel Task tcR tcL)
    tpR tpL (Htp : CsParRel Task tpR tpL) tdR tdL (Htd : CsParRel Task tdR tdL) nR nL (Hn : SubNatRel nR nL) aR a'R aL a'L (Ha : CtafRel Task nR nL Hn aR aL) (Ha' : CtafRel Task nR nL Hn a'R a'L)
    tsR tsL (Hts : ClListRel (B := Task) cid tsR tsL) :
  CtBoolRel (@ResponseTimeIterationEDF.edf_schedulable Task tcR tpR tdR nR aR a'R tsR) (I.Prosa_Classic_Analysis_Apa_BertognaEdfComp_ResponseTimeIterationEDF_edf_schedulable Task (ct_decidable_eq Task) tcL tpL tdL nL aL a'L tsL).
Proof. exact (cfe_edf_schedulable' Task tcR tpR tdR tcL tpL tdL Htc Htp Htd nR nL Hn aR a'R aL a'L Ha Ha' tsR tsL Hts). Qed.

(** The iteration [f k] of the source (section-local [Let]s unfolded) with all inputs as hypotheses. *)
Lemma cfe_f (Task : eqType) tcR tcL (Htc : CsParRel Task tcR tcL)
    tpR tpL (Htp : CsParRel Task tpR tpL) tdR tdL (Htd : CsParRel Task tdR tdL) nR nL (Hn : SubNatRel nR nL) aR a'R aL a'L (Ha : CtafRel Task nR nL Hn aR aL) (Ha' : CtafRel Task nR nL Hn a'R a'L)
    kR kL (Hk : SubNatRel kR kL) tsR tsL (Hts : ClListRel (B := Task) cid tsR tsL) :
  ClListRel (cibfp_pair Task)
    (iter kR (@ResponseTimeIterationEDF.edf_rta_iteration Task tcR tpR tdR nR aR a'R) (map (fun t => (t, tcR t)) tsR))
    (I.Prosa_Classic_Util_Fixedpoint_iter (I.List (I.Prod_inst2 Task Lean.Nat)) kL
       (I.Prosa_Classic_Analysis_Apa_BertognaEdfComp_ResponseTimeIterationEDF_edf_rta_iteration Task (ct_decidable_eq Task) tcL tpL tdL nL aL a'L) (I.Prosa_Classic_Analysis_Apa_BertognaEdfComp_ResponseTimeIterationEDF_initial_state Task (ct_decidable_eq Task) tcL tsL)).
Proof. exact (cfe_f' Task tcR tpR tdR tcL tpL tdL Htc Htp Htd nR nL Hn aR a'R aL a'L Ha Ha' kR kL Hk tsR tsL Hts). Qed.

Lemma cfe_map_ub (Task : eqType) tcR tcL (Htc : CsParRel Task tcR tcL)
    tpR tpL (Htp : CsParRel Task tpR tpL) tdR tdL (Htd : CsParRel Task tdR tdL) nR nL (Hn : SubNatRel nR nL) aR a'R aL a'L (Ha : CtafRel Task nR nL Hn aR aL) (Ha' : CtafRel Task nR nL Hn a'R a'L)
    rR rL (Hr : ClListRel (cibfp_pair Task) rR rL) l lL (Hl : ClListRel (cibfp_pair Task) l lL) :
  ClListRel (cibfp_pair Task) (map (@ResponseTimeIterationEDF.update_bound Task tcR tpR tdR nR aR a'R rR) l)
    (I.List_map (I.Prod_inst2 Task Lean.Nat) (I.Prod_inst2 Task Lean.Nat) (I.Prosa_Classic_Analysis_Apa_BertognaEdfComp_ResponseTimeIterationEDF_update_bound Task (ct_decidable_eq Task) tcL tpL tdL nL aL a'L rL) lL).
Proof. exact (cfe_map_ub' Task tcR tpR tdR tcL tpL tdL Htc Htp Htd nR nL Hn aR a'R aL a'L Ha Ha' rR rL Hr l lL Hl). Qed.

Lemma cfe_init (Task : eqType) tcR tcL (Htc : CsParRel Task tcR tcL) tsR tsL (Hts : ClListRel (B := Task) cid tsR tsL) :
  ClListRel (cibfp_pair Task) (map (fun t => (t, tcR t)) tsR) (I.Prosa_Classic_Analysis_Apa_BertognaEdfComp_ResponseTimeIterationEDF_initial_state Task (ct_decidable_eq Task) tcL tsL).
Proof. exact (cfe_init' Task tcR tcL Htc tsR tsL Hts). Qed.

Lemma cfe_max_steps (Task : eqType) tcR tcL (Htc : CsParRel Task tcR tcL) tdR tdL (Htd : CsParRel Task tdR tdL)
    tsR tsL (Hts : ClListRel (B := Task) cid tsR tsL) :
  SubNatRel (\sum_(tsk <- tsR) (tdR tsk - tcR tsk) + 1) (I.Prosa_Classic_Analysis_Apa_BertognaEdfComp_ResponseTimeIterationEDF_max_steps Task (ct_decidable_eq Task) tcL tdL tsL).
Proof. exact (cfe_max_steps' Task tcR tdR tcL tdL Htc Htd tsR tsL Hts). Qed.

Theorem ResponseTimeIterationEDF_no_deadline_missed_by_task_correspondence (Task Job : eqType) nR nL (Hn : SubNatRel nR nL)
    sR sL (Hs : CsSchedRel Job nR nL sR sL) aR aL (Ha : CsParRel Job aR aL) cR cL (Hc : CsParRel Job cR cL)
    dR dL (Hd : CsParRel Job dR dL) (job_task : Job -> Task) arrR arrL (Harr : CsArrRel Job arrR arrL) tsk :
  PropSPropRel (@ResponseTimeIterationEDF.no_deadline_missed_by_task Task Job aR cR dR job_task nR arrR sR tsk)
    (I.Prosa_Classic_Analysis_Apa_BertognaEdfComp_ResponseTimeIterationEDF_no_deadline_missed_by_task Task Job (ct_decidable_eq Task) (ct_decidable_eq Job) aL cL dL job_task nL arrL sL tsk).
Proof. exact (cfc_task_misses_no_deadline Task Job nR nL Hn sR sL Hs aR aL Ha cR cL Hc dR dL Hd job_task arrR arrL Harr tsk). Qed.

Theorem ResponseTimeIterationEDF_no_deadline_missed_by_job_correspondence (Job : eqType) nR nL (Hn : SubNatRel nR nL)
    sR sL (Hs : CsSchedRel Job nR nL sR sL) aR aL (Ha : CsParRel Job aR aL) cR cL (Hc : CsParRel Job cR cL)
    dR dL (Hd : CsParRel Job dR dL) j :
  CtBoolRel (@ResponseTimeIterationEDF.no_deadline_missed_by_job Job aR cR dR nR sR j)
    (I.Prosa_Classic_Analysis_Apa_BertognaEdfComp_ResponseTimeIterationEDF_no_deadline_missed_by_job Job (ct_decidable_eq Job) aL cL dL nL sL j).
Proof. exact (cfc_job_misses_no_deadline Job nR nL Hn sR sL Hs aR aL Ha cR cL Hc dR dL Hd j). Qed.

(* ------------------------------------------------------------------ *)
(** * The informative induction principle [bertogna_edf_comp_iteration_inductive]

    Its motive is [Type]-valued, so it is related by maps in both directions: a source (resp. target) inhabitant
    yields a target (resp. source) inhabitant at the totals of every input relation, the motive being transported
    along the pair-sequence conversion ([cibfp_pair], with left inverse [cpair_unpair]) and the iterates related
    by [cfe_f]. *)

Definition cfe_tr {A : Type} (P : A -> Type) {x y : A} (E : Logic.eq x y) (p : P x) : P y :=
  match E in Logic.eq _ z return P z with Logic.eq_refl => p end.

Definition src_bertogna_edf_comp_iteration_inductive (Task : eqType) : Type :=
  ltac:(let X := type of (@ResponseTimeIterationEDF.bertogna_edf_comp_iteration_inductive Task) in exact X).
Definition tgt_bertogna_edf_comp_iteration_inductive (Task : eqType) : Type :=
  ltac:(let X := type of (I.Prosa_Classic_Analysis_Apa_BertognaEdfComp_ResponseTimeIterationEDF_bertogna_edf_comp_iteration_inductive Task (ct_decidable_eq Task)) in exact X).

Theorem ResponseTimeIterationEDF_bertogna_edf_comp_iteration_inductive_correspondence (Task : eqType) :
  Datatypes.prod (src_bertogna_edf_comp_iteration_inductive Task -> tgt_bertogna_edf_comp_iteration_inductive Task)
                 (tgt_bertogna_edf_comp_iteration_inductive Task -> src_bertogna_edf_comp_iteration_inductive Task).
Proof.
  unfold src_bertogna_edf_comp_iteration_inductive, tgt_bertogna_edf_comp_iteration_inductive. split.
  - intros H tcL tpL tdL nL aL a'L tsL PL P0 Pn.
    pose tcR := fun x => sub_nat_to_rocq (tcL x). pose tpR := fun x => sub_nat_to_rocq (tpL x).
    pose tdR := fun x => sub_nat_to_rocq (tdL x). pose nR := sub_nat_to_rocq nL.
    pose tsR := cl_unmap (fun z : Task => z) tsL.
    have Htc : CsParRel Task tcR tcL := fun x => sub_nat_rel_surjective (tcL x).
    have Htp : CsParRel Task tpR tpL := fun x => sub_nat_rel_surjective (tpL x).
    have Htd : CsParRel Task tdR tdL := fun x => sub_nat_rel_surjective (tdL x).
    have Hn : SubNatRel nR nL := sub_nat_rel_surjective nL.
    pose aR := fun tsk => caf_to_source nR nL Hn (aL tsk). pose a'R := fun tsk => caf_to_source nR nL Hn (a'L tsk).
    have Ha : CtafRel Task nR nL Hn aR aL := fun tsk => caf_surjective nR nL Hn (aL tsk).
    have Ha' : CtafRel Task nR nL Hn a'R a'L := fun tsk => caf_surjective nR nL Hn (a'L tsk).
    have Hts : ClListRel (B := Task) cid tsR tsL :=
      coq_eq_to_imported_eq _ _ (cl_map_unmap (fun z : Task => z) (fun z : Task => z) (fun _ => Logic.eq_refl _) tsL).
    pose PR := fun l => PL (cl_map (cibfp_pair Task) l).
    have Ei := cfc_EQ (cfe_init Task tcR tcL Htc tsR tsL Hts).
    have Ef := fun kR kL (Hk : SubNatRel kR kL) =>
      cfc_EQ (cfe_f Task tcR tcL Htc tpR tpL Htp tdR tdL Htd nR nL Hn aR a'R aL a'L Ha Ha' kR kL Hk tsR tsL Hts).
    have Em := cfe_max_steps Task tcR tcL Htc tdR tdL Htd tsR tsL Hts.
    refine (cfe_tr PL (Ef _ _ Em) (H tcR tpR tdR nR aR a'R tsR PR (cfe_tr PL (Logic.eq_sym Ei) P0) _)).
    intros k p.
    exact (cfe_tr PL (Logic.eq_sym (Ef _ _ (cta_succ_rel _ _ (sub_nat_rel_canonical k))))
             (Pn (sub_nat_to_imported k) (cfe_tr PL (Ef _ _ (sub_nat_rel_canonical k)) p))).
  - intros HL tcR tpR tdR nR aR a'R tsR PR P0 Pn.
    pose tcL := fun x => sub_nat_to_imported (tcR x). pose tpL := fun x => sub_nat_to_imported (tpR x).
    pose tdL := fun x => sub_nat_to_imported (tdR x). pose nL := sub_nat_to_imported nR.
    pose tsL := cl_map (fun z : Task => z) tsR.
    have Htc : CsParRel Task tcR tcL := fun x => sub_nat_rel_canonical (tcR x).
    have Htp : CsParRel Task tpR tpL := fun x => sub_nat_rel_canonical (tpR x).
    have Htd : CsParRel Task tdR tdL := fun x => sub_nat_rel_canonical (tdR x).
    have Hn : SubNatRel nR nL := sub_nat_rel_canonical nR.
    pose aL := fun tsk => caf_to_target nR nL Hn (aR tsk). pose a'L := fun tsk => caf_to_target nR nL Hn (a'R tsk).
    have Ha : CtafRel Task nR nL Hn aR aL := fun tsk => caf_canonical nR nL Hn (aR tsk).
    have Ha' : CtafRel Task nR nL Hn a'R a'L := fun tsk => caf_canonical nR nL Hn (a'R tsk).
    have Hts : ClListRel (B := Task) cid tsR tsL := @Lean.eq_refl _ _.
    pose PL := fun lL => PR (cl_unmap (cpair_unpair Task) lL).
    have Eu := fun l => cl_unmap_map (cibfp_pair Task) (cpair_unpair Task) (cpair_dc Task) l.
    have Ei := cfc_EQ (cfe_init Task tcR tcL Htc tsR tsL Hts).
    have Ef := fun kR kL (Hk : SubNatRel kR kL) =>
      cfc_EQ (cfe_f Task tcR tcL Htc tpR tpL Htp tdR tdL Htd nR nL Hn aR a'R aL a'L Ha Ha' kR kL Hk tsR tsL Hts).
    have Em := cfe_max_steps Task tcR tcL Htc tdR tdL Htd tsR tsL Hts.
    have R0 : PL (I.Prosa_Classic_Analysis_Apa_BertognaEdfComp_ResponseTimeIterationEDF_initial_state Task (ct_decidable_eq Task) tcL tsL) :=
      cfe_tr PL Ei (cfe_tr PR (Logic.eq_sym (Eu _)) P0).
    have Rn : forall kL, PL (I.Prosa_Classic_Util_Fixedpoint_iter (I.List (I.Prod_inst2 Task Lean.Nat)) kL
                              (I.Prosa_Classic_Analysis_Apa_BertognaEdfComp_ResponseTimeIterationEDF_edf_rta_iteration Task (ct_decidable_eq Task) tcL tpL tdL nL aL a'L)
                              (I.Prosa_Classic_Analysis_Apa_BertognaEdfComp_ResponseTimeIterationEDF_initial_state Task (ct_decidable_eq Task) tcL tsL)) ->
                         PL (I.Prosa_Classic_Util_Fixedpoint_iter (I.List (I.Prod_inst2 Task Lean.Nat))
                              (I.HAdd_hAdd_inst7 Lean.Nat Lean.Nat Lean.Nat (I.instHAdd_inst1 Lean.Nat I.instAddNat) kL
                                 (I.OfNat_ofNat_inst1 Lean.Nat 1 (I.instOfNatNat 1)))
                              (I.Prosa_Classic_Analysis_Apa_BertognaEdfComp_ResponseTimeIterationEDF_edf_rta_iteration Task (ct_decidable_eq Task) tcL tpL tdL nL aL a'L)
                              (I.Prosa_Classic_Analysis_Apa_BertognaEdfComp_ResponseTimeIterationEDF_initial_state Task (ct_decidable_eq Task) tcL tsL)).
    { intros kL p. have Hk := sub_nat_rel_surjective kL.
      have p1 := cfe_tr PR (Eu _) (cfe_tr PL (Logic.eq_sym (Ef _ _ Hk)) p).
      exact (cfe_tr PL (Ef _ _ (cta_succ_rel _ _ Hk)) (cfe_tr PR (Logic.eq_sym (Eu _)) (Pn _ p1))). }
    exact (cfe_tr PR (Eu _) (cfe_tr PL (Logic.eq_sym (Ef _ _ Em)) (HL tcL tpL tdL nL aL a'L tsL PL R0 Rn))).
Qed.

(* ------------------------------------------------------------------ *)
(** * Statement relation search

    [crel] proves a [PropSPropRel P PL] (and the [SubNatRel], [CtBoolRel], [ClListRel] and relation goals it
    generates) by the structure of the source side [P], as in the accepted classic case-study certificates: each
    binder by the cover lemma of its type's relation, each connective by its [LogicalRelation]/base lemma, and
    each atom by the correspondence lemma of its head (above), whose remaining relation premises are hypotheses
    introduced by the binders.  It only chains lemmas proved in this file or its imports; a goal it cannot close
    makes the proof fail. *)

Ltac crel_hyp :=
  match goal with
  | |- SubNatRel (?f ?x) (?g ?x) => match goal with H : CsParRel _ f g |- _ => exact (H x) end
  | |- CafRel _ _ _ (?f ?x) (?g ?x) => match goal with H : CtafRel _ _ _ _ f g |- _ => exact (H x) end
  | |- CtBoolRel (?f ?x ?y) (?g ?x ?y) => match goal with H : CpRelRel _ f g |- _ => exact (H x y) end
  end.

Ltac crel_isnat T := first [ unify T nat | unify T Lean.Nat ].

Ltac crel_intro_defs T :=
  lazymatch T with
  | Affinity.task_affinity _ ?n => match goal with Hn : SubNatRel n _ |- _ => apply: (cai_forall_taff _ _ _ Hn); intros ? ? ? end
  | Affinity.affinity ?n => match goal with Hn : SubNatRel n _ |- _ => apply: (caf_forall _ _ Hn); intros ? ? ? end
  | ArrivalSequence.arrival_sequence _ => apply: cwb_forall_arr; intros ? ? ?
  | Schedule.schedule _ ?n => match goal with Hn : SubNatRel n _ |- _ => apply: (cs_forall_sched _ _ _ Hn); intros ? ? ? end
  | SporadicTaskset.taskset_of _ => apply: cts_forall; intros ? ? ?
  | seq (_ * _) => apply: cpair_forall; intros ? ? ?
  | seq _ => apply: cfc_forall_list; intros ? ? ?
  | _ => apply: ct_forall_identity; intro
  end.

Ltac crel_intro T :=
  tryif crel_isnat T then (apply: ct_forall_nat; intros ? ? ?) else
  lazymatch T with
  | ?A -> ?B => tryif crel_isnat B then (apply: cs_forall_par; intros ? ? ?) else crel_intro_defs T
  | _ => crel_intro_defs T
  end.

Ltac crel :=
  first
  [ assumption
  | crel_hyp; crel
  | lazymatch goal with
    | |- forall x : prod _ _, _ => intros [? ?]; cbv beta iota zeta; cbn [cibfp_pair fst snd]; crel
    | |- forall _, _ => intro; crel
    | |- CpRelRel _ _ _ => first [ assumption | eapply cpe_edf; crel ]
    | |- SubNatRel (minn _ _) _ => eapply cib_min_rel; crel
    | |- SubNatRel 1 _ => exact (sub_nat_rel_canonical 1)
    | |- SubNatRel 0 _ => exact (sub_nat_rel_canonical 0)
    | |- ClListRel _ (prosa.util.seqset._set_seq ?t) _ => match goal with H : CtsRel _ t _ |- _ => exact H end
    | |- ClListRel _ (iter _ (@ResponseTimeIterationEDF.edf_rta_iteration _ _ _ _ _ _ _) (map _ _)) _ => eapply cfe_f; crel
    | |- ClListRel _ (@ResponseTimeIterationEDF.edf_rta_iteration _ _ _ _ _ _ _ _) _ => eapply ResponseTimeIterationEDF_edf_rta_iteration_correspondence; crel
    | |- ClListRel _ (map (fun _ => (_, _)) _) _ => eapply cfe_init; crel
    | |- ClListRel _ (map (fun _ => @ResponseTimeIterationEDF.update_bound _ _ _ _ _ _ _ _ _) _) _ => eapply cfe_map_ub; crel
    | |- ClListRel _ (map (@ResponseTimeIterationEDF.update_bound _ _ _ _ _ _ _ _) _) _ => eapply cfe_map_ub; crel
    | |- CfcORel _ (@ResponseTimeIterationEDF.edf_claimed_bounds _ _ _ _ _ _ _ _) _ => eapply ResponseTimeIterationEDF_edf_claimed_bounds_correspondence; crel
    | |- CfcORel _ (Some _) _ => eapply cfc_osome; crel
    | |- CtBoolRel (andb (eq_op (unzip1 _) (unzip1 _)) (all _ (zip _ _))) _ => eapply cfe_all_le; crel
    | |- CtBoolRel (andb (eq_op (unzip1 _) (unzip1 _)) (has _ (zip _ _))) _ => eapply cfe_one_lt; crel
    | |- SubNatRel (addn _ 1) (I.Prosa_Classic_Analysis_Apa_BertognaEdfComp_ResponseTimeIterationEDF_max_steps _ _ _ _ _) => eapply cfe_max_steps; crel
    | |- CsParRel _ (fun _ => _) (fun _ => _) => intro; cbv beta; crel
    | |- SubNatRel ?a _ => crel_n a
    | |- CtBoolRel ?b _ => crel_b b
    | |- ClListRel _ ?l _ => crel_l l
    | |- PropSPropRel ?P _ => crel_p P
    end ]
with crel_n a :=
  lazymatch a with
  | addn _ _ => eapply sub_add_correspondence; crel
  | subn _ _ => first [ eapply ct_sub_rel; crel | eapply dm_sub_correspondence; crel ]
  | muln _ _ => first [ eapply dm_mul_correspondence; crel | eapply sub_mul_correspondence; crel ]
  | modn _ _ => eapply dm_mod_correspondence; crel
  | S _ => eapply cs_succ_rel; crel
  | _ => first [ exact (sub_nat_rel_canonical _) | crel_n_defs ]
  end
with crel_b b :=
  lazymatch b with
  | andb _ _ => eapply ct_bool_and; crel
  | negb _ => eapply ct_bool_not; crel
  | leq _ _ => first [ eapply ct_decide_lt; crel | eapply ct_decide_le; crel ]
  | @eq_op ?T _ _ => first [ eapply ct_decide_eq_nat; crel | eapply ct_decide_eq; crel | eapply cfe_pairs_eqb; crel | eapply cfe_ids_eqb; crel ]
  | _ => crel_b_defs
  end
with crel_l l := crel_l_defs
with crel_p P :=
  lazymatch P with
  | forall x : ?T, _ => lazymatch type of T with Prop => eapply ct_imp; crel | _ => crel_intro T; crel end
  | exists x : ?T, _ =>
      tryif crel_isnat T then (apply: ct_exists_nat; intros ? ? ?; crel)
      else (apply: ct_exists_identity; intro; crel)
  | _ /\ _ => eapply ct_and; crel
  | _ <-> _ => fail; crel
  | _ <> _ => eapply cs_ne
  | ~ _ => eapply ct_imp; [crel | exact cs_false_rel]
  | @Logic.eq bool _ _ => eapply ct_bool_eq; crel
  | @Logic.eq ?T _ _ => tryif crel_isnat T then (eapply sub_nat_eq_correspondence; crel) else crel_eq_defs
  | is_true (leq _ _) => first [ eapply sub_nat_lt_correspondence; crel | eapply sub_nat_le_correspondence; crel
                              | eapply ct_bool_truth; crel ]
  | is_true _ => first [ crel_p_defs | eapply ct_bool_truth; crel ]
  | _ => crel_p_defs
  end
with crel_eq_defs := first [ eapply ct_eq_rel | eapply cbe_unzip1; crel | eapply cfc_oeq; crel | eapply cfe_pairs_eq; crel | eapply cfc_list_eq; crel ]
with crel_n_defs := first [ (match goal with |- context [@ResponseTimeIterationEDF.edf_response_time_bound] => idtac end; eapply ResponseTimeIterationEDF_edf_response_time_bound_correspondence; crel)
    | eapply cfc_size_pair; crel
    | eapply cfe_sum_slack; crel
    | eapply caf_card; crel
    | (match goal with |- context [@InterferenceBoundEDF.edf_specific_interference_bound] => idtac end; eapply InterferenceBoundEDF_edf_specific_interference_bound_correspondence; crel)
    | (match goal with |- context [@InterferenceBoundEDF.interference_bound_edf] => idtac end; eapply InterferenceBoundEDF_interference_bound_edf_correspondence; crel)
    | (match goal with |- context [@InterferenceBoundEDF.total_interference_bound_edf] => idtac end; eapply InterferenceBoundEDF_total_interference_bound_edf_correspondence; crel)
    | (match goal with |- context [@WorkloadBound.W] => idtac end; eapply cib_W; crel)
    | eapply dm_div_floor_correspondence; crel
    | eapply cs_list_size; crel
    | eapply ccount_rel; crel
    | eapply cwb_sumSeq_rel; crel
    | eapply (cibfp_sumSeq_rel _ _ _ (cibfp_pair _)); crel
    | eapply cai_sumFiltered_rel; crel
    | eapply (cibfp_sumFiltered_rel _ _ _ _ (cibfp_pair _)); crel
    | eapply cs_ico; crel ]
with crel_b_defs := first [ (match goal with |- context [@ResponseTimeIterationEDF.edf_schedulable] => idtac end; eapply ResponseTimeIterationEDF_edf_schedulable_correspondence; crel)
    | (match goal with |- context [@ResponseTimeIterationEDF.no_deadline_missed_by_job] => idtac end; eapply ResponseTimeIterationEDF_no_deadline_missed_by_job_correspondence; crel)
    | eapply cfc_optIn; crel
    | (match goal with |- context [@Schedulability.job_misses_no_deadline] => idtac end; eapply cfc_job_misses_no_deadline; crel)
    | (match goal with |- context [@Schedule.completed] => idtac end; eapply cf_Schedule_completed; crel)
    | (match goal with |- context [@Schedule.pending] => idtac end; eapply cf_Schedule_pending; crel)
    | (match goal with |- context [@Schedule.backlogged] => idtac end; eapply cf_Schedule_backlogged; crel)
    | (match goal with |- context [@Schedule.scheduled] => idtac end; eapply cf_Schedule_scheduled; crel)
    | (match goal with |- context [@Schedule.scheduled_on] => idtac end; eapply cf_Schedule_scheduled_on; crel)
    | (match goal with |- context [@Interference.different_task_in] => idtac end; eapply Interference_different_task_in_correspondence; crel)
    | (match goal with |- context [@Affinity.can_execute_on] => idtac end; eapply cai_can_execute_on; crel) ]
with crel_l_defs := first [ eapply cfc_rcons_id; crel
    | eapply cfc_rcons_pair; crel
    | eapply cfc_take_id; crel
    | eapply cfc_take_pair; crel
    | eapply cfc_unzip1; crel
    | eapply cts_filter; crel
    | eapply cta_sort_rel; crel ]
with crel_p_defs := first [ (match goal with |- context [@ResponseTimeIterationEDF.no_deadline_missed_by_task] => idtac end; eapply ResponseTimeIterationEDF_no_deadline_missed_by_task_correspondence; crel)
    | (match goal with |- context [@Schedulability.task_misses_no_deadline] => idtac end; eapply cfc_task_misses_no_deadline; crel)
    | (match goal with |- context [@ArrivalSequence.arrives_in] => idtac end; eapply cs_arrives_in; crel)
    | (match goal with |- context [@TaskArrival.sporadic_task_model] => idtac end; eapply cwb_sporadic_task_model; crel)
    | (match goal with |- context [@Job.valid_sporadic_job] => idtac end; eapply cwb_valid_sporadic_job; crel)
    | (match goal with |- context [@SporadicTaskset.valid_sporadic_taskset] => idtac end; eapply cts_valid_taskset; crel)
    | eapply cts_mem; crel
    | eapply cpair_mem; crel
    | eapply cmem_list; crel
    | (match goal with |- context [@Affinity.is_subaffinity] => idtac end; eapply Affinity_is_subaffinity_correspondence; crel)
    | (match goal with |- context [@Platform.respects_affinity] => idtac end; eapply Platform_respects_affinity_correspondence; crel)
    | (match goal with |- context [@Platform.apa_work_conserving] => idtac end; eapply Platform_apa_work_conserving_correspondence; crel)
    | (match goal with |- context [@Platform.respects_JLFP_policy_under_weak_APA] => idtac end; eapply Platform_respects_JLFP_policy_under_weak_APA_correspondence; crel)
    | (match goal with |- context [@Schedule.jobs_come_from_arrival_sequence] => idtac end; eapply cf_Schedule_jobs_come_from_arrival_sequence; crel)
    | (match goal with |- context [@Schedule.sequential_jobs] => idtac end; eapply cf_Schedule_sequential_jobs; crel)
    | (match goal with |- context [@Schedule.jobs_must_arrive_to_execute] => idtac end; eapply cf_Schedule_jobs_must_arrive_to_execute; crel)
    | (match goal with |- context [@Schedule.completed_jobs_dont_execute] => idtac end; eapply cf_Schedule_completed_jobs_dont_execute; crel)
    | eapply cbe_unzip1; crel
    | (match goal with |- context [@ResponseTime.is_response_time_bound_of_task] => idtac end; eapply ResponseTime_is_response_time_bound_of_task_correspondence; crel)
    | eapply cs_mem; crel
    | eapply cs_uniq; crel ].

Ltac crel_spine :=
  repeat lazymatch goal with
  | |- PropSPropRel (forall x : ?T, _) _ =>
      lazymatch type of T with Prop => eapply ct_imp; [ crel | idtac ] | _ => crel_intro T end
  end.

(* ------------------------------------------------------------------ *)
(** * Statements *)

Definition src_edf_claimed_bounds_unzip1_update_bound (Task : eqType) : Prop :=
  ltac:(type_of_term (@ResponseTimeIterationEDF.edf_claimed_bounds_unzip1_update_bound Task)).
Definition tgt_edf_claimed_bounds_unzip1_update_bound (Task : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Analysis_Apa_BertognaEdfComp_ResponseTimeIterationEDF_edf_claimed_bounds_unzip1_update_bound Task (ct_decidable_eq Task))).
Theorem ResponseTimeIterationEDF_edf_claimed_bounds_unzip1_update_bound_correspondence (Task : eqType) :
  PropSPropRel (src_edf_claimed_bounds_unzip1_update_bound Task) (tgt_edf_claimed_bounds_unzip1_update_bound Task).
Proof. unfold src_edf_claimed_bounds_unzip1_update_bound, tgt_edf_claimed_bounds_unzip1_update_bound. rewrite ?/reflexive ?/transitive; cbv beta zeta. crel_spine. crel. Unshelve. all: crel. Qed.

Definition src_edf_claimed_bounds_unzip1_iteration (Task : eqType) : Prop :=
  ltac:(type_of_term (@ResponseTimeIterationEDF.edf_claimed_bounds_unzip1_iteration Task)).
Definition tgt_edf_claimed_bounds_unzip1_iteration (Task : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Analysis_Apa_BertognaEdfComp_ResponseTimeIterationEDF_edf_claimed_bounds_unzip1_iteration Task (ct_decidable_eq Task))).
Theorem ResponseTimeIterationEDF_edf_claimed_bounds_unzip1_iteration_correspondence (Task : eqType) :
  PropSPropRel (src_edf_claimed_bounds_unzip1_iteration Task) (tgt_edf_claimed_bounds_unzip1_iteration Task).
Proof. unfold src_edf_claimed_bounds_unzip1_iteration, tgt_edf_claimed_bounds_unzip1_iteration. rewrite ?/reflexive ?/transitive; cbv beta zeta. crel_spine. crel. Unshelve. all: crel. Qed.

Definition src_edf_claimed_bounds_size (Task : eqType) : Prop :=
  ltac:(type_of_term (@ResponseTimeIterationEDF.edf_claimed_bounds_size Task)).
Definition tgt_edf_claimed_bounds_size (Task : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Analysis_Apa_BertognaEdfComp_ResponseTimeIterationEDF_edf_claimed_bounds_size Task (ct_decidable_eq Task))).
Theorem ResponseTimeIterationEDF_edf_claimed_bounds_size_correspondence (Task : eqType) :
  PropSPropRel (src_edf_claimed_bounds_size Task) (tgt_edf_claimed_bounds_size Task).
Proof. unfold src_edf_claimed_bounds_size, tgt_edf_claimed_bounds_size. rewrite ?/reflexive ?/transitive; cbv beta zeta. crel_spine. crel. Unshelve. all: crel. Qed.

Definition src_edf_claimed_bounds_ge_cost (Task : eqType) : Prop :=
  ltac:(type_of_term (@ResponseTimeIterationEDF.edf_claimed_bounds_ge_cost Task)).
Definition tgt_edf_claimed_bounds_ge_cost (Task : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Analysis_Apa_BertognaEdfComp_ResponseTimeIterationEDF_edf_claimed_bounds_ge_cost Task (ct_decidable_eq Task))).
Theorem ResponseTimeIterationEDF_edf_claimed_bounds_ge_cost_correspondence (Task : eqType) :
  PropSPropRel (src_edf_claimed_bounds_ge_cost Task) (tgt_edf_claimed_bounds_ge_cost Task).
Proof. unfold src_edf_claimed_bounds_ge_cost, tgt_edf_claimed_bounds_ge_cost. rewrite ?/reflexive ?/transitive; cbv beta zeta. crel_spine. crel. Unshelve. all: crel. Qed.

Definition src_edf_claimed_bounds_le_deadline (Task : eqType) : Prop :=
  ltac:(type_of_term (@ResponseTimeIterationEDF.edf_claimed_bounds_le_deadline Task)).
Definition tgt_edf_claimed_bounds_le_deadline (Task : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Analysis_Apa_BertognaEdfComp_ResponseTimeIterationEDF_edf_claimed_bounds_le_deadline Task (ct_decidable_eq Task))).
Theorem ResponseTimeIterationEDF_edf_claimed_bounds_le_deadline_correspondence (Task : eqType) :
  PropSPropRel (src_edf_claimed_bounds_le_deadline Task) (tgt_edf_claimed_bounds_le_deadline Task).
Proof. unfold src_edf_claimed_bounds_le_deadline, tgt_edf_claimed_bounds_le_deadline. rewrite ?/reflexive ?/transitive; cbv beta zeta. crel_spine. crel. Unshelve. all: crel. Qed.

Definition src_edf_claimed_bounds_has_R_for_every_task (Task : eqType) : Prop :=
  ltac:(type_of_term (@ResponseTimeIterationEDF.edf_claimed_bounds_has_R_for_every_task Task)).
Definition tgt_edf_claimed_bounds_has_R_for_every_task (Task : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Analysis_Apa_BertognaEdfComp_ResponseTimeIterationEDF_edf_claimed_bounds_has_R_for_every_task Task (ct_decidable_eq Task))).
Theorem ResponseTimeIterationEDF_edf_claimed_bounds_has_R_for_every_task_correspondence (Task : eqType) :
  PropSPropRel (src_edf_claimed_bounds_has_R_for_every_task Task) (tgt_edf_claimed_bounds_has_R_for_every_task Task).
Proof. unfold src_edf_claimed_bounds_has_R_for_every_task, tgt_edf_claimed_bounds_has_R_for_every_task. rewrite ?/reflexive ?/transitive; cbv beta zeta. crel_spine. crel. Unshelve. all: crel. Qed.

Definition src_all_le_reflexive (Task : eqType) : Prop :=
  ltac:(type_of_term (@ResponseTimeIterationEDF.all_le_reflexive Task)).
Definition tgt_all_le_reflexive (Task : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Analysis_Apa_BertognaEdfComp_ResponseTimeIterationEDF_all_le_reflexive Task (ct_decidable_eq Task))).
Theorem ResponseTimeIterationEDF_all_le_reflexive_correspondence (Task : eqType) :
  PropSPropRel (src_all_le_reflexive Task) (tgt_all_le_reflexive Task).
Proof. unfold src_all_le_reflexive, tgt_all_le_reflexive. rewrite ?/reflexive ?/transitive; cbv beta zeta. crel_spine. crel. Unshelve. all: crel. Qed.

Definition src_all_le_transitive (Task : eqType) : Prop :=
  ltac:(type_of_term (@ResponseTimeIterationEDF.all_le_transitive Task)).
Definition tgt_all_le_transitive (Task : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Analysis_Apa_BertognaEdfComp_ResponseTimeIterationEDF_all_le_transitive Task (ct_decidable_eq Task))).
Theorem ResponseTimeIterationEDF_all_le_transitive_correspondence (Task : eqType) :
  PropSPropRel (src_all_le_transitive Task) (tgt_all_le_transitive Task).
Proof. unfold src_all_le_transitive, tgt_all_le_transitive. rewrite ?/reflexive ?/transitive; cbv beta zeta. crel_spine. crel. Unshelve. all: crel. Qed.

Definition src_bertogna_edf_comp_iteration_preserves_minimum (Task : eqType) : Prop :=
  ltac:(type_of_term (@ResponseTimeIterationEDF.bertogna_edf_comp_iteration_preserves_minimum Task)).
Definition tgt_bertogna_edf_comp_iteration_preserves_minimum (Task : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Analysis_Apa_BertognaEdfComp_ResponseTimeIterationEDF_bertogna_edf_comp_iteration_preserves_minimum Task (ct_decidable_eq Task))).
Theorem ResponseTimeIterationEDF_bertogna_edf_comp_iteration_preserves_minimum_correspondence (Task : eqType) :
  PropSPropRel (src_bertogna_edf_comp_iteration_preserves_minimum Task) (tgt_bertogna_edf_comp_iteration_preserves_minimum Task).
Proof. unfold src_bertogna_edf_comp_iteration_preserves_minimum, tgt_bertogna_edf_comp_iteration_preserves_minimum. rewrite ?/reflexive ?/transitive; cbv beta zeta. crel_spine. crel. Unshelve. all: crel. Qed.

Definition src_bertogna_edf_comp_iteration_preserves_order (Task : eqType) : Prop :=
  ltac:(type_of_term (@ResponseTimeIterationEDF.bertogna_edf_comp_iteration_preserves_order Task)).
Definition tgt_bertogna_edf_comp_iteration_preserves_order (Task : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Analysis_Apa_BertognaEdfComp_ResponseTimeIterationEDF_bertogna_edf_comp_iteration_preserves_order Task (ct_decidable_eq Task))).
Theorem ResponseTimeIterationEDF_bertogna_edf_comp_iteration_preserves_order_correspondence (Task : eqType) :
  PropSPropRel (src_bertogna_edf_comp_iteration_preserves_order Task) (tgt_bertogna_edf_comp_iteration_preserves_order Task).
Proof. unfold src_bertogna_edf_comp_iteration_preserves_order, tgt_bertogna_edf_comp_iteration_preserves_order. rewrite ?/reflexive ?/transitive; cbv beta zeta. crel_spine. crel. Unshelve. all: crel. Qed.

Definition src_bertogna_edf_comp_iteration_monotonic (Task : eqType) : Prop :=
  ltac:(type_of_term (@ResponseTimeIterationEDF.bertogna_edf_comp_iteration_monotonic Task)).
Definition tgt_bertogna_edf_comp_iteration_monotonic (Task : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Analysis_Apa_BertognaEdfComp_ResponseTimeIterationEDF_bertogna_edf_comp_iteration_monotonic Task (ct_decidable_eq Task))).
Theorem ResponseTimeIterationEDF_bertogna_edf_comp_iteration_monotonic_correspondence (Task : eqType) :
  PropSPropRel (src_bertogna_edf_comp_iteration_monotonic Task) (tgt_bertogna_edf_comp_iteration_monotonic Task).
Proof. unfold src_bertogna_edf_comp_iteration_monotonic, tgt_bertogna_edf_comp_iteration_monotonic. rewrite ?/reflexive ?/transitive; cbv beta zeta. crel_spine. crel. Unshelve. all: crel. Qed.

Definition src_bertogna_edf_comp_f_converges_with_no_tasks (Task : eqType) : Prop :=
  ltac:(type_of_term (@ResponseTimeIterationEDF.bertogna_edf_comp_f_converges_with_no_tasks Task)).
Definition tgt_bertogna_edf_comp_f_converges_with_no_tasks (Task : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Analysis_Apa_BertognaEdfComp_ResponseTimeIterationEDF_bertogna_edf_comp_f_converges_with_no_tasks Task (ct_decidable_eq Task))).
Theorem ResponseTimeIterationEDF_bertogna_edf_comp_f_converges_with_no_tasks_correspondence (Task : eqType) :
  PropSPropRel (src_bertogna_edf_comp_f_converges_with_no_tasks Task) (tgt_bertogna_edf_comp_f_converges_with_no_tasks Task).
Proof. unfold src_bertogna_edf_comp_f_converges_with_no_tasks, tgt_bertogna_edf_comp_f_converges_with_no_tasks. rewrite ?/reflexive ?/transitive; cbv beta zeta. crel_spine. crel. Unshelve. all: crel. Qed.

Definition src_bertogna_edf_comp_f_converges_early (Task : eqType) : Prop :=
  ltac:(type_of_term (@ResponseTimeIterationEDF.bertogna_edf_comp_f_converges_early Task)).
Definition tgt_bertogna_edf_comp_f_converges_early (Task : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Analysis_Apa_BertognaEdfComp_ResponseTimeIterationEDF_bertogna_edf_comp_f_converges_early Task (ct_decidable_eq Task))).
Theorem ResponseTimeIterationEDF_bertogna_edf_comp_f_converges_early_correspondence (Task : eqType) :
  PropSPropRel (src_bertogna_edf_comp_f_converges_early Task) (tgt_bertogna_edf_comp_f_converges_early Task).
Proof. unfold src_bertogna_edf_comp_f_converges_early, tgt_bertogna_edf_comp_f_converges_early. rewrite ?/reflexive ?/transitive; cbv beta zeta. crel_spine. crel. Unshelve. all: crel. Qed.

Definition src_bertogna_edf_comp_f_increases (Task : eqType) : Prop :=
  ltac:(type_of_term (@ResponseTimeIterationEDF.bertogna_edf_comp_f_increases Task)).
Definition tgt_bertogna_edf_comp_f_increases (Task : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Analysis_Apa_BertognaEdfComp_ResponseTimeIterationEDF_bertogna_edf_comp_f_increases Task (ct_decidable_eq Task))).
Theorem ResponseTimeIterationEDF_bertogna_edf_comp_f_increases_correspondence (Task : eqType) :
  PropSPropRel (src_bertogna_edf_comp_f_increases Task) (tgt_bertogna_edf_comp_f_increases Task).
Proof. unfold src_bertogna_edf_comp_f_increases, tgt_bertogna_edf_comp_f_increases. rewrite ?/reflexive ?/transitive; cbv beta zeta. crel_spine. crel. Unshelve. all: crel. Qed.

Definition src_bertogna_edf_comp_rt_grows_too_much (Task : eqType) : Prop :=
  ltac:(type_of_term (@ResponseTimeIterationEDF.bertogna_edf_comp_rt_grows_too_much Task)).
Definition tgt_bertogna_edf_comp_rt_grows_too_much (Task : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Analysis_Apa_BertognaEdfComp_ResponseTimeIterationEDF_bertogna_edf_comp_rt_grows_too_much Task (ct_decidable_eq Task))).
Theorem ResponseTimeIterationEDF_bertogna_edf_comp_rt_grows_too_much_correspondence (Task : eqType) :
  PropSPropRel (src_bertogna_edf_comp_rt_grows_too_much Task) (tgt_bertogna_edf_comp_rt_grows_too_much Task).
Proof. unfold src_bertogna_edf_comp_rt_grows_too_much, tgt_bertogna_edf_comp_rt_grows_too_much. rewrite ?/reflexive ?/transitive; cbv beta zeta. crel_spine. crel. Unshelve. all: crel. Qed.

Definition src_edf_claimed_bounds_finds_fixed_point_of_list (Task : eqType) : Prop :=
  ltac:(type_of_term (@ResponseTimeIterationEDF.edf_claimed_bounds_finds_fixed_point_of_list Task)).
Definition tgt_edf_claimed_bounds_finds_fixed_point_of_list (Task : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Analysis_Apa_BertognaEdfComp_ResponseTimeIterationEDF_edf_claimed_bounds_finds_fixed_point_of_list Task (ct_decidable_eq Task))).
Theorem ResponseTimeIterationEDF_edf_claimed_bounds_finds_fixed_point_of_list_correspondence (Task : eqType) :
  PropSPropRel (src_edf_claimed_bounds_finds_fixed_point_of_list Task) (tgt_edf_claimed_bounds_finds_fixed_point_of_list Task).
Proof. unfold src_edf_claimed_bounds_finds_fixed_point_of_list, tgt_edf_claimed_bounds_finds_fixed_point_of_list. rewrite ?/reflexive ?/transitive; cbv beta zeta. crel_spine. crel. Unshelve. all: crel. Qed.

Definition src_edf_claimed_bounds_finds_least_fixed_point (Task : eqType) : Prop :=
  ltac:(type_of_term (@ResponseTimeIterationEDF.edf_claimed_bounds_finds_least_fixed_point Task)).
Definition tgt_edf_claimed_bounds_finds_least_fixed_point (Task : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Analysis_Apa_BertognaEdfComp_ResponseTimeIterationEDF_edf_claimed_bounds_finds_least_fixed_point Task (ct_decidable_eq Task))).
Theorem ResponseTimeIterationEDF_edf_claimed_bounds_finds_least_fixed_point_correspondence (Task : eqType) :
  PropSPropRel (src_edf_claimed_bounds_finds_least_fixed_point Task) (tgt_edf_claimed_bounds_finds_least_fixed_point Task).
Proof. unfold src_edf_claimed_bounds_finds_least_fixed_point, tgt_edf_claimed_bounds_finds_least_fixed_point. rewrite ?/reflexive ?/transitive; cbv beta zeta. crel_spine. crel. Unshelve. all: crel. Qed.

Definition src_edf_claimed_bounds_finds_fixed_point_for_each_bound (Task : eqType) : Prop :=
  ltac:(type_of_term (@ResponseTimeIterationEDF.edf_claimed_bounds_finds_fixed_point_for_each_bound Task)).
Definition tgt_edf_claimed_bounds_finds_fixed_point_for_each_bound (Task : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Analysis_Apa_BertognaEdfComp_ResponseTimeIterationEDF_edf_claimed_bounds_finds_fixed_point_for_each_bound Task (ct_decidable_eq Task))).
Theorem ResponseTimeIterationEDF_edf_claimed_bounds_finds_fixed_point_for_each_bound_correspondence (Task : eqType) :
  PropSPropRel (src_edf_claimed_bounds_finds_fixed_point_for_each_bound Task) (tgt_edf_claimed_bounds_finds_fixed_point_for_each_bound Task).
Proof. unfold src_edf_claimed_bounds_finds_fixed_point_for_each_bound, tgt_edf_claimed_bounds_finds_fixed_point_for_each_bound. rewrite ?/reflexive ?/transitive; cbv beta zeta. crel_spine. crel. Unshelve. all: crel. Qed.

Definition src_edf_analysis_yields_response_time_bounds (Task Job : eqType) : Prop :=
  forall p0 p1 p2 : Task -> nat,
    ltac:(type_of_term (@ResponseTimeIterationEDF.edf_analysis_yields_response_time_bounds Task p0 p1 p2 Job)).
Definition tgt_edf_analysis_yields_response_time_bounds (Task Job : eqType) : SProp :=
  forall p0 p1 p2 : Task -> Lean.Nat,
    ltac:(type_of_term (I.Prosa_Classic_Analysis_Apa_BertognaEdfComp_ResponseTimeIterationEDF_edf_analysis_yields_response_time_bounds Task (ct_decidable_eq Task) p0 p1 p2 Job (ct_decidable_eq Job))).
Theorem ResponseTimeIterationEDF_edf_analysis_yields_response_time_bounds_correspondence (Task Job : eqType) :
  PropSPropRel (src_edf_analysis_yields_response_time_bounds Task Job) (tgt_edf_analysis_yields_response_time_bounds Task Job).
Proof. unfold src_edf_analysis_yields_response_time_bounds, tgt_edf_analysis_yields_response_time_bounds. rewrite ?/reflexive ?/transitive; cbv beta zeta. crel_spine. crel. Unshelve. all: crel. Qed.

Definition src_taskset_schedulable_by_edf_rta (Task Job : eqType) : Prop :=
  forall p0 p1 p2 : Task -> nat,
    ltac:(type_of_term (@ResponseTimeIterationEDF.taskset_schedulable_by_edf_rta Task p0 p1 p2 Job)).
Definition tgt_taskset_schedulable_by_edf_rta (Task Job : eqType) : SProp :=
  forall p0 p1 p2 : Task -> Lean.Nat,
    ltac:(type_of_term (I.Prosa_Classic_Analysis_Apa_BertognaEdfComp_ResponseTimeIterationEDF_taskset_schedulable_by_edf_rta Task (ct_decidable_eq Task) p0 p1 p2 Job (ct_decidable_eq Job))).
Theorem ResponseTimeIterationEDF_taskset_schedulable_by_edf_rta_correspondence (Task Job : eqType) :
  PropSPropRel (src_taskset_schedulable_by_edf_rta Task Job) (tgt_taskset_schedulable_by_edf_rta Task Job).
Proof. unfold src_taskset_schedulable_by_edf_rta, tgt_taskset_schedulable_by_edf_rta. rewrite ?/reflexive ?/transitive; cbv beta zeta. crel_spine. crel. Unshelve. all: crel. Qed.

Definition src_jobs_schedulable_by_edf_rta (Task Job : eqType) : Prop :=
  forall p0 p1 p2 : Task -> nat,
    ltac:(type_of_term (@ResponseTimeIterationEDF.jobs_schedulable_by_edf_rta Task p0 p1 p2 Job)).
Definition tgt_jobs_schedulable_by_edf_rta (Task Job : eqType) : SProp :=
  forall p0 p1 p2 : Task -> Lean.Nat,
    ltac:(type_of_term (I.Prosa_Classic_Analysis_Apa_BertognaEdfComp_ResponseTimeIterationEDF_jobs_schedulable_by_edf_rta Task (ct_decidable_eq Task) p0 p1 p2 Job (ct_decidable_eq Job))).
Theorem ResponseTimeIterationEDF_jobs_schedulable_by_edf_rta_correspondence (Task Job : eqType) :
  PropSPropRel (src_jobs_schedulable_by_edf_rta Task Job) (tgt_jobs_schedulable_by_edf_rta Task Job).
Proof. unfold src_jobs_schedulable_by_edf_rta, tgt_jobs_schedulable_by_edf_rta. rewrite ?/reflexive ?/transitive; cbv beta zeta. crel_spine. crel. Unshelve. all: crel. Qed.
