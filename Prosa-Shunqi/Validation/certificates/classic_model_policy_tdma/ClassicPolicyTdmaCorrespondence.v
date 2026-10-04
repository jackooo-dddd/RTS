From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq bigop div.
From prosa Require Import util.seqset classic.model.time classic.util.list classic.model.policy_tdma.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedClassicPolicyTdma.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence ClassicPolicyTdmaBase ClassicPolicyTdmaList.

Module I := ImportedClassicPolicyTdma.
Local Open Scope nat_scope.

(** Certificates for [classic/model/policy_tdma.v] (ProsaBuddy classic, commit f692cb7).

    Inputs: the task type is an [eqType], identified, with the Lean [DecidableEq] instance given by the eqType's decision
    procedure ([ct_decidable_eq]); task sets [{set Task}] by the elementwise image of their sequence ([CtdSetRel],
    two-way totals); slot functions [Task -> duration] pointwise through [SubNatRel]; slot orders [rel Task] pointwise
    on Booleans (two-way totals); times by [SubNatRel].

    Computation: MathComp's sequence sums [\sum_(x <- s) F x] and [\sum_(x <- s | P x) F x] against the v0.6
    [sumSeq]/[sumFiltered] through the exported kernel-checked constructor equations (as in the accepted v0.6
    request-bound-function certificates); [%%] and [-] against Lean [%] and truncated [-] through the accepted
    Euclidean bridge ([DivModInterface] equations, re-bound); [x != y] against [!decide (x = y)].

    Statements: the source side is the exact elaborated type of the pinned lemma (via [type of]; the source proof
    is not used). *)

Ltac type_of_term t := let T := type of t in exact T.
Notation cid := (fun z => z).

(* ------------------------------------------------------------------ *)
(** * Helpers (re-bound to this export from the accepted classic certificates) *)

(** Base definitions (as in the accepted classic base library), provided here when this export's library lacks them. *)

(* ------------------------------------------------------------------ *)
(** * Generic covers and helpers *)

Lemma ctd_forall_cover (A B : Type) (Rel : A -> B -> SProp) (toB : A -> B) (toA : B -> A)
    (HB : forall a, Rel a (toB a)) (HA : forall b, Rel (toA b) b) (PR : A -> Prop) (PL : B -> SProp) :
  (forall a b, Rel a b -> PropSPropRel (PR a) (PL b)) -> PropSPropRel (forall a, PR a) (forall b, PL b).
Proof.
  intro H. apply prop_sprop_rel_intro.
  - intros HR b. exact (prop_to_sprop _ _ (H _ _ (HA b)) (HR _)).
  - intro HL. apply strictly_inhabits. intro a. exact (sprop_to_prop _ _ (H _ _ (HB a)) (HL _)).
Qed.

Lemma ctd_false_rel : PropSPropRel Logic.False I.False.
Proof.
  apply prop_sprop_rel_intro.
  - exact ct_coq_false_to_target.
  - exact ct_target_false_to_strict.
Qed.

Lemma ctd_ne (T : Type) (x y : T) : PropSPropRel (x <> y) (I.Ne T x y).
Proof. exact (ct_imp _ _ _ _ (ct_eq_rel T x y) ctd_false_rel). Qed.

Lemma ctd_mem (T : eqType) x s sL : ClListRel cid s sL ->
  PropSPropRel (x \in s) (I.Membership_mem T (I.List T) (I.List_instMembership T) sL x).
Proof. exact (cl_mem_rel_list T T cid cid (fun _ => Logic.eq_refl _) x s sL). Qed.

Lemma ctd_uniq (T : eqType) s sL : ClListRel cid s sL -> PropSPropRel (uniq s) (I.List_Nodup T sL).
Proof. exact (cl_uniq_rel_list T T cid cid (fun _ => Logic.eq_refl _) (fun _ => Logic.eq_refl _) s sL). Qed.

Lemma ctd_unmap_rel (T : Type) (l : I.List T) : ClListRel cid (cl_unmap cid l) l.
Proof. apply: coq_eq_to_imported_eq. exact (cl_map_unmap cid cid (fun _ => Logic.eq_refl _) l). Qed.

Lemma ctd_cl_map_inj (T : Type) (s1 s2 : seq T) : Logic.eq (cl_map cid s1) (cl_map cid s2) -> Logic.eq s1 s2.
Proof.
  intro E. rewrite -(cl_unmap_map cid cid (fun _ => Logic.eq_refl _) s1) -(cl_unmap_map cid cid (fun _ => Logic.eq_refl _) s2).
  by rewrite E.
Qed.

Lemma ctd_succ_rel nR nL : SubNatRel nR nL ->
  SubNatRel nR.+1 (I.HAdd_hAdd_inst7 Lean.Nat Lean.Nat Lean.Nat (I.instHAdd_inst1 Lean.Nat I.instAddNat) nL
                     (I.OfNat_ofNat_inst1 Lean.Nat 1 (I.instOfNatNat 1))).
Proof. intro Hn. exact (sub_imported_eq_congr Lean.Nat_succ _ _ Hn). Qed.

(* ------------------------------------------------------------------ *)
(** * Big concatenation over a half-open interval (as in the accepted arrival_sequence certificate) *)

Definition CtdParRel (T : Type) (pR : T -> nat) (pL : T -> Lean.Nat) : SProp := forall x, SubNatRel (pR x) (pL x).

Lemma ctd_forall_par (T : Type) (PR : (T -> nat) -> Prop) (PL : (T -> Lean.Nat) -> SProp) :
  (forall pR pL, CtdParRel T pR pL -> PropSPropRel (PR pR) (PL pL)) -> PropSPropRel (forall p, PR p) (forall p, PL p).
Proof.
  exact (ctd_forall_cover _ _ (CtdParRel T) (fun pR j => sub_nat_to_imported (pR j)) (fun pL j => sub_nat_to_rocq (pL j))
           (fun pR j => sub_nat_rel_canonical (pR j)) (fun pL j => sub_nat_rel_surjective (pL j)) PR PL).
Qed.

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

Definition dm_imported_zero : Lean.Nat :=
  I.OfNat_ofNat_inst1 Lean.Nat Lean.Nat_zero
    (I.instOfNatNat Lean.Nat_zero).

Definition dm_imported_one : Lean.Nat :=
  I.OfNat_ofNat_inst1 Lean.Nat
    (Lean.Nat_succ Lean.Nat_zero)
    (I.instOfNatNat (Lean.Nat_succ Lean.Nat_zero)).

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

Lemma dm_bool_false_no_truth (b : bool) :
  Logic.eq b false -> is_true b -> Logic.False.
Proof. destruct b; cbn; intros Hfalse Htruth; discriminate. Qed.

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



(* ------------------------------------------------------------------ *)
(** * Sequence sums against [sumSeq] / [sumFiltered] (as in the accepted v0.6 request-bound-function certificates) *)

Section Sums.
Variable X : Type.
Variable FR : X -> nat.
Variable FL : X -> Lean.Nat.
Hypothesis HF : forall x, SubNatRel (FR x) (FL x).

Lemma ctd_sum_canonical (xs : seq X) :
  SubNatRel (\sum_(x <- xs) FR x) (I.Prosa_Util_Sum_sumSeq X (cl_map cid xs) FL).
Proof.
  induction xs as [|x xs IH].
  - rewrite big_nil.
    exact (sub_imported_eq_sym _ _ (I.Prosa_Validation_ClassicPolicyTdmaInterface_production_sumSeq_nil X FL)).
  - rewrite big_cons. cbn [cl_map].
    refine (sub_imported_eq_trans _ _ _ _ (sub_imported_eq_sym _ _
      (I.Prosa_Validation_ClassicPolicyTdmaInterface_production_sumSeq_cons X FL x (cl_map cid xs)))).
    exact (sub_add_correspondence _ _ _ _ (HF x) IH).
Qed.

Lemma ctd_sum_rel xsR xsL : ClListRel cid xsR xsL ->
  SubNatRel (\sum_(x <- xsR) FR x) (I.Prosa_Util_Sum_sumSeq X xsL FL).
Proof.
  intro Hxs.
  exact (sub_imported_eq_trans _ _ _ (ctd_sum_canonical xsR)
    (sub_imported_eq_congr (fun l => I.Prosa_Util_Sum_sumSeq X l FL) _ _ Hxs)).
Qed.

Variable PR : X -> bool.
Variable PL : X -> I.Bool.
Hypothesis HP : forall x, CtBoolRel (PR x) (PL x).

Lemma ctd_sum_filtered_canonical (xs : seq X) :
  SubNatRel (\sum_(x <- xs | PR x) FR x) (I.Prosa_Util_Sum_sumFiltered X (cl_map cid xs) PL FL).
Proof.
  induction xs as [|x xs IH].
  - rewrite big_nil.
    exact (sub_imported_eq_sym _ _ (I.Prosa_Validation_ClassicPolicyTdmaInterface_production_sumFiltered_nil X PL FL)).
  - rewrite big_cons. cbn [cl_map].
    have Hx := HP x. unfold CtBoolRel in Hx.
    destruct (PR x).
    + refine (sub_imported_eq_trans _ _ _ _ (sub_imported_eq_sym _ _
        (I.Prosa_Validation_ClassicPolicyTdmaInterface_production_sumFiltered_cons_true
          X PL FL x (cl_map cid xs) (sub_imported_eq_sym _ _ Hx)))).
      exact (sub_add_correspondence _ _ _ _ (HF x) IH).
    + exact (sub_imported_eq_trans _ _ _ IH (sub_imported_eq_sym _ _
        (I.Prosa_Validation_ClassicPolicyTdmaInterface_production_sumFiltered_cons_false
          X PL FL x (cl_map cid xs) (sub_imported_eq_sym _ _ Hx)))).
Qed.

Lemma ctd_sum_filtered_rel xsR xsL : ClListRel cid xsR xsL ->
  SubNatRel (\sum_(x <- xsR | PR x) FR x) (I.Prosa_Util_Sum_sumFiltered X xsL PL FL).
Proof.
  intro Hxs.
  exact (sub_imported_eq_trans _ _ _ (ctd_sum_filtered_canonical xsR)
    (sub_imported_eq_congr (fun l => I.Prosa_Util_Sum_sumFiltered X l PL FL) _ _ Hxs)).
Qed.
End Sums.

(* ------------------------------------------------------------------ *)
(** * Task sets, slots and slot orders *)

Section Rel.
Variable Task : eqType.
Notation dT := (ct_decidable_eq Task).
Notation LSet := (I.Prosa_Util_Seqset_set Task dT).

Definition CtdSetRel (sR : {set Task}) (sL : LSet) : SProp :=
  ClListRel cid (@prosa.util.seqset._set_seq Task sR) (I.Prosa_Util_Seqset_set_val Task dT sL).

Lemma ctd_uniq_rel (xs : seq Task) : PropSPropRel (uniq xs) (I.List_Nodup Task (cl_map cid xs)).
Proof. exact (cl_uniq_rel Task Task cid cid (fun _ => Logic.eq_refl _) (fun _ => Logic.eq_refl _) xs). Qed.

Definition ctd_set_to_target (sR : {set Task}) : LSet :=
  match sR with
  | @prosa.util.seqset.Build_set _ xs Hu =>
      I.Prosa_Util_Seqset_set_mk Task dT (cl_map cid xs) (prop_to_sprop _ _ (ctd_uniq_rel xs) Hu)
  end.

Lemma ctd_import_uniq (xs : I.List Task) (Hn : I.List_Nodup Task xs) : uniq (cl_unmap cid xs).
Proof.
  apply (sprop_to_prop _ _ (ctd_uniq_rel (cl_unmap cid xs))).
  rewrite (cl_map_unmap cid cid (fun _ => Logic.eq_refl _) xs). exact Hn.
Qed.

Definition ctd_set_to_source (sL : LSet) : {set Task} :=
  match sL with
  | I.Prosa_Util_Seqset_set_mk xs Hn => @prosa.util.seqset.Build_set Task (cl_unmap cid xs) (ctd_import_uniq xs Hn)
  end.

Lemma ctd_set_canonical sR : CtdSetRel sR (ctd_set_to_target sR).
Proof. destruct sR. exact (@Lean.eq_refl _ _). Qed.

Lemma ctd_set_surjective sL : CtdSetRel (ctd_set_to_source sL) sL.
Proof.
  destruct sL as [xs Hn]. unfold CtdSetRel. cbn.
  exact (coq_eq_to_imported_eq _ _ (cl_map_unmap cid cid (fun _ => Logic.eq_refl _) xs)).
Qed.

Lemma ctd_forall_set (PR : {set Task} -> Prop) (PL : LSet -> SProp) :
  (forall sR sL, CtdSetRel sR sL -> PropSPropRel (PR sR) (PL sL)) -> PropSPropRel (forall s, PR s) (forall s, PL s).
Proof. exact (ctd_forall_cover _ _ CtdSetRel ctd_set_to_target ctd_set_to_source ctd_set_canonical ctd_set_surjective PR PL). Qed.

Lemma ctd_set_mem x sR sL (Hs : CtdSetRel sR sL) :
  PropSPropRel (x \in sR) (I.Membership_mem Task LSet (I.Prosa_Util_Seqset_instMembershipSet Task dT) sL x).
Proof. exact (cl_mem_rel_list Task Task cid cid (fun _ => Logic.eq_refl _) x _ _ Hs). Qed.

Definition CtdOrdRel (oR : rel Task) (oL : Task -> Task -> I.Bool) : SProp := forall a b, CtBoolRel (oR a b) (oL a b).

Definition ctd_ord_to_target (oR : rel Task) : Task -> Task -> I.Bool := fun a b => ct_b2l (oR a b).
Definition ctd_ord_to_source (oL : Task -> Task -> I.Bool) : rel Task := fun a b => ct_l2b (oL a b).

Lemma ctd_ord_canonical oR : CtdOrdRel oR (ctd_ord_to_target oR).
Proof. intros a b. exact (ct_bool_canonical _). Qed.

Lemma ctd_ord_surjective oL : CtdOrdRel (ctd_ord_to_source oL) oL.
Proof. intros a b. exact (ct_bool_surjective _). Qed.

Lemma ctd_forall_ord (PR : rel Task -> Prop) (PL : (Task -> Task -> I.Bool) -> SProp) :
  (forall oR oL, CtdOrdRel oR oL -> PropSPropRel (PR oR) (PL oL)) -> PropSPropRel (forall o, PR o) (forall o, PL o).
Proof. exact (ctd_forall_cover _ _ CtdOrdRel ctd_ord_to_target ctd_ord_to_source ctd_ord_canonical ctd_ord_surjective PR PL). Qed.

Lemma ctd_neq x y : CtBoolRel (x != y) (I.Bool_not (I.Decidable_decide (Lean.eq x y) (dT x y))).
Proof. exact (ct_bool_not _ _ (ct_decide_eq Task x y)). Qed.
End Rel.

(* ------------------------------------------------------------------ *)
(** * Definitions *)

Section Defs.
Variable Task : eqType.
Notation dT := (ct_decidable_eq Task).

Theorem PolicyTDMA_TDMA_slot_correspondence :
  And (forall sR : PolicyTDMA.TDMA_slot Task, CtdParRel Task sR (fun x => sub_nat_to_imported (sR x)))
      (forall sL : I.Prosa_Classic_Model_PolicyTdma_PolicyTDMA_TDMA_slot Task dT, CtdParRel Task (fun x => sub_nat_to_rocq (sL x)) sL).
Proof.
  exact (And_intro _ _ (fun sR x => sub_nat_rel_canonical (sR x)) (fun sL x => sub_nat_rel_surjective (sL x))).
Qed.

Theorem PolicyTDMA_TDMA_slot_order_correspondence :
  And (forall oR : PolicyTDMA.TDMA_slot_order Task, CtdOrdRel Task oR (ctd_ord_to_target Task oR))
      (forall oL : I.Prosa_Classic_Model_PolicyTdma_PolicyTDMA_TDMA_slot_order Task dT, CtdOrdRel Task (ctd_ord_to_source Task oL) oL).
Proof. exact (And_intro _ _ (ctd_ord_canonical Task) (ctd_ord_surjective Task)). Qed.

Theorem PolicyTDMA_slot_order_is_transitive_correspondence oR oL (Ho : CtdOrdRel Task oR oL) :
  PropSPropRel (PolicyTDMA.slot_order_is_transitive oR) (I.Prosa_Classic_Model_PolicyTdma_PolicyTDMA_slot_order_is_transitive Task dT oL).
Proof.
  apply: ct_forall_identity => y. apply: ct_forall_identity => x. apply: ct_forall_identity => z.
  apply: ct_imp; first exact (ct_bool_truth _ _ (Ho x y)).
  apply: ct_imp; first exact (ct_bool_truth _ _ (Ho y z)).
  exact (ct_bool_truth _ _ (Ho x z)).
Qed.

Theorem PolicyTDMA_slot_order_is_total_over_task_set_correspondence sR sL (Hs : CtdSetRel Task sR sL) oR oL (Ho : CtdOrdRel Task oR oL) :
  PropSPropRel (PolicyTDMA.slot_order_is_total_over_task_set sR oR) (I.Prosa_Classic_Model_PolicyTdma_PolicyTDMA_slot_order_is_total_over_task_set Task dT sL oL).
Proof.
  apply: ct_forall_identity => x1. apply: ct_forall_identity => x2.
  apply: ct_imp; first exact (cl_mem_rel_list Task Task cid cid (fun _ => Logic.eq_refl _) x1 _ _ Hs).
  apply: ct_imp; first exact (cl_mem_rel_list Task Task cid cid (fun _ => Logic.eq_refl _) x2 _ _ Hs).
  exact (ct_or _ _ _ _ (ct_bool_truth _ _ (Ho x1 x2)) (ct_bool_truth _ _ (Ho x2 x1))).
Qed.

Theorem PolicyTDMA_slot_order_is_antisymmetric_over_task_set_correspondence sR sL (Hs : CtdSetRel Task sR sL) oR oL
    (Ho : CtdOrdRel Task oR oL) :
  PropSPropRel (PolicyTDMA.slot_order_is_antisymmetric_over_task_set sR oR)
    (I.Prosa_Classic_Model_PolicyTdma_PolicyTDMA_slot_order_is_antisymmetric_over_task_set Task dT sL oL).
Proof.
  apply: ct_forall_identity => x1. apply: ct_forall_identity => x2.
  apply: ct_imp; first exact (cl_mem_rel_list Task Task cid cid (fun _ => Logic.eq_refl _) x1 _ _ Hs).
  apply: ct_imp; first exact (cl_mem_rel_list Task Task cid cid (fun _ => Logic.eq_refl _) x2 _ _ Hs).
  apply: ct_imp; first exact (ct_bool_truth _ _ (Ho x1 x2)).
  apply: ct_imp; first exact (ct_bool_truth _ _ (Ho x2 x1)).
  exact (ct_eq_rel Task x1 x2).
Qed.

Theorem PolicyTDMA_is_valid_time_slot_correspondence task slR slL (Hsl : CtdParRel Task slR slL) :
  CtBoolRel (PolicyTDMA.is_valid_time_slot task slR) (I.Prosa_Classic_Model_PolicyTdma_PolicyTDMA_is_valid_time_slot Task dT task slL).
Proof. exact (ct_decide_lt _ _ _ _ (sub_nat_rel_canonical 0) (Hsl task)). Qed.

Theorem PolicyTDMA_TDMA_cycle_correspondence sR sL (Hs : CtdSetRel Task sR sL) slR slL (Hsl : CtdParRel Task slR slL) :
  SubNatRel (PolicyTDMA.TDMA_cycle sR slR) (I.Prosa_Classic_Model_PolicyTdma_PolicyTDMA_TDMA_cycle Task dT sL slL).
Proof. exact (ctd_sum_rel Task slR slL Hsl _ _ Hs). Qed.

Theorem PolicyTDMA_Task_slot_offset_correspondence sR sL (Hs : CtdSetRel Task sR sL) oR oL (Ho : CtdOrdRel Task oR oL)
    task slR slL (Hsl : CtdParRel Task slR slL) :
  SubNatRel (PolicyTDMA.Task_slot_offset sR oR task slR) (I.Prosa_Classic_Model_PolicyTdma_PolicyTDMA_Task_slot_offset Task dT sL oL task slL).
Proof.
  exact (ctd_sum_filtered_rel Task slR slL Hsl _
    (fun p => I.Bool_and (oL p task) (I.Bool_not (I.Decidable_decide (Lean.eq p task) (dT p task))))
    (fun p => ct_bool_and _ _ _ _ (Ho p task) (ctd_neq Task p task)) _ _ Hs).
Qed.

Theorem PolicyTDMA_Task_in_time_slot_correspondence sR sL (Hs : CtdSetRel Task sR sL) oR oL (Ho : CtdOrdRel Task oR oL)
    task slR slL (Hsl : CtdParRel Task slR slL) tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (PolicyTDMA.Task_in_time_slot sR oR task slR tR) (I.Prosa_Classic_Model_PolicyTdma_PolicyTDMA_Task_in_time_slot Task dT sL oL task slL tL).
Proof.
  have HC := PolicyTDMA_TDMA_cycle_correspondence sR sL Hs slR slL Hsl.
  have HO := PolicyTDMA_Task_slot_offset_correspondence sR sL Hs oR oL Ho task slR slL Hsl.
  apply: ct_decide_lt; last exact (Hsl task).
  apply: dm_mod_correspondence; last exact HC.
  apply: dm_sub_correspondence; last exact (dm_mod_correspondence _ _ _ _ HO HC).
  exact (sub_add_correspondence _ _ _ _ Ht HC).
Qed.
End Defs.

(* ------------------------------------------------------------------ *)
(** * Statements *)

Definition src_TDMA_cycle_ge_each_time_slot (Task : eqType) : Prop :=
  ltac:(type_of_term (@PolicyTDMA.TDMA_cycle_ge_each_time_slot Task)).
Definition tgt_TDMA_cycle_ge_each_time_slot (Task : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Model_PolicyTdma_PolicyTDMA_TDMA_cycle_ge_each_time_slot Task (ct_decidable_eq Task))).

Theorem PolicyTDMA_TDMA_cycle_ge_each_time_slot_correspondence (Task : eqType) :
  PropSPropRel (src_TDMA_cycle_ge_each_time_slot Task) (tgt_TDMA_cycle_ge_each_time_slot Task).
Proof.
  unfold src_TDMA_cycle_ge_each_time_slot, tgt_TDMA_cycle_ge_each_time_slot.
  apply: ctd_forall_set => sR sL Hs. apply: ct_forall_identity => task.
  apply: ct_imp; first exact (ctd_set_mem Task task sR sL Hs).
  apply: ctd_forall_par => slR slL Hsl.
  exact (sub_nat_le_correspondence _ _ _ _ (Hsl task) (PolicyTDMA_TDMA_cycle_correspondence Task sR sL Hs slR slL Hsl)).
Qed.

Definition src_TDMA_cycle_positive (Task : eqType) : Prop :=
  ltac:(type_of_term (@PolicyTDMA.TDMA_cycle_positive Task)).
Definition tgt_TDMA_cycle_positive (Task : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Model_PolicyTdma_PolicyTDMA_TDMA_cycle_positive Task (ct_decidable_eq Task))).

Theorem PolicyTDMA_TDMA_cycle_positive_correspondence (Task : eqType) :
  PropSPropRel (src_TDMA_cycle_positive Task) (tgt_TDMA_cycle_positive Task).
Proof.
  unfold src_TDMA_cycle_positive, tgt_TDMA_cycle_positive.
  apply: ctd_forall_set => sR sL Hs. apply: ct_forall_identity => task.
  apply: ct_imp; first exact (ctd_set_mem Task task sR sL Hs).
  apply: ctd_forall_par => slR slL Hsl.
  apply: ct_imp; first exact (ct_bool_truth _ _ (PolicyTDMA_is_valid_time_slot_correspondence Task task slR slL Hsl)).
  exact (sub_nat_lt_correspondence _ _ _ _ (sub_nat_rel_canonical 0) (PolicyTDMA_TDMA_cycle_correspondence Task sR sL Hs slR slL Hsl)).
Qed.

Definition src_Offset_lt_cycle (Task : eqType) : Prop :=
  ltac:(type_of_term (@PolicyTDMA.Offset_lt_cycle Task)).
Definition tgt_Offset_lt_cycle (Task : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Model_PolicyTdma_PolicyTDMA_Offset_lt_cycle Task (ct_decidable_eq Task))).

Theorem PolicyTDMA_Offset_lt_cycle_correspondence (Task : eqType) :
  PropSPropRel (src_Offset_lt_cycle Task) (tgt_Offset_lt_cycle Task).
Proof.
  unfold src_Offset_lt_cycle, tgt_Offset_lt_cycle.
  apply: ctd_forall_set => sR sL Hs. apply: ctd_forall_ord => oR oL Ho. apply: ct_forall_identity => task.
  apply: ct_imp; first exact (ctd_set_mem Task task sR sL Hs).
  apply: ctd_forall_par => slR slL Hsl.
  apply: ct_imp; first exact (ct_bool_truth _ _ (PolicyTDMA_is_valid_time_slot_correspondence Task task slR slL Hsl)).
  exact (sub_nat_lt_correspondence _ _ _ _ (PolicyTDMA_Task_slot_offset_correspondence Task sR sL Hs oR oL Ho task slR slL Hsl)
           (PolicyTDMA_TDMA_cycle_correspondence Task sR sL Hs slR slL Hsl)).
Qed.

Definition src_Offset_add_slot_leq_cycle (Task : eqType) : Prop :=
  ltac:(type_of_term (@PolicyTDMA.Offset_add_slot_leq_cycle Task)).
Definition tgt_Offset_add_slot_leq_cycle (Task : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Model_PolicyTdma_PolicyTDMA_Offset_add_slot_leq_cycle Task (ct_decidable_eq Task))).

Theorem PolicyTDMA_Offset_add_slot_leq_cycle_correspondence (Task : eqType) :
  PropSPropRel (src_Offset_add_slot_leq_cycle Task) (tgt_Offset_add_slot_leq_cycle Task).
Proof.
  unfold src_Offset_add_slot_leq_cycle, tgt_Offset_add_slot_leq_cycle.
  apply: ctd_forall_set => sR sL Hs. apply: ctd_forall_ord => oR oL Ho. apply: ct_forall_identity => task.
  apply: ct_imp; first exact (ctd_set_mem Task task sR sL Hs).
  apply: ctd_forall_par => slR slL Hsl.
  exact (sub_nat_le_correspondence _ _ _ _
           (sub_add_correspondence _ _ _ _ (PolicyTDMA_Task_slot_offset_correspondence Task sR sL Hs oR oL Ho task slR slL Hsl) (Hsl task))
           (PolicyTDMA_TDMA_cycle_correspondence Task sR sL Hs slR slL Hsl)).
Qed.

Definition src_relation_offset (Task : eqType) : Prop :=
  ltac:(type_of_term (@PolicyTDMA.relation_offset Task)).
Definition tgt_relation_offset (Task : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Model_PolicyTdma_PolicyTDMA_relation_offset Task (ct_decidable_eq Task))).

Theorem PolicyTDMA_relation_offset_correspondence (Task : eqType) :
  PropSPropRel (src_relation_offset Task) (tgt_relation_offset Task).
Proof.
  unfold src_relation_offset, tgt_relation_offset.
  apply: ctd_forall_set => sR sL Hs. apply: ctd_forall_ord => oR oL Ho. apply: ctd_forall_par => slR slL Hsl.
  apply: ct_imp; first exact (PolicyTDMA_slot_order_is_antisymmetric_over_task_set_correspondence Task sR sL Hs oR oL Ho).
  apply: ct_imp; first exact (PolicyTDMA_slot_order_is_transitive_correspondence Task oR oL Ho).
  apply: ct_forall_identity => tsk1. apply: ct_forall_identity => tsk2.
  apply: ct_imp; first exact (ctd_set_mem Task tsk1 sR sL Hs).
  apply: ct_imp; first exact (ctd_set_mem Task tsk2 sR sL Hs).
  apply: ct_imp; first exact (ct_bool_truth _ _ (Ho tsk1 tsk2)).
  apply: ct_imp; first exact (ct_bool_truth _ _ (ctd_neq Task tsk1 tsk2)).
  exact (sub_nat_le_correspondence _ _ _ _
           (sub_add_correspondence _ _ _ _ (PolicyTDMA_Task_slot_offset_correspondence Task sR sL Hs oR oL Ho tsk1 slR slL Hsl) (Hsl tsk1))
           (PolicyTDMA_Task_slot_offset_correspondence Task sR sL Hs oR oL Ho tsk2 slR slL Hsl)).
Qed.

Definition src_task_in_time_slot_uniq (Task : eqType) : Prop :=
  ltac:(type_of_term (@PolicyTDMA.task_in_time_slot_uniq Task)).
Definition tgt_task_in_time_slot_uniq (Task : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Model_PolicyTdma_PolicyTDMA_task_in_time_slot_uniq Task (ct_decidable_eq Task))).

Theorem PolicyTDMA_task_in_time_slot_uniq_correspondence (Task : eqType) :
  PropSPropRel (src_task_in_time_slot_uniq Task) (tgt_task_in_time_slot_uniq Task).
Proof.
  unfold src_task_in_time_slot_uniq, tgt_task_in_time_slot_uniq.
  apply: ctd_forall_set => sR sL Hs. apply: ctd_forall_ord => oR oL Ho. apply: ctd_forall_par => slR slL Hsl.
  apply: ct_imp; first exact (PolicyTDMA_slot_order_is_total_over_task_set_correspondence Task sR sL Hs oR oL Ho).
  apply: ct_imp; first exact (PolicyTDMA_slot_order_is_antisymmetric_over_task_set_correspondence Task sR sL Hs oR oL Ho).
  apply: ct_imp; first exact (PolicyTDMA_slot_order_is_transitive_correspondence Task oR oL Ho).
  apply: ct_forall_identity => tsk1. apply: ct_forall_identity => tsk2. apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (ctd_set_mem Task tsk1 sR sL Hs).
  apply: ct_imp; first exact (sub_nat_lt_correspondence _ _ _ _ (sub_nat_rel_canonical 0) (Hsl tsk1)).
  apply: ct_imp; first exact (ctd_set_mem Task tsk2 sR sL Hs).
  apply: ct_imp; first exact (sub_nat_lt_correspondence _ _ _ _ (sub_nat_rel_canonical 0) (Hsl tsk2)).
  apply: ct_imp; first exact (ct_bool_truth _ _ (PolicyTDMA_Task_in_time_slot_correspondence Task sR sL Hs oR oL Ho tsk1 slR slL Hsl tR tL Ht)).
  apply: ct_imp; first exact (ct_bool_truth _ _ (PolicyTDMA_Task_in_time_slot_correspondence Task sR sL Hs oR oL Ho tsk2 slR slL Hsl tR tL Ht)).
  exact (ct_eq_rel Task tsk1 tsk2).
Qed.
