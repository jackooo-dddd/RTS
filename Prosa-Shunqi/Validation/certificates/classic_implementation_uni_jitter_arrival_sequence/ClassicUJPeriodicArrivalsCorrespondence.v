From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq div.
From prosa Require Import util.seqset classic.model.time classic.model.arrival.basic.arrival_sequence classic.model.arrival.basic.job classic.model.arrival.basic.task classic.model.arrival.basic.task_arrival classic.implementation.uni.jitter.task classic.implementation.uni.jitter.job classic.implementation.uni.jitter.arrival_sequence.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedClassicUJPeriodicArrivals.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence ClassicUJPeriodicArrivalsBase ClassicUJPeriodicArrivalsList ClassicUJPeriodicArrivalsList1 ClassicUJPeriodicArrivalsRec.



Module I := ImportedClassicUJPeriodicArrivals.
Local Open Scope nat_scope.

(** Certificates for [classic/implementation/uni/jitter/arrival_sequence.v] (ProsaBuddy classic, commit f692cb7).

    Inputs: concrete tasks and concrete jobs are related through their field-wise embeddings into the imported Lean
    structures ([ItRel], [IjRel]: injective, with left inverses; two-way totals), concrete task sets elementwise
    ([ItsRel]); times by [SubNatRel].  The generic arrival-sequence notions are instantiated at concrete jobs, whose
    Rocq and Lean types differ: they are related below at that instance (membership through [cl1_mem_rel_list]
    with the job embedding, the Lean [decide] by [ct_decide_bool] for the derived [DecidableEq] instance);
    [%|] / [%/] through the accepted div/mod relation; [pmap] against [List.filterMap]. *)

Ltac type_of_term t := let T := type of t in exact T.
Notation cid := (fun z => z).

(* ------------------------------------------------------------------ *)
(** * Helpers (re-bound to this export from the accepted classic certificates) *)

(** Base definitions (as in the accepted classic base library), provided here when this export's library lacks them. *)

(* ------------------------------------------------------------------ *)
(** * Generic covers and helpers *)

Lemma cua_forall_cover (A B : Type) (Rel : A -> B -> SProp) (toB : A -> B) (toA : B -> A)
    (HB : forall a, Rel a (toB a)) (HA : forall b, Rel (toA b) b) (PR : A -> Prop) (PL : B -> SProp) :
  (forall a b, Rel a b -> PropSPropRel (PR a) (PL b)) -> PropSPropRel (forall a, PR a) (forall b, PL b).
Proof.
  intro H. apply prop_sprop_rel_intro.
  - intros HR b. exact (prop_to_sprop _ _ (H _ _ (HA b)) (HR _)).
  - intro HL. apply strictly_inhabits. intro a. exact (sprop_to_prop _ _ (H _ _ (HB a)) (HL _)).
Qed.

Lemma cua_false_rel : PropSPropRel Logic.False I.False.
Proof.
  apply prop_sprop_rel_intro.
  - exact ct_coq_false_to_target.
  - exact ct_target_false_to_strict.
Qed.

Lemma cua_ne (T : Type) (x y : T) : PropSPropRel (x <> y) (I.Ne T x y).
Proof. exact (ct_imp _ _ _ _ (ct_eq_rel T x y) cua_false_rel). Qed.

Lemma cua_mem (T : eqType) x s sL : ClListRel cid s sL ->
  PropSPropRel (x \in s) (I.Membership_mem T (I.List T) (I.List_instMembership T) sL x).
Proof. exact (cl_mem_rel_list T T cid cid (fun _ => Logic.eq_refl _) x s sL). Qed.

Lemma cua_uniq (T : eqType) s sL : ClListRel cid s sL -> PropSPropRel (uniq s) (I.List_Nodup T sL).
Proof. exact (cl_uniq_rel_list T T cid cid (fun _ => Logic.eq_refl _) (fun _ => Logic.eq_refl _) s sL). Qed.

Lemma cua_unmap_rel (T : Type) (l : I.List T) : ClListRel cid (cl_unmap cid l) l.
Proof. apply: coq_eq_to_imported_eq. exact (cl_map_unmap cid cid (fun _ => Logic.eq_refl _) l). Qed.

Lemma cua_cl_map_inj (T : Type) (s1 s2 : seq T) : Logic.eq (cl_map cid s1) (cl_map cid s2) -> Logic.eq s1 s2.
Proof.
  intro E. rewrite -(cl_unmap_map cid cid (fun _ => Logic.eq_refl _) s1) -(cl_unmap_map cid cid (fun _ => Logic.eq_refl _) s2).
  by rewrite E.
Qed.

Lemma cua_succ_rel nR nL : SubNatRel nR nL ->
  SubNatRel nR.+1 (I.HAdd_hAdd_inst7 Lean.Nat Lean.Nat Lean.Nat (I.instHAdd_inst1 Lean.Nat I.instAddNat) nL
                     (I.OfNat_ofNat_inst1 Lean.Nat 1 (I.instOfNatNat 1))).
Proof. intro Hn. exact (sub_imported_eq_congr Lean.Nat_succ _ _ Hn). Qed.

(* ------------------------------------------------------------------ *)
(** * Big concatenation over a half-open interval (as in the accepted arrival_sequence certificate) *)

Lemma cua_forall_list (T : Type) (PR : seq T -> Prop) (PL : I.List T -> SProp) :
  (forall sR sL, ClListRel (B := T) cid sR sL -> PropSPropRel (PR sR) (PL sL)) -> PropSPropRel (forall s, PR s) (forall s, PL s).
Proof.
  exact (cua_forall_cover _ _ (fun sR sL => ClListRel (B := T) cid sR sL) (cl_map cid) (cl_unmap cid)
           (fun s => @Lean.eq_refl _ _) (fun l => cua_unmap_rel T l) PR PL).
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

Import (canonicals) TT. Import (canonicals) TJ.
(* ------------------------------------------------------------------ *)
(** * Concrete jobs and tasks: covers and memberships *)

Notation JR := TJ.concrete_job.
Notation JL := I.Prosa_Classic_Implementation_Uni_Jitter_Job_ConcreteJob_concrete_job.
Notation dJL := I.Prosa_Classic_Implementation_Uni_Jitter_Job_ConcreteJob_instDecidableEqConcrete_job.
Notation TR := TT.concrete_task.
Notation TL := I.Prosa_Classic_Implementation_Uni_Jitter_Task_ConcreteTask_concrete_task.
Notation dTL := I.Prosa_Classic_Implementation_Uni_Jitter_Task_ConcreteTask_instDecidableEqConcrete_task.
Notation TSL := I.Prosa_Classic_Implementation_Uni_Jitter_Task_ConcreteTask_concrete_taskset.
Notation EQ H := (imported_eq_to_coq_eq _ _ H).

Lemma cua_forall_job (PR : JR -> Prop) (PL : JL -> SProp) :
  (forall jR jL, IjRel jR jL -> PropSPropRel (PR jR) (PL jL)) -> PropSPropRel (forall j, PR j) (forall j, PL j).
Proof. exact (cua_forall_cover _ _ IjRel ij_export ij_import ConcreteJob_concrete_job_source_total ConcreteJob_concrete_job_target_total PR PL). Qed.

Lemma cua_forall_ts (PR : TT.concrete_taskset -> Prop) (PL : TSL -> SProp) :
  (forall sR sL, ItsRel sR sL -> PropSPropRel (PR sR) (PL sL)) -> PropSPropRel (forall s, PR s) (forall s, PL s).
Proof.
  exact (cua_forall_cover _ _ ItsRel its_export its_import ConcreteTask_concrete_taskset_source_total
    ConcreteTask_concrete_taskset_target_total PR PL).
Qed.

Lemma cua_forall_task (PR : TR -> Prop) (PL : TL -> SProp) :
  (forall tR tL, ItRel tR tL -> PropSPropRel (PR tR) (PL tL)) -> PropSPropRel (forall t, PR t) (forall t, PL t).
Proof. exact (cua_forall_cover _ _ ItRel it_export it_import ConcreteTask_concrete_task_source_total ConcreteTask_concrete_task_target_total PR PL). Qed.

Lemma cua_job_mem jR jL (Hj : IjRel jR jL) sR sL (Hs : ClListRel1 ij_export sR sL) :
  PropSPropRel (jR \in sR) (I.List_Mem_inst1 JL jL sL).
Proof. destruct Hj. exact (cl1_mem_rel_list _ _ ij_export ij_import ij_source_roundtrip jR sR sL Hs). Qed.

Lemma cua_task_mem tR tL (Ht : ItRel tR tL) sR sL (Hs : ItsRel sR sL) :
  PropSPropRel (tR \in sR)
    (I.Membership_mem_inst3 TL TSL (I.Prosa_Util_Seqset_instMembershipSet_inst1 TL dTL) sL tL).
Proof.
  destruct Ht. destruct sL as [xs Hn].
  exact (cl1_mem_rel_list _ _ it_export it_import it_source_roundtrip tR _ xs Hs).
Qed.

(* ------------------------------------------------------------------ *)
(** * The generic arrival-sequence and job/task notions at the concrete types *)

Definition CuaArrRel (aR : ArrivalSequence.arrival_sequence JR) (aL : I.Prosa_Classic_Model_Time_Time_time -> I.List_inst1 JL) : SProp :=
  forall tR tL, SubNatRel tR tL -> ClListRel1 ij_export (aR tR) (aL tL).

Section Generic.
Variables (aR : ArrivalSequence.arrival_sequence JR) (aL : I.Prosa_Classic_Model_Time_Time_time -> I.List_inst1 JL).
Hypothesis Ha : CuaArrRel aR aL.

Lemma cua_arrives_in jR jL (Hj : IjRel jR jL) :
  PropSPropRel (ArrivalSequence.arrives_in aR jR)
    (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrives_in_inst1 JL dJL aL jL).
Proof. apply: ct_exists_nat => tR tL Ht. exact (cua_job_mem _ _ Hj _ _ (Ha tR tL Ht)). Qed.

Lemma cua_consistent :
  PropSPropRel (ArrivalSequence.arrival_times_are_consistent TJ.job_arrival aR)
    (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrival_times_are_consistent_inst1 JL dJL
       I.Prosa_Classic_Implementation_Uni_Jitter_Job_ConcreteJob_concrete_job_job_arrival aL).
Proof.
  apply: cua_forall_job => jR jL Hj. apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (ct_bool_truth _ _ (ct_decide_bool _ _ _ (cua_job_mem _ _ Hj _ _ (Ha tR tL Ht)))).
  exact (sub_nat_eq_correspondence _ _ _ _ (ij_job_arrival _ _ Hj) Ht).
Qed.

Lemma cua_is_a_set :
  PropSPropRel (ArrivalSequence.arrival_sequence_is_a_set aR)
    (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrival_sequence_is_a_set_inst1 JL dJL aL).
Proof.
  apply: ct_forall_nat => tR tL Ht.
  exact (cl1_uniq_rel_list _ _ ij_export ij_import ij_source_roundtrip ij_target_roundtrip _ _ (Ha tR tL Ht)).
Qed.

Lemma cua_sporadic_task_model :
  PropSPropRel (TaskArrival.sporadic_task_model TT.task_period TJ.job_arrival TJ.job_task aR)
    (I.Prosa_Classic_Model_Arrival_Basic_TaskArrival_TaskArrival_sporadic_task_model_inst3 TL dTL
       I.Prosa_Classic_Implementation_Uni_Jitter_Task_ConcreteTask_concrete_task_task_period JL dJL
       I.Prosa_Classic_Implementation_Uni_Jitter_Job_ConcreteJob_concrete_job_job_arrival
       I.Prosa_Classic_Implementation_Uni_Jitter_Job_ConcreteJob_concrete_job_job_task aL).
Proof.
  apply: cua_forall_job => jR jL Hj. apply: cua_forall_job => jR' jL' Hj'.
  apply: ct_imp; first exact (ct_imp _ _ _ _ (ij_equality _ _ _ _ Hj Hj') cua_false_rel).
  apply: ct_imp; first exact (cua_arrives_in _ _ Hj).
  apply: ct_imp; first exact (cua_arrives_in _ _ Hj').
  apply: ct_imp; first exact (it_equality _ _ _ _ (ij_job_task _ _ Hj) (ij_job_task _ _ Hj')).
  apply: ct_imp; first exact (sub_nat_le_correspondence _ _ _ _ (ij_job_arrival _ _ Hj) (ij_job_arrival _ _ Hj')).
  exact (sub_nat_le_correspondence _ _ _ _
    (sub_add_correspondence _ _ _ _ (ij_job_arrival _ _ Hj) (it_task_period _ _ (ij_job_task _ _ Hj))) (ij_job_arrival _ _ Hj')).
Qed.

End Generic.

(* ------------------------------------------------------------------ *)
(** * Definitions *)

Notation OptJ := (fun o : option JR => match o with Some j => I.Option_some_inst1 JL (ij_export j) | None => I.Option_none_inst1 JL end).

Lemma cua_add_job_eq tR tskR :
  Logic.eq (I.Prosa_Classic_Implementation_Uni_Jitter_ArrivalSequence_ConcreteArrivalSequence_add_job (sub_nat_to_imported tR) (it_export tskR)) (OptJ (ConcreteArrivalSequence.add_job tR tskR)).
Proof.
  rewrite /ConcreteArrivalSequence.add_job. unfold I.Prosa_Classic_Implementation_Uni_Jitter_ArrivalSequence_ConcreteArrivalSequence_add_job.
  rewrite (ct_bool_rel_logic _ _ (ct_decide_bool _ _ _ (dm_dvd_correspondence _ _ _ _ (sub_nat_rel_canonical tR)
             (it_task_period _ _ (ConcreteTask_concrete_task_source_total tskR))))).
  case: (TT.task_period tskR %| tR).
  - cbn. f_equal. unfold ij_export. cbn. f_equal.
    exact (EQ (sub_imported_eq_sym _ _ (dm_div_correspondence _ _ _ _ (sub_nat_rel_canonical tR)
             (it_task_period _ _ (ConcreteTask_concrete_task_source_total tskR))))).
  - reflexivity.
Qed.

Theorem ConcreteArrivalSequence_add_job_correspondence tR tL (Ht : SubNatRel tR tL) tskR tskL (Htsk : ItRel tskR tskL) :
  Lean.eq (OptJ (ConcreteArrivalSequence.add_job tR tskR)) (I.Prosa_Classic_Implementation_Uni_Jitter_ArrivalSequence_ConcreteArrivalSequence_add_job tL tskL).
Proof.
  have E := cl_nat_logic _ _ Ht. subst tL. destruct Htsk.
  exact (coq_eq_to_imported_eq _ _ (Logic.eq_sym (cua_add_job_eq tR tskR))).
Qed.

Lemma cua_pas_eq tR : forall s : seq TR,
  Logic.eq (cl1_map ij_export (pmap (ConcreteArrivalSequence.add_job tR) s))
           (I.List_filterMap_inst3 TL JL (I.Prosa_Classic_Implementation_Uni_Jitter_ArrivalSequence_ConcreteArrivalSequence_add_job (sub_nat_to_imported tR)) (cl1_map it_export s)).
Proof.
  elim => [|x s IH]; first exact (Logic.eq_sym (EQ (I.Prosa_Validation_ClassicUJPeriodicArrivalsInterface_filterMap_nil (I.Prosa_Classic_Implementation_Uni_Jitter_ArrivalSequence_ConcreteArrivalSequence_add_job (sub_nat_to_imported tR))))).
  have Hx := cua_add_job_eq tR x. cbn [pmap cl1_map].
  case E: (ConcreteArrivalSequence.add_job tR x) => [y|]; rewrite E in Hx.
  - rewrite (EQ (I.Prosa_Validation_ClassicUJPeriodicArrivalsInterface_filterMap_cons_some _ _ _ _ (coq_eq_to_imported_eq _ _ Hx))).
    cbn. by rewrite IH.
  - rewrite (EQ (I.Prosa_Validation_ClassicUJPeriodicArrivalsInterface_filterMap_cons_none _ _ _ (coq_eq_to_imported_eq _ _ Hx))).
    exact IH.
Qed.

Theorem ConcreteArrivalSequence_periodic_arrival_sequence_correspondence tsR tsL (Hts : ItsRel tsR tsL) tR tL (Ht : SubNatRel tR tL) :
  ClListRel1 ij_export (ConcreteArrivalSequence.periodic_arrival_sequence tsR tR) (I.Prosa_Classic_Implementation_Uni_Jitter_ArrivalSequence_ConcreteArrivalSequence_periodic_arrival_sequence tsL tL).
Proof.
  have E := cl_nat_logic _ _ Ht. subst tL. destruct tsL as [xs Hn].
  apply: coq_eq_to_imported_eq. rewrite /ConcreteArrivalSequence.periodic_arrival_sequence (cua_pas_eq tR).
  have Exs := EQ Hts. cbn in Exs. rewrite Exs. reflexivity.
Qed.

Lemma cua_pas tsR tsL (Hts : ItsRel tsR tsL) :
  CuaArrRel (ConcreteArrivalSequence.periodic_arrival_sequence tsR) (I.Prosa_Classic_Implementation_Uni_Jitter_ArrivalSequence_ConcreteArrivalSequence_periodic_arrival_sequence tsL).
Proof. intros tR tL Ht. exact (ConcreteArrivalSequence_periodic_arrival_sequence_correspondence _ _ Hts _ _ Ht). Qed.

(* ------------------------------------------------------------------ *)
(** * Statements *)

Definition src_periodic_arrivals_are_consistent : Prop := ltac:(type_of_term ConcreteArrivalSequence.periodic_arrivals_are_consistent).
Definition tgt_periodic_arrivals_are_consistent : SProp := ltac:(type_of_term I.Prosa_Classic_Implementation_Uni_Jitter_ArrivalSequence_ConcreteArrivalSequence_periodic_arrivals_are_consistent).
Theorem ConcreteArrivalSequence_periodic_arrivals_are_consistent_correspondence :
  PropSPropRel src_periodic_arrivals_are_consistent tgt_periodic_arrivals_are_consistent.
Proof.
  unfold src_periodic_arrivals_are_consistent, tgt_periodic_arrivals_are_consistent.
  apply: cua_forall_ts => tsR tsL Hts.
  exact (cua_consistent _ _ (cua_pas _ _ Hts)).
Qed.

Definition src_periodic_arrivals_all_jobs_from_taskset : Prop := ltac:(type_of_term ConcreteArrivalSequence.periodic_arrivals_all_jobs_from_taskset).
Definition tgt_periodic_arrivals_all_jobs_from_taskset : SProp := ltac:(type_of_term I.Prosa_Classic_Implementation_Uni_Jitter_ArrivalSequence_ConcreteArrivalSequence_periodic_arrivals_all_jobs_from_taskset).
Theorem ConcreteArrivalSequence_periodic_arrivals_all_jobs_from_taskset_correspondence :
  PropSPropRel src_periodic_arrivals_all_jobs_from_taskset tgt_periodic_arrivals_all_jobs_from_taskset.
Proof.
  unfold src_periodic_arrivals_all_jobs_from_taskset, tgt_periodic_arrivals_all_jobs_from_taskset.
  apply: cua_forall_ts => tsR tsL Hts.
  apply: cua_forall_job => jR jL Hj.
  apply: ct_imp; first exact (cua_arrives_in _ _ (cua_pas _ _ Hts) _ _ Hj).
  exact (cua_task_mem _ _ (ij_job_task _ _ Hj) _ _ Hts).
Qed.

Definition src_periodic_arrivals_are_sporadic : Prop := ltac:(type_of_term ConcreteArrivalSequence.periodic_arrivals_are_sporadic).
Definition tgt_periodic_arrivals_are_sporadic : SProp := ltac:(type_of_term I.Prosa_Classic_Implementation_Uni_Jitter_ArrivalSequence_ConcreteArrivalSequence_periodic_arrivals_are_sporadic).
Theorem ConcreteArrivalSequence_periodic_arrivals_are_sporadic_correspondence :
  PropSPropRel src_periodic_arrivals_are_sporadic tgt_periodic_arrivals_are_sporadic.
Proof.
  unfold src_periodic_arrivals_are_sporadic, tgt_periodic_arrivals_are_sporadic.
  apply: cua_forall_ts => tsR tsL Hts.
  exact (cua_sporadic_task_model _ _ (cua_pas _ _ Hts)).
Qed.

Definition src_periodic_arrivals_job_cost_le_task_cost : Prop := ltac:(type_of_term ConcreteArrivalSequence.periodic_arrivals_job_cost_le_task_cost).
Definition tgt_periodic_arrivals_job_cost_le_task_cost : SProp := ltac:(type_of_term I.Prosa_Classic_Implementation_Uni_Jitter_ArrivalSequence_ConcreteArrivalSequence_periodic_arrivals_job_cost_le_task_cost).
Theorem ConcreteArrivalSequence_periodic_arrivals_job_cost_le_task_cost_correspondence :
  PropSPropRel src_periodic_arrivals_job_cost_le_task_cost tgt_periodic_arrivals_job_cost_le_task_cost.
Proof.
  unfold src_periodic_arrivals_job_cost_le_task_cost, tgt_periodic_arrivals_job_cost_le_task_cost.
  apply: cua_forall_ts => tsR tsL Hts.
  apply: cua_forall_job => jR jL Hj.
  apply: ct_imp; first exact (cua_arrives_in _ _ (cua_pas _ _ Hts) _ _ Hj).
  exact (sub_nat_le_correspondence _ _ _ _ (ij_job_cost _ _ Hj) (it_task_cost _ _ (ij_job_task _ _ Hj))).
Qed.

Definition src_periodic_arrivals_job_deadline_eq_task_deadline : Prop := ltac:(type_of_term ConcreteArrivalSequence.periodic_arrivals_job_deadline_eq_task_deadline).
Definition tgt_periodic_arrivals_job_deadline_eq_task_deadline : SProp := ltac:(type_of_term I.Prosa_Classic_Implementation_Uni_Jitter_ArrivalSequence_ConcreteArrivalSequence_periodic_arrivals_job_deadline_eq_task_deadline).
Theorem ConcreteArrivalSequence_periodic_arrivals_job_deadline_eq_task_deadline_correspondence :
  PropSPropRel src_periodic_arrivals_job_deadline_eq_task_deadline tgt_periodic_arrivals_job_deadline_eq_task_deadline.
Proof.
  unfold src_periodic_arrivals_job_deadline_eq_task_deadline, tgt_periodic_arrivals_job_deadline_eq_task_deadline.
  apply: cua_forall_ts => tsR tsL Hts.
  apply: cua_forall_job => jR jL Hj.
  apply: ct_imp; first exact (cua_arrives_in _ _ (cua_pas _ _ Hts) _ _ Hj).
  exact (sub_nat_eq_correspondence _ _ _ _ (ij_job_deadline _ _ Hj) (it_task_deadline _ _ (ij_job_task _ _ Hj))).
Qed.

Definition src_periodic_arrivals_is_a_set : Prop := ltac:(type_of_term ConcreteArrivalSequence.periodic_arrivals_is_a_set).
Definition tgt_periodic_arrivals_is_a_set : SProp := ltac:(type_of_term I.Prosa_Classic_Implementation_Uni_Jitter_ArrivalSequence_ConcreteArrivalSequence_periodic_arrivals_is_a_set).
Theorem ConcreteArrivalSequence_periodic_arrivals_is_a_set_correspondence :
  PropSPropRel src_periodic_arrivals_is_a_set tgt_periodic_arrivals_is_a_set.
Proof.
  unfold src_periodic_arrivals_is_a_set, tgt_periodic_arrivals_is_a_set.
  apply: cua_forall_ts => tsR tsL Hts.
  exact (cua_is_a_set _ _ (cua_pas _ _ Hts)).
Qed.
