From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq fintype div.
From prosa Require Import util.seqset classic.model.time classic.model.arrival.basic.arrival_sequence classic.model.arrival.basic.job classic.model.arrival.basic.task classic.model.arrival.basic.task_arrival classic.model.schedule.apa.affinity classic.implementation.apa.task classic.implementation.apa.job classic.implementation.apa.arrival_sequence.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedClassicApaPeriodicArrivals.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence ClassicApaPeriodicArrivalsBase ClassicApaPeriodicArrivalsList ClassicApaPeriodicArrivalsOrd ClassicApaPeriodicArrivalsList1.



Module I := ImportedClassicApaPeriodicArrivals.
Local Open Scope nat_scope.

(** Certificates for [classic/implementation/apa/arrival_sequence.v] (ProsaBuddy classic, commit f692cb7).

    Inputs: processor counts by [SubNatRel]; concrete APA tasks and jobs related through their field-wise embeddings into
    the imported Lean structures at related processor counts ([ItRel], [IjRel], as in the accepted classic APA task and
    job certificates: Nat fields by the canonical Nat map, affinities through the ordinal conversion), with two-way
    totals; task sets elementwise; times by [SubNatRel].  [add_job] and [periodic_arrival_sequence] are related by the
    divisibility bridge and the [filterMap] equations (kernel-checked rfl/simp fixture theorems); each statement is
    proved from these relations. *)

Ltac type_of_term t := let T := type of t in exact T.
Notation cid := (fun z => z).

(* ------------------------------------------------------------------ *)
(** * Helpers (re-bound to this export from the accepted classic certificates) *)

(** Base definitions (as in the accepted classic base library), provided here when this export's library lacks them. *)

(* ------------------------------------------------------------------ *)
(** * Generic covers and helpers *)

Lemma caa_forall_cover (A B : Type) (Rel : A -> B -> SProp) (toB : A -> B) (toA : B -> A)
    (HB : forall a, Rel a (toB a)) (HA : forall b, Rel (toA b) b) (PR : A -> Prop) (PL : B -> SProp) :
  (forall a b, Rel a b -> PropSPropRel (PR a) (PL b)) -> PropSPropRel (forall a, PR a) (forall b, PL b).
Proof.
  intro H. apply prop_sprop_rel_intro.
  - intros HR b. exact (prop_to_sprop _ _ (H _ _ (HA b)) (HR _)).
  - intro HL. apply strictly_inhabits. intro a. exact (sprop_to_prop _ _ (H _ _ (HB a)) (HL _)).
Qed.

Lemma caa_false_rel : PropSPropRel Logic.False I.False.
Proof.
  apply prop_sprop_rel_intro.
  - exact ct_coq_false_to_target.
  - exact ct_target_false_to_strict.
Qed.

Lemma caa_ne (T : Type) (x y : T) : PropSPropRel (x <> y) (I.Ne T x y).
Proof. exact (ct_imp _ _ _ _ (ct_eq_rel T x y) caa_false_rel). Qed.

Lemma caa_mem (T : eqType) x s sL : ClListRel cid s sL ->
  PropSPropRel (x \in s) (I.Membership_mem T (I.List T) (I.List_instMembership T) sL x).
Proof. exact (cl_mem_rel_list T T cid cid (fun _ => Logic.eq_refl _) x s sL). Qed.

Lemma caa_uniq (T : eqType) s sL : ClListRel cid s sL -> PropSPropRel (uniq s) (I.List_Nodup T sL).
Proof. exact (cl_uniq_rel_list T T cid cid (fun _ => Logic.eq_refl _) (fun _ => Logic.eq_refl _) s sL). Qed.

Lemma caa_unmap_rel (T : Type) (l : I.List T) : ClListRel cid (cl_unmap cid l) l.
Proof. apply: coq_eq_to_imported_eq. exact (cl_map_unmap cid cid (fun _ => Logic.eq_refl _) l). Qed.

Lemma caa_cl_map_inj (T : Type) (s1 s2 : seq T) : Logic.eq (cl_map cid s1) (cl_map cid s2) -> Logic.eq s1 s2.
Proof.
  intro E. rewrite -(cl_unmap_map cid cid (fun _ => Logic.eq_refl _) s1) -(cl_unmap_map cid cid (fun _ => Logic.eq_refl _) s2).
  by rewrite E.
Qed.

Lemma caa_succ_rel nR nL : SubNatRel nR nL ->
  SubNatRel nR.+1 (I.HAdd_hAdd_inst7 Lean.Nat Lean.Nat Lean.Nat (I.instHAdd_inst1 Lean.Nat I.instAddNat) nL
                     (I.OfNat_ofNat_inst1 Lean.Nat 1 (I.instOfNatNat 1))).
Proof. intro Hn. exact (sub_imported_eq_congr Lean.Nat_succ _ _ Hn). Qed.

(* ------------------------------------------------------------------ *)
(** * Big concatenation over a half-open interval (as in the accepted arrival_sequence certificate) *)

Lemma caa_forall_list (T : Type) (PR : seq T -> Prop) (PL : I.List T -> SProp) :
  (forall sR sL, ClListRel (B := T) cid sR sL -> PropSPropRel (PR sR) (PL sL)) -> PropSPropRel (forall s, PR s) (forall s, PL s).
Proof.
  exact (caa_forall_cover _ _ (fun sR sL => ClListRel (B := T) cid sR sL) (cl_map cid) (cl_unmap cid)
           (fun s => @Lean.eq_refl _ _) (fun l => caa_unmap_rel T l) PR PL).
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

Module T := prosa.classic.implementation.apa.task.ConcreteTask.
Module J := prosa.classic.implementation.apa.job.ConcreteJob.
Import (canonicals) T. Import (canonicals) J.

(* ------------------------------------------------------------------ *)
(** * Concrete APA tasks, jobs and task sets (as in the accepted classic APA task and job certificates, re-stated for
    this export; all at related processor counts) *)

Notation LTask := I.Prosa_Classic_Implementation_Apa_Task_ConcreteTask_concrete_task.
Notation LAff := I.Prosa_Classic_Model_Schedule_Apa_Affinity_Affinity_affinity.

Lemma caa_rec_forall_cover (A B : Type) (Rel : A -> B -> SProp) (toB : A -> B) (toA : B -> A)
    (Hc : forall a, Rel a (toB a)) (Hs : forall b, Rel (toA b) b) (PR : A -> Prop) (PL : B -> SProp) :
  (forall a b, Rel a b -> PropSPropRel (PR a) (PL b)) -> PropSPropRel (forall a, PR a) (forall b, PL b).
Proof.
  intro H. apply prop_sprop_rel_intro.
  - intros HR b. exact (prop_to_sprop _ _ (H _ _ (Hs b)) (HR (toA b))).
  - intros HL. apply strictly_inhabits. intro a. exact (sprop_to_prop _ _ (H _ _ (Hc a)) (HL (toB a))).
Qed.

(* ------------------------------------------------------------------ *)
(** * Affinities (as in the accepted classic APA certificates) *)

Section Aff.
Variables (nR : nat) (nL : Lean.Nat).
Hypothesis Hn : SubNatRel nR nL.
Notation c := (co_ord_to_fin nR nL Hn).
Notation d := (co_fin_to_ord nR nL Hn).
Notation LVal := (I.Prosa_Util_Seqset_set_val_inst1 (Fin nL) (I.instDecidableEqFin nL)).

Lemma caf_cd (y : Fin nL) : Logic.eq (c (d y)) y.
Proof. exact (co_fin_rel_eq _ _ _ _ _ (co_ord_canonical nR nL Hn (d y)) (co_ord_surjective nR nL Hn y)). Qed.

Lemma caf_dc (x : 'I_nR) : Logic.eq (d (c x)) x.
Proof. exact (co_ord_eq _ _ _ _ _ (co_ord_surjective nR nL Hn (c x)) (co_ord_canonical nR nL Hn x)). Qed.

Definition caf_to_target (aR : Affinity.affinity nR) : LAff nL :=
  I.Prosa_Util_Seqset_set_mk_inst1 (Fin nL) (I.instDecidableEqFin nL) (cl1_map c (@prosa.util.seqset._set_seq _ aR))
    (prop_to_sprop _ _ (cl1_uniq_rel _ _ c d caf_dc caf_cd _) (@prosa.util.seqset.set_uniq _ aR)).

Definition caf_to_source (aL : LAff nL) : Affinity.affinity nR :=
  @prosa.util.seqset.Build_set _ (cl1_unmap d (LVal aL))
    (interpret_strict _ (cl1_uniq_backward _ _ c d caf_cd _
                           (@I.nodup0 (Fin nL) (I.instDecidableEqFin nL) aL))).

Lemma caf_source_roundtrip aR : Logic.eq (caf_to_source (caf_to_target aR)) aR.
Proof.
  apply: val_inj. rewrite /caf_to_source /caf_to_target /=. exact (cl1_unmap_map c d caf_dc _).
Qed.

Lemma caf_set_mk_eq xs ys p q : Logic.eq xs ys ->
  Logic.eq (I.Prosa_Util_Seqset_set_mk_inst1 (Fin nL) (I.instDecidableEqFin nL) xs p)
           (I.Prosa_Util_Seqset_set_mk_inst1 (Fin nL) (I.instDecidableEqFin nL) ys q).
Proof. intro E. destruct E. reflexivity. Qed.

Lemma caf_target_roundtrip aL : Logic.eq (caf_to_target (caf_to_source aL)) aL.
Proof.
  destruct aL as [xs p]. rewrite /caf_to_target /caf_to_source /=.
  apply: caf_set_mk_eq. exact (cl1_map_unmap c d caf_cd xs).
Qed.

End Aff.

(* ------------------------------------------------------------------ *)
(** * Concrete tasks *)

Section Task.
Variables (nR : nat) (nL : Lean.Nat).
Hypothesis Hn : SubNatRel nR nL.

Definition it_export (tR : @T.concrete_task nR) : LTask nL :=
  I.Prosa_Classic_Implementation_Apa_Task_ConcreteTask_concrete_task_mk nL
    (sub_nat_to_imported (T.task_id tR)) (sub_nat_to_imported (T.task_cost tR))
    (sub_nat_to_imported (T.task_period tR)) (sub_nat_to_imported (T.task_deadline tR))
    (caf_to_target nR nL Hn (T.task_affinity tR)).

Definition it_import (tL : LTask nL) : @T.concrete_task nR :=
  match tL with I.Prosa_Classic_Implementation_Apa_Task_ConcreteTask_concrete_task_mk a b c' d' e =>
  {| T.task_id := sub_nat_to_rocq a; T.task_cost := sub_nat_to_rocq b; T.task_period := sub_nat_to_rocq c';
     T.task_deadline := sub_nat_to_rocq d'; T.task_affinity := caf_to_source nR nL Hn e |} end.

Definition ItRel (tR : @T.concrete_task nR) (tL : LTask nL) : SProp := Lean.eq (it_export tR) tL.

Lemma it_source_roundtrip tR : Logic.eq (it_import (it_export tR)) tR.
Proof.
  destruct tR as [a b c' d' e]. unfold it_import, it_export. cbn.
  rewrite (sub_nat_rocq_roundtrip a) (sub_nat_rocq_roundtrip b) (sub_nat_rocq_roundtrip c') (sub_nat_rocq_roundtrip d')
          (caf_source_roundtrip nR nL Hn e).
  reflexivity.
Qed.

Lemma it_target_roundtrip tL : Logic.eq (it_export (it_import tL)) tL.
Proof.
  destruct tL as [a b c' d' e]. unfold it_import, it_export. cbn.
  have Ha := imported_eq_to_coq_eq _ _ (sub_nat_imported_roundtrip a).
  have Hb := imported_eq_to_coq_eq _ _ (sub_nat_imported_roundtrip b).
  have Hc := imported_eq_to_coq_eq _ _ (sub_nat_imported_roundtrip c').
  have Hd := imported_eq_to_coq_eq _ _ (sub_nat_imported_roundtrip d').
  rewrite Ha Hb Hc Hd (caf_target_roundtrip nR nL Hn e). reflexivity.
Qed.

Lemma it_equality xR xL yR yL : ItRel xR xL -> ItRel yR yL -> PropSPropRel (Logic.eq xR yR) (Lean.eq xL yL).
Proof.
  intros Hx Hy. apply prop_sprop_rel_intro.
  - intro Hxy. destruct Hxy. destruct Hx. destruct Hy. exact (@Lean.eq_refl _ _).
  - intro Hxy. apply strictly_inhabits. destruct Hx. destruct Hy.
    have Hdecoded := f_equal it_import (imported_eq_to_coq_eq _ _ Hxy).
    by rewrite !it_source_roundtrip in Hdecoded.
Qed.

Lemma it_aff_equality xR xL yR yL : Lean.eq (caf_to_target nR nL Hn xR) xL -> Lean.eq (caf_to_target nR nL Hn yR) yL ->
  PropSPropRel (Logic.eq xR yR) (Lean.eq xL yL).
Proof.
  intros Hx Hy. apply prop_sprop_rel_intro.
  - intro Hxy. destruct Hxy. destruct Hx. destruct Hy. exact (@Lean.eq_refl _ _).
  - intro Hxy. apply strictly_inhabits. destruct Hx. destruct Hy.
    have Hdecoded := f_equal (caf_to_source nR nL Hn) (imported_eq_to_coq_eq _ _ Hxy).
    by rewrite !caf_source_roundtrip in Hdecoded.
Qed.
Lemma caf_eq_rel a b :
  PropSPropRel (a == b) (Lean.eq (caf_to_target nR nL Hn a) (caf_to_target nR nL Hn b)).
Proof.
  have E := it_aff_equality a _ b _ (@Lean.eq_refl _ _) (@Lean.eq_refl _ _).
  apply prop_sprop_rel_intro.
  - move=> /eqP H. exact (prop_to_sprop _ _ E H).
  - intro H. apply strictly_inhabits. apply/eqP. exact (sprop_to_prop _ _ E H).
Qed.

End Task.

Lemma it_source_total nR nL (Hn : SubNatRel nR nL) (tR : @T.concrete_task nR) :
  ItRel nR nL Hn tR (it_export nR nL Hn tR).
Proof. exact (@Lean.eq_refl _ _). Qed.

Lemma it_target_total nR nL (Hn : SubNatRel nR nL) (tL : LTask nL) :
  ItRel nR nL Hn (it_import nR nL Hn tL) tL.
Proof. exact (coq_eq_to_imported_eq _ _ (it_target_roundtrip nR nL Hn tL)). Qed.

(* ------------------------------------------------------------------ *)
(** * Boolean equality and its reflection *)

Lemma it_eq_rel nR nL (Hn : SubNatRel nR nL) a b :
  PropSPropRel (a == b) (Lean.eq (it_export nR nL Hn a) (it_export nR nL Hn b)).
Proof.
  have E := it_equality nR nL Hn a _ b _ (@Lean.eq_refl _ _) (@Lean.eq_refl _ _).
  apply prop_sprop_rel_intro.
  - move=> /eqP H. exact (prop_to_sprop _ _ E H).
  - intro H. apply strictly_inhabits. apply/eqP. exact (sprop_to_prop _ _ E H).
Qed.

(* ------------------------------------------------------------------ *)
(** * Concrete jobs *)

Notation LJob := I.Prosa_Classic_Implementation_Apa_Job_ConcreteJob_concrete_job.

Section Job.
Variables (nR : nat) (nL : Lean.Nat).
Hypothesis Hn : SubNatRel nR nL.

Definition ij_export (jR : @J.concrete_job nR) : LJob nL :=
  I.Prosa_Classic_Implementation_Apa_Job_ConcreteJob_concrete_job_mk nL
    (sub_nat_to_imported (J.job_id jR)) (sub_nat_to_imported (J.job_arrival jR))
    (sub_nat_to_imported (J.job_cost jR)) (sub_nat_to_imported (J.job_deadline jR))
    (it_export nR nL Hn (J.job_task jR)).

Definition ij_import (jL : LJob nL) : @J.concrete_job nR :=
  match jL with I.Prosa_Classic_Implementation_Apa_Job_ConcreteJob_concrete_job_mk a b c' d' e =>
  {| J.job_id := sub_nat_to_rocq a; J.job_arrival := sub_nat_to_rocq b; J.job_cost := sub_nat_to_rocq c';
     J.job_deadline := sub_nat_to_rocq d'; J.job_task := it_import nR nL Hn e |} end.

Definition IjRel (jR : @J.concrete_job nR) (jL : LJob nL) : SProp := Lean.eq (ij_export jR) jL.

Lemma ij_source_roundtrip jR : Logic.eq (ij_import (ij_export jR)) jR.
Proof.
  destruct jR as [a b c' d' e]. unfold ij_import, ij_export. cbn.
  rewrite (sub_nat_rocq_roundtrip a) (sub_nat_rocq_roundtrip b) (sub_nat_rocq_roundtrip c') (sub_nat_rocq_roundtrip d')
          (it_source_roundtrip nR nL Hn e).
  reflexivity.
Qed.

Lemma ij_target_roundtrip jL : Logic.eq (ij_export (ij_import jL)) jL.
Proof.
  destruct jL as [a b c' d' e]. unfold ij_import, ij_export. cbn.
  have Ha := imported_eq_to_coq_eq _ _ (sub_nat_imported_roundtrip a).
  have Hb := imported_eq_to_coq_eq _ _ (sub_nat_imported_roundtrip b).
  have Hc := imported_eq_to_coq_eq _ _ (sub_nat_imported_roundtrip c').
  have Hd := imported_eq_to_coq_eq _ _ (sub_nat_imported_roundtrip d').
  rewrite Ha Hb Hc Hd (it_target_roundtrip nR nL Hn e). reflexivity.
Qed.

Lemma ij_equality xR xL yR yL : IjRel xR xL -> IjRel yR yL -> PropSPropRel (Logic.eq xR yR) (Lean.eq xL yL).
Proof.
  intros Hx Hy. apply prop_sprop_rel_intro.
  - intro Hxy. destruct Hxy. destruct Hx. destruct Hy. exact (@Lean.eq_refl _ _).
  - intro Hxy. apply strictly_inhabits. destruct Hx. destruct Hy.
    have Hdecoded := f_equal ij_import (imported_eq_to_coq_eq _ _ Hxy).
    by rewrite !ij_source_roundtrip in Hdecoded.
Qed.

End Job.

Theorem ConcreteJob_concrete_job_source_total nR nL (Hn : SubNatRel nR nL) (jR : @J.concrete_job nR) :
  IjRel nR nL Hn jR (ij_export nR nL Hn jR).
Proof. exact (@Lean.eq_refl _ _). Qed.

Theorem ConcreteJob_concrete_job_target_total nR nL (Hn : SubNatRel nR nL) (jL : LJob nL) :
  IjRel nR nL Hn (ij_import nR nL Hn jL) jL.
Proof. exact (coq_eq_to_imported_eq _ _ (ij_target_roundtrip nR nL Hn jL)). Qed.

Lemma it_task_cost nR nL (Hn : SubNatRel nR nL) tR tL : ItRel nR nL Hn tR tL -> SubNatRel (T.task_cost tR) (I.Prosa_Classic_Implementation_Apa_Task_ConcreteTask_concrete_task_task_cost nL tL).
Proof. intro H. destruct H. exact (@Lean.eq_refl _ _). Qed.

Lemma it_task_period nR nL (Hn : SubNatRel nR nL) tR tL : ItRel nR nL Hn tR tL -> SubNatRel (T.task_period tR) (I.Prosa_Classic_Implementation_Apa_Task_ConcreteTask_concrete_task_task_period nL tL).
Proof. intro H. destruct H. exact (@Lean.eq_refl _ _). Qed.

Lemma it_task_deadline nR nL (Hn : SubNatRel nR nL) tR tL : ItRel nR nL Hn tR tL -> SubNatRel (T.task_deadline tR) (I.Prosa_Classic_Implementation_Apa_Task_ConcreteTask_concrete_task_task_deadline nL tL).
Proof. intro H. destruct H. exact (@Lean.eq_refl _ _). Qed.

Lemma ij_job_arrival nR nL (Hn : SubNatRel nR nL) jR jL : IjRel nR nL Hn jR jL -> SubNatRel (J.job_arrival jR) (I.Prosa_Classic_Implementation_Apa_Job_ConcreteJob_concrete_job_job_arrival nL jL).
Proof. intro H. destruct H. exact (@Lean.eq_refl _ _). Qed.

Lemma ij_job_cost nR nL (Hn : SubNatRel nR nL) jR jL : IjRel nR nL Hn jR jL -> SubNatRel (J.job_cost jR) (I.Prosa_Classic_Implementation_Apa_Job_ConcreteJob_concrete_job_job_cost nL jL).
Proof. intro H. destruct H. exact (@Lean.eq_refl _ _). Qed.

Lemma ij_job_deadline nR nL (Hn : SubNatRel nR nL) jR jL : IjRel nR nL Hn jR jL -> SubNatRel (J.job_deadline jR) (I.Prosa_Classic_Implementation_Apa_Job_ConcreteJob_concrete_job_job_deadline nL jL).
Proof. intro H. destruct H. exact (@Lean.eq_refl _ _). Qed.

Lemma ij_job_task nR nL (Hn : SubNatRel nR nL) jR jL : IjRel nR nL Hn jR jL -> ItRel nR nL Hn (J.job_task jR) (I.Prosa_Classic_Implementation_Apa_Job_ConcreteJob_concrete_job_job_task nL jL).
Proof. intro H. destruct H. exact (@Lean.eq_refl _ _). Qed.
Section Taskset.
Variables (nR : nat) (nL : Lean.Nat).
Hypothesis Hn : SubNatRel nR nL.
Notation LTs := (I.Prosa_Classic_Implementation_Apa_Task_ConcreteTask_concrete_taskset nL).
Notation ex := (it_export nR nL Hn).
Notation im := (it_import nR nL Hn).

Lemma it_uniq_rel (s : seq (@T.concrete_task nR)) :
  PropSPropRel (uniq s) (I.List_Nodup_inst1 (LTask nL) (cl1_map ex s)).
Proof. exact (cl1_uniq_rel _ _ ex im (it_source_roundtrip nR nL Hn) (it_target_roundtrip nR nL Hn) s). Qed.

Definition its_list (sL : LTs) : I.List_inst1 (LTask nL) :=
  match sL with I.Prosa_Util_Seqset_set_mk_inst1 xs _ => xs end.

Definition ItsRel (sR : T.concrete_taskset nR) (sL : LTs) : SProp :=
  Lean.eq (cl1_map ex (@_set_seq (@T.concrete_task nR) sR)) (its_list sL).

Definition its_export (sR : T.concrete_taskset nR) : LTs :=
  match sR with
  | @Build_set _ xs Hu => I.Prosa_Util_Seqset_set_mk_inst1 _ _ (cl1_map ex xs) (prop_to_sprop _ _ (it_uniq_rel xs) Hu)
  end.

Lemma its_import_uniq (xs : I.List_inst1 (LTask nL)) (Hu : I.List_Nodup_inst1 _ xs) : uniq (cl1_unmap im xs).
Proof.
  apply (sprop_to_prop _ _ (it_uniq_rel (cl1_unmap im xs))).
  rewrite (cl1_map_unmap ex im (it_target_roundtrip nR nL Hn) xs). exact Hu.
Qed.

Definition its_import (sL : LTs) : T.concrete_taskset nR :=
  match sL with
  | I.Prosa_Util_Seqset_set_mk_inst1 xs Hu => @Build_set (@T.concrete_task nR) (cl1_unmap im xs) (its_import_uniq xs Hu)
  end.

End Taskset.

Lemma its_source_total nR nL (Hn : SubNatRel nR nL) (sR : T.concrete_taskset nR) :
  ItsRel nR nL Hn sR (its_export nR nL Hn sR).
Proof. destruct sR. exact (@Lean.eq_refl _ _). Qed.

Lemma its_target_total nR nL (Hn : SubNatRel nR nL)
    (sL : I.Prosa_Classic_Implementation_Apa_Task_ConcreteTask_concrete_taskset nL) :
  ItsRel nR nL Hn (its_import nR nL Hn sL) sL.
Proof.
  destruct sL as [xs Hu]. unfold ItsRel, its_import, its_list. cbn.
  exact (coq_eq_to_imported_eq _ _ (cl1_map_unmap _ _ (it_target_roundtrip nR nL Hn) xs)).
Qed.

(* ------------------------------------------------------------------ *)
(** * Concrete jobs and tasks: covers and memberships *)

Section Apa.
Variables (nR : nat) (nL : Lean.Nat).
Hypothesis HnA : SubNatRel nR nL.
Notation JR := (@J.concrete_job nR).
Notation JL := (I.Prosa_Classic_Implementation_Apa_Job_ConcreteJob_concrete_job nL).
Notation dJL := (I.Prosa_Classic_Implementation_Apa_Job_ConcreteJob_instDecidableEqConcrete_job nL).
Notation TR := (@T.concrete_task nR).
Notation TL := (I.Prosa_Classic_Implementation_Apa_Task_ConcreteTask_concrete_task nL).
Notation dTL := (I.Prosa_Classic_Implementation_Apa_Task_ConcreteTask_instDecidableEqConcrete_task nL).
Notation TSL := (I.Prosa_Classic_Implementation_Apa_Task_ConcreteTask_concrete_taskset nL).
Local Notation EQ H := (imported_eq_to_coq_eq _ _ H).

Lemma caa_forall_job (PR : JR -> Prop) (PL : JL -> SProp) :
  (forall jR jL, (IjRel nR nL HnA) jR jL -> PropSPropRel (PR jR) (PL jL)) -> PropSPropRel (forall j, PR j) (forall j, PL j).
Proof. exact (caa_forall_cover _ _ (IjRel nR nL HnA) (ij_export nR nL HnA) (ij_import nR nL HnA) (ConcreteJob_concrete_job_source_total nR nL HnA) (ConcreteJob_concrete_job_target_total nR nL HnA) PR PL). Qed.

Lemma caa_forall_ts (PR : (T.concrete_taskset nR) -> Prop) (PL : TSL -> SProp) :
  (forall sR sL, (ItsRel nR nL HnA) sR sL -> PropSPropRel (PR sR) (PL sL)) -> PropSPropRel (forall s, PR s) (forall s, PL s).
Proof.
  exact (caa_forall_cover _ _ (ItsRel nR nL HnA) (its_export nR nL HnA) (its_import nR nL HnA) (its_source_total nR nL HnA)
    (its_target_total nR nL HnA) PR PL).
Qed.

Lemma caa_forall_task (PR : TR -> Prop) (PL : TL -> SProp) :
  (forall tR tL, (ItRel nR nL HnA) tR tL -> PropSPropRel (PR tR) (PL tL)) -> PropSPropRel (forall t, PR t) (forall t, PL t).
Proof. exact (caa_forall_cover _ _ (ItRel nR nL HnA) (it_export nR nL HnA) (it_import nR nL HnA) (it_source_total nR nL HnA) (it_target_total nR nL HnA) PR PL). Qed.

Lemma caa_job_mem jR jL (Hj : (IjRel nR nL HnA) jR jL) sR sL (Hs : ClListRel1 (ij_export nR nL HnA) sR sL) :
  PropSPropRel (jR \in sR) (I.List_Mem_inst1 JL jL sL).
Proof. destruct Hj. exact (cl1_mem_rel_list _ _ (ij_export nR nL HnA) (ij_import nR nL HnA) (ij_source_roundtrip nR nL HnA) jR sR sL Hs). Qed.

Lemma caa_task_mem tR tL (Ht : (ItRel nR nL HnA) tR tL) sR sL (Hs : (ItsRel nR nL HnA) sR sL) :
  PropSPropRel (tR \in sR)
    (I.Membership_mem_inst3 TL TSL (I.Prosa_Util_Seqset_instMembershipSet_inst1 TL dTL) sL tL).
Proof.
  destruct Ht. destruct sL as [xs Hn].
  exact (cl1_mem_rel_list _ _ (it_export nR nL HnA) (it_import nR nL HnA) (it_source_roundtrip nR nL HnA) tR _ xs Hs).
Qed.

(* ------------------------------------------------------------------ *)
(** * The generic arrival-sequence and job/task notions at the concrete types *)

Definition CaaArrRel (aR : ArrivalSequence.arrival_sequence JR) (aL : I.Prosa_Classic_Model_Time_Time_time -> I.List_inst1 JL) : SProp :=
  forall tR tL, SubNatRel tR tL -> ClListRel1 (ij_export nR nL HnA) (aR tR) (aL tL).

Section Generic.
Variables (aR : ArrivalSequence.arrival_sequence JR) (aL : I.Prosa_Classic_Model_Time_Time_time -> I.List_inst1 JL).
Hypothesis Ha : CaaArrRel aR aL.

Lemma caa_arrives_in jR jL (Hj : (IjRel nR nL HnA) jR jL) :
  PropSPropRel (ArrivalSequence.arrives_in aR jR)
    (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrives_in_inst1 JL dJL aL jL).
Proof. apply: ct_exists_nat => tR tL Ht. exact (caa_job_mem _ _ Hj _ _ (Ha tR tL Ht)). Qed.

Lemma caa_consistent :
  PropSPropRel (ArrivalSequence.arrival_times_are_consistent J.job_arrival aR)
    (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrival_times_are_consistent_inst1 JL dJL
       (I.Prosa_Classic_Implementation_Apa_Job_ConcreteJob_concrete_job_job_arrival nL) aL).
Proof.
  apply: caa_forall_job => jR jL Hj. apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (ct_bool_truth _ _ (ct_decide_bool _ _ _ (caa_job_mem _ _ Hj _ _ (Ha tR tL Ht)))).
  exact (sub_nat_eq_correspondence _ _ _ _ ((ij_job_arrival nR nL HnA) _ _ Hj) Ht).
Qed.

Lemma caa_is_a_set :
  PropSPropRel (ArrivalSequence.arrival_sequence_is_a_set aR)
    (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrival_sequence_is_a_set_inst1 JL dJL aL).
Proof.
  apply: ct_forall_nat => tR tL Ht.
  exact (cl1_uniq_rel_list _ _ (ij_export nR nL HnA) (ij_import nR nL HnA) (ij_source_roundtrip nR nL HnA) (ij_target_roundtrip nR nL HnA) _ _ (Ha tR tL Ht)).
Qed.

Lemma caa_sporadic_task_model :
  PropSPropRel (TaskArrival.sporadic_task_model T.task_period J.job_arrival J.job_task aR)
    (I.Prosa_Classic_Model_Arrival_Basic_TaskArrival_TaskArrival_sporadic_task_model_inst3 TL dTL
       (I.Prosa_Classic_Implementation_Apa_Task_ConcreteTask_concrete_task_task_period nL) JL dJL
       (I.Prosa_Classic_Implementation_Apa_Job_ConcreteJob_concrete_job_job_arrival nL)
       (I.Prosa_Classic_Implementation_Apa_Job_ConcreteJob_concrete_job_job_task nL) aL).
Proof.
  apply: caa_forall_job => jR jL Hj. apply: caa_forall_job => jR' jL' Hj'.
  apply: ct_imp; first exact (ct_imp _ _ _ _ ((ij_equality nR nL HnA) _ _ _ _ Hj Hj') caa_false_rel).
  apply: ct_imp; first exact (caa_arrives_in _ _ Hj).
  apply: ct_imp; first exact (caa_arrives_in _ _ Hj').
  apply: ct_imp; first exact ((it_equality nR nL HnA) _ _ _ _ ((ij_job_task nR nL HnA) _ _ Hj) ((ij_job_task nR nL HnA) _ _ Hj')).
  apply: ct_imp; first exact (sub_nat_le_correspondence _ _ _ _ ((ij_job_arrival nR nL HnA) _ _ Hj) ((ij_job_arrival nR nL HnA) _ _ Hj')).
  exact (sub_nat_le_correspondence _ _ _ _
    (sub_add_correspondence _ _ _ _ ((ij_job_arrival nR nL HnA) _ _ Hj) ((it_task_period nR nL HnA) _ _ ((ij_job_task nR nL HnA) _ _ Hj))) ((ij_job_arrival nR nL HnA) _ _ Hj')).
Qed.

End Generic.

Lemma caa_valid_sporadic_job jR jL (Hj : (IjRel nR nL HnA) jR jL) :
  PropSPropRel (Job.valid_sporadic_job T.task_cost T.task_deadline J.job_cost J.job_deadline J.job_task jR)
    (I.Prosa_Classic_Model_Arrival_Basic_Job_Job_valid_sporadic_job_inst3 TL dTL
       (I.Prosa_Classic_Implementation_Apa_Task_ConcreteTask_concrete_task_task_cost nL)
       (I.Prosa_Classic_Implementation_Apa_Task_ConcreteTask_concrete_task_task_deadline nL) JL dJL
       (I.Prosa_Classic_Implementation_Apa_Job_ConcreteJob_concrete_job_job_cost nL)
       (I.Prosa_Classic_Implementation_Apa_Job_ConcreteJob_concrete_job_job_deadline nL)
       (I.Prosa_Classic_Implementation_Apa_Job_ConcreteJob_concrete_job_job_task nL) jL).
Proof.
  have Hc := (ij_job_cost nR nL HnA) _ _ Hj. have Hd := (ij_job_deadline nR nL HnA) _ _ Hj. have Ht := (ij_job_task nR nL HnA) _ _ Hj.
  apply: ct_and.
  - apply: ct_and; first exact (ct_bool_truth _ _ (ct_decide_lt _ _ _ _ (sub_nat_rel_canonical 0) Hc)).
    apply: ct_and; first exact (ct_bool_truth _ _ (ct_decide_le _ _ _ _ Hc Hd)).
    exact (ct_bool_truth _ _ (ct_decide_lt _ _ _ _ (sub_nat_rel_canonical 0) Hd)).
  - apply: ct_and; first exact (ct_bool_truth _ _ (ct_decide_le _ _ _ _ Hc ((it_task_cost nR nL HnA) _ _ Ht))).
    exact (sub_nat_eq_correspondence _ _ _ _ Hd ((it_task_deadline nR nL HnA) _ _ Ht)).
Qed.

Lemma caa_valid_sporadic_taskset sR sL (Hs : (ItsRel nR nL HnA) sR sL) :
  PropSPropRel (SporadicTaskset.valid_sporadic_taskset T.task_cost T.task_period T.task_deadline (prosa.util.seqset._set_seq sR))
    (I.Prosa_Classic_Model_Arrival_Basic_Task_SporadicTaskset_valid_sporadic_taskset_inst1 TL dTL
       (I.Prosa_Classic_Implementation_Apa_Task_ConcreteTask_concrete_task_task_cost nL)
       (I.Prosa_Classic_Implementation_Apa_Task_ConcreteTask_concrete_task_task_period nL)
       (I.Prosa_Classic_Implementation_Apa_Task_ConcreteTask_concrete_task_task_deadline nL)
       (I.Prosa_Util_Seqset_set_val_inst1 TL dTL sL)).
Proof.
  apply: caa_forall_task => tR tL Ht.
  apply: ct_imp; first exact (caa_task_mem _ _ Ht _ _ Hs).
  have Hc := (it_task_cost nR nL HnA) _ _ Ht. have Hp := (it_task_period nR nL HnA) _ _ Ht. have Hd := (it_task_deadline nR nL HnA) _ _ Ht.
  apply: ct_and; first exact (ct_bool_truth _ _ (ct_decide_lt _ _ _ _ (sub_nat_rel_canonical 0) Hc)).
  apply: ct_and; first exact (ct_bool_truth _ _ (ct_decide_lt _ _ _ _ (sub_nat_rel_canonical 0) Hp)).
  apply: ct_and; first exact (ct_bool_truth _ _ (ct_decide_lt _ _ _ _ (sub_nat_rel_canonical 0) Hd)).
  apply: ct_and; first exact (ct_bool_truth _ _ (ct_decide_le _ _ _ _ Hc Hd)).
  exact (ct_bool_truth _ _ (ct_decide_le _ _ _ _ Hc Hp)).
Qed.

(* ------------------------------------------------------------------ *)
(** * Definitions *)

Local Notation OptJ := (fun o : option JR => match o with Some j => I.Option_some_inst1 JL ((ij_export nR nL HnA) j) | None => I.Option_none_inst1 JL end).

Lemma caa_add_job_eq tR tskR :
  Logic.eq (I.Prosa_Classic_Implementation_Apa_ArrivalSequence_ConcreteArrivalSequence_add_job nL (sub_nat_to_imported tR) ((it_export nR nL HnA) tskR)) (OptJ (@ConcreteArrivalSequence.add_job nR tR tskR)).
Proof.
  rewrite /ConcreteArrivalSequence.add_job. unfold I.Prosa_Classic_Implementation_Apa_ArrivalSequence_ConcreteArrivalSequence_add_job.
  rewrite (ct_bool_rel_logic _ _ (ct_decide_bool _ _ _ (dm_dvd_correspondence _ _ _ _ (sub_nat_rel_canonical tR)
             ((it_task_period nR nL HnA) _ _ ((it_source_total nR nL HnA) tskR))))).
  case: (T.task_period tskR %| tR).
  - cbn. f_equal. unfold ij_export. cbn. f_equal.
    exact (EQ (sub_imported_eq_sym _ _ (dm_div_correspondence _ _ _ _ (sub_nat_rel_canonical tR)
             ((it_task_period nR nL HnA) _ _ ((it_source_total nR nL HnA) tskR))))).
  - reflexivity.
Qed.

Theorem ConcreteArrivalSequence_add_job_correspondence tR tL (Ht : SubNatRel tR tL) tskR tskL (Htsk : (ItRel nR nL HnA) tskR tskL) :
  Lean.eq (OptJ (@ConcreteArrivalSequence.add_job nR tR tskR)) (I.Prosa_Classic_Implementation_Apa_ArrivalSequence_ConcreteArrivalSequence_add_job nL tL tskL).
Proof.
  have E := cl_nat_logic _ _ Ht. subst tL. destruct Htsk.
  exact (coq_eq_to_imported_eq _ _ (Logic.eq_sym (caa_add_job_eq tR tskR))).
Qed.

Lemma caa_pas_eq tR : forall s : seq TR,
  Logic.eq (cl1_map (ij_export nR nL HnA) (pmap (@ConcreteArrivalSequence.add_job nR tR) s))
           (I.List_filterMap_inst3 TL JL (I.Prosa_Classic_Implementation_Apa_ArrivalSequence_ConcreteArrivalSequence_add_job nL (sub_nat_to_imported tR)) (cl1_map (it_export nR nL HnA) s)).
Proof.
  elim => [|x s IH]; first exact (Logic.eq_sym (EQ (I.Prosa_Validation_ClassicApaPeriodicArrivalsInterface_filterMap_nil nL (I.Prosa_Classic_Implementation_Apa_ArrivalSequence_ConcreteArrivalSequence_add_job nL (sub_nat_to_imported tR))))).
  have Hx := caa_add_job_eq tR x. cbn [pmap cl1_map].
  case E: (@ConcreteArrivalSequence.add_job nR tR x) => [y|]; rewrite E in Hx.
  - rewrite (EQ (I.Prosa_Validation_ClassicApaPeriodicArrivalsInterface_filterMap_cons_some nL _ _ _ _ (coq_eq_to_imported_eq _ _ Hx))).
    cbn. by rewrite IH.
  - rewrite (EQ (I.Prosa_Validation_ClassicApaPeriodicArrivalsInterface_filterMap_cons_none nL _ _ _ (coq_eq_to_imported_eq _ _ Hx))).
    exact IH.
Qed.

Theorem ConcreteArrivalSequence_periodic_arrival_sequence_correspondence tsR tsL (Hts : (ItsRel nR nL HnA) tsR tsL) tR tL (Ht : SubNatRel tR tL) :
  ClListRel1 (ij_export nR nL HnA) (@ConcreteArrivalSequence.periodic_arrival_sequence nR tsR tR) (I.Prosa_Classic_Implementation_Apa_ArrivalSequence_ConcreteArrivalSequence_periodic_arrival_sequence nL tsL tL).
Proof.
  have E := cl_nat_logic _ _ Ht. subst tL. destruct tsL as [xs Hn].
  apply: coq_eq_to_imported_eq. rewrite /ConcreteArrivalSequence.periodic_arrival_sequence (caa_pas_eq tR).
  have Exs := EQ Hts. cbn in Exs. rewrite Exs. reflexivity.
Qed.

Lemma caa_pas tsR tsL (Hts : (ItsRel nR nL HnA) tsR tsL) :
  CaaArrRel (@ConcreteArrivalSequence.periodic_arrival_sequence nR tsR) (I.Prosa_Classic_Implementation_Apa_ArrivalSequence_ConcreteArrivalSequence_periodic_arrival_sequence nL tsL).
Proof. intros tR tL Ht. exact (ConcreteArrivalSequence_periodic_arrival_sequence_correspondence _ _ Hts _ _ Ht). Qed.

End Apa.

(* ------------------------------------------------------------------ *)
(** * Statements *)

Definition src_periodic_arrivals_are_consistent : Prop := ltac:(type_of_term @ConcreteArrivalSequence.periodic_arrivals_are_consistent).
Definition tgt_periodic_arrivals_are_consistent : SProp := ltac:(type_of_term I.Prosa_Classic_Implementation_Apa_ArrivalSequence_ConcreteArrivalSequence_periodic_arrivals_are_consistent).
Theorem ConcreteArrivalSequence_periodic_arrivals_are_consistent_correspondence :
  PropSPropRel src_periodic_arrivals_are_consistent tgt_periodic_arrivals_are_consistent.
Proof.
  unfold src_periodic_arrivals_are_consistent, tgt_periodic_arrivals_are_consistent.
  apply: ct_forall_nat => nR nL Hn.
  apply: (caa_forall_ts nR nL Hn) => tsR tsL Hts.
  exact (caa_consistent nR nL Hn _ _ (caa_pas nR nL Hn _ _ Hts)).
Qed.

Definition src_periodic_arrivals_all_jobs_from_taskset : Prop := ltac:(type_of_term @ConcreteArrivalSequence.periodic_arrivals_all_jobs_from_taskset).
Definition tgt_periodic_arrivals_all_jobs_from_taskset : SProp := ltac:(type_of_term I.Prosa_Classic_Implementation_Apa_ArrivalSequence_ConcreteArrivalSequence_periodic_arrivals_all_jobs_from_taskset).
Theorem ConcreteArrivalSequence_periodic_arrivals_all_jobs_from_taskset_correspondence :
  PropSPropRel src_periodic_arrivals_all_jobs_from_taskset tgt_periodic_arrivals_all_jobs_from_taskset.
Proof.
  unfold src_periodic_arrivals_all_jobs_from_taskset, tgt_periodic_arrivals_all_jobs_from_taskset.
  apply: ct_forall_nat => nR nL Hn.
  apply: (caa_forall_ts nR nL Hn) => tsR tsL Hts.
  apply: (caa_forall_job nR nL Hn) => jR jL Hj.
  apply: ct_imp; first exact (caa_arrives_in nR nL Hn _ _ (caa_pas nR nL Hn _ _ Hts) _ _ Hj).
  exact (caa_task_mem nR nL Hn _ _ (ij_job_task nR nL Hn _ _ Hj) _ _ Hts).
Qed.

Definition src_periodic_arrivals_valid_job_parameters : Prop := ltac:(type_of_term @ConcreteArrivalSequence.periodic_arrivals_valid_job_parameters).
Definition tgt_periodic_arrivals_valid_job_parameters : SProp := ltac:(type_of_term I.Prosa_Classic_Implementation_Apa_ArrivalSequence_ConcreteArrivalSequence_periodic_arrivals_valid_job_parameters).
Theorem ConcreteArrivalSequence_periodic_arrivals_valid_job_parameters_correspondence :
  PropSPropRel src_periodic_arrivals_valid_job_parameters tgt_periodic_arrivals_valid_job_parameters.
Proof.
  unfold src_periodic_arrivals_valid_job_parameters, tgt_periodic_arrivals_valid_job_parameters.
  apply: ct_forall_nat => nR nL Hn.
  apply: (caa_forall_ts nR nL Hn) => tsR tsL Hts.
  apply: ct_imp; first exact (caa_valid_sporadic_taskset nR nL Hn _ _ Hts).
  apply: (caa_forall_job nR nL Hn) => jR jL Hj.
  apply: ct_imp; first exact (caa_arrives_in nR nL Hn _ _ (caa_pas nR nL Hn _ _ Hts) _ _ Hj).
  exact (caa_valid_sporadic_job nR nL Hn _ _ Hj).
Qed.

Definition src_periodic_arrivals_are_sporadic : Prop := ltac:(type_of_term @ConcreteArrivalSequence.periodic_arrivals_are_sporadic).
Definition tgt_periodic_arrivals_are_sporadic : SProp := ltac:(type_of_term I.Prosa_Classic_Implementation_Apa_ArrivalSequence_ConcreteArrivalSequence_periodic_arrivals_are_sporadic).
Theorem ConcreteArrivalSequence_periodic_arrivals_are_sporadic_correspondence :
  PropSPropRel src_periodic_arrivals_are_sporadic tgt_periodic_arrivals_are_sporadic.
Proof.
  unfold src_periodic_arrivals_are_sporadic, tgt_periodic_arrivals_are_sporadic.
  apply: ct_forall_nat => nR nL Hn.
  apply: (caa_forall_ts nR nL Hn) => tsR tsL Hts.
  exact (caa_sporadic_task_model nR nL Hn _ _ (caa_pas nR nL Hn _ _ Hts)).
Qed.

Definition src_periodic_arrivals_is_a_set : Prop := ltac:(type_of_term @ConcreteArrivalSequence.periodic_arrivals_is_a_set).
Definition tgt_periodic_arrivals_is_a_set : SProp := ltac:(type_of_term I.Prosa_Classic_Implementation_Apa_ArrivalSequence_ConcreteArrivalSequence_periodic_arrivals_is_a_set).
Theorem ConcreteArrivalSequence_periodic_arrivals_is_a_set_correspondence :
  PropSPropRel src_periodic_arrivals_is_a_set tgt_periodic_arrivals_is_a_set.
Proof.
  unfold src_periodic_arrivals_is_a_set, tgt_periodic_arrivals_is_a_set.
  apply: ct_forall_nat => nR nL Hn.
  apply: (caa_forall_ts nR nL Hn) => tsR tsL Hts.
  apply: ct_imp; first exact (caa_valid_sporadic_taskset nR nL Hn _ _ Hts).
  exact (caa_is_a_set nR nL Hn _ _ (caa_pas nR nL Hn _ _ Hts)).
Qed.
