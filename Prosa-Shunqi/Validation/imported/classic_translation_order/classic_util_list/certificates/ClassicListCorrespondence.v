From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From prosa Require Import classic.util.list.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedClassicList.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence ClassicListBase ClassicListOps.

Module I := ImportedClassicList.
Local Open Scope nat_scope.

(** Certificates for [classic/util/list.v] (ProsaBuddy classic, commit f692cb7).

    Inputs.  Type parameters and their elements are identified; for an
    [eqType] the Lean [DecidableEq] instance is the eqType's decision procedure
    ([ct_decidable_eq]); sequences are related to Lean lists elementwise
    ([ClListRel], through the identity or, for pairs, the pair conversion
    [cl_pair]); options constructor-wise; natural numbers by [SubNatRel];
    Booleans constructor-wise; functions and predicates pointwise.  All
    relations have two-way totals (covers [cl_forall_list], [ct_forall_*]).

    Computation: the operation lemmas of [ClassicListOps] (structural
    induction, Lean side unfolded by conversion).  Lean's decision procedures
    are never unfolded ([ct_decide_bool]).

    Statements: the source side is the exact elaborated type of the pinned
    lemma (via [type of]; the source proof is not used).  The two [Type]-valued
    [reflect] views ([mapP2], [zipP]) are related to the Lean [BoolReflect]
    family by constructor-preserving maps (as for the accepted v0.6
    [quiet_time_P]). *)

Ltac type_of_term t := let T := type of t in exact T.

(* ------------------------------------------------------------------ *)
(** * Shorthands *)

Notation cid := (fun z => z).
Definition cl_id_rt (T : Type) : forall x : T, Logic.eq (cid (cid x)) x := fun x => Logic.eq_refl x.

Lemma cc_forall_list (T : Type) (PR : seq T -> Prop) (PL : I.List T -> SProp) :
  (forall sR sL, ClListRel cid sR sL -> PropSPropRel (PR sR) (PL sL)) ->
  PropSPropRel (forall s, PR s) (forall s, PL s).
Proof. exact (cl_forall_list cid cid (cl_id_rt T) PR PL). Qed.

Lemma cc_mem (T : eqType) x s sL : ClListRel cid s sL ->
  PropSPropRel (x \in s) (I.Membership_mem T (I.List T) (I.List_instMembership T) sL x).
Proof. exact (cl_mem_rel_list T T cid cid (cl_id_rt T) x s sL). Qed.

Lemma cc_val_eq (T : Type) (aR aL bR bL : T) :
  Logic.eq aR aL -> Logic.eq bR bL -> PropSPropRel (Logic.eq aR bR) (Lean.eq aL bL).
Proof.
  intros -> ->. apply prop_sprop_rel_intro.
  - exact (coq_eq_to_imported_eq _ _).
  - intro H. exact (strictly_inhabits (imported_eq_to_coq_eq _ _ H)).
Qed.

Lemma cc_ne (T : Type) (a b : T) : PropSPropRel (a <> b) (I.Ne T a b).
Proof.
  apply prop_sprop_rel_intro.
  - intros N E. exact (ct_coq_false_to_target (N (imported_eq_to_coq_eq _ _ E))).
  - intro N. apply strictly_inhabits. intro E.
    exact (interpret_strict _ (ct_target_false_to_strict (N (coq_eq_to_imported_eq _ _ E)))).
Qed.

Lemma cc_list_eq {A B} (c : A -> B) (d : B -> A) (Hdc : forall x, Logic.eq (d (c x)) x) s1 s2 l1 l2 :
  ClListRel c s1 l1 -> ClListRel c s2 l2 -> PropSPropRel (Logic.eq s1 s2) (Lean.eq l1 l2).
Proof.
  intros H1 H2. rewrite (cl_list_logic _ _ _ H1) (cl_list_logic _ _ _ H2). apply prop_sprop_rel_intro.
  - intros ->. exact (@Lean.eq_refl _ _).
  - intro E. apply strictly_inhabits. have E' := f_equal (cl_unmap d) (imported_eq_to_coq_eq _ _ E).
    by rewrite !(cl_unmap_map c d Hdc) in E'.
Qed.

Lemma cc_opt_eq {A} (o1 o2 : option A) : PropSPropRel (Logic.eq o1 o2) (Lean.eq (cl_opt o1) (cl_opt o2)).
Proof.
  apply prop_sprop_rel_intro.
  - intros ->. exact (@Lean.eq_refl _ _).
  - intro E. apply strictly_inhabits. have E' := f_equal cl_unopt (imported_eq_to_coq_eq _ _ E).
    by rewrite !cl_unopt_opt in E'.
Qed.

Fixpoint cc_in_backward (T : Type) (x : T) (l : I.List T) (H : I.List_Mem T x l) :
    StrictlyInhabited (List.In x (cl_unmap cid l)) :=
  match H with
  | I.List_Mem_head l' => strictly_inhabits (or_introl Logic.eq_refl)
  | I.List_Mem_tail y l' Ht =>
      match cc_in_backward T x l' Ht with strictly_inhabits Hi => strictly_inhabits (or_intror Hi) end
  end.

Fixpoint cc_in_forward (T : Type) (x : T) (s : seq T) : List.In x s -> I.List_Mem T x (cl_map cid s) :=
  match s as s0 return List.In x s0 -> I.List_Mem T x (cl_map cid s0) with
  | [::] => fun H => match H return I.List_Mem T x (I.List_nil T) with end
  | y :: s' => fun H =>
      match H with
      | or_introl E => match E in Logic.eq _ z return I.List_Mem T z (I.List_cons T y (cl_map cid s')) with
                       | Logic.eq_refl => I.List_Mem_head T y _ end
      | or_intror Hs => I.List_Mem_tail T x y _ (cc_in_forward T x s' Hs)
      end
  end.

Lemma cc_in_rel (T : Type) (x : T) (s : seq T) : PropSPropRel (List.In x s) (I.List_Mem T x (cl_map cid s)).
Proof.
  apply prop_sprop_rel_intro; first exact (cc_in_forward T x s).
  intro H. have S := cc_in_backward T x _ H. by rewrite (cl_unmap_map cid cid (cl_id_rt T)) in S.
Qed.

Lemma cc_exists_identity (T : Type) (PR : T -> Prop) (PL : T -> SProp) :
  (forall x, PropSPropRel (PR x) (PL x)) -> PropSPropRel (exists x, PR x) (I.Exists T PL).
Proof.
  intro H. apply prop_sprop_rel_intro.
  - intros [x Hx]. exact (I.Exists_intro T PL x (prop_to_sprop _ _ (H x) Hx)).
  - intros [x Hx]. apply strictly_inhabits. exists x. exact (sprop_to_prop _ _ (H x) Hx).
Qed.

Lemma cc_exists2_identity (T : Type) (AR BR : T -> Prop) (AL BL : T -> SProp) :
  (forall x, PropSPropRel (AR x) (AL x)) -> (forall x, PropSPropRel (BR x) (BL x)) ->
  PropSPropRel (exists2 x, AR x & BR x) (I.Exists T (fun x => And (AL x) (BL x))).
Proof.
  intros HA HB. apply prop_sprop_rel_intro.
  - intros [x Ha Hb]. exact (I.Exists_intro T _ x (And_intro _ _ (prop_to_sprop _ _ (HA x) Ha) (prop_to_sprop _ _ (HB x) Hb))).
  - intros [x [Ha Hb]]. apply strictly_inhabits. exists x; [exact (sprop_to_prop _ _ (HA x) Ha) | exact (sprop_to_prop _ _ (HB x) Hb)].
Qed.

Lemma cc_iff (P Q : Prop) (PL QL : SProp) :
  PropSPropRel P PL -> PropSPropRel Q QL -> PropSPropRel (P <-> Q) (I.Iff PL QL).
Proof.
  intros HP HQ. apply prop_sprop_rel_intro.
  - intros [f g]. apply I.Iff_intro.
    + intro p. exact (prop_to_sprop _ _ HQ (f (sprop_to_prop _ _ HP p))).
    + intro q. exact (prop_to_sprop _ _ HP (g (sprop_to_prop _ _ HQ q))).
  - intros [f g]. apply strictly_inhabits. split.
    + intro p. exact (sprop_to_prop _ _ HQ (f (prop_to_sprop _ _ HP p))).
    + intro q. exact (sprop_to_prop _ _ HP (g (prop_to_sprop _ _ HQ q))).
Qed.

Lemma cc_not (P : Prop) (PL : SProp) : PropSPropRel P PL -> PropSPropRel (~ P) (I.Not PL).
Proof.
  intro H. apply prop_sprop_rel_intro.
  - intros N p. exact (ct_coq_false_to_target (N (sprop_to_prop _ _ H p))).
  - intro N. apply strictly_inhabits. intro p. exact (interpret_strict _ (ct_target_false_to_strict (N (prop_to_sprop _ _ H p)))).
Qed.

Lemma cc_decide_eqtype (T : eqType) (a b : T) :
  CtBoolRel (a == b) (I.Decidable_decide (Lean.eq a b) (ct_decidable_eq T a b)).
Proof. exact (ct_decide_eq T a b). Qed.

(** Pairs of eqTypes: the elements of [T1 * T2] against [Prod T1 T2]. *)
Definition cc_pair_rt (T1 T2 : Type) : forall p : T1 * T2, Logic.eq (cl_unpair (cl_pair p)) p := @cl_unpair_pair T1 T2.
Definition cc_pair_rt' (T1 T2 : Type) : forall p : I.Prod T1 T2, Logic.eq (cl_pair (cl_unpair p)) p := @cl_pair_unpair T1 T2.

(* ------------------------------------------------------------------ *)
(** * The [reflect] view *)

Definition cc_reflect_forward (PR : Prop) (PL : SProp) (bR : bool) (bL : I.Bool)
    (HP : PropSPropRel PR PL) (Hb : CtBoolRel bR bL) :
    reflect PR bR -> I.Prosa_Classic_Util_List_BoolReflect PL bL.
Proof.
  destruct Hb. intro HR. destruct HR as [Htrue | Hfalse].
  - exact (I.Prosa_Classic_Util_List_BoolReflect_isTrue PL (prop_to_sprop _ _ HP Htrue)).
  - exact (I.Prosa_Classic_Util_List_BoolReflect_isFalse PL
      (fun HL => ct_coq_false_to_target (Hfalse (sprop_to_prop _ _ HP HL)))).
Defined.

Definition cc_reflect_backward_at_bool (PR : Prop) (PL : SProp) (HP : PropSPropRel PR PL) (bL : I.Bool) :
    I.Prosa_Classic_Util_List_BoolReflect PL bL -> reflect PR (ct_l2b bL) :=
  fun HL =>
    match HL in I.Prosa_Classic_Util_List_BoolReflect _ b return reflect PR (ct_l2b b) with
    | I.Prosa_Classic_Util_List_BoolReflect_isTrue Htrue => ReflectT PR (sprop_to_prop _ _ HP Htrue)
    | I.Prosa_Classic_Util_List_BoolReflect_isFalse Hfalse =>
        ReflectF PR (fun HR => interpret_strict Logic.False
          (ct_target_false_to_strict (Hfalse (prop_to_sprop _ _ HP HR))))
    end.

Definition cc_reflect_backward (PR : Prop) (PL : SProp) (bR : bool) (bL : I.Bool)
    (HP : PropSPropRel PR PL) (Hb : CtBoolRel bR bL) :
    I.Prosa_Classic_Util_List_BoolReflect PL bL -> reflect PR bR.
Proof. destruct Hb. destruct bR; cbn; exact (cc_reflect_backward_at_bool PR PL HP _). Defined.

(* ------------------------------------------------------------------ *)
(** * Definitions *)

Theorem nth_or_none_correspondence (T : Type) : forall (s : seq T) n,
  Logic.eq (cl_opt (nth_or_none s n)) (I.Prosa_Classic_Util_List_nth_or_none T (cl_map cid s) (sub_nat_to_imported n)).
Proof. elim => [|x s IH] [|n] //=. Qed.

Lemma cc_set_nth_lt (T : Type) (x0 y : T) : forall (s : seq T) n, (n < size s)%nat ->
  Logic.eq (cl_map cid (set_nth x0 s n y)) (I.List_set T (cl_map cid s) (sub_nat_to_imported n) y).
Proof. elim => [|x s IH] [|n] //= H. by rewrite IH. Qed.

Lemma cc_set_nth_if_exists_unfold (T : Type) (s : seq T) n (y : T) :
  Logic.eq (set_nth_if_exists s n y) (if (n < size s)%nat then set_nth y s n y else s).
Proof.
  rewrite /set_nth_if_exists. case: (n < size s)%nat => //.
Qed.

Theorem set_nth_if_exists_correspondence (T : Type) (s : seq T) n (y : T) :
  Logic.eq (cl_map cid (set_nth_if_exists s n y))
    (I.Prosa_Classic_Util_List_set_nth_if_exists T (cl_map cid s) (sub_nat_to_imported n) y).
Proof.
  rewrite cc_set_nth_if_exists_unfold.
  have Hlt := sub_nat_lt_correspondence _ _ _ _ (sub_nat_rel_canonical n) (cl_size cid s).
  unfold I.Prosa_Classic_Util_List_set_nth_if_exists.
  destruct (I.Nat_decLt (sub_nat_to_imported n) (I.List_length T (cl_map cid s))) as [h|h].
  - have Hge : ~~ (n < size s)%nat.
    { apply/negP => Hs. exact (interpret_strict _ (ct_target_false_to_strict (h (prop_to_sprop _ _ Hlt Hs)))). }
    rewrite (negbTE Hge). reflexivity.
  - have Hs : (n < size s)%nat := sprop_to_prop _ _ Hlt h.
    rewrite Hs. exact (cc_set_nth_lt T y y s n Hs).
Qed.

Lemma cc_replace_first_cons (T : Type) (P : T -> I.Bool) (f : T -> T) x l :
  Logic.eq (I.Prosa_Classic_Util_List_replace_first T P f (I.List_cons T x l))
    (match P x with
     | I.Bool_true => I.List_cons T (f x) l
     | I.Bool_false => I.List_cons T x (I.Prosa_Classic_Util_List_replace_first T P f l) end).
Proof. cbn. destruct (P x); reflexivity. Qed.

Theorem replace_first_correspondence (T : Type) (PR : T -> bool) (PL : T -> I.Bool)
    (HP : forall x, CtBoolRel (PR x) (PL x)) (f : T -> T) : forall s,
  Logic.eq (cl_map cid (replace_first PR f s)) (I.Prosa_Classic_Util_List_replace_first T PL f (cl_map cid s)).
Proof.
  elim => [|x s IH] //=. rewrite cc_replace_first_cons (ct_bool_rel_logic _ _ (HP x)).
  case: (PR x) => /=; last by rewrite IH. reflexivity.
Qed.

Theorem replace_first_const_correspondence (T : Type) (PR : T -> bool) (PL : T -> I.Bool)
    (HP : forall x, CtBoolRel (PR x) (PL x)) (y : T) s :
  Logic.eq (cl_map cid (replace_first_const PR y s)) (I.Prosa_Classic_Util_List_replace_first_const T PL y (cl_map cid s)).
Proof. exact (replace_first_correspondence T PR PL HP (fun _ => y) s). Qed.

Theorem set_pair_1nd_correspondence (T1 T2 : Type) (y : T2) (p : T1 * T2) :
  Logic.eq (cl_pair (set_pair_1nd y p)) (I.Prosa_Classic_Util_List_set_pair_1nd T1 T2 y (cl_pair p)).
Proof. reflexivity. Qed.

Theorem set_pair_2nd_correspondence (T1 T2 : Type) (y : T2) (p : T1 * T2) :
  Logic.eq (cl_pair (set_pair_2nd y p)) (I.Prosa_Classic_Util_List_set_pair_2nd T1 T2 y (cl_pair p)).
Proof. reflexivity. Qed.

Lemma cc_unzip1 (T1 T2 : Type) (l : seq (T1 * T2)) :
  Logic.eq (cl_map cid (unzip1 l)) (I.List_map (I.Prod T1 T2) T1 (I.Prod_fst T1 T2) (cl_map cl_pair l)).
Proof. exact (cl_map_op cl_pair cid (@Datatypes.fst T1 T2) (I.Prod_fst T1 T2) (fun _ => Logic.eq_refl _) l). Qed.

Lemma cc_unzip2 (T1 T2 : Type) (l : seq (T1 * T2)) :
  Logic.eq (cl_map cid (unzip2 l)) (I.List_map (I.Prod T1 T2) T2 (I.Prod_snd T1 T2) (cl_map cl_pair l)).
Proof. exact (cl_map_op cl_pair cid (@Datatypes.snd T1 T2) (I.Prod_snd T1 T2) (fun _ => Logic.eq_refl _) l). Qed.

Theorem pairs_to_function_correspondence (T1 : eqType) (T2 : Type) (y0 : T2) (l : seq (T1 * T2)) (x : T1) :
  Logic.eq (pairs_to_function y0 l x)
    (I.Prosa_Classic_Util_List_pairs_to_function T1 (ct_decidable_eq T1) T2 y0 (cl_map cl_pair l) x).
Proof.
  rewrite /pairs_to_function /I.Prosa_Classic_Util_List_pairs_to_function -cc_unzip1 -cc_unzip2.
  rewrite (cl_nat_logic _ _ (cl_index T1 x (ct_decidable_eq T1) (cc_decide_eqtype T1) (unzip1 l))).
  exact (cl_nth cid y0 (unzip2 l) (index x (unzip1 l))).
Qed.

Theorem total_over_list_correspondence (T : eqType) (relR : T -> T -> bool) (relL : T -> T -> I.Bool)
    (Hrel : forall a b, CtBoolRel (relR a b) (relL a b)) s sL (Hs : ClListRel cid s sL) :
  PropSPropRel (total_over_list relR s) (I.Prosa_Classic_Util_List_total_over_list T (ct_decidable_eq T) relL sL).
Proof.
  apply: ct_forall_identity => x1. apply: ct_forall_identity => x2.
  apply: ct_imp; first exact (cc_mem T x1 s sL Hs).
  apply: ct_imp; first exact (cc_mem T x2 s sL Hs).
  exact (ct_or _ _ _ _ (ct_bool_truth _ _ (Hrel x1 x2)) (ct_bool_truth _ _ (Hrel x2 x1))).
Qed.

Theorem antisymmetric_over_list_correspondence (T : eqType) (relR : T -> T -> bool) (relL : T -> T -> I.Bool)
    (Hrel : forall a b, CtBoolRel (relR a b) (relL a b)) s sL (Hs : ClListRel cid s sL) :
  PropSPropRel (antisymmetric_over_list relR s)
    (I.Prosa_Classic_Util_List_antisymmetric_over_list T (ct_decidable_eq T) relL sL).
Proof.
  apply: ct_forall_identity => x1. apply: ct_forall_identity => x2.
  apply: ct_imp; first exact (cc_mem T x1 s sL Hs).
  apply: ct_imp; first exact (cc_mem T x2 s sL Hs).
  apply: ct_imp; first exact (ct_bool_truth _ _ (Hrel x1 x2)).
  apply: ct_imp; first exact (ct_bool_truth _ _ (Hrel x2 x1)).
  exact (ct_eq_rel T x1 x2).
Qed.

(* ------------------------------------------------------------------ *)
(** * Statement helpers *)

Lemma cc_list_rel_canonical {A B} (c : A -> B) s : ClListRel c s (cl_map c s).
Proof. exact (@Lean.eq_refl _ _). Qed.

Lemma cc_rel_of_eq {A B} (c : A -> B) s l : Logic.eq (cl_map c s) l -> ClListRel c s l.
Proof. exact (cl_lean_eq _ (cl_map c s) l). Qed.

Lemma cc_uniq (T : eqType) s sL : ClListRel cid s sL -> PropSPropRel (uniq s) (I.List_Nodup T sL).
Proof. exact (cl_uniq_rel_list T T cid cid (cl_id_rt T) (cl_id_rt T) s sL). Qed.

Lemma cc_succ nR nL : SubNatRel nR nL ->
  SubNatRel nR.+1 (I.HAdd_hAdd_inst7 Lean.Nat Lean.Nat Lean.Nat (I.instHAdd_inst1 Lean.Nat I.instAddNat) nL
                    (I.OfNat_ofNat_inst1 Lean.Nat 1 (I.instOfNatNat 1))).
Proof. intro H. have := sub_add_correspondence _ _ 1 _ H (sub_nat_rel_canonical 1). by rewrite addn1. Qed.

Lemma cc_index (T : eqType) x s sL : ClListRel cid s sL ->
  SubNatRel (index x s) (I.List_idxOf T (I.instBEqOfDecidableEq T (ct_decidable_eq T)) x sL).
Proof. intro H. destruct H. exact (cl_index T x (ct_decidable_eq T) (cc_decide_eqtype T) s). Qed.

Lemma cc_filter (T : Type) (pR : T -> bool) (pL : T -> I.Bool) (Hp : forall x, CtBoolRel (pR x) (pL x)) s sL :
  ClListRel cid s sL -> ClListRel cid (filter pR s) (I.List_filter T pL sL).
Proof. intro H. destruct H. exact (cc_rel_of_eq _ _ _ (cl_filter cid pR pL Hp s)). Qed.

Lemma cc_take (T : Type) nR nL s sL : SubNatRel nR nL -> ClListRel cid s sL ->
  ClListRel (B := T) cid (take nR s) (I.List_take T nL sL).
Proof.
  intros Hn H. destruct H. rewrite (cl_nat_logic _ _ Hn). exact (cc_rel_of_eq _ _ _ (cl_take cid nR s)).
Qed.

Lemma cc_nth (T : Type) (x0 : T) s sL nR nL : ClListRel cid s sL -> SubNatRel nR nL ->
  Logic.eq (nth x0 s nR) (I.List_getD T sL nL x0).
Proof. intros H Hn. destruct H. rewrite (cl_nat_logic _ _ Hn). exact (cl_nth cid x0 s nR). Qed.

Lemma cc_size (T : Type) s sL : ClListRel (B := T) cid s sL -> SubNatRel (size s) (I.List_length T sL).
Proof. intro H. destruct H. exact (cl_size cid s). Qed.

(* ------------------------------------------------------------------ *)
(** * Statements: indices, filters, prefixes *)

Definition src_idx_lt_rcons (T : eqType) : Prop := ltac:(type_of_term (@idx_lt_rcons T)).
Definition tgt_idx_lt_rcons (T : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Util_List_idx_lt_rcons T (ct_decidable_eq T))).
Theorem idx_lt_rcons_correspondence (T : eqType) : PropSPropRel (src_idx_lt_rcons T) (tgt_idx_lt_rcons T).
Proof.
  unfold src_idx_lt_rcons, tgt_idx_lt_rcons.
  apply: cc_forall_list => l lL Hl. apply: ct_forall_nat => i iL Hi. apply: ct_forall_identity => x0.
  apply: ct_imp; first exact (cc_uniq T l lL Hl).
  apply: ct_imp; first exact (sub_nat_lt_correspondence _ _ _ _ Hi (cc_size T l lL Hl)).
  apply: (cc_list_eq cid cid (cl_id_rt T)).
  - apply: (cc_filter T _ _ _ l lL Hl) => x. exact (ct_decide_lt _ _ _ _ (cc_index T x l lL Hl) (cc_succ _ _ Hi)).
  - have Hf : ClListRel cid (filter (fun x => index x l < i) l) _ :=
      cc_filter T _ _ (fun x => ct_decide_lt _ _ _ _ (cc_index T x l lL Hl) Hi) l lL Hl.
    apply: cc_rel_of_eq. rewrite cl_rcons -(cl_list_logic _ _ _ Hf) (cc_nth T x0 l lL i iL Hl Hi). reflexivity.
Qed.

Definition src_filter_idx_lt_take (T : eqType) : Prop := ltac:(type_of_term (@filter_idx_lt_take T)).
Definition tgt_filter_idx_lt_take (T : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Util_List_filter_idx_lt_take T (ct_decidable_eq T))).
Theorem filter_idx_lt_take_correspondence (T : eqType) :
  PropSPropRel (src_filter_idx_lt_take T) (tgt_filter_idx_lt_take T).
Proof.
  unfold src_filter_idx_lt_take, tgt_filter_idx_lt_take.
  apply: cc_forall_list => l lL Hl. apply: ct_forall_nat => i iL Hi.
  apply: ct_imp; first exact (cc_uniq T l lL Hl).
  apply: ct_imp; first exact (sub_nat_lt_correspondence _ _ _ _ Hi (cc_size T l lL Hl)).
  apply: (cc_list_eq cid cid (cl_id_rt T)).
  - apply: (cc_filter T _ _ _ l lL Hl) => x. exact (ct_decide_lt _ _ _ _ (cc_index T x l lL Hl) Hi).
  - exact (cc_take T _ _ l lL Hi Hl).
Qed.

Definition src_filter_idx_le_takeS (T : eqType) : Prop := ltac:(type_of_term (@filter_idx_le_takeS T)).
Definition tgt_filter_idx_le_takeS (T : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Util_List_filter_idx_le_takeS T (ct_decidable_eq T))).
Theorem filter_idx_le_takeS_correspondence (T : eqType) :
  PropSPropRel (src_filter_idx_le_takeS T) (tgt_filter_idx_le_takeS T).
Proof.
  unfold src_filter_idx_le_takeS, tgt_filter_idx_le_takeS.
  apply: cc_forall_list => l lL Hl. apply: ct_forall_nat => i iL Hi.
  apply: ct_imp; first exact (cc_uniq T l lL Hl).
  apply: ct_imp; first exact (sub_nat_lt_correspondence _ _ _ _ Hi (cc_size T l lL Hl)).
  apply: (cc_list_eq cid cid (cl_id_rt T)).
  - apply: (cc_filter T _ _ _ l lL Hl) => x. exact (ct_decide_le _ _ _ _ (cc_index T x l lL Hl) Hi).
  - exact (cc_take T _ _ l lL (cc_succ _ _ Hi) Hl).
Qed.

(* ------------------------------------------------------------------ *)
(** * Statements: the [reflect] views *)

Definition src_mapP2 (T : Type) (T' : eqType) : Type := ltac:(type_of_term (@mapP2 T T')).
Definition tgt_mapP2 (T : Type) (T' : eqType) : Type :=
  ltac:(type_of_term (I.Prosa_Classic_Util_List_mapP2 T T' (ct_decidable_eq T'))).

Lemma cc_mapP2_prop (T : Type) (T' : eqType) (s : seq T) (f : T -> T') (y : T') :
  PropSPropRel (exists2 x : T, List.In x s & Logic.eq y (f x))
    (I.Exists T (fun x => And (I.Membership_mem T (I.List T) (I.List_instMembership T) (cl_map cid s) x) (Lean.eq y (f x)))).
Proof. apply: cc_exists2_identity => x; [exact (cc_in_rel T x s) | exact (ct_eq_rel T' y (f x))]. Qed.

Lemma cc_mapP2_bool (T : Type) (T' : eqType) (s : seq T) (f : T -> T') (y : T') :
  CtBoolRel (y \in [seq f i | i <- s])
    (I.Decidable_decide (I.Membership_mem T' (I.List T') (I.List_instMembership T') (I.List_map T T' f (cl_map cid s)) y)
       (I.List_instDecidableMemOfLawfulBEq T' (I.instBEqOfDecidableEq T' (ct_decidable_eq T'))
          (I.instLawfulBEq T' (ct_decidable_eq T')) y (I.List_map T T' f (cl_map cid s)))).
Proof.
  apply: ct_decide_bool. apply: (cc_mem T' y _ _).
  exact (cc_rel_of_eq _ _ _ (cl_map_op cid cid f f (fun _ => Logic.eq_refl _) s)).
Qed.

Theorem mapP2_correspondence (T : Type) (T' : eqType) :
  Datatypes.prod (src_mapP2 T T' -> tgt_mapP2 T T') (tgt_mapP2 T T' -> src_mapP2 T T').
Proof.
  split.
  - intros g sL f y. rewrite -(cl_map_unmap cid cid (cl_id_rt T) sL).
    exact (cc_reflect_forward _ _ _ _ (cc_mapP2_prop T T' _ f y) (cc_mapP2_bool T T' _ f y) (g _ f y)).
  - intros h s f y.
    exact (cc_reflect_backward _ _ _ _ (cc_mapP2_prop T T' s f y) (cc_mapP2_bool T T' s f y) (h _ f y)).
Defined.

(* ------------------------------------------------------------------ *)
(** * Pairs *)

Lemma cc_size_gen {A B} (c : A -> B) s sL : ClListRel c s sL -> SubNatRel (size s) (I.List_length B sL).
Proof. intro H. destruct H. exact (cl_size c s). Qed.

Lemma cc_zip (T1 T2 : Type) l1 L1 l2 L2 : ClListRel (B := T1) cid l1 L1 -> ClListRel (B := T2) cid l2 L2 ->
  ClListRel cl_pair (zip l1 l2) (I.List_zip T1 T2 L1 L2).
Proof. intros H1 H2. destruct H1, H2. exact (cc_rel_of_eq _ _ _ (cl_zip cid cid l1 l2)). Qed.

Lemma cc_mem_pair (T1 T2 : eqType) (x1 : T1) (x2 : T2) s sL : ClListRel cl_pair s sL ->
  PropSPropRel ((x1, x2) \in s) (I.Membership_mem (I.Prod T1 T2) (I.List (I.Prod T1 T2)) (I.List_instMembership (I.Prod T1 T2)) sL (I.Prod_mk T1 T2 x1 x2)).
Proof. exact (cl_mem_rel_list _ (I.Prod T1 T2) cl_pair cl_unpair (cc_pair_rt T1 T2) (x1, x2) s sL). Qed.

Lemma cc_forall_pair_list (T1 T2 : Type) (PR : seq (T1 * T2) -> Prop) (PL : I.List (I.Prod T1 T2) -> SProp) :
  (forall sR sL, ClListRel cl_pair sR sL -> PropSPropRel (PR sR) (PL sL)) ->
  PropSPropRel (forall s, PR s) (forall s, PL s).
Proof. exact (cl_forall_list cl_pair cl_unpair (cc_pair_rt' T1 T2) PR PL). Qed.

Lemma cc_forall_pair (T1 T2 : Type) (PR : T1 * T2 -> Prop) (PL : I.Prod T1 T2 -> SProp) :
  (forall p, PropSPropRel (PR p) (PL (cl_pair p))) -> PropSPropRel (forall p, PR p) (forall p, PL p).
Proof.
  intro H. apply prop_sprop_rel_intro.
  - intros HR pL. exact (prop_to_sprop _ _ (H (cl_unpair pL)) (HR _)).
  - intro HL. apply strictly_inhabits. intro p. exact (sprop_to_prop _ _ (H p) (HL _)).
Qed.

Lemma cc_forall_type_fun (A B : Type) (PR : (A -> B) -> Prop) (PL : (A -> B) -> SProp) :
  (forall f, PropSPropRel (PR f) (PL f)) -> PropSPropRel (forall f, PR f) (forall f, PL f).
Proof. exact (ct_forall_identity (A -> B) PR PL). Qed.

Lemma cc_forall_bool_rel2 (A : Type) (PR : (A -> A -> bool) -> Prop) (PL : (A -> A -> I.Bool) -> SProp) :
  (forall pR pL, (forall a b, CtBoolRel (pR a b) (pL a b)) -> PropSPropRel (PR pR) (PL pL)) ->
  PropSPropRel (forall p, PR p) (forall p, PL p).
Proof.
  intro H. apply prop_sprop_rel_intro.
  - intros HR pL. exact (prop_to_sprop _ _ (H (fun a b => ct_l2b (pL a b)) pL (fun a b => ct_bool_surjective _)) (HR _)).
  - intro HL. apply strictly_inhabits. intro pR.
    exact (sprop_to_prop _ _ (H pR (fun a b => ct_b2l (pR a b)) (fun a b => ct_bool_canonical _)) (HL _)).
Qed.

Lemma cc_forall_bool_rel1 (A : Type) (PR : (A -> bool) -> Prop) (PL : (A -> I.Bool) -> SProp) :
  (forall pR pL, (forall a, CtBoolRel (pR a) (pL a)) -> PropSPropRel (PR pR) (PL pL)) ->
  PropSPropRel (forall p, PR p) (forall p, PL p).
Proof.
  intro H. apply prop_sprop_rel_intro.
  - intros HR pL. exact (prop_to_sprop _ _ (H (fun a => ct_l2b (pL a)) pL (fun a => ct_bool_surjective _)) (HR _)).
  - intro HL. apply strictly_inhabits. intro pR.
    exact (sprop_to_prop _ _ (H pR (fun a => ct_b2l (pR a)) (fun a => ct_bool_canonical _)) (HL _)).
Qed.

(** [zipP] *)

Lemma cc_zipP_prop (T : eqType) (x0 : T) PR PL (HP : forall a b, CtBoolRel (PR a b) (PL a b)) X XL Y YL :
  ClListRel cid X XL -> ClListRel cid Y YL ->
  PropSPropRel (forall i, i < size (zip X Y) -> PR (nth x0 X i) (nth x0 Y i))
    (forall i : Lean.Nat, I.LT_lt_inst1 Lean.Nat I.instLTNat i (I.List_length (I.Prod T T) (I.List_zip T T XL YL)) ->
       Lean.eq (PL (I.List_getD T XL i x0) (I.List_getD T YL i x0)) I.Bool_true).
Proof.
  intros HX HY. apply: ct_forall_nat => iR iL Hi.
  apply: ct_imp; first exact (sub_nat_lt_correspondence _ _ _ _ Hi (cc_size_gen cl_pair _ _ (cc_zip T T X XL Y YL HX HY))).
  rewrite -(cc_nth T x0 X XL iR iL HX Hi) -(cc_nth T x0 Y YL iR iL HY Hi). exact (ct_bool_truth _ _ (HP _ _)).
Qed.

Lemma cc_zipP_bool (T : eqType) PR PL (HP : forall a b, CtBoolRel (PR a b) (PL a b)) X XL Y YL :
  ClListRel cid X XL -> ClListRel cid Y YL ->
  CtBoolRel (all (fun p : T * T => PR p.1 p.2) (zip X Y))
    (I.List_all (I.Prod T T) (I.List_zip T T XL YL) (fun p => PL (I.Prod_fst T T p) (I.Prod_snd T T p))).
Proof.
  intros HX HY. have Z := cc_zip T T X XL Y YL HX HY. rewrite (cl_list_logic _ _ _ Z).
  apply: cl_all => p. exact (HP _ _).
Qed.

Definition src_zipP (T : eqType) : Type := ltac:(type_of_term (@zipP T)).
Definition tgt_zipP (T : eqType) : Type := ltac:(type_of_term (I.Prosa_Classic_Util_List_zipP T (ct_decidable_eq T))).
Theorem zipP_correspondence (T : eqType) :
  Datatypes.prod (src_zipP T -> tgt_zipP T) (tgt_zipP T -> src_zipP T).
Proof.
  split.
  - intros g x0 PL XL YL HL.
    have HP : forall a b, CtBoolRel (ct_l2b (PL a b)) (PL a b) := fun a b => ct_bool_surjective _.
    have HX := cc_rel_of_eq cid _ _ (cl_map_unmap cid cid (cl_id_rt T) XL).
    have HY := cc_rel_of_eq cid _ _ (cl_map_unmap cid cid (cl_id_rt T) YL).
    have HS := sprop_to_prop _ _ (sub_nat_eq_correspondence _ _ _ _ (cc_size T _ _ HX) (cc_size T _ _ HY)) HL.
    exact (cc_reflect_forward _ _ _ _ (cc_zipP_prop T x0 _ _ HP _ _ _ _ HX HY) (cc_zipP_bool T _ _ HP _ _ _ _ HX HY)
      (g x0 (fun a b => ct_l2b (PL a b)) _ _ HS)).
  - intros h x0 PR X Y HS.
    have HP : forall a b, CtBoolRel (PR a b) (ct_b2l (PR a b)) := fun a b => ct_bool_canonical _.
    have HX := cc_list_rel_canonical (B := T) cid X. have HY := cc_list_rel_canonical (B := T) cid Y.
    have HL := prop_to_sprop _ _ (sub_nat_eq_correspondence _ _ _ _ (cc_size T _ _ HX) (cc_size T _ _ HY)) HS.
    exact (cc_reflect_backward _ _ _ _ (cc_zipP_prop T x0 _ _ HP _ _ _ _ HX HY) (cc_zipP_bool T _ _ HP _ _ _ _ HX HY)
      (h x0 (fun a b => ct_b2l (PR a b)) _ _ HL)).
Defined.

Definition src_mem_zip_exists (T T' : eqType) : Prop := ltac:(type_of_term (@mem_zip_exists T T')).
Definition tgt_mem_zip_exists (T T' : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Util_List_mem_zip_exists T T' (ct_decidable_eq T) (ct_decidable_eq T'))).
Theorem mem_zip_exists_correspondence (T T' : eqType) : PropSPropRel (src_mem_zip_exists T T') (tgt_mem_zip_exists T T').
Proof.
  unfold src_mem_zip_exists, tgt_mem_zip_exists.
  apply: ct_forall_identity => x1. apply: ct_forall_identity => x2.
  apply: cc_forall_list => l1 L1 H1. apply: cc_forall_list => l2 L2 H2.
  apply: ct_forall_identity => e1. apply: ct_forall_identity => e2.
  apply: ct_imp; first exact (sub_nat_eq_correspondence _ _ _ _ (cc_size T _ _ H1) (cc_size T' _ _ H2)).
  apply: ct_imp; first exact (cc_mem_pair T T' x1 x2 _ _ (cc_zip T T' l1 L1 l2 L2 H1 H2)).
  apply: ct_exists_nat => iR iL Hi.
  apply: ct_and; first exact (sub_nat_lt_correspondence _ _ _ _ Hi (cc_size T _ _ H1)).
  apply: ct_and; first exact (sub_nat_lt_correspondence _ _ _ _ Hi (cc_size T' _ _ H2)).
  apply: ct_and.
  - exact (cc_val_eq T _ _ _ _ (Logic.eq_refl _) (cc_nth T e1 l1 L1 iR iL H1 Hi)).
  - exact (cc_val_eq T' _ _ _ _ (Logic.eq_refl _) (cc_nth T' e2 l2 L2 iR iL H2 Hi)).
Qed.

Definition src_mem_zip (T T' : eqType) : Prop := ltac:(type_of_term (@mem_zip T T')).
Definition tgt_mem_zip (T T' : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Util_List_mem_zip T T' (ct_decidable_eq T) (ct_decidable_eq T'))).
Theorem mem_zip_correspondence (T T' : eqType) : PropSPropRel (src_mem_zip T T') (tgt_mem_zip T T').
Proof.
  unfold src_mem_zip, tgt_mem_zip.
  apply: ct_forall_identity => x1. apply: ct_forall_identity => x2.
  apply: cc_forall_list => l1 L1 H1. apply: cc_forall_list => l2 L2 H2.
  apply: ct_imp; first exact (sub_nat_eq_correspondence _ _ _ _ (cc_size T _ _ H1) (cc_size T' _ _ H2)).
  apply: ct_imp; first exact (cc_mem_pair T T' x1 x2 _ _ (cc_zip T T' l1 L1 l2 L2 H1 H2)).
  exact (ct_and _ _ _ _ (cc_mem T x1 l1 L1 H1) (cc_mem T' x2 l2 L2 H2)).
Qed.

Lemma cc_nseq (T : Type) (y : T) nR nL : SubNatRel nR nL -> ClListRel (B := T) cid (nseq nR y) (I.List_replicate T nL y).
Proof. intro Hn. rewrite (cl_nat_logic _ _ Hn). exact (cc_rel_of_eq _ _ _ (cl_nseq cid y nR)). Qed.

Definition src_mem_zip_nseq_r (T1 T2 : eqType) : Prop := ltac:(type_of_term (@mem_zip_nseq_r T1 T2)).
Definition tgt_mem_zip_nseq_r (T1 T2 : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Util_List_mem_zip_nseq_r T1 T2 (ct_decidable_eq T1) (ct_decidable_eq T2))).
Theorem mem_zip_nseq_r_correspondence (T1 T2 : eqType) : PropSPropRel (src_mem_zip_nseq_r T1 T2) (tgt_mem_zip_nseq_r T1 T2).
Proof.
  unfold src_mem_zip_nseq_r, tgt_mem_zip_nseq_r.
  apply: ct_forall_identity => x. apply: ct_forall_identity => y.
  apply: ct_forall_nat => nR nL Hn. apply: cc_forall_list => l L H.
  apply: ct_imp; first exact (sub_nat_eq_correspondence _ _ _ _ (cc_size T1 _ _ H) Hn).
  apply: ct_bool_eq; apply: ct_decide_bool.
  - exact (cc_mem_pair T1 T2 x y _ _ (cc_zip T1 T2 _ _ _ _ H (cc_nseq T2 y nR nL Hn))).
  - exact (cc_mem T1 x l L H).
Qed.

Definition src_mem_zip_nseq_l (T1 T2 : eqType) : Prop := ltac:(type_of_term (@mem_zip_nseq_l T1 T2)).
Definition tgt_mem_zip_nseq_l (T1 T2 : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Util_List_mem_zip_nseq_l T1 T2 (ct_decidable_eq T1) (ct_decidable_eq T2))).
Theorem mem_zip_nseq_l_correspondence (T1 T2 : eqType) : PropSPropRel (src_mem_zip_nseq_l T1 T2) (tgt_mem_zip_nseq_l T1 T2).
Proof.
  unfold src_mem_zip_nseq_l, tgt_mem_zip_nseq_l.
  apply: ct_forall_identity => x. apply: ct_forall_identity => y.
  apply: ct_forall_nat => nR nL Hn. apply: cc_forall_list => l L H.
  apply: ct_imp; first exact (sub_nat_eq_correspondence _ _ _ _ (cc_size T2 _ _ H) Hn).
  apply: ct_bool_eq; apply: ct_decide_bool.
  - exact (cc_mem_pair T1 T2 x y _ _ (cc_zip T1 T2 _ _ _ _ (cc_nseq T1 x nR nL Hn) H)).
  - exact (cc_mem T2 y l L H).
Qed.

Definition src_unzip1_pair (T1 T2 : eqType) : Prop := ltac:(type_of_term (@unzip1_pair T1 T2)).
Definition tgt_unzip1_pair (T1 T2 : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Util_List_unzip1_pair T1 T2 (ct_decidable_eq T1) (ct_decidable_eq T2))).
Theorem unzip1_pair_correspondence (T1 T2 : eqType) : PropSPropRel (src_unzip1_pair T1 T2) (tgt_unzip1_pair T1 T2).
Proof.
  unfold src_unzip1_pair, tgt_unzip1_pair.
  apply: cc_forall_list => l L H. apply: cc_forall_type_fun => f. destruct H.
  apply: (cc_list_eq cid cid (cl_id_rt T1)); last exact (cc_list_rel_canonical cid l).
  apply: cc_rel_of_eq. rewrite cc_unzip1.
  rewrite (cl_map_op cid cl_pair (fun x => (x, f x)) (fun x => I.Prod_mk T1 T2 x (f x)) (fun _ => Logic.eq_refl _) l).
  reflexivity.
Qed.

Definition src_unzip2_pair (T1 T2 : eqType) : Prop := ltac:(type_of_term (@unzip2_pair T1 T2)).
Definition tgt_unzip2_pair (T1 T2 : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Util_List_unzip2_pair T1 T2 (ct_decidable_eq T1) (ct_decidable_eq T2))).
Theorem unzip2_pair_correspondence (T1 T2 : eqType) : PropSPropRel (src_unzip2_pair T1 T2) (tgt_unzip2_pair T1 T2).
Proof.
  unfold src_unzip2_pair, tgt_unzip2_pair.
  apply: cc_forall_list => l L H. apply: cc_forall_type_fun => f. destruct H.
  apply: (cc_list_eq cid cid (cl_id_rt T1)); last exact (cc_list_rel_canonical cid l).
  apply: cc_rel_of_eq. rewrite cc_unzip2.
  rewrite (cl_map_op cid cl_pair (fun x => (f x, x)) (fun x => I.Prod_mk T2 T1 (f x) x) (fun _ => Logic.eq_refl _) l).
  reflexivity.
Qed.

Definition src_eq_unzip1 (T1 T2 : eqType) : Prop := ltac:(type_of_term (@eq_unzip1 T1 T2)).
Definition tgt_eq_unzip1 (T1 T2 : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Util_List_eq_unzip1 T1 T2 (ct_decidable_eq T1) (ct_decidable_eq T2))).
Theorem eq_unzip1_correspondence (T1 T2 : eqType) : PropSPropRel (src_eq_unzip1 T1 T2) (tgt_eq_unzip1 T1 T2).
Proof.
  unfold src_eq_unzip1, tgt_eq_unzip1.
  apply: cc_forall_pair_list => l1 L1 H1. apply: cc_forall_pair_list => l2 L2 H2. apply: cc_forall_pair => x0.
  apply: ct_imp; first exact (sub_nat_eq_correspondence _ _ _ _ (cc_size_gen cl_pair _ _ H1) (cc_size_gen cl_pair _ _ H2)).
  destruct H1, H2. apply: ct_imp.
  - apply: ct_forall_nat => iR iL Hi. rewrite (cl_nat_logic _ _ Hi).
    apply: ct_imp; first exact (sub_nat_lt_correspondence _ _ _ _ (sub_nat_rel_canonical iR) (cl_size cl_pair l1)).
    rewrite -(cl_nth cl_pair x0 l1 iR) -(cl_nth cl_pair x0 l2 iR). exact (ct_eq_rel T1 _ _).
  - apply: (cc_list_eq cid cid (cl_id_rt T1)); apply: cc_rel_of_eq; exact (cc_unzip1 T1 T2 _).
Qed.

Definition src_eq_unzip2 (T1 T2 : eqType) : Prop := ltac:(type_of_term (@eq_unzip2 T1 T2)).
Definition tgt_eq_unzip2 (T1 T2 : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Util_List_eq_unzip2 T1 T2 (ct_decidable_eq T1) (ct_decidable_eq T2))).
Theorem eq_unzip2_correspondence (T1 T2 : eqType) : PropSPropRel (src_eq_unzip2 T1 T2) (tgt_eq_unzip2 T1 T2).
Proof.
  unfold src_eq_unzip2, tgt_eq_unzip2.
  apply: cc_forall_pair_list => l1 L1 H1. apply: cc_forall_pair_list => l2 L2 H2. apply: cc_forall_pair => x0.
  apply: ct_imp; first exact (sub_nat_eq_correspondence _ _ _ _ (cc_size_gen cl_pair _ _ H1) (cc_size_gen cl_pair _ _ H2)).
  destruct H1, H2. apply: ct_imp.
  - apply: ct_forall_nat => iR iL Hi. rewrite (cl_nat_logic _ _ Hi).
    apply: ct_imp; first exact (sub_nat_lt_correspondence _ _ _ _ (sub_nat_rel_canonical iR) (cl_size cl_pair l1)).
    rewrite -(cl_nth cl_pair x0 l1 iR) -(cl_nth cl_pair x0 l2 iR). exact (ct_eq_rel T2 _ _).
  - apply: (cc_list_eq cid cid (cl_id_rt T2)); apply: cc_rel_of_eq; exact (cc_unzip2 T1 T2 _).
Qed.

(* ------------------------------------------------------------------ *)
(** * [nth] and [nth_or_none] *)

Lemma cc_nth_or_none_eq (T : Type) l L n nL (o : option T) : ClListRel cid l L -> SubNatRel n nL ->
  PropSPropRel (Logic.eq (nth_or_none l n) o) (Lean.eq (I.Prosa_Classic_Util_List_nth_or_none T L nL) (cl_opt o)).
Proof.
  intros H Hn. destruct H. rewrite (cl_nat_logic _ _ Hn) -nth_or_none_correspondence. exact (cc_opt_eq _ _).
Qed.

Definition src_nth_in_or_default (T : eqType) : Prop := ltac:(type_of_term (@nth_in_or_default T)).
Definition tgt_nth_in_or_default (T : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Util_List_nth_in_or_default T (ct_decidable_eq T))).
Theorem nth_in_or_default_correspondence (T : eqType) : PropSPropRel (src_nth_in_or_default T) (tgt_nth_in_or_default T).
Proof.
  unfold src_nth_in_or_default, tgt_nth_in_or_default.
  apply: cc_forall_list => l L H. apply: ct_forall_identity => x0. apply: ct_forall_nat => iR iL Hi.
  rewrite (cc_nth T x0 l L iR iL H Hi).
  exact (ct_or _ _ _ _ (cc_mem T _ l L H) (ct_eq_rel T _ _)).
Qed.

Definition src_nth_neq_default (T : eqType) : Prop := ltac:(type_of_term (@nth_neq_default T)).
Definition tgt_nth_neq_default (T : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Util_List_nth_neq_default T (ct_decidable_eq T))).
Theorem nth_neq_default_correspondence (T : eqType) : PropSPropRel (src_nth_neq_default T) (tgt_nth_neq_default T).
Proof.
  unfold src_nth_neq_default, tgt_nth_neq_default.
  apply: cc_forall_list => l L H. apply: ct_forall_identity => x0. apply: ct_forall_nat => iR iL Hi.
  apply: ct_forall_identity => y. rewrite (cc_nth T x0 l L iR iL H Hi).
  apply: ct_imp; first exact (ct_eq_rel T _ _).
  exact (ct_imp _ _ _ _ (cc_ne T y x0) (cc_mem T y l L H)).
Qed.

Definition src_nth_or_none_mem (T : eqType) : Prop := ltac:(type_of_term (@nth_or_none_mem T)).
Definition tgt_nth_or_none_mem (T : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Util_List_nth_or_none_mem T (ct_decidable_eq T))).
Theorem nth_or_none_mem_correspondence (T : eqType) : PropSPropRel (src_nth_or_none_mem T) (tgt_nth_or_none_mem T).
Proof.
  unfold src_nth_or_none_mem, tgt_nth_or_none_mem.
  apply: cc_forall_list => l L H. apply: ct_forall_nat => nR nL Hn. apply: ct_forall_identity => x.
  exact (ct_imp _ _ _ _ (cc_nth_or_none_eq T l L nR nL (Some x) H Hn) (cc_mem T x l L H)).
Qed.

Definition src_nth_or_none_mem_exists (T : eqType) : Prop := ltac:(type_of_term (@nth_or_none_mem_exists T)).
Definition tgt_nth_or_none_mem_exists (T : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Util_List_nth_or_none_mem_exists T (ct_decidable_eq T))).
Theorem nth_or_none_mem_exists_correspondence (T : eqType) :
  PropSPropRel (src_nth_or_none_mem_exists T) (tgt_nth_or_none_mem_exists T).
Proof.
  unfold src_nth_or_none_mem_exists, tgt_nth_or_none_mem_exists.
  apply: cc_forall_list => l L H. apply: ct_forall_identity => x.
  apply: ct_imp; first exact (cc_mem T x l L H).
  apply: ct_exists_nat => nR nL Hn. exact (cc_nth_or_none_eq T l L nR nL (Some x) H Hn).
Qed.

Definition src_nth_or_none_size_none (T : eqType) : Prop := ltac:(type_of_term (@nth_or_none_size_none T)).
Definition tgt_nth_or_none_size_none (T : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Util_List_nth_or_none_size_none T (ct_decidable_eq T))).
Theorem nth_or_none_size_none_correspondence (T : eqType) :
  PropSPropRel (src_nth_or_none_size_none T) (tgt_nth_or_none_size_none T).
Proof.
  unfold src_nth_or_none_size_none, tgt_nth_or_none_size_none.
  apply: cc_forall_list => l L H. apply: ct_forall_nat => nR nL Hn.
  exact (cc_iff _ _ _ _ (cc_nth_or_none_eq T l L nR nL None H Hn) (sub_nat_le_correspondence _ _ _ _ (cc_size T l L H) Hn)).
Qed.

Definition src_nth_or_none_size_some (T : eqType) : Prop := ltac:(type_of_term (@nth_or_none_size_some T)).
Definition tgt_nth_or_none_size_some (T : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Util_List_nth_or_none_size_some T (ct_decidable_eq T))).
Theorem nth_or_none_size_some_correspondence (T : eqType) :
  PropSPropRel (src_nth_or_none_size_some T) (tgt_nth_or_none_size_some T).
Proof.
  unfold src_nth_or_none_size_some, tgt_nth_or_none_size_some.
  apply: cc_forall_list => l L H. apply: ct_forall_nat => nR nL Hn. apply: ct_forall_identity => x.
  exact (ct_imp _ _ _ _ (cc_nth_or_none_eq T l L nR nL (Some x) H Hn) (sub_nat_lt_correspondence _ _ _ _ Hn (cc_size T l L H))).
Qed.

Definition src_nth_or_none_uniq (T : eqType) : Prop := ltac:(type_of_term (@nth_or_none_uniq T)).
Definition tgt_nth_or_none_uniq (T : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Util_List_nth_or_none_uniq T (ct_decidable_eq T))).
Theorem nth_or_none_uniq_correspondence (T : eqType) : PropSPropRel (src_nth_or_none_uniq T) (tgt_nth_or_none_uniq T).
Proof.
  unfold src_nth_or_none_uniq, tgt_nth_or_none_uniq.
  apply: cc_forall_list => l L H. apply: ct_forall_nat => iR iL Hi. apply: ct_forall_nat => jR jL Hj.
  apply: ct_forall_identity => x.
  apply: ct_imp; first exact (cc_uniq T l L H).
  apply: ct_imp; first exact (cc_nth_or_none_eq T l L iR iL (Some x) H Hi).
  apply: ct_imp; first exact (cc_nth_or_none_eq T l L jR jL (Some x) H Hj).
  exact (sub_nat_eq_correspondence _ _ _ _ Hi Hj).
Qed.

Definition src_nth_or_none_nth (T : eqType) : Prop := ltac:(type_of_term (@nth_or_none_nth T)).
Definition tgt_nth_or_none_nth (T : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Util_List_nth_or_none_nth T (ct_decidable_eq T))).
Theorem nth_or_none_nth_correspondence (T : eqType) : PropSPropRel (src_nth_or_none_nth T) (tgt_nth_or_none_nth T).
Proof.
  unfold src_nth_or_none_nth, tgt_nth_or_none_nth.
  apply: cc_forall_list => l L H. apply: ct_forall_nat => nR nL Hn.
  apply: ct_forall_identity => x. apply: ct_forall_identity => x0.
  apply: ct_imp; first exact (cc_nth_or_none_eq T l L nR nL (Some x) H Hn).
  exact (cc_val_eq T _ _ _ _ (cc_nth T x0 l L nR nL H Hn) (Logic.eq_refl _)).
Qed.

(* ------------------------------------------------------------------ *)
(** * [pmap] *)

Definition CcOptFunRel {A B : Type} (fR : A -> option B) (fL : A -> I.Option B) : Prop :=
  forall x, Logic.eq (fL x) (cl_opt (fR x)).

Lemma cc_forall_optfun (A B : Type) (PR : (A -> option B) -> Prop) (PL : (A -> I.Option B) -> SProp) :
  (forall fR fL, CcOptFunRel fR fL -> PropSPropRel (PR fR) (PL fL)) ->
  PropSPropRel (forall f, PR f) (forall f, PL f).
Proof.
  intro H. apply prop_sprop_rel_intro.
  - intros HR fL. apply (prop_to_sprop _ _ (H (fun x => cl_unopt (fL x)) fL (fun x => Logic.eq_sym (cl_opt_unopt _))) (HR _)).
  - intro HL. apply strictly_inhabits. intro fR. exact (sprop_to_prop _ _ (H fR (fun x => cl_opt (fR x)) (fun _ => Logic.eq_refl _)) (HL _)).
Qed.

Lemma cc_optfun_eq {A B : Type} (fR : A -> option B) fL (Hf : CcOptFunRel fR fL) x y :
  PropSPropRel (Logic.eq (fR x) (fR y)) (Lean.eq (fL x) (fL y)).
Proof. rewrite (Hf x) (Hf y). exact (cc_opt_eq _ _). Qed.

Lemma cc_pmap (T T' : Type) fR fL (Hf : CcOptFunRel fR fL) s L : ClListRel (B := T) cid s L ->
  ClListRel (B := T') cid (pmap fR s) (I.List_filterMap T T' fL L).
Proof.
  intro H. destruct H. apply: cc_rel_of_eq. apply: cl_pmap => x. rewrite Hf. by case: (fR x).
Qed.

Definition src_pmap_inj_in_uniq (T T' : eqType) : Prop := ltac:(type_of_term (@pmap_inj_in_uniq T T')).
Definition tgt_pmap_inj_in_uniq (T T' : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Util_List_pmap_inj_in_uniq T T' (ct_decidable_eq T) (ct_decidable_eq T'))).
Theorem pmap_inj_in_uniq_correspondence (T T' : eqType) : PropSPropRel (src_pmap_inj_in_uniq T T') (tgt_pmap_inj_in_uniq T T').
Proof.
  unfold src_pmap_inj_in_uniq, tgt_pmap_inj_in_uniq.
  apply: cc_forall_list => s L H. apply: cc_forall_optfun => fR fL Hf.
  apply: ct_imp.
  - rewrite /prop_in11. apply: ct_forall_identity => x. apply: ct_forall_identity => y.
    apply: ct_imp; first exact (cc_mem T x s L H).
    apply: ct_imp; first exact (cc_mem T y s L H).
    exact (ct_imp _ _ _ _ (cc_optfun_eq fR fL Hf x y) (ct_eq_rel T x y)).
  - apply: ct_imp; first exact (cc_uniq T s L H).
    exact (cc_uniq T' _ _ (cc_pmap T T' fR fL Hf s L H)).
Qed.

Definition src_pmap_inj_uniq (T T' : eqType) : Prop := ltac:(type_of_term (@pmap_inj_uniq T T')).
Definition tgt_pmap_inj_uniq (T T' : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Util_List_pmap_inj_uniq T T' (ct_decidable_eq T) (ct_decidable_eq T'))).
Theorem pmap_inj_uniq_correspondence (T T' : eqType) : PropSPropRel (src_pmap_inj_uniq T T') (tgt_pmap_inj_uniq T T').
Proof.
  unfold src_pmap_inj_uniq, tgt_pmap_inj_uniq.
  apply: cc_forall_list => s L H. apply: cc_forall_optfun => fR fL Hf.
  apply: ct_imp.
  - rewrite /injective. apply: ct_forall_identity => x. apply: ct_forall_identity => y.
    exact (ct_imp _ _ _ _ (cc_optfun_eq fR fL Hf x y) (ct_eq_rel T x y)).
  - apply: ct_imp; first exact (cc_uniq T s L H).
    exact (cc_uniq T' _ _ (cc_pmap T T' fR fL Hf s L H)).
Qed.

(* ------------------------------------------------------------------ *)
(** * [replace_first] *)

Lemma cc_replace_first (T : Type) PR PL (HP : forall x, CtBoolRel (PR x) (PL x)) (f : T -> T) l L :
  ClListRel cid l L -> ClListRel cid (replace_first PR f l) (I.Prosa_Classic_Util_List_replace_first T PL f L).
Proof. intro H. destruct H. exact (cc_rel_of_eq _ _ _ (replace_first_correspondence T PR PL HP f l)). Qed.

Definition src_replace_first_size (T : eqType) : Prop := ltac:(type_of_term (@replace_first_size T)).
Definition tgt_replace_first_size (T : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Util_List_replace_first_size T (ct_decidable_eq T))).
Theorem replace_first_size_correspondence (T : eqType) : PropSPropRel (src_replace_first_size T) (tgt_replace_first_size T).
Proof.
  unfold src_replace_first_size, tgt_replace_first_size.
  apply: cc_forall_bool_rel1 => PR PL HP. apply: ct_forall_identity => f. apply: cc_forall_list => l L H.
  exact (sub_nat_eq_correspondence _ _ _ _ (cc_size T _ _ (cc_replace_first T PR PL HP f l L H)) (cc_size T _ _ H)).
Qed.

Definition src_replace_first_cases (T : eqType) : Prop := ltac:(type_of_term (@replace_first_cases T)).
Definition tgt_replace_first_cases (T : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Util_List_replace_first_cases T (ct_decidable_eq T))).
Theorem replace_first_cases_correspondence (T : eqType) : PropSPropRel (src_replace_first_cases T) (tgt_replace_first_cases T).
Proof.
  unfold src_replace_first_cases, tgt_replace_first_cases.
  apply: cc_forall_bool_rel1 => PR PL HP. apply: ct_forall_identity => f. apply: cc_forall_list => l L H.
  apply: ct_forall_identity => x.
  apply: ct_imp; first exact (cc_mem T x _ _ (cc_replace_first T PR PL HP f l L H)).
  apply: ct_or; first exact (cc_mem T x l L H).
  apply: cc_exists_identity => y.
  apply: ct_and; first exact (ct_eq_rel T _ _).
  exact (ct_and _ _ _ _ (ct_bool_truth _ _ (HP y)) (cc_mem T y l L H)).
Qed.

Definition src_replace_first_no_change (T : eqType) : Prop := ltac:(type_of_term (@replace_first_no_change T)).
Definition tgt_replace_first_no_change (T : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Util_List_replace_first_no_change T (ct_decidable_eq T))).
Theorem replace_first_no_change_correspondence (T : eqType) :
  PropSPropRel (src_replace_first_no_change T) (tgt_replace_first_no_change T).
Proof.
  unfold src_replace_first_no_change, tgt_replace_first_no_change.
  apply: cc_forall_bool_rel1 => PR PL HP. apply: ct_forall_identity => f. apply: cc_forall_list => l L H.
  apply: ct_forall_identity => x.
  apply: ct_imp; first exact (cc_mem T x l L H).
  apply: ct_imp; first exact (ct_bool_truth _ _ (ct_bool_not _ _ (HP x))).
  exact (cc_mem T x _ _ (cc_replace_first T PR PL HP f l L H)).
Qed.

Definition src_replace_first_idempotent (T : eqType) : Prop := ltac:(type_of_term (@replace_first_idempotent T)).
Definition tgt_replace_first_idempotent (T : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Util_List_replace_first_idempotent T (ct_decidable_eq T))).
Theorem replace_first_idempotent_correspondence (T : eqType) :
  PropSPropRel (src_replace_first_idempotent T) (tgt_replace_first_idempotent T).
Proof.
  unfold src_replace_first_idempotent, tgt_replace_first_idempotent.
  apply: cc_forall_bool_rel1 => PR PL HP. apply: ct_forall_identity => f. apply: cc_forall_list => l L H.
  apply: ct_forall_identity => x.
  apply: ct_imp; first exact (cc_mem T x l L H).
  apply: ct_imp; first exact (ct_eq_rel T _ _).
  exact (cc_mem T x _ _ (cc_replace_first T PR PL HP f l L H)).
Qed.

Definition src_replace_first_new (T : eqType) : Prop := ltac:(type_of_term (@replace_first_new T)).
Definition tgt_replace_first_new (T : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Util_List_replace_first_new T (ct_decidable_eq T))).
Theorem replace_first_new_correspondence (T : eqType) : PropSPropRel (src_replace_first_new T) (tgt_replace_first_new T).
Proof.
  unfold src_replace_first_new, tgt_replace_first_new.
  apply: cc_forall_bool_rel1 => PR PL HP. apply: ct_forall_identity => f. apply: cc_forall_list => l L H.
  apply: ct_forall_identity => x1. apply: ct_forall_identity => x2.
  have HR := cc_replace_first T PR PL HP f l L H.
  apply: ct_imp; first exact (cl_notin_rel T T cid cid (cl_id_rt T) x1 l L H).
  apply: ct_imp; first exact (cl_notin_rel T T cid cid (cl_id_rt T) x2 l L H).
  apply: ct_imp; first exact (cc_mem T x1 _ _ HR).
  apply: ct_imp; first exact (cc_mem T x2 _ _ HR).
  exact (ct_eq_rel T _ _).
Qed.

Definition src_replace_first_previous (T : eqType) : Prop := ltac:(type_of_term (@replace_first_previous T)).
Definition tgt_replace_first_previous (T : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Util_List_replace_first_previous T (ct_decidable_eq T))).
Theorem replace_first_previous_correspondence (T : eqType) :
  PropSPropRel (src_replace_first_previous T) (tgt_replace_first_previous T).
Proof.
  unfold src_replace_first_previous, tgt_replace_first_previous.
  apply: cc_forall_bool_rel1 => PR PL HP. apply: ct_forall_identity => f. apply: cc_forall_list => l L H.
  apply: ct_forall_identity => x.
  have HR := cc_replace_first T PR PL HP f l L H.
  apply: ct_imp; first exact (cc_mem T x l L H).
  apply: ct_or; first exact (cc_mem T x _ _ HR).
  exact (ct_and _ _ _ _ (ct_bool_truth _ _ (HP x)) (cc_mem T (f x) _ _ HR)).
Qed.

Definition src_replace_first_failed (T : eqType) : Prop := ltac:(type_of_term (@replace_first_failed T)).
Definition tgt_replace_first_failed (T : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Util_List_replace_first_failed T (ct_decidable_eq T))).
Theorem replace_first_failed_correspondence (T : eqType) :
  PropSPropRel (src_replace_first_failed T) (tgt_replace_first_failed T).
Proof.
  unfold src_replace_first_failed, tgt_replace_first_failed.
  apply: cc_forall_bool_rel1 => PR PL HP. apply: ct_forall_identity => f. apply: cc_forall_list => l L H.
  have HR := cc_replace_first T PR PL HP f l L H.
  apply: ct_imp.
  - apply: ct_forall_identity => x.
    apply: ct_imp; first exact (cc_mem T x l L H).
    exact (cl_notin_rel T T cid cid (cl_id_rt T) (f x) _ _ HR).
  - apply: ct_forall_identity => x.
    exact (ct_imp _ _ _ _ (cc_mem T x l L H) (ct_bool_truth _ _ (ct_bool_not _ _ (HP x)))).
Qed.

(* ------------------------------------------------------------------ *)
(** * Pairs as functions *)

Lemma cc_pairs_to_function (T1 T2 : eqType) (y0 : T2) l L x : ClListRel cl_pair l L ->
  Logic.eq (pairs_to_function y0 l x) (I.Prosa_Classic_Util_List_pairs_to_function T1 (ct_decidable_eq T1) T2 y0 L x).
Proof. intro H. destruct H. exact (pairs_to_function_correspondence T1 T2 y0 l x). Qed.

Definition src_pairs_to_function_neq_default (T1 T2 : eqType) : Prop :=
  ltac:(type_of_term (@pairs_to_function_neq_default T1 T2)).
Definition tgt_pairs_to_function_neq_default (T1 T2 : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Util_List_pairs_to_function_neq_default T1 T2 (ct_decidable_eq T1) (ct_decidable_eq T2))).
Theorem pairs_to_function_neq_default_correspondence (T1 T2 : eqType) :
  PropSPropRel (src_pairs_to_function_neq_default T1 T2) (tgt_pairs_to_function_neq_default T1 T2).
Proof.
  unfold src_pairs_to_function_neq_default, tgt_pairs_to_function_neq_default.
  apply: ct_forall_identity => y0. apply: cc_forall_pair_list => l L H.
  apply: ct_forall_identity => x. apply: ct_forall_identity => y.
  apply: ct_imp; first exact (cc_val_eq T2 _ _ _ _ (cc_pairs_to_function T1 T2 y0 l L x H) (Logic.eq_refl _)).
  exact (ct_imp _ _ _ _ (cc_ne T2 y y0) (cc_mem_pair T1 T2 x y l L H)).
Qed.

Definition src_pairs_to_function_mem (T1 T2 : eqType) : Prop := ltac:(type_of_term (@pairs_to_function_mem T1 T2)).
Definition tgt_pairs_to_function_mem (T1 T2 : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Util_List_pairs_to_function_mem T1 T2 (ct_decidable_eq T1) (ct_decidable_eq T2))).
Theorem pairs_to_function_mem_correspondence (T1 T2 : eqType) :
  PropSPropRel (src_pairs_to_function_mem T1 T2) (tgt_pairs_to_function_mem T1 T2).
Proof.
  unfold src_pairs_to_function_mem, tgt_pairs_to_function_mem.
  apply: ct_forall_identity => y0. apply: cc_forall_pair_list => l L H.
  apply: ct_forall_identity => x. apply: ct_forall_identity => y.
  apply: ct_imp.
  - apply: (cc_uniq T1). destruct H. exact (cc_rel_of_eq _ _ _ (cc_unzip1 T1 T2 l)).
  - apply: ct_imp; first exact (cc_mem_pair T1 T2 x y l L H).
    exact (cc_val_eq T2 _ _ _ _ (cc_pairs_to_function T1 T2 y0 l L x H) (Logic.eq_refl _)).
Qed.

(* ------------------------------------------------------------------ *)
(** * Additional lemmas *)

Definition src_in_cat (X : eqType) : Prop := ltac:(type_of_term (@in_cat X)).
Definition tgt_in_cat (X : eqType) : SProp := ltac:(type_of_term (I.Prosa_Classic_Util_List_in_cat X (ct_decidable_eq X))).
Theorem in_cat_correspondence (X : eqType) : PropSPropRel (src_in_cat X) (tgt_in_cat X).
Proof.
  unfold src_in_cat, tgt_in_cat.
  apply: ct_forall_identity => x. apply: cc_forall_list => xs XS H.
  apply: ct_imp; first exact (cc_mem X x xs XS H).
  apply: (cl_exists_list cid cid (cl_id_rt X)) => l1 L1 H1. apply: (cl_exists_list cid cid (cl_id_rt X)) => l2 L2 H2.
  apply: (cc_list_eq cid cid (cl_id_rt X)); first exact H.
  destruct H1, H2. apply: cc_rel_of_eq. rewrite catA cl_cat cl_cat. reflexivity.
Qed.

(** Natural-number lists live in the [Set]-level Lean list. *)
Fixpoint cc_natl (s : seq nat) : I.List_inst1 Lean.Nat :=
  match s with [::] => I.List_nil_inst1 _ | x :: s' => I.List_cons_inst1 _ (sub_nat_to_imported x) (cc_natl s') end.
Fixpoint cc_unnatl (l : I.List_inst1 Lean.Nat) : seq nat :=
  match l with I.List_nil_inst1 => [::] | I.List_cons_inst1 x l' => sub_nat_to_rocq x :: cc_unnatl l' end.
Lemma cc_natl_unnatl l : Logic.eq (cc_natl (cc_unnatl l)) l.
Proof. induction l as [|x l IH]; first reflexivity. cbn. by rewrite sub_nat_imported_roundtrip IH. Qed.

Lemma cc_forall_natl (PR : seq nat -> Prop) (PL : I.List_inst1 Lean.Nat -> SProp) :
  (forall s, PropSPropRel (PR s) (PL (cc_natl s))) -> PropSPropRel (forall s, PR s) (forall l, PL l).
Proof.
  intro H. apply prop_sprop_rel_intro.
  - intros HR l. have S := prop_to_sprop _ _ (H (cc_unnatl l)) (HR _). rewrite cc_natl_unnatl in S. exact S.
  - intro HL. apply strictly_inhabits. intro s. exact (sprop_to_prop _ _ (H s) (HL _)).
Qed.

Lemma cc_maxn a b : Logic.eq (sub_nat_to_imported (maxn a b)) (I.Nat_max (sub_nat_to_imported a) (sub_nat_to_imported b)).
Proof.
  have Hle := sub_nat_le_correspondence _ _ _ _ (sub_nat_rel_canonical a) (sub_nat_rel_canonical b).
  have -> : Logic.eq (I.Nat_max (sub_nat_to_imported a) (sub_nat_to_imported b))
      (I.ite Lean.Nat (I.LE_le_inst1 Lean.Nat I.instLENat (sub_nat_to_imported a) (sub_nat_to_imported b))
         (I.Nat_decLe (sub_nat_to_imported a) (sub_nat_to_imported b)) (sub_nat_to_imported b) (sub_nat_to_imported a))
    by reflexivity.
  destruct (I.Nat_decLe (sub_nat_to_imported a) (sub_nat_to_imported b)) as [h|h].
  - have Hab : ~~ (a <= b).
    { apply/negP => Hs. exact (interpret_strict _ (ct_target_false_to_strict (h (prop_to_sprop _ _ Hle Hs)))). }
    rewrite -ltnNge in Hab. rewrite (maxn_idPl (ltnW Hab)). reflexivity.
  - have Hab : a <= b := sprop_to_prop _ _ Hle h. rewrite (maxn_idPr Hab). reflexivity.
Qed.

Lemma cc_foldl_maxn : forall (s : seq nat) a,
  Logic.eq (sub_nat_to_imported (foldl maxn a s)) (I.List_foldl_inst3 Lean.Nat Lean.Nat I.Nat_max (sub_nat_to_imported a) (cc_natl s)).
Proof. elim => [|x s IH] a //=. by rewrite IH cc_maxn. Qed.

Definition src_seq_max_cons : Prop := ltac:(type_of_term @seq_max_cons).
Definition tgt_seq_max_cons : SProp := ltac:(type_of_term I.Prosa_Classic_Util_List_seq_max_cons).
Theorem seq_max_cons_correspondence : PropSPropRel src_seq_max_cons tgt_seq_max_cons.
Proof.
  unfold src_seq_max_cons, tgt_seq_max_cons.
  apply: ct_forall_nat => x xL Hx. apply: cc_forall_natl => s. rewrite (cl_nat_logic _ _ Hx).
  apply: sub_nat_eq_correspondence; apply: cl_lean_eq.
  - exact (cc_foldl_maxn (x :: s) 0).
  - by rewrite cc_maxn (cc_foldl_maxn s 0).
Qed.

Definition src_subseq_leq_size (X : eqType) : Prop := ltac:(type_of_term (@subseq_leq_size X)).
Definition tgt_subseq_leq_size (X : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Util_List_subseq_leq_size X (ct_decidable_eq X))).
Theorem subseq_leq_size_correspondence (X : eqType) : PropSPropRel (src_subseq_leq_size X) (tgt_subseq_leq_size X).
Proof.
  unfold src_subseq_leq_size, tgt_subseq_leq_size.
  apply: cc_forall_list => xs XS Hx. apply: cc_forall_list => ys YS Hy.
  apply: ct_imp; first exact (cc_uniq X xs XS Hx).
  apply: ct_imp.
  - apply: ct_forall_identity => x. exact (ct_imp _ _ _ _ (cc_mem X x xs XS Hx) (cc_mem X x ys YS Hy)).
  - exact (sub_nat_le_correspondence _ _ _ _ (cc_size X _ _ Hx) (cc_size X _ _ Hy)).
Qed.
