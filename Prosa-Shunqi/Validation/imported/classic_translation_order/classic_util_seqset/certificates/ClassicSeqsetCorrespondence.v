From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq fintype.
From prosa Require Import classic.util.seqset.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedClassicSeqset.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence ClassicSeqsetAdapter.

Module I := ImportedClassicSeqset.

(** Certificates for [classic/util/seqset.v] (ProsaBuddy classic, commit f692cb7).

    Inputs.  For an [eqType] [T], the Lean [DecidableEq T] instance is the
    eqType's decision procedure ([seqset_decidable_eq], as for the accepted v0.6
    [util/seqset]); sequence-sets are related by the accepted [RocqSeqSetRel]
    (two-way totals); for a [finType] [T], the Lean [Fintype T] instance is
    built from MathComp's enumeration [enum T] ([cs_fintype]).  Natural numbers
    by [SubNatRel], Booleans constructor-wise.

    Membership.  Lean's [decide (x ∈ l)] is related to [x \in l] through the
    propositional correspondence of membership ([cs_decide_bool]); the Lean
    decision procedure itself is never unfolded.

    Statements.  The source side is the exact elaborated type of the pinned
    lemma (via [type of]; the source proof is not used). *)

Ltac type_of_term t := let T := type of t in exact T.

(* ------------------------------------------------------------------ *)
(** * Booleans and natural numbers *)

Definition cs_b2l (b : bool) : I.Bool := if b then I.Bool_true else I.Bool_false.
Definition CsBoolRel (bR : bool) (bL : I.Bool) : SProp := Lean.eq (cs_b2l bR) bL.

Lemma cs_bool_rel_logic bR bL : CsBoolRel bR bL -> Logic.eq bL (cs_b2l bR).
Proof. intro H. exact (Logic.eq_sym (imported_eq_to_coq_eq _ _ H)). Qed.

Definition cs_false_elim (Q : SProp) (H : I.False) : Q := match H return Q with end.

Lemma cs_decide_bool (b : bool) (Q : SProp) (d : I.Decidable Q) :
  PropSPropRel (is_true b) Q -> CsBoolRel b (I.Decidable_decide Q d).
Proof.
  intro Hrel. unfold CsBoolRel.
  destruct d as [Hfalse | Htrue]; destruct b; cbn.
  - exact (cs_false_elim _ (Hfalse (prop_to_sprop _ _ Hrel (Logic.eq_refl true)))).
  - exact (@Lean.eq_refl _ _).
  - exact (@Lean.eq_refl _ _).
  - exact (cs_false_elim _ (seqset_coq_false_to_imported (match sprop_to_prop _ _ Hrel Htrue with end))).
Qed.

Lemma cs_bool_eq aR aL bR bL :
  CsBoolRel aR aL -> CsBoolRel bR bL -> PropSPropRel (Logic.eq aR bR) (Lean.eq aL bL).
Proof.
  intros Ha Hb. rewrite (cs_bool_rel_logic _ _ Ha) (cs_bool_rel_logic _ _ Hb). clear Ha Hb.
  apply prop_sprop_rel_intro.
  - intro E. rewrite E. exact (@Lean.eq_refl _ _).
  - intro E. apply strictly_inhabits. have E' := imported_eq_to_coq_eq _ _ E. clear E.
    move: E'. by case: aR; case: bR.
Qed.

(* ------------------------------------------------------------------ *)
(** * Sequences, membership, sets *)

Lemma cs_mem_rel (T : eqType) (x : T) (l : seq T) (lL : I.List T) :
  Lean.eq (seqset_seq_to_list l) lL -> PropSPropRel (x \in l) (I.List_Mem T x lL).
Proof.
  intro H. destruct H. apply prop_sprop_rel_intro.
  - intro Hx. exact (seqset_mem_forward x l (seqset_bool_prop_to_truth _ Hx)).
  - intro Hx. have S := seqset_imported_mem_to_strict x _ Hx.
    rewrite seqset_seq_roundtrip in S. exact S.
Qed.

Lemma cs_seqset_target_total (T : eqType) (s : I.Prosa_Util_Seqset_set T (seqset_decidable_eq T)) :
  RocqSeqSetRel T (imported_to_source_seqset T s) s.
Proof. destruct s as [xs Hnodup]. exact (seqset_list_roundtrip xs). Qed.

Lemma cs_forall_seqset (T : eqType) (PR : @prosa.util.seqset.set T -> Prop)
    (PL : I.Prosa_Util_Seqset_set T (seqset_decidable_eq T) -> SProp) :
  (forall sR sL, RocqSeqSetRel T sR sL -> PropSPropRel (PR sR) (PL sL)) ->
  PropSPropRel (forall s, PR s) (forall s, PL s).
Proof.
  intro H. apply prop_sprop_rel_intro.
  - intros HR sL. exact (prop_to_sprop _ _ (H _ _ (cs_seqset_target_total T sL)) (HR _)).
  - intro HL. apply strictly_inhabits. intro sR.
    exact (sprop_to_prop _ _ (H _ _ (seqset_relation_source_total T sR)) (HL _)).
Qed.

Lemma cs_forall_identity (A : Type) (PR : A -> Prop) (PL : A -> SProp) :
  (forall x, PropSPropRel (PR x) (PL x)) -> PropSPropRel (forall x, PR x) (forall x, PL x).
Proof.
  intro H. apply prop_sprop_rel_intro.
  - intros HR x. exact (prop_to_sprop _ _ (H x) (HR x)).
  - intro HL. apply strictly_inhabits. intro x. exact (sprop_to_prop _ _ (H x) (HL x)).
Qed.

(* ------------------------------------------------------------------ *)
(** * [set_mem] *)

Definition src_set_mem (T : eqType) : Prop := ltac:(type_of_term (@set_mem T)).
Definition tgt_set_mem (T : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Util_Seqset_set_mem T (seqset_decidable_eq T))).

Theorem set_mem_correspondence (T : eqType) : PropSPropRel (src_set_mem T) (tgt_set_mem T).
Proof.
  unfold src_set_mem, tgt_set_mem.
  apply: cs_forall_seqset => sR sL Hs. apply: cs_forall_identity => x.
  have Hm := cs_mem_rel T x _ _ Hs.
  apply: cs_bool_eq; exact (cs_decide_bool _ _ _ Hm).
Qed.

(* ------------------------------------------------------------------ *)
(** * Finite types: the Lean [Fintype] instance of a [finType] *)

Definition cs_enum_list (T : finType) : I.List T := seqset_seq_to_list (enum T).

Definition cs_enum_nodup (T : finType) :
    I.Multiset_Nodup T (I.Multiset_ofList T (cs_enum_list T)) :=
  source_uniq_to_imported_nodup (enum T) (enum_uniq T).

Definition cs_finset_univ (T : finType) : I.Finset T :=
  I.Finset_mk T (I.Multiset_ofList T (cs_enum_list T)) (cs_enum_nodup T).

Definition cs_fintype_complete (T : finType) (x : T) :
    I.Membership_mem T (I.Finset T) (I.SetLike_instMembership (I.Finset T) T (I.Finset_instSetLike T))
      (cs_finset_univ T) x :=
  seqset_mem_forward x (enum T) (seqset_bool_prop_to_truth _ (mem_enum T x)).

Definition cs_fintype (T : finType) : I.Fintype T :=
  I.Fintype_mk T (cs_finset_univ T) (cs_fintype_complete T).

(** Source side: [#|A|] counts the enumeration filtered by [A]. *)
Lemma cs_card_filter (T : finType) (A : pred T) : Logic.eq #|A| (size (filter A (enum T))).
Proof.
  rewrite cardE /enum_mem.
  have -> : [seq x <- Finite.enum T | ssrbool.mem T x] = Finite.enum T by apply/all_filterP/allP.
  by [].
Qed.

Lemma cs_size_rel (T : Type) (l : seq T) (lL : I.List T) :
  Lean.eq (seqset_seq_to_list l) lL -> SubNatRel (size l) (I.List_length T lL).
Proof.
  intro H. destruct H. apply: coq_eq_to_imported_eq.
  elim: l => [|x l IH] //=. by rewrite IH.
Qed.

Lemma cs_filter_rel (T : Type) (pR : T -> bool) (pL : T -> I.Bool) (HP : forall x, CsBoolRel (pR x) (pL x)) :
  forall l : seq T, Lean.eq (seqset_seq_to_list (filter pR l)) (I.List_filter T pL (seqset_seq_to_list l)).
Proof.
  move=> l. apply: coq_eq_to_imported_eq. elim: l => [|x l IH] //=.
  change (Logic.eq (seqset_seq_to_list (if pR x then x :: filter pR l else filter pR l))
    (I.List_filter_match_1 (fun _ => I.List T) (pL x)
       (fun _ => I.List_cons T x (I.List_filter T pL (seqset_seq_to_list l)))
       (fun _ => I.List_filter T pL (seqset_seq_to_list l)))).
  rewrite (cs_bool_rel_logic _ _ (HP x)) -IH. by case: (pR x).
Qed.

(* ------------------------------------------------------------------ *)
(** * [set_card] *)

Definition src_set_card (T : finType) : Prop := ltac:(type_of_term (@set_card T)).
Definition tgt_set_card (T : finType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Util_Seqset_set_card T (cs_fintype T) (seqset_decidable_eq T))).

Theorem set_card_correspondence (T : finType) : PropSPropRel (src_set_card T) (tgt_set_card T).
Proof.
  unfold src_set_card, tgt_set_card.
  apply: cs_forall_seqset => sR sL Hs.
  apply: sub_nat_eq_correspondence; last exact (cs_size_rel _ _ _ Hs).
  rewrite cs_card_filter.
  apply: cs_size_rel. apply: cs_filter_rel => x.
  exact (cs_decide_bool _ _ _ (cs_mem_rel T x _ _ Hs)).
Qed.
