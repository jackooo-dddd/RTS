From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From prosa Require Import classic.util.notation.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedClassicNotation.
From FoundationCertificates Require Import PropSPropFoundation.

Module I := ImportedClassicNotation.

(** Certificates for [classic/util/notation.v] (ProsaBuddy classic, commit f692cb7).

    Inputs.  Type parameters are identified, as in the accepted v0.6
    [util/notation] certificate.  Rocq pairs [A * B] and Lean [Prod A B] are
    related componentwise ([CnPairRel]); triples [A * B * C] = [(A * B) * C]
    against [Prod (Prod A B) C] ([CnTripleRel]); options and sequences
    constructor-wise ([CnOptRel], [CnSeqRel]).  Every relation is the graph of a
    conversion and has two-way totals ([*_canonical], [*_surjective]).

    The six definitions compute to related values on related inputs. *)

(* ------------------------------------------------------------------ *)
(** * Carriers *)

Definition cn_pair {A B : Type} (p : A * B) : I.Prod A B := I.Prod_mk A B p.1 p.2.
Definition cn_unpair {A B : Type} (p : I.Prod A B) : A * B := (I.Prod_fst A B p, I.Prod_snd A B p).

Definition CnPairRel (A B : Type) (pR : A * B) (pL : I.Prod A B) : SProp := Lean.eq (cn_pair pR) pL.

Lemma cn_pair_canonical A B (p : A * B) : CnPairRel A B p (cn_pair p).
Proof. exact (@Lean.eq_refl _ _). Qed.

Lemma cn_pair_surjective A B (p : I.Prod A B) : CnPairRel A B (cn_unpair p) p.
Proof. exact (@Lean.eq_refl _ _). Qed.

Definition cn_triple {A B C : Type} (p : A * B * C) : I.Prod (I.Prod A B) C :=
  I.Prod_mk (I.Prod A B) C (cn_pair p.1) p.2.
Definition cn_untriple {A B C : Type} (p : I.Prod (I.Prod A B) C) : A * B * C :=
  (cn_unpair (I.Prod_fst (I.Prod A B) C p), I.Prod_snd (I.Prod A B) C p).

Definition CnTripleRel (A B C : Type) (pR : A * B * C) (pL : I.Prod (I.Prod A B) C) : SProp :=
  Lean.eq (cn_triple pR) pL.

Lemma cn_triple_canonical A B C (p : A * B * C) : CnTripleRel A B C p (cn_triple p).
Proof. exact (@Lean.eq_refl _ _). Qed.

Lemma cn_triple_surjective A B C (p : I.Prod (I.Prod A B) C) : CnTripleRel A B C (cn_untriple p) p.
Proof. exact (@Lean.eq_refl _ _). Qed.

Definition cn_opt {T : Type} (o : option T) : I.Option T :=
  if o is Some x then I.Option_some T x else I.Option_none T.
Definition cn_unopt {T : Type} (o : I.Option T) : option T :=
  match o with I.Option_some x => Some x | I.Option_none => None end.

Definition CnOptRel (T : Type) (oR : option T) (oL : I.Option T) : SProp := Lean.eq (cn_opt oR) oL.

Lemma cn_opt_canonical T (o : option T) : CnOptRel T o (cn_opt o).
Proof. exact (@Lean.eq_refl _ _). Qed.

Lemma cn_opt_surjective T (o : I.Option T) : CnOptRel T (cn_unopt o) o.
Proof. destruct o; exact (@Lean.eq_refl _ _). Qed.

Fixpoint cn_seq {T : Type} (s : seq T) : I.List T :=
  match s with [::] => I.List_nil T | x :: s' => I.List_cons T x (cn_seq s') end.
Fixpoint cn_unseq {T : Type} (s : I.List T) : seq T :=
  match s with I.List_nil => [::] | I.List_cons x s' => x :: cn_unseq s' end.

Definition CnSeqRel (T : Type) (sR : seq T) (sL : I.List T) : SProp := Lean.eq (cn_seq sR) sL.

Lemma cn_seq_canonical T (s : seq T) : CnSeqRel T s (cn_seq s).
Proof. exact (@Lean.eq_refl _ _). Qed.

Lemma cn_seq_surjective T (s : I.List T) : CnSeqRel T (cn_unseq s) s.
Proof.
  apply: coq_eq_to_imported_eq. elim: s => [|x s IH] //=. by rewrite IH.
Qed.

(* ------------------------------------------------------------------ *)
(** * Definitions *)

Theorem pair_1st_correspondence A B pR pL :
  CnPairRel A B pR pL -> Lean.eq (@pair_1st A B pR) (I.Prosa_Classic_Util_Notation_pair_1st A B pL).
Proof. intro H. destruct H. exact (@Lean.eq_refl _ _). Qed.

Theorem pair_2nd_correspondence A B pR pL :
  CnPairRel A B pR pL -> Lean.eq (@pair_2nd A B pR) (I.Prosa_Classic_Util_Notation_pair_2nd A B pL).
Proof. intro H. destruct H. exact (@Lean.eq_refl _ _). Qed.

Theorem triple_1st_correspondence A B C pR pL :
  CnTripleRel A B C pR pL ->
  Lean.eq (@triple_1st A B C pR) (I.Prosa_Classic_Util_Notation_triple_1st A B C pL).
Proof. intro H. destruct H. exact (@Lean.eq_refl _ _). Qed.

Theorem triple_2nd_correspondence A B C pR pL :
  CnTripleRel A B C pR pL ->
  Lean.eq (@triple_2nd A B C pR) (I.Prosa_Classic_Util_Notation_triple_2nd A B C pL).
Proof. intro H. destruct H. exact (@Lean.eq_refl _ _). Qed.

Theorem triple_3rd_correspondence A B C pR pL :
  CnTripleRel A B C pR pL ->
  Lean.eq (@triple_3rd A B C pR) (I.Prosa_Classic_Util_Notation_triple_3rd A B C pL).
Proof. intro H. destruct H. exact (@Lean.eq_refl _ _). Qed.

Theorem make_sequence_correspondence T oR oL :
  CnOptRel T oR oL -> CnSeqRel T (@make_sequence T oR) (I.Prosa_Classic_Util_Notation_make_sequence T oL).
Proof. intro H. destruct H. destruct oR; exact (@Lean.eq_refl _ _). Qed.
