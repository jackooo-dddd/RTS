(* Re-bound base of the accepted certificates/implementation_refinements_refinements/RefinementsCorrespondence.v:
   the same file with the imported module renamed (ImportedRefinements -> ImportedRefTask), without the 26 statement
   correspondences of refinements.v (their statement-only targets are not part of this export), and without the
   commands that mention refinements constants absent from this export (scratchpad prune_base.py; the dropped names
   are listed in the file's report).  Every kept command is unchanged. *)
(** Correspondences for [implementation/refinements/refinements.v].

    The source is the official file, compiled on its official proof closure with CoqEAL 2.1.2 (unchanged).  The
    target is the Lean translation, whose file also translates the fragment of Rocq's binary numbers and of CoqEAL
    the source uses.  Relations:
    - unary numbers by the canonical map; binary numbers ([positive], [N], the subtraction [mask], [comparison]),
      Booleans, pairs and lists by the constructor-preserving maps onto the Lean mirrors, with two-way roundtrips;
    - every mirrored Stdlib/MathComp operation commutes with these maps (by structural induction: the Lean
      definitions have the same recursions);
    - each of the file's definitions is related to its translation for related inputs (generic element types by
      identity, operation-class instances by their single field);
    - each [Type]-valued statement (CoqEAL [refines] instances and lemmas) is related to its translation by maps
      in both directions between the source statement and the target statement ([TypeCorrespondence]); the two
      [Prop]-valued lemmas by [PropSPropRel].
    No certificate uses its own source or target theorem: statements are taken with [type of], never applied. *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq div bigop.
From CoqEAL Require Import hrel param refinements binnat.
From prosa Require Import implementation.refinements.refinements.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedRefTask ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation SubadditivityNatCorrespondence.
Import Refinements.Op.

Set Warnings "-notation-for-abbreviation,-deprecated".

Module I := ImportedRefTask.
Module Rf := prosa.implementation.refinements.refinements.

(** ** Imported names *)
Abbreviation LN := Lean.Nat.
Abbreviation IPos := I.Prosa_Implementation_Refinements_Refinements_positive.
Abbreviation IxI := I.Prosa_Implementation_Refinements_Refinements_positive_xI.
Abbreviation IxO := I.Prosa_Implementation_Refinements_Refinements_positive_xO.
Abbreviation IxH := I.Prosa_Implementation_Refinements_Refinements_positive_xH.
Abbreviation IN := I.Prosa_Implementation_Refinements_Refinements_N.
Abbreviation IN0 := I.Prosa_Implementation_Refinements_Refinements_N_N0.
Abbreviation INpos := I.Prosa_Implementation_Refinements_Refinements_N_Npos.
Abbreviation IMask := I.Prosa_Implementation_Refinements_Refinements_Pos_mask.
Abbreviation IIsNul := I.Prosa_Implementation_Refinements_Refinements_Pos_mask_IsNul.
Abbreviation IIsPos := I.Prosa_Implementation_Refinements_Refinements_Pos_mask_IsPos.
Abbreviation IIsNeg := I.Prosa_Implementation_Refinements_Refinements_Pos_mask_IsNeg.
Abbreviation IList := I.List_inst1.
Abbreviation Inil := I.List_nil_inst1.
Abbreviation Icons := I.List_cons_inst1.
Abbreviation IProd := I.Prod_inst3.
Abbreviation Ipair := I.Prod_mk_inst3.

(** ** Equality tools *)
Definition rf_sym {A : Type} (x y : A) := sub_imported_eq_sym x y.
Definition rf_trans {A : Type} (x y z : A) := sub_imported_eq_trans x y z.
Definition rf_congr {A B : Type} (f : A -> B) (x y : A) := sub_imported_eq_congr f x y.
Definition rf_congr2 {A B C : Type} (f : A -> B -> C) x1 x2 y1 y2 := sub_imported_eq_congr2 f x1 x2 y1 y2.
Definition rf_refl {A : Type} (x : A) : Lean.eq x x := @Lean.eq_refl A x.

(** Transport along a target equality, into any sort. *)
Definition rf_tr {A : Type} (P : A -> Type) {x y : A} (H : Lean.eq x y) : P x -> P y :=
  match H in Lean.eq _ z return P x -> P z with Lean.eq_refl => fun p => p end.

Definition rf_tr2 {A B : Type} (P : A -> B -> Type) {x y : A} {u v : B}
    (H : Lean.eq x y) (H' : Lean.eq u v) (p : P x u) : P y v :=
  rf_tr (fun z => P y z) H' (rf_tr (fun z => P z u) H p).

Definition rf_to_coq {A : Type} {x y : A} (H : Lean.eq x y) : x = y := imported_eq_to_coq_eq x y H.
Definition rf_of_coq {A : Type} {x y : A} (H : x = y) : Lean.eq x y := coq_eq_to_imported_eq x y H.

(** An SProp conjunction. *)
Record SAnd (P Q : SProp) : SProp := sconj { sfst : P; ssnd : Q }.
Arguments sconj {P Q}.
Arguments sfst {P Q}.
Arguments ssnd {P Q}.

(** ** Unary numbers *)
Abbreviation ne := sub_nat_to_imported.
Abbreviation ni := sub_nat_to_rocq.
Lemma rf_ni_ne (n : nat) : ni (ne n) = n. Proof. exact (sub_nat_rocq_roundtrip n). Qed.
Lemma rf_ne_ni (n : LN) : Lean.eq (ne (ni n)) n. Proof. exact (sub_nat_imported_roundtrip n). Qed.

Lemma rf_add_ex (a b : nat) : Lean.eq (ne (a + b)) (sub_imported_add (ne a) (ne b)).
Proof. exact (rf_sym _ _ (sub_add_canonical a b)). Qed.

(** ** Binary numbers *)
Fixpoint pe (p : positive) : IPos :=
  match p with xI q => IxI (pe q) | xO q => IxO (pe q) | xH => IxH end.
Fixpoint pi (p : IPos) : positive :=
  match p with IxI q => xI (pi q) | IxO q => xO (pi q) | IxH => xH end.
Lemma rf_pi_pe p : pi (pe p) = p. Proof. by elim: p => //= p ->. Qed.
Lemma rf_pe_pi p : Lean.eq (pe (pi p)) p.
Proof.
  induction p; cbn.
  - exact (rf_congr IxI _ _ IHp).
  - exact (rf_congr IxO _ _ IHp).
  - exact (rf_refl _).
Qed.

Definition Ne_ (n : N) : IN := match n with N0 => IN0 | Npos p => INpos (pe p) end.
Definition Ni (n : IN) : N := match n with IN0 => N0 | INpos p => Npos (pi p) end.
Lemma rf_Ni_Ne n : Ni (Ne_ n) = n. Proof. by case: n => //= p; rewrite rf_pi_pe. Qed.
Lemma rf_Ne_Ni n : Lean.eq (Ne_ (Ni n)) n.
Proof. destruct n; cbn; [exact (rf_refl _) | exact (rf_congr INpos _ _ (rf_pe_pi _))]. Qed.

Definition me (m : Pos.mask) : IMask :=
  match m with Pos.IsNul => IIsNul | Pos.IsPos p => IIsPos (pe p) | Pos.IsNeg => IIsNeg end.

Definition ce (c : comparison) : I.Ordering :=
  match c with Eq => I.Ordering_eq | Lt => I.Ordering_lt | Gt => I.Ordering_gt end.

Definition be (b : bool) : I.Bool := if b then I.Bool_true else I.Bool_false.
Definition bi (b : I.Bool) : bool := match b with I.Bool_true => true | I.Bool_false => false end.
Lemma rf_bi_be b : bi (be b) = b. Proof. by case: b. Qed.
Lemma rf_be_bi b : Lean.eq (be (bi b)) b. Proof. destruct b; exact (rf_refl _). Qed.

(** ** Pairs and lists *)
Definition pre {A B C D : Type} (f : A -> C) (g : B -> D) (x : A * B) : IProd C D :=
  Ipair C D (f x.1) (g x.2).
Definition pri {A B C D : Type} (f : C -> A) (g : D -> B) (x : IProd C D) : A * B :=
  (f (I.Prod_fst_inst3 C D x), g (I.Prod_snd_inst3 C D x)).

Fixpoint lex {A B : Type} (f : A -> B) (xs : seq A) : IList B :=
  match xs with [::] => Inil B | x :: xs' => Icons B (f x) (lex f xs') end.
Fixpoint lim {A B : Type} (f : B -> A) (xs : IList B) : seq A :=
  match xs with I.List_nil_inst1 => [::] | I.List_cons_inst1 x xs' => f x :: lim f xs' end.

Lemma rf_lim_lex {A B : Type} (f : A -> B) (g : B -> A) (H : forall a, g (f a) = a) xs :
  lim g (lex f xs) = xs.
Proof. by elim: xs => //= x xs ->; rewrite H. Qed.

Lemma rf_lex_lim {A B : Type} (f : A -> B) (g : B -> A) (H : forall b, Lean.eq (f (g b)) b) xs :
  Lean.eq (lex f (lim g xs)) xs.
Proof.
  induction xs as [|x xs IH]; cbn.
  - exact (rf_refl _).
  - exact (rf_congr2 (Icons B) _ _ _ _ (H x) IH).
Qed.

Lemma rf_lex_ext {A B : Type} (f g : A -> B) (H : forall a, Lean.eq (f a) (g a)) xs :
  Lean.eq (lex f xs) (lex g xs).
Proof.
  induction xs as [|x xs IH]; cbn.
  - exact (rf_refl _).
  - exact (rf_congr2 (Icons B) _ _ _ _ (H x) IH).
Qed.

(** ** Mirrored Stdlib operations on [positive] *)
Abbreviation IPsucc := I.Prosa_Implementation_Refinements_Refinements_Pos_succ.
Abbreviation IPadd := I.Prosa_Implementation_Refinements_Refinements_Pos_add.
Abbreviation IPaddc := I.Prosa_Implementation_Refinements_Refinements_Pos_add_carry.
Abbreviation IPpred_double := I.Prosa_Implementation_Refinements_Refinements_Pos_pred_double.
Abbreviation IPpred_N := I.Prosa_Implementation_Refinements_Refinements_Pos_pred_N.
Abbreviation IPsdm := I.Prosa_Implementation_Refinements_Refinements_Pos_succ_double_mask.
Abbreviation IPdm := I.Prosa_Implementation_Refinements_Refinements_Pos_double_mask.
Abbreviation IPdpm := I.Prosa_Implementation_Refinements_Refinements_Pos_double_pred_mask.
Abbreviation IPsub_mask := I.Prosa_Implementation_Refinements_Refinements_Pos_sub_mask.
Abbreviation IPsub_maskc := I.Prosa_Implementation_Refinements_Refinements_Pos_sub_mask_carry.
Abbreviation IPcompare_cont := I.Prosa_Implementation_Refinements_Refinements_Pos_compare_cont.
Abbreviation IPcompare := I.Prosa_Implementation_Refinements_Refinements_Pos_compare.
Abbreviation IPeqb := I.Prosa_Implementation_Refinements_Refinements_Pos_eqb.

Lemma rf_succ_ex p : Lean.eq (pe (Pos.succ p)) (IPsucc (pe p)).
Proof.
  induction p; cbn.
  - exact (rf_congr IxO _ _ IHp).
  - exact (rf_refl _).
  - exact (rf_refl _).
Qed.

Lemma rf_add_pos_ex p q :
  SAnd (Lean.eq (pe (Pos.add p q)) (IPadd (pe p) (pe q)))
       (Lean.eq (pe (Pos.add_carry p q)) (IPaddc (pe p) (pe q))).
Proof.
  revert q; induction p; intro q; destruct q; cbn; apply sconj;
  first [ exact (rf_congr IxO _ _ (ssnd (IHp q)))
        | exact (rf_congr IxI _ _ (ssnd (IHp q)))
        | exact (rf_congr IxO _ _ (sfst (IHp q)))
        | exact (rf_congr IxI _ _ (sfst (IHp q)))
        | exact (rf_congr IxO _ _ (rf_succ_ex _))
        | exact (rf_congr IxI _ _ (rf_succ_ex _))
        | exact (rf_refl _) ].
Qed.

Lemma rf_pred_double_ex p : Lean.eq (pe (Pos.pred_double p)) (IPpred_double (pe p)).
Proof.
  induction p; cbn.
  - exact (rf_refl _).
  - exact (rf_congr IxI _ _ IHp).
  - exact (rf_refl _).
Qed.

Lemma rf_pred_N_ex p : Lean.eq (Ne_ (Pos.pred_N p)) (IPpred_N (pe p)).
Proof.
  destruct p; cbn.
  - exact (rf_refl _).
  - exact (rf_congr INpos _ _ (rf_pred_double_ex p)).
  - exact (rf_refl _).
Qed.

Lemma rf_sdm_ex m : Lean.eq (me (Pos.succ_double_mask m)) (IPsdm (me m)).
Proof. destruct m; exact (rf_refl _). Qed.
Lemma rf_dm_ex m : Lean.eq (me (Pos.double_mask m)) (IPdm (me m)).
Proof. destruct m; exact (rf_refl _). Qed.
Lemma rf_dpm_ex p : Lean.eq (me (Pos.double_pred_mask p)) (IPdpm (pe p)).
Proof.
  destruct p; cbn.
  - exact (rf_refl _).
  - exact (rf_congr (fun z => IIsPos (IxO z)) _ _ (rf_pred_double_ex p)).
  - exact (rf_refl _).
Qed.

Lemma rf_sub_mask_ex p q :
  SAnd (Lean.eq (me (Pos.sub_mask p q)) (IPsub_mask (pe p) (pe q)))
       (Lean.eq (me (Pos.sub_mask_carry p q)) (IPsub_maskc (pe p) (pe q))).
Proof.
  revert p; induction q; intro p; destruct p; cbn; apply sconj;
  first [ exact (rf_trans _ _ _ (rf_dm_ex _) (rf_congr IPdm _ _ (sfst (IHq p))))
        | exact (rf_trans _ _ _ (rf_dm_ex _) (rf_congr IPdm _ _ (ssnd (IHq p))))
        | exact (rf_trans _ _ _ (rf_sdm_ex _) (rf_congr IPsdm _ _ (sfst (IHq p))))
        | exact (rf_trans _ _ _ (rf_sdm_ex _) (rf_congr IPsdm _ _ (ssnd (IHq p))))
        | exact (rf_congr IIsPos _ _ (rf_pred_double_ex p))
        | exact (rf_dpm_ex p)
        | exact (rf_refl _) ].
Qed.

Lemma rf_compare_cont_ex r p q :
  Lean.eq (ce (Pos.compare_cont r p q)) (IPcompare_cont (ce r) (pe p) (pe q)).
Proof.
  revert r p; induction q; intros r p; destruct p; cbn;
  first [ exact (IHq _ _) | exact (rf_refl _) ].
Qed.

Lemma rf_compare_ex p q : Lean.eq (ce (Pos.compare p q)) (IPcompare (pe p) (pe q)).
Proof. exact (rf_compare_cont_ex Eq p q). Qed.

Lemma rf_eqb_pos_ex p q : Lean.eq (be (Pos.eqb p q)) (IPeqb (pe p) (pe q)).
Proof.
  revert q; induction p; intro q; destruct q; cbn;
  first [ exact (IHp _) | exact (rf_refl _) ].
Qed.

(** Transport along a target equality, inside an SProp goal. *)
Definition rf_trs {A : Type} (P : A -> SProp) {x y : A} (H : Lean.eq x y) : P x -> P y :=
  match H in Lean.eq _ z return P x -> P z with Lean.eq_refl => fun p => p end.

(** ** Mirrored Stdlib operations on [N] *)
Abbreviation INsucc_double := I.Prosa_Implementation_Refinements_Refinements_N_succ_double.
Abbreviation INdouble := I.Prosa_Implementation_Refinements_Refinements_N_double.
Abbreviation INsub := I.Prosa_Implementation_Refinements_Refinements_N_sub.
Abbreviation INcompare := I.Prosa_Implementation_Refinements_Refinements_N_compare.
Abbreviation INleb := I.Prosa_Implementation_Refinements_Refinements_N_leb.
Abbreviation INltb := I.Prosa_Implementation_Refinements_Refinements_N_ltb.
Abbreviation INeqb := I.Prosa_Implementation_Refinements_Refinements_N_eqb.
Abbreviation INadd := I.Prosa_Implementation_Refinements_Refinements_N_add.
Abbreviation INsucc := I.Prosa_Implementation_Refinements_Refinements_N_succ.
Abbreviation INpde := I.Prosa_Implementation_Refinements_Refinements_N_pos_div_eucl.
Abbreviation INde := I.Prosa_Implementation_Refinements_Refinements_N_div_eucl.
Abbreviation INdiv := I.Prosa_Implementation_Refinements_Refinements_N_div.
Abbreviation INmod := I.Prosa_Implementation_Refinements_Refinements_N_modulo.
Abbreviation INzero := I.Prosa_Implementation_Refinements_Refinements_N_zero.
Abbreviation INone := I.Prosa_Implementation_Refinements_Refinements_N_one.

Lemma rf_N_succ_double_ex n : Lean.eq (Ne_ (N.succ_double n)) (INsucc_double (Ne_ n)).
Proof. destruct n; exact (rf_refl _). Qed.
Lemma rf_N_double_ex n : Lean.eq (Ne_ (N.double n)) (INdouble (Ne_ n)).
Proof. destruct n; exact (rf_refl _). Qed.

Abbreviation INsub_m1 := I.Prosa_Implementation_Refinements_Refinements_N_sub_match_1.

Lemma rf_N_sub_ex a b : Lean.eq (Ne_ (N.sub a b)) (INsub (Ne_ a) (Ne_ b)).
Proof.
  destruct a as [|p]; destruct b as [|q]; try exact (rf_refl _).
  cbn [N.sub Ne_].
  refine (rf_trs (fun m => Lean.eq _ (INsub_m1 (fun _ => IN) m (fun z => INpos z) (fun _ => IN0)))
            (sfst (rf_sub_mask_ex p q)) _).
  destruct (Pos.sub_mask p q); exact (rf_refl _).
Qed.

(** [rf_rw H] with [H : Lean.eq u t] replaces the target subterm [t] by [u] in an SProp goal. *)
Ltac rf_rw H :=
  lazymatch type of H with Lean.eq ?u ?t => pattern t; refine (rf_trs _ H _); cbv beta end.

Lemma rf_pair_eq {A B : Type} (a a' : A) (b b' : B) :
  Lean.eq a a' -> Lean.eq b b' -> Lean.eq (Ipair A B a b) (Ipair A B a' b').
Proof. intros Ha Hb. exact (rf_congr2 (Ipair A B) _ _ _ _ Ha Hb). Qed.

Lemma rf_N_compare_ex a b : Lean.eq (ce (N.compare a b)) (INcompare (Ne_ a) (Ne_ b)).
Proof.
  destruct a as [|p]; destruct b as [|q]; try exact (rf_refl _).
  exact (rf_compare_ex p q).
Qed.

Lemma rf_N_leb_ex a b : Lean.eq (be (N.leb a b)) (INleb (Ne_ a) (Ne_ b)).
Proof.
  have H := rf_N_compare_ex a b.
  unfold INleb, N.leb. rf_rw H.
  destruct (N.compare a b); exact (rf_refl _).
Qed.

Lemma rf_N_ltb_ex a b : Lean.eq (be (N.ltb a b)) (INltb (Ne_ a) (Ne_ b)).
Proof.
  have H := rf_N_compare_ex a b.
  unfold INltb, N.ltb. rf_rw H.
  destruct (N.compare a b); exact (rf_refl _).
Qed.

Lemma rf_N_eqb_ex a b : Lean.eq (be (N.eqb a b)) (INeqb (Ne_ a) (Ne_ b)).
Proof.
  destruct a as [|p]; destruct b as [|q]; try exact (rf_refl _).
  exact (rf_eqb_pos_ex p q).
Qed.

Lemma rf_N_add_ex a b : Lean.eq (Ne_ (N.add a b)) (INadd (Ne_ a) (Ne_ b)).
Proof.
  destruct a as [|p]; destruct b as [|q]; try exact (rf_refl _).
  exact (rf_congr INpos _ _ (sfst (rf_add_pos_ex p q))).
Qed.

Lemma rf_N_succ_ex a : Lean.eq (Ne_ (N.succ a)) (INsucc (Ne_ a)).
Proof. destruct a as [|p]; [exact (rf_refl _) | exact (rf_congr INpos _ _ (rf_succ_ex p))]. Qed.

Ltac rf_red_m4 :=
  lazymatch goal with
  | |- context [I.Prosa_Implementation_Refinements_Refinements_N_pos_div_eucl_match_4 ?P (Ipair _ _ ?q ?r) ?F] =>
      change (I.Prosa_Implementation_Refinements_Refinements_N_pos_div_eucl_match_4 P (Ipair _ _ q r) F)
        with (F q r); cbv beta zeta; cbn [fst snd]
  end.

Lemma rf_N_pde_ex a b : Lean.eq (pre Ne_ Ne_ (N.pos_div_eucl a b)) (INpde (pe a) (Ne_ b)).
Proof.
  induction a as [a IH|a IH|].
  - cbn [N.pos_div_eucl pe].
    destruct (N.pos_div_eucl a b) as [q r].
    unfold INpde at 1. cbn [I.Prosa_Implementation_Refinements_Refinements_positive_brecOn].
    change (Lean.eq (pre Ne_ Ne_ (let r' := N.succ_double r in
                       if N.leb b r' then (N.succ_double q, N.sub r' b) else (N.double q, r')))
              (I.Prosa_Implementation_Refinements_Refinements_N_pos_div_eucl_match_4
                 (fun _ => IProd IN IN) (INpde (pe a) (Ne_ b))
                 (fun q r => let r' := INsucc_double r in
                    I.ite (IProd IN IN) (Lean.eq (INleb (Ne_ b) r') I.Bool_true)
                      (I.instDecidableEqBool (INleb (Ne_ b) r') I.Bool_true)
                      (Ipair IN IN (INsucc_double q) (INsub r' (Ne_ b)))
                      (Ipair IN IN (INdouble q) r')))).
    change (Lean.eq (Ipair IN IN (Ne_ q) (Ne_ r)) (INpde (pe a) (Ne_ b))) in IH.
    rf_rw IH. rf_red_m4.
    have Hd := rf_N_succ_double_ex r. rf_rw Hd.
    have Hl := rf_N_leb_ex b (N.succ_double r). rf_rw Hl.
    destruct (N.leb b (N.succ_double r)); cbn [be].
    + exact (rf_pair_eq _ _ _ _ (rf_N_succ_double_ex q) (rf_N_sub_ex _ _)).
    + exact (rf_pair_eq _ _ _ _ (rf_N_double_ex q) (rf_refl _)).
  - cbn [N.pos_div_eucl pe].
    destruct (N.pos_div_eucl a b) as [q r].
    unfold INpde at 1. cbn [I.Prosa_Implementation_Refinements_Refinements_positive_brecOn].
    change (Lean.eq (pre Ne_ Ne_ (let r' := N.double r in
                       if N.leb b r' then (N.succ_double q, N.sub r' b) else (N.double q, r')))
              (I.Prosa_Implementation_Refinements_Refinements_N_pos_div_eucl_match_4
                 (fun _ => IProd IN IN) (INpde (pe a) (Ne_ b))
                 (fun q r => let r' := INdouble r in
                    I.ite (IProd IN IN) (Lean.eq (INleb (Ne_ b) r') I.Bool_true)
                      (I.instDecidableEqBool (INleb (Ne_ b) r') I.Bool_true)
                      (Ipair IN IN (INsucc_double q) (INsub r' (Ne_ b)))
                      (Ipair IN IN (INdouble q) r')))).
    change (Lean.eq (Ipair IN IN (Ne_ q) (Ne_ r)) (INpde (pe a) (Ne_ b))) in IH.
    rf_rw IH. rf_red_m4.
    have Hd := rf_N_double_ex r. rf_rw Hd.
    have Hl := rf_N_leb_ex b (N.double r). rf_rw Hl.
    destruct (N.leb b (N.double r)); cbn [be].
    + exact (rf_pair_eq _ _ _ _ (rf_N_succ_double_ex q) (rf_N_sub_ex _ _)).
    + exact (rf_pair_eq _ _ _ _ (rf_N_double_ex q) (rf_refl _)).
  - destruct b as [|[p|p|]]; exact (rf_refl _).
Qed.

Lemma rf_N_de_ex a b : Lean.eq (pre Ne_ Ne_ (N.div_eucl a b)) (INde (Ne_ a) (Ne_ b)).
Proof.
  destruct a as [|p]; destruct b as [|q]; try exact (rf_refl _).
  exact (rf_N_pde_ex p (Npos q)).
Qed.

Lemma rf_N_div_ex a b : Lean.eq (Ne_ (N.div a b)) (INdiv (Ne_ a) (Ne_ b)).
Proof. exact (rf_congr (I.Prod_fst_inst3 IN IN) _ _ (rf_N_de_ex a b)). Qed.

Lemma rf_N_mod_ex a b : Lean.eq (Ne_ (N.modulo a b)) (INmod (Ne_ a) (Ne_ b)).
Proof. exact (rf_congr (I.Prod_snd_inst3 IN IN) _ _ (rf_N_de_ex a b)). Qed.

(** ** MathComp's [nat_of_bin] and [bin_of_nat] *)
Abbreviation ITadd := I.Prosa_Implementation_Refinements_Refinements_NatTrec_add.
Abbreviation ITdouble := I.Prosa_Implementation_Refinements_Refinements_NatTrec_double.
Abbreviation Inat_of_pos := I.Prosa_Implementation_Refinements_Refinements_nat_of_pos.
Abbreviation Inat_of_bin := I.Prosa_Implementation_Refinements_Refinements_nat_of_bin.
Abbreviation Ipos_of_nat := I.Prosa_Implementation_Refinements_Refinements_pos_of_nat.
Abbreviation Ibin_of_nat := I.Prosa_Implementation_Refinements_Refinements_bin_of_nat.

Lemma rf_trec_add_ex m n : Lean.eq (ne (NatTrec.add m n)) (ITadd (ne m) (ne n)).
Proof.
  revert n; induction m as [|m IH]; intro n.
  - exact (rf_refl _).
  - exact (IH n.+1).
Qed.

Lemma rf_trec_double_ex n : Lean.eq (ne (NatTrec.double n)) (ITdouble (ne n)).
Proof. destruct n as [|n]; [exact (rf_refl _) | exact (rf_trec_add_ex n n.+2)]. Qed.

Lemma rf_nat_of_pos_ex p : Lean.eq (ne (nat_of_pos p)) (Inat_of_pos (pe p)).
Proof.
  induction p as [p IH|p IH|]; cbn [nat_of_pos pe].
  - exact (rf_congr Lean.Nat_succ _ _
      (rf_trans _ _ _ (rf_trec_double_ex _) (rf_congr ITdouble _ _ IH))).
  - exact (rf_trans _ _ _ (rf_trec_double_ex _) (rf_congr ITdouble _ _ IH)).
  - exact (rf_refl _).
Qed.

Lemma rf_nat_of_bin_ex a : Lean.eq (ne (nat_of_bin a)) (Inat_of_bin (Ne_ a)).
Proof. destruct a as [|p]; [exact (rf_refl _) | exact (rf_nat_of_pos_ex p)]. Qed.

Lemma rf_pos_of_nat_ex n m : Lean.eq (pe (pos_of_nat n m)) (Ipos_of_nat (ne n) (ne m)).
Proof.
  revert m; induction n as [|n IH]; intro m.
  - exact (rf_refl _).
  - destruct m as [|[|m]]; cbn [pos_of_nat pe].
    + exact (rf_congr IxI _ _ (IH n)).
    + exact (rf_congr IxO _ _ (IH n)).
    + exact (IH m).
Qed.

Lemma rf_bin_of_nat_ex n : Lean.eq (Ne_ (bin_of_nat n)) (Ibin_of_nat (ne n)).
Proof. destruct n as [|n]; [exact (rf_refl _) | exact (rf_congr INpos _ _ (rf_pos_of_nat_ex n n))]. Qed.

(** ** Lists *)
(** The identity (the imported module also exports Lean's [id]). *)
Definition idr {A : Type} (x : A) : A := x.

Lemma rf_map_ex {A B C D : Type} (eA : A -> C) (eB : B -> D) (F : A -> B) (FL : C -> D)
    (HF : forall a, Lean.eq (eB (F a)) (FL (eA a))) xs :
  Lean.eq (lex eB (map F xs)) (I.List_map_inst3 C D FL (lex eA xs)).
Proof.
  induction xs as [|x xs IH]; cbn [map lex].
  - exact (rf_refl _).
  - exact (rf_congr2 (Icons D) _ _ _ _ (HF x) IH).
Qed.

Lemma rf_filter_ex {A C : Type} (eA : A -> C) (P : A -> bool) (PL : C -> I.Bool)
    (HP : forall a, Lean.eq (be (P a)) (PL (eA a))) xs :
  Lean.eq (lex eA (filter P xs)) (I.List_filter_inst1 C PL (lex eA xs)).
Proof.
  induction xs as [|x xs IH]; cbn [filter lex].
  - exact (rf_refl _).
  - change (Lean.eq (lex eA (if P x then x :: filter P xs else filter P xs))
      (I.Bool_casesOn (fun _ => IList C) (PL (eA x)) (I.List_filter_inst1 C PL (lex eA xs))
         (Icons C (eA x) (I.List_filter_inst1 C PL (lex eA xs))))).
    have Hx := HP x. rf_rw Hx.
    destruct (P x); cbn [be lex].
    + exact (rf_congr (Icons C (eA x)) _ _ IH).
    + exact IH.
Qed.

(** ** The operation classes: an instance is related to the single field of its Lean structure *)
Abbreviation Izero_op := I.Prosa_Implementation_Refinements_Refinements_zero_of_zero_op.
Abbreviation Ione_op := I.Prosa_Implementation_Refinements_Refinements_one_of_one_op.
Abbreviation Iadd_op := I.Prosa_Implementation_Refinements_Refinements_add_of_add_op.
Abbreviation Isub_op := I.Prosa_Implementation_Refinements_Refinements_sub_of_sub_op.
Abbreviation Idiv_op := I.Prosa_Implementation_Refinements_Refinements_div_of_div_op.
Abbreviation Imod_op := I.Prosa_Implementation_Refinements_Refinements_mod_of_mod_op.
Abbreviation Ieq_op := I.Prosa_Implementation_Refinements_Refinements_eq_of_eq_op.
Abbreviation Ileq_op := I.Prosa_Implementation_Refinements_Refinements_leq_of_leq_op.
Abbreviation Ilt_op := I.Prosa_Implementation_Refinements_Refinements_lt_of_lt_op.
Abbreviation Izero_of := I.Prosa_Implementation_Refinements_Refinements_zero_of.
Abbreviation Ione_of := I.Prosa_Implementation_Refinements_Refinements_one_of.
Abbreviation Iadd_of := I.Prosa_Implementation_Refinements_Refinements_add_of.
Abbreviation Isub_of := I.Prosa_Implementation_Refinements_Refinements_sub_of.
Abbreviation Idiv_of := I.Prosa_Implementation_Refinements_Refinements_div_of.
Abbreviation Imod_of := I.Prosa_Implementation_Refinements_Refinements_mod_of.
Abbreviation Ieq_of := I.Prosa_Implementation_Refinements_Refinements_eq_of.
Abbreviation Ileq_of := I.Prosa_Implementation_Refinements_Refinements_leq_of.
Abbreviation Ilt_of := I.Prosa_Implementation_Refinements_Refinements_lt_of.

Definition ZeroRel {T : Type} (zR : zero_of T) (zL : Izero_of T) : SProp := Lean.eq zR (Izero_op T zL).
Definition OneRel {T : Type} (oR : one_of T) (oL : Ione_of T) : SProp := Lean.eq oR (Ione_op T oL).
Definition Op2Rel {T : Type} (fR : T -> T -> T) (fL : T -> T -> T) : SProp :=
  forall x y, Lean.eq (fR x y) (fL x y).
Definition BOpRel {T : Type} (fR : T -> T -> bool) (fL : T -> T -> I.Bool) : SProp :=
  forall x y, Lean.eq (be (fR x y)) (fL x y).

(** ** The file's definitions *)
Lemma m_b2n_correspondence bR bL :
  Lean.eq (lex Ne_ bR) bL -> Lean.eq (lex ne (Rf.m_b2n bR)) (I.Prosa_Implementation_Refinements_Refinements_m_b2n bL).
Proof. intro H. destruct H. exact (rf_map_ex Ne_ ne _ _ rf_nat_of_bin_ex bR). Qed.

Lemma m_n2b_correspondence nR nL :
  Lean.eq (lex ne nR) nL -> Lean.eq (lex Ne_ (Rf.m_n2b nR)) (I.Prosa_Implementation_Refinements_Refinements_m_n2b nL).
Proof. intro H. destruct H. exact (rf_map_ex ne Ne_ _ _ rf_bin_of_nat_ex nR). Qed.

Lemma tmap_correspondence (X Y : Type) (f : X -> Y) tR tL :
  Lean.eq (pre idr idr tR) tL ->
  Lean.eq (pre idr idr (Rf.tmap f tR)) (I.Prosa_Implementation_Refinements_Refinements_tmap X Y f tL).
Proof. intro H. destruct H. destruct tR. exact (rf_refl _). Qed.

Lemma rf_tb2tn_ex t : Lean.eq (pre ne ne (Rf.tb2tn t)) (I.Prosa_Implementation_Refinements_Refinements_tb2tn (pre Ne_ Ne_ t)).
Proof. destruct t as [a b]. exact (rf_pair_eq _ _ _ _ (rf_nat_of_bin_ex a) (rf_nat_of_bin_ex b)). Qed.
Lemma rf_tn2tb_ex t : Lean.eq (pre Ne_ Ne_ (Rf.tn2tb t)) (I.Prosa_Implementation_Refinements_Refinements_tn2tb (pre ne ne t)).
Proof. destruct t as [a b]. exact (rf_pair_eq _ _ _ _ (rf_bin_of_nat_ex a) (rf_bin_of_nat_ex b)). Qed.

Lemma tb2tn_correspondence tR tL :
  Lean.eq (pre Ne_ Ne_ tR) tL ->
  Lean.eq (pre ne ne (Rf.tb2tn tR)) (I.Prosa_Implementation_Refinements_Refinements_tb2tn tL).
Proof. intro H. destruct H. exact (rf_tb2tn_ex tR). Qed.

Lemma tn2tb_correspondence tR tL :
  Lean.eq (pre ne ne tR) tL ->
  Lean.eq (pre Ne_ Ne_ (Rf.tn2tb tR)) (I.Prosa_Implementation_Refinements_Refinements_tn2tb tL).
Proof. intro H. destruct H. exact (rf_tn2tb_ex tR). Qed.

Lemma m_tb2tn_correspondence xsR xsL :
  Lean.eq (lex (pre Ne_ Ne_) xsR) xsL ->
  Lean.eq (lex (pre ne ne) (Rf.m_tb2tn xsR)) (I.Prosa_Implementation_Refinements_Refinements_m_tb2tn xsL).
Proof. intro H. destruct H. exact (rf_map_ex _ _ _ _ rf_tb2tn_ex xsR). Qed.

Lemma m_tn2tb_correspondence xsR xsL :
  Lean.eq (lex (pre ne ne) xsR) xsL ->
  Lean.eq (lex (pre Ne_ Ne_) (Rf.m_tn2tb xsR)) (I.Prosa_Implementation_Refinements_Refinements_m_tn2tb xsL).
Proof. intro H. destruct H. exact (rf_map_ex _ _ _ _ rf_tn2tb_ex xsR). Qed.

Lemma predn_T_correspondence (T : Type) (oR : one_of T) oL (sR : sub_of T) sL :
  OneRel oR oL -> Op2Rel sR (Isub_op T sL) ->
  forall nR nL, Lean.eq nR nL ->
  Lean.eq (@Rf.predn_T T oR sR nR) (I.Prosa_Implementation_Refinements_Refinements_predn_T T oL sL nL).
Proof.
  intros Ho Hs nR nL Hn. destruct Hn.
  exact (rf_trans _ _ _ (Hs nR oR) (rf_congr (Isub_op T sL nR) _ _ Ho)).
Qed.

Lemma maxn_T_correspondence (T : Type) (lR : lt_of T) lL :
  BOpRel lR (Ilt_op T lL) ->
  forall mR mL nR nL, Lean.eq mR mL -> Lean.eq nR nL ->
  Lean.eq (@Rf.maxn_T T lR mR nR) (I.Prosa_Implementation_Refinements_Refinements_maxn_T T lL mL nL).
Proof.
  intros Hl mR mL nR nL Hm Hn. destruct Hm. destruct Hn.
  unfold I.Prosa_Implementation_Refinements_Refinements_maxn_T, Rf.maxn_T.
  have H := Hl mR nR. rf_rw H.
  change (@lt_op T lR mR nR) with (lR mR nR).
  destruct (lR mR nR); exact (rf_refl _).
Qed.

Lemma minn_T_correspondence (T : Type) (lR : lt_of T) lL :
  BOpRel lR (Ilt_op T lL) ->
  forall mR mL nR nL, Lean.eq mR mL -> Lean.eq nR nL ->
  Lean.eq (@Rf.minn_T T lR mR nR) (I.Prosa_Implementation_Refinements_Refinements_minn_T T lL mL nL).
Proof.
  intros Hl mR mL nR nL Hm Hn. destruct Hm. destruct Hn.
  unfold I.Prosa_Implementation_Refinements_Refinements_minn_T, Rf.minn_T.
  have H := Hl mR nR. rf_rw H.
  change (@lt_op T lR mR nR) with (lR mR nR).
  destruct (lR mR nR); exact (rf_refl _).
Qed.

Lemma rf_dvdn_T_ex (T : Type) (zR : zero_of T) zL (mR : mod_of T) mL (eR : eq_of T) eL :
  ZeroRel zR zL -> Op2Rel mR (Imod_op T mL) -> BOpRel eR (Ieq_op T eL) ->
  forall d m, Lean.eq (be (@Rf.dvdn_T T zR mR eR d m))
                      (I.Prosa_Implementation_Refinements_Refinements_dvdn_T T zL mL eL d m).
Proof.
  intros Hz Hm He d m.
  unfold I.Prosa_Implementation_Refinements_Refinements_dvdn_T, Rf.dvdn_T.
  have H1 := Hm m d. rf_rw H1.
  have Hz' : Lean.eq zR (Izero_op T zL) := Hz. rf_rw Hz'.
  exact (He (mR m d) zR).
Qed.

Lemma dvdn_T_correspondence (T : Type) (zR : zero_of T) zL (mR : mod_of T) mL (eR : eq_of T) eL :
  ZeroRel zR zL -> Op2Rel mR (Imod_op T mL) -> BOpRel eR (Ieq_op T eL) ->
  forall dR dL mR' mL', Lean.eq dR dL -> Lean.eq mR' mL' ->
  Lean.eq (be (@Rf.dvdn_T T zR mR eR dR mR'))
          (I.Prosa_Implementation_Refinements_Refinements_dvdn_T T zL mL eL dL mL').
Proof.
  intros Hz Hm He dR dL mR' mL' Hd Hm'. destruct Hd. destruct Hm'.
  exact (rf_dvdn_T_ex T zR zL mR mL eR eL Hz Hm He dR mR').
Qed.

Lemma div_ceil_T_correspondence (T : Type) (zR : zero_of T) zL (oR : one_of T) oL (aR : add_of T) aL
    (dR : div_of T) dL (mR : mod_of T) mL (eR : eq_of T) eL :
  ZeroRel zR zL -> OneRel oR oL -> Op2Rel aR (Iadd_op T aL) -> Op2Rel dR (Idiv_op T dL) ->
  Op2Rel mR (Imod_op T mL) -> BOpRel eR (Ieq_op T eL) ->
  forall xR xL yR yL, Lean.eq xR xL -> Lean.eq yR yL ->
  Lean.eq (@Rf.div_ceil_T T zR oR aR dR mR eR xR yR)
          (I.Prosa_Implementation_Refinements_Refinements_div_ceil_T T zL oL aL dL mL eL xL yL).
Proof.
  intros Hz Ho Ha Hd Hm He xR xL yR yL Hx Hy. destruct Hx. destruct Hy.
  unfold I.Prosa_Implementation_Refinements_Refinements_div_ceil_T, Rf.div_ceil_T.
  have Hb := rf_dvdn_T_ex T zR zL mR mL eR eL Hz Hm He yR xR. rf_rw Hb.
  destruct (Rf.dvdn_T yR xR); cbn [be].
  - exact (Hd xR yR).
  - exact (rf_trans _ _ _ (Ha oR (dR xR yR))
      (rf_congr2 (Iadd_op T aL) _ _ _ _ Ho (Hd xR yR))).
Qed.

Lemma iota_T_correspondence (T : Type) (oR : one_of T) oL (aR : add_of T) aL :
  OneRel oR oL -> Op2Rel aR (Iadd_op T aL) ->
  forall xR xL nR nL, Lean.eq xR xL -> SubNatRel nR nL ->
  Lean.eq (lex idr (@Rf.iota_T T oR aR xR nR))
          (I.Prosa_Implementation_Refinements_Refinements_iota_T T oL aL xL nL).
Proof.
  intros Ho Ha xR xL nR nL Hx Hn. destruct Hx. destruct Hn.
  revert xR; induction nR as [|n IH]; intro x.
  - exact (rf_refl _).
  - cbn [Rf.iota_T lex sub_nat_to_imported].
    refine (rf_congr (Icons T (idr x)) _ _ _).
    have H := IH (aR x oR).
    exact (rf_trans _ _ _ H
      (rf_congr (fun z => I.Prosa_Implementation_Refinements_Refinements_iota_T T oL aL z (ne n)) _ _
        (rf_trans _ _ _ (Ha x oR) (rf_congr (Iadd_op T aL x) _ _ Ho)))).
Qed.

Lemma size_T_correspondence (T : Type) (zR : zero_of T) zL (oR : one_of T) oL (aR : add_of T) aL :
  ZeroRel zR zL -> OneRel oR oL -> Op2Rel aR (Iadd_op T aL) ->
  forall (X : Type) sR sL, Lean.eq (lex idr sR) sL ->
  Lean.eq (@Rf.size_T T zR oR aR X sR) (I.Prosa_Implementation_Refinements_Refinements_size_T T zL oL aL X sL).
Proof.
  intros Hz Ho Ha X sR sL Hs. destruct Hs.
  induction sR as [|x s IH]; cbn [Rf.size_T lex].
  - exact Hz.
  - exact (rf_trans _ _ _ (Ha oR _) (rf_congr2 (Iadd_op T aL) _ _ _ _ Ho IH)).
Qed.

Lemma shift_points_pos_T_correspondence (T : Type) (aR : add_of T) aL :
  Op2Rel aR (Iadd_op T aL) ->
  forall xsR xsL sR sL, Lean.eq (lex idr xsR) xsL -> Lean.eq sR sL ->
  Lean.eq (lex idr (@Rf.shift_points_pos_T T aR xsR sR))
          (I.Prosa_Implementation_Refinements_Refinements_shift_points_pos_T T aL xsL sL).
Proof.
  intros Ha xsR xsL sR sL Hx Hs. destruct Hx. destruct Hs.
  exact (rf_map_ex idr idr _ _ (fun x => Ha sR x) xsR).
Qed.

Lemma shift_points_neg_T_correspondence (T : Type) (sR : sub_of T) sL (lR : leq_of T) lL :
  Op2Rel sR (Isub_op T sL) -> BOpRel lR (Ileq_op T lL) ->
  forall xsR xsL tR tL, Lean.eq (lex idr xsR) xsL -> Lean.eq tR tL ->
  Lean.eq (lex idr (@Rf.shift_points_neg_T T sR lR xsR tR))
          (I.Prosa_Implementation_Refinements_Refinements_shift_points_neg_T T sL lL xsL tL).
Proof.
  intros Hs Hl xsR xsL tR tL Hx Ht. destruct Hx. destruct Ht.
  unfold Rf.shift_points_neg_T, I.Prosa_Implementation_Refinements_Refinements_shift_points_neg_T.
  cbv zeta.
  have Hf := rf_filter_ex idr (fun x => lR tR x) (fun x => Ileq_op T lL tR x) (fun x => Hl tR x) xsR.
  rf_rw Hf.
  exact (rf_map_ex idr idr _ _ (fun x => Hs x tR) _).
Qed.

(** ** [Nat] operations of the target *)
Definition rf_add (a b : LN) : LN := I.HAdd_hAdd_inst7 LN LN LN (I.instHAdd_inst1 LN I.instAddNat) a b.
Definition rf_mul (a b : LN) : LN := I.HMul_hMul_inst7 LN LN LN (I.instHMul_inst1 LN I.instMulNat) a b.
Definition rf_sub (a b : LN) : LN := I.HSub_hSub_inst7 LN LN LN (I.instHSub_inst1 LN I.instSubNat) a b.
Definition rf_div (a b : LN) : LN := I.HDiv_hDiv_inst7 LN LN LN (I.instHDiv_inst1 LN I.Nat_instDiv) a b.
Definition rf_mod (a b : LN) : LN := I.HMod_hMod_inst7 LN LN LN (I.instHMod_inst1 LN I.Nat_instMod) a b.
Definition rf_lt (a b : LN) : SProp := I.LT_lt_inst1 LN I.instLTNat a b.
Definition rf_le (a b : LN) : SProp := I.LE_le_inst1 LN I.instLENat a b.
Definition rf_dvd (a b : LN) : SProp := I.Dvd_dvd_inst1 LN I.Nat_instDvd a b.
Definition rf_zero : LN := I.OfNat_ofNat_inst1 LN Lean.Nat_zero (I.instOfNatNat Lean.Nat_zero).

Lemma rf_add_rel aR aL bR bL : SubNatRel aR aL -> SubNatRel bR bL -> SubNatRel (aR + bR) (rf_add aL bL).
Proof. exact (sub_add_correspondence aR aL bR bL). Qed.
Lemma rf_mul_rel aR aL bR bL : SubNatRel aR aL -> SubNatRel bR bL -> SubNatRel (aR * bR) (rf_mul aL bL).
Proof. exact (sub_mul_correspondence aR aL bR bL). Qed.
Lemma rf_lt_rel aR aL bR bL : SubNatRel aR aL -> SubNatRel bR bL -> PropSPropRel (is_true (ltn aR bR)) (rf_lt aL bL).
Proof. exact (sub_nat_lt_correspondence aR aL bR bL). Qed.
Lemma rf_le_rel aR aL bR bL : SubNatRel aR aL -> SubNatRel bR bL -> PropSPropRel (is_true (leq aR bR)) (rf_le aL bL).
Proof. exact (sub_nat_le_correspondence aR aL bR bL). Qed.
Lemma rf_eq_rel aR aL bR bL : SubNatRel aR aL -> SubNatRel bR bL -> PropSPropRel (aR = bR) (Lean.eq aL bL).
Proof. exact (sub_nat_eq_correspondence aR aL bR bL). Qed.

Lemma rf_pred_ex n : Lean.eq (ne n.-1) (I.Nat_pred (ne n)).
Proof. destruct n; exact (rf_refl _). Qed.

Lemma rf_sub_ex a b : Lean.eq (ne (a - b)) (rf_sub (ne a) (ne b)).
Proof.
  revert a; induction b as [|b IH]; intro a.
  - rewrite subn0. exact (rf_refl _).
  - rewrite subnS.
    refine (rf_trans _ _ _ _ (rf_congr I.Nat_pred _ _ (IH a))).
    exact (rf_pred_ex (a - b)).
Qed.

Lemma rf_div_mod_decoded (x y : nat) :
  ni (rf_div (ne x) (ne y)) = x %/ y /\ ni (rf_mod (ne x) (ne y)) = x %% y.
Proof.
  case Hy: y => [|y'].
  - subst y. split.
    + rewrite divn0.
      exact (f_equal ni (rf_to_coq (I.Prosa_Validation_DivModInterface_production_div_zero (ne x)))).
    + rewrite modn0.
      transitivity (ni (ne x)).
      * exact (f_equal ni (rf_to_coq (I.Prosa_Validation_DivModInterface_production_mod_zero (ne x)))).
      * exact (rf_ni_ne x).
  - have Hypos : is_true (ltn O y'.+1) by done.
    set xL := ne x. set yL := ne y'.+1.
    set qL := rf_div xL yL. set rL := rf_mod xL yL.
    have HrLtR : is_true (ltn (ni rL) y'.+1).
    { exact (sprop_to_prop _ _
        (rf_lt_rel (ni rL) rL y'.+1 yL (sub_nat_rel_surjective rL) (sub_nat_rel_canonical y'.+1))
        (I.Prosa_Validation_DivModInterface_production_mod_lt xL yL
          (prop_to_sprop _ _
            (rf_lt_rel O rf_zero y'.+1 yL (sub_nat_rel_canonical O) (sub_nat_rel_canonical y'.+1))
            Hypos))). }
    have HdecompR : y'.+1 * ni qL + ni rL = x.
    { exact (sprop_to_prop _ _
        (rf_eq_rel (y'.+1 * ni qL + ni rL) (rf_add (rf_mul yL qL) rL) x xL
          (rf_add_rel _ _ _ _
            (rf_mul_rel y'.+1 yL (ni qL) qL (sub_nat_rel_canonical y'.+1) (sub_nat_rel_surjective qL))
            (sub_nat_rel_surjective rL))
          (sub_nat_rel_canonical x))
        (I.Prosa_Validation_DivModInterface_production_div_add_mod xL yL)). }
    have Hx : x = ni qL * y'.+1 + ni rL.
    { rewrite mulnC. exact (Logic.eq_sym HdecompR). }
    have Hedge : edivn x y'.+1 = (ni qL, ni rL).
    { rewrite Hx. exact (@edivn_eq y'.+1 (ni qL) (ni rL) HrLtR). }
    have Hq := f_equal (@Datatypes.fst nat nat) Hedge.
    change (Logic.eq (divn x (S y')) (ni qL)) in Hq.
    have Hr := f_equal (@Datatypes.snd nat nat) Hedge.
    change (Logic.eq (Datatypes.snd (edivn x (S y'))) (ni rL)) in Hr.
    rewrite <- (modn_def x y'.+1) in Hr.
    split; exact (Logic.eq_sym Hq) || exact (Logic.eq_sym Hr).
Qed.

Lemma rf_div_ex x y : Lean.eq (ne (x %/ y)) (rf_div (ne x) (ne y)).
Proof.
  have H := proj1 (rf_div_mod_decoded x y).
  exact (rf_trans _ _ _ (rf_of_coq (f_equal ne (Logic.eq_sym H))) (rf_ne_ni _)).
Qed.

Lemma rf_mod_ex x y : Lean.eq (ne (x %% y)) (rf_mod (ne x) (ne y)).
Proof.
  have H := proj2 (rf_div_mod_decoded x y).
  exact (rf_trans _ _ _ (rf_of_coq (f_equal ne (Logic.eq_sym H))) (rf_ne_ni _)).
Qed.

Lemma rf_dvd_rel x y : PropSPropRel (is_true (y %| x)) (rf_dvd (ne y) (ne x)).
Proof.
  apply prop_sprop_rel_intro.
  - intro HdvdR.
    apply (I.Iff_mpr _ _ (I.Prosa_Validation_DivModInterface_production_dvd_iff_mod_eq_zero (ne x) (ne y))).
    apply (prop_to_sprop _ _
      (rf_eq_rel (x %% y) (rf_mod (ne x) (ne y)) O rf_zero (rf_mod_ex x y) (sub_nat_rel_canonical O))).
    move: HdvdR. rewrite /dvdn. by move/eqP.
  - intro HdvdL. apply strictly_inhabits.
    rewrite /dvdn. apply/eqP.
    apply (sprop_to_prop _ _
      (rf_eq_rel (x %% y) (rf_mod (ne x) (ne y)) O rf_zero (rf_mod_ex x y) (sub_nat_rel_canonical O))).
    exact (I.Iff_mp _ _ (I.Prosa_Validation_DivModInterface_production_dvd_iff_mod_eq_zero (ne x) (ne y)) HdvdL).
Qed.

(** A Boolean decided in the target by any [Decidable] instance of a related proposition. *)
Definition rf_false_elim (Q : SProp) (H : I.False) : Q := match H return Q with end.

Lemma rf_decide_ex (b : bool) (Q : SProp) (d : I.Decidable Q) :
  PropSPropRel (is_true b) Q -> Lean.eq (be b) (I.Decidable_decide Q d).
Proof.
  intro H. destruct d as [hn|hy]; destruct b; cbn [be].
  - exact (rf_false_elim _ (hn (prop_to_sprop _ _ H Logic.eq_refl))).
  - exact (rf_refl _).
  - exact (rf_refl _).
  - have F := sprop_to_prop _ _ H hy. discriminate F.
Qed.

(** A target [ite] on a related proposition. *)
Lemma rf_ite_ex {A : Type} (b : bool) (Q : SProp) (d : I.Decidable Q) (x y : A) :
  PropSPropRel (is_true b) Q -> Lean.eq (if b then x else y) (I.ite A Q d x y).
Proof.
  intro H. destruct d as [hn|hy]; destruct b.
  - exact (rf_false_elim _ (hn (prop_to_sprop _ _ H Logic.eq_refl))).
  - exact (rf_refl _).
  - exact (rf_refl _).
  - have F := sprop_to_prop _ _ H hy. discriminate F.
Qed.

Lemma rf_lt_decide_ex a b : Lean.eq (be (ltn a b)) (I.Decidable_decide (rf_lt (ne a) (ne b)) (I.Nat_decLt (ne a) (ne b))).
Proof. exact (rf_decide_ex _ _ _ (rf_lt_rel a _ b _ (sub_nat_rel_canonical a) (sub_nat_rel_canonical b))). Qed.

Lemma rf_le_decide_ex a b : Lean.eq (be (leq a b)) (I.Decidable_decide (rf_le (ne a) (ne b)) (I.Nat_decLe (ne a) (ne b))).
Proof. exact (rf_decide_ex _ _ _ (rf_le_rel a _ b _ (sub_nat_rel_canonical a) (sub_nat_rel_canonical b))). Qed.

Lemma rf_dvd_decide_ex d m : Lean.eq (be (d %| m)) (I.Decidable_decide (rf_dvd (ne d) (ne m)) (I.Nat_decidable_dvd (ne d) (ne m))).
Proof. exact (rf_decide_ex _ _ _ (rf_dvd_rel m d)). Qed.

Lemma rf_div_ceil_ex x y : Lean.eq (ne (div_ceil x y)) (I.Prosa_Util_Div_mod_div_ceil (ne x) (ne y)).
Proof.
  unfold div_ceil, I.Prosa_Util_Div_mod_div_ceil.
  refine (rf_trans _ _ _ _ (rf_ite_ex (y %| x) _ (I.Nat_decidable_dvd (ne y) (ne x)) _ _ (rf_dvd_rel x y))).
  destruct (y %| x).
  - exact (rf_div_ex x y).
  - rewrite -addn1.
    exact (rf_trans _ _ _ (rf_add_ex (x %/ y) (S O)) (rf_congr (fun z => rf_add z (ne (S O))) _ _ (rf_div_ex x y))).
Qed.

(** ** List functions of the statements *)
Lemma rf_all_ex {A C : Type} (eA : A -> C) (P : A -> bool) (PL : C -> I.Bool)
    (HP : forall a, Lean.eq (be (P a)) (PL (eA a))) xs :
  Lean.eq (be (all P xs)) (I.List_all_inst1 C (lex eA xs) PL).
Proof.
  induction xs as [|x xs IH]; cbn [all lex].
  - exact (rf_refl _).
  - change (Lean.eq (be (P x && all P xs)) (I.Bool_and (PL (eA x)) (I.List_all_inst1 C (lex eA xs) PL))).
    have Hx := HP x. rf_rw Hx. rf_rw IH.
    destruct (P x); exact (rf_refl _).
Qed.

Lemma rf_cat_ex {A C : Type} (eA : A -> C) xs ys :
  Lean.eq (lex eA (xs ++ ys)) (I.List_append_inst1 C (lex eA xs) (lex eA ys)).
Proof.
  induction xs as [|x xs IH]; cbn [cat lex].
  - exact (rf_refl _).
  - exact (rf_congr (Icons C (eA x)) _ _ IH).
Qed.

Lemma rf_flatten_ex {A C : Type} (eA : A -> C) xss :
  Lean.eq (lex eA (flatten xss)) (I.List_flatten_inst1 C (lex (lex eA) xss)).
Proof.
  induction xss as [|xs xss IH]; cbn [lex].
  - exact (rf_refl _).
  - change (Lean.eq (lex eA (xs ++ flatten xss))
      (I.List_append_inst1 C (lex eA xs) (I.List_flatten_inst1 C (lex (lex eA) xss)))).
    exact (rf_trans _ _ _ (rf_cat_ex eA xs (flatten xss)) (rf_congr (I.List_append_inst1 C (lex eA xs)) _ _ IH)).
Qed.

Lemma rf_last_ex {A C : Type} (eA : A -> C) x xs :
  Lean.eq (eA (last x xs)) (I.Prosa_Implementation_Refinements_Refinements_seq_last C (eA x) (lex eA xs)).
Proof.
  revert x; induction xs as [|y xs IH]; intro x; cbn [last lex].
  - exact (rf_refl _).
  - exact (IH y).
Qed.

Lemma rf_foldr_ex {A B C D : Type} (eA : A -> C) (eB : B -> D) (f : A -> B -> B) (fL : C -> D -> D)
    (Hf : forall a b, Lean.eq (eB (f a b)) (fL (eA a) (eB b))) z xs :
  Lean.eq (eB (foldr f z xs)) (I.List_foldr_inst3 C D fL (eB z) (lex eA xs)).
Proof.
  induction xs as [|x xs IH]; cbn [foldr lex].
  - exact (rf_refl _).
  - exact (rf_trans _ _ _ (Hf x _) (rf_congr (fL (eA x)) _ _ IH)).
Qed.

Lemma rf_spp_ex xs s : Lean.eq (lex ne (shift_points_pos xs s)) (I.Prosa_Util_List_shift_points_pos (lex ne xs) (ne s)).
Proof. exact (rf_map_ex ne ne _ _ (fun x => rf_add_ex s x) xs). Qed.

Lemma rf_spn_ex xs s : Lean.eq (lex ne (shift_points_neg xs s)) (I.Prosa_Util_List_shift_points_neg (lex ne xs) (ne s)).
Proof.
  unfold shift_points_neg, I.Prosa_Util_List_shift_points_neg. cbv zeta.
  have Hf := rf_filter_ex ne (fun x => leq s x)
    (fun xL => I.Decidable_decide (I.LE_le_inst1 LN I.instLENat (ne s) xL) (I.Nat_decLe (ne s) xL))
    (fun x => rf_le_decide_ex s x) xs.
  rf_rw Hf.
  exact (rf_map_ex ne ne _ (fun x => rf_sub x (ne s)) (fun x => rf_sub_ex x s) _).
Qed.

(** ** CoqEAL's relations *)
Abbreviation IRnat := I.Prosa_Implementation_Refinements_Refinements_Rnat.
Abbreviation IbR := I.Prosa_Implementation_Refinements_Refinements_bool_R.
Abbreviation IlR := I.Prosa_Implementation_Refinements_Refinements_list_R.
Abbreviation IpR := I.Prosa_Implementation_Refinements_Refinements_prod_R.
Abbreviation Iref := I.Prosa_Implementation_Refinements_Refinements_refines.
Abbreviation Iref_mk := I.Prosa_Implementation_Refinements_Refinements_refines_mk.
Abbreviation Iref_rel := I.Prosa_Implementation_Refinements_Refinements_refines_refines_rel.
Abbreviation Ihr := I.Prosa_Implementation_Refinements_Refinements_hrespectful.

(** Maps in both directions between a source statement and a target statement. *)
Record TypeCorrespondence (S T : Type) : Type := TypeCorr { to_target : S -> T; to_source : T -> S }.
Arguments TypeCorr {S T}.

Definition rf_ref_out {A B : Type} {R : A -> B -> Type} {a : A} {b : B} (H : refines R a b) : R a b :=
  refinesP H.
Definition rf_ref_in {A B : Type} {R : A -> B -> Type} {a : A} {b : B} (H : R a b) : refines R a b :=
  match Logic.eq_sym (refinesE R) in Logic.eq _ T return T a b with Logic.eq_refl => H end.

(** [Rnat] *)
Definition rnat_fw (n : nat) (x : N) (H : Rnat n x) : IRnat (ne n) (Ne_ x) :=
  I.PLift_up_inst1 _ (rf_trans _ _ _ (rf_sym _ _ (rf_nat_of_bin_ex x))
    (rf_of_coq (f_equal ne (H : Logic.eq (nat_of_bin x) n)))).

Lemma rnat_bw (nL : LN) (xL : IN) (H : IRnat nL xL) : Rnat (ni nL) (Ni xL).
Proof.
  have h : Lean.eq (Inat_of_bin xL) nL := I.PLift_down_inst1 _ H.
  change (Logic.eq (nat_of_bin (Ni xL)) (ni nL)).
  have H1 : Lean.eq (ne (nat_of_bin (Ni xL))) nL :=
    rf_trans _ _ _ (rf_nat_of_bin_ex (Ni xL)) (rf_trans _ _ _ (rf_congr Inat_of_bin _ _ (rf_Ne_Ni xL)) h).
  have H2 := f_equal ni (rf_to_coq H1).
  by rewrite rf_ni_ne in H2.
Qed.

Definition rnat_bw' (n : nat) (x : N) (H : IRnat (ne n) (Ne_ x)) : Rnat n x.
Proof. have H' := rnat_bw _ _ H. by rewrite rf_ni_ne rf_Ni_Ne in H'. Defined.

(** [bool_R] *)
Definition boolR_fw (b b' : bool) (H : bool_R b b') : IbR (be b) (be b') :=
  match H in bool_R b b' return IbR (be b) (be b') with
  | true_R => I.Prosa_Implementation_Refinements_Refinements_bool_R_true_R
  | false_R => I.Prosa_Implementation_Refinements_Refinements_bool_R_false_R
  end.
Definition boolR_bw (b b' : I.Bool) (H : IbR b b') : bool_R (bi b) (bi b') :=
  match H in IbR b b' return bool_R (bi b) (bi b') with
  | I.Prosa_Implementation_Refinements_Refinements_bool_R_true_R => true_R
  | I.Prosa_Implementation_Refinements_Refinements_bool_R_false_R => false_R
  end.
Definition boolR_bw' (b b' : bool) (H : IbR (be b) (be b')) : bool_R b b'.
Proof. have H' := boolR_bw _ _ H. by rewrite !rf_bi_be in H'. Defined.
Definition boolR_of_eq (b b' : bool) (H : Logic.eq b b') : bool_R b b'.
Proof. destruct H; destruct b; constructor. Defined.

(** [list_R], for any element maps *)
Fixpoint listR_fw {A A' C C' : Type} (eA : A -> C) (eA' : A' -> C') (R : A -> A' -> Type) (RL : C -> C' -> Type)
    (h : forall a a', R a a' -> RL (eA a) (eA' a')) (xs : seq A) (xs' : seq A') (H : list_R R xs xs') {struct H} :
    IlR C C' RL (lex eA xs) (lex eA' xs') :=
  match H in list_R _ xs xs' return IlR C C' RL (lex eA xs) (lex eA' xs') with
  | nil_R => I.Prosa_Implementation_Refinements_Refinements_list_R_nil_R C C' RL
  | cons_R x1 x2 hx s1 s2 hs =>
      I.Prosa_Implementation_Refinements_Refinements_list_R_cons_R C C' RL _ _ (h _ _ hx) _ _
        (listR_fw eA eA' R RL h s1 s2 hs)
  end.

Fixpoint listR_bw {A A' C C' : Type} (iA : C -> A) (iA' : C' -> A') (R : A -> A' -> Type) (RL : C -> C' -> Type)
    (h : forall c c', RL c c' -> R (iA c) (iA' c')) (xs : IList C) (xs' : IList C') (H : IlR C C' RL xs xs')
    {struct H} : list_R R (lim iA xs) (lim iA' xs') :=
  match H in IlR _ _ _ xs xs' return list_R R (lim iA xs) (lim iA' xs') with
  | I.Prosa_Implementation_Refinements_Refinements_list_R_nil_R => nil_R R
  | I.Prosa_Implementation_Refinements_Refinements_list_R_cons_R x1 x2 hx s1 s2 hs =>
      @cons_R _ _ R _ _ (h _ _ hx) _ _ (listR_bw iA iA' R RL h s1 s2 hs)
  end.

(** [prod_R] *)
Definition prodR_fw {A A' B B' C C' D D' : Type} (eA : A -> C) (eA' : A' -> C') (eB : B -> D) (eB' : B' -> D')
    (RA : A -> A' -> Type) (RAL : C -> C' -> Type) (RB : B -> B' -> Type) (RBL : D -> D' -> Type)
    (hA : forall a a', RA a a' -> RAL (eA a) (eA' a')) (hB : forall b b', RB b b' -> RBL (eB b) (eB' b'))
    (x : A * B) (x' : A' * B') (H : prod_R RA RB x x') : IpR C C' RAL D D' RBL (pre eA eB x) (pre eA' eB' x') :=
  match H in prod_R _ _ x x' return IpR C C' RAL D D' RBL (pre eA eB x) (pre eA' eB' x') with
  | pair_R a a' ha b b' hb =>
      I.Prosa_Implementation_Refinements_Refinements_prod_R_pair_R C C' RAL D D' RBL _ _ (hA _ _ ha) _ _ (hB _ _ hb)
  end.

(** ** Statement correspondences *)
Ltac src_ty c := let t := type of c in exact t.

(** Shapes [refines (Rnat ==> Rnat) f g] and [refines (Rnat ==> Rnat ==> R) f g]. *)
Definition rf_corr_11 (f : nat -> nat) (g : N -> N) (fL : LN -> LN) (gL : IN -> IN)
    (Hf : forall n, Lean.eq (ne (f n)) (fL (ne n))) (Hg : forall x, Lean.eq (Ne_ (g x)) (gL (Ne_ x))) :
  TypeCorrespondence (refines (hrespectful Rnat Rnat) f g)
    (Iref (LN -> LN) (IN -> IN) (Ihr LN IN LN IN IRnat IRnat) fL gL).
Proof.
  split.
  - intro s. apply Iref_mk. intros nL xL r.
    have o := rnat_fw _ _ (rf_ref_out s (ni nL) (Ni xL) (rnat_bw _ _ r)).
    refine (rf_tr2 IRnat _ _ o).
    + exact (rf_trans _ _ _ (Hf _) (rf_congr fL _ _ (rf_ne_ni nL))).
    + exact (rf_trans _ _ _ (Hg _) (rf_congr gL _ _ (rf_Ne_Ni xL))).
  - intro t. apply rf_ref_in. intros n x r.
    have o := Iref_rel _ _ _ _ _ t (ne n) (Ne_ x) (rnat_fw _ _ r).
    apply rnat_bw'.
    exact (rf_tr2 IRnat (rf_sym _ _ (Hf n)) (rf_sym _ _ (Hg x)) o).
Defined.

Definition rf_corr_21 (f : nat -> nat -> nat) (g : N -> N -> N) (fL : LN -> LN -> LN) (gL : IN -> IN -> IN)
    (Hf : forall n m, Lean.eq (ne (f n m)) (fL (ne n) (ne m)))
    (Hg : forall x y, Lean.eq (Ne_ (g x y)) (gL (Ne_ x) (Ne_ y))) :
  TypeCorrespondence (refines (hrespectful Rnat (hrespectful Rnat Rnat)) f g)
    (Iref (LN -> LN -> LN) (IN -> IN -> IN)
       (Ihr LN IN (LN -> LN) (IN -> IN) IRnat (Ihr LN IN LN IN IRnat IRnat)) fL gL).
Proof.
  split.
  - intro s. apply Iref_mk. intros nL xL r mL yL r2.
    have o := rnat_fw _ _ (rf_ref_out s (ni nL) (Ni xL) (rnat_bw _ _ r) (ni mL) (Ni yL) (rnat_bw _ _ r2)).
    refine (rf_tr2 IRnat _ _ o).
    + exact (rf_trans _ _ _ (Hf _ _) (rf_congr2 fL _ _ _ _ (rf_ne_ni nL) (rf_ne_ni mL))).
    + exact (rf_trans _ _ _ (Hg _ _) (rf_congr2 gL _ _ _ _ (rf_Ne_Ni xL) (rf_Ne_Ni yL))).
  - intro t. apply rf_ref_in. intros n x r m y r2.
    have o := Iref_rel _ _ _ _ _ t (ne n) (Ne_ x) (rnat_fw _ _ r) (ne m) (Ne_ y) (rnat_fw _ _ r2).
    apply rnat_bw'.
    exact (rf_tr2 IRnat (rf_sym _ _ (Hf n m)) (rf_sym _ _ (Hg x y)) o).
Defined.

Definition rf_corr_2b (f : nat -> nat -> bool) (g : N -> N -> bool) (fL : LN -> LN -> I.Bool)
    (gL : IN -> IN -> I.Bool)
    (Hf : forall n m, Lean.eq (be (f n m)) (fL (ne n) (ne m)))
    (Hg : forall x y, Lean.eq (be (g x y)) (gL (Ne_ x) (Ne_ y))) :
  TypeCorrespondence (refines (hrespectful Rnat (hrespectful Rnat bool_R)) f g)
    (Iref (LN -> LN -> I.Bool) (IN -> IN -> I.Bool)
       (Ihr LN IN (LN -> I.Bool) (IN -> I.Bool) IRnat (Ihr LN IN I.Bool I.Bool IRnat IbR)) fL gL).
Proof.
  split.
  - intro s. apply Iref_mk. intros nL xL r mL yL r2.
    have o := boolR_fw _ _ (rf_ref_out s (ni nL) (Ni xL) (rnat_bw _ _ r) (ni mL) (Ni yL) (rnat_bw _ _ r2)).
    refine (rf_tr2 IbR _ _ o).
    + exact (rf_trans _ _ _ (Hf _ _) (rf_congr2 fL _ _ _ _ (rf_ne_ni nL) (rf_ne_ni mL))).
    + exact (rf_trans _ _ _ (Hg _ _) (rf_congr2 gL _ _ _ _ (rf_Ne_Ni xL) (rf_Ne_Ni yL))).
  - intro t. apply rf_ref_in. intros n x r m y r2.
    have o := Iref_rel _ _ _ _ _ t (ne n) (Ne_ x) (rnat_fw _ _ r) (ne m) (Ne_ y) (rnat_fw _ _ r2).
    apply boolR_bw'.
    exact (rf_tr2 IbR (rf_sym _ _ (Hf n m)) (rf_sym _ _ (Hg x y)) o).
Defined.

(** The [N] instances of CoqEAL [binnat] are the Lean ones. *)
Lemma rf_predn_T_N_ex x :
  Lean.eq (Ne_ (Rf.predn_T x))
    (I.Prosa_Implementation_Refinements_Refinements_predn_T IN I.Prosa_Implementation_Refinements_Refinements_one_N
       I.Prosa_Implementation_Refinements_Refinements_sub_N (Ne_ x)).
Proof. exact (rf_N_sub_ex x (Npos xH)). Qed.

Lemma rf_dvdn_T_N_ex d m :
  Lean.eq (be (Rf.dvdn_T d m))
    (I.Prosa_Implementation_Refinements_Refinements_dvdn_T IN I.Prosa_Implementation_Refinements_Refinements_zero_N
       I.Prosa_Implementation_Refinements_Refinements_mod_N I.Prosa_Implementation_Refinements_Refinements_eq_N
       (Ne_ d) (Ne_ m)).
Proof.
  exact (rf_trans _ _ _ (rf_N_eqb_ex (N.modulo m d) N0) (rf_congr (fun z => INeqb z IN0) _ _ (rf_N_mod_ex m d))).
Qed.

Lemma rf_div_ceil_T_N_ex x y :
  Lean.eq (Ne_ (Rf.div_ceil_T x y))
    (I.Prosa_Implementation_Refinements_Refinements_div_ceil_T IN I.Prosa_Implementation_Refinements_Refinements_zero_N
       I.Prosa_Implementation_Refinements_Refinements_one_N I.Prosa_Implementation_Refinements_Refinements_add_N
       I.Prosa_Implementation_Refinements_Refinements_div_N I.Prosa_Implementation_Refinements_Refinements_mod_N
       I.Prosa_Implementation_Refinements_Refinements_eq_N (Ne_ x) (Ne_ y)).
Proof.
  unfold I.Prosa_Implementation_Refinements_Refinements_div_ceil_T, Rf.div_ceil_T.
  have Hb := rf_dvdn_T_N_ex y x. rf_rw Hb.
  destruct (Rf.dvdn_T y x); cbn [be].
  - exact (rf_N_div_ex x y).
  - exact (rf_trans _ _ _ (rf_N_add_ex (Npos xH) (N.div x y))
      (rf_congr (INadd (INpos IxH)) _ _ (rf_N_div_ex x y))).
Qed.

Lemma rf_minn_T_N_ex x y :
  Lean.eq (Ne_ (Rf.minn_T x y))
    (I.Prosa_Implementation_Refinements_Refinements_minn_T IN I.Prosa_Implementation_Refinements_Refinements_lt_N
       (Ne_ x) (Ne_ y)).
Proof.
  unfold I.Prosa_Implementation_Refinements_Refinements_minn_T, Rf.minn_T.
  have H : Lean.eq (be (N.ltb x y)) (Ilt_op IN I.Prosa_Implementation_Refinements_Refinements_lt_N (Ne_ x) (Ne_ y))
    := rf_N_ltb_ex x y.
  rf_rw H.
  change (@lt_op N lt_N x y) with (N.ltb x y).
  destruct (N.ltb x y); exact (rf_refl _).
Qed.

Lemma rf_maxn_T_N_ex x y :
  Lean.eq (Ne_ (Rf.maxn_T x y))
    (I.Prosa_Implementation_Refinements_Refinements_maxn_T IN I.Prosa_Implementation_Refinements_Refinements_lt_N
       (Ne_ x) (Ne_ y)).
Proof.
  unfold I.Prosa_Implementation_Refinements_Refinements_maxn_T, Rf.maxn_T.
  have H : Lean.eq (be (N.ltb x y)) (Ilt_op IN I.Prosa_Implementation_Refinements_Refinements_lt_N (Ne_ x) (Ne_ y))
    := rf_N_ltb_ex x y.
  rf_rw H.
  change (@lt_op N lt_N x y) with (N.ltb x y).
  destruct (N.ltb x y); exact (rf_refl _).
Qed.

(** Lists of [Rnat]-related numbers. *)
Definition lrnat_fw xs xs' (H : list_R Rnat xs xs') : IlR LN IN IRnat (lex ne xs) (lex Ne_ xs') :=
  listR_fw ne Ne_ Rnat IRnat rnat_fw xs xs' H.
Definition lrnat_bw xsL xsL' (H : IlR LN IN IRnat xsL xsL') : list_R Rnat (lim ni xsL) (lim Ni xsL') :=
  listR_bw ni Ni Rnat IRnat rnat_bw xsL xsL' H.
Definition lrnat_bw' xs xs' (H : IlR LN IN IRnat (lex ne xs) (lex Ne_ xs')) : list_R Rnat xs xs'.
Proof.
  have H' := lrnat_bw _ _ H.
  by rewrite (rf_lim_lex ne ni rf_ni_ne) (rf_lim_lex Ne_ Ni rf_Ni_Ne) in H'.
Defined.
Definition rf_lne_lni xsL : Lean.eq (lex ne (lim ni xsL)) xsL := rf_lex_lim ne ni rf_ne_ni xsL.
Definition rf_lNe_lNi xsL : Lean.eq (lex Ne_ (lim Ni xsL)) xsL := rf_lex_lim Ne_ Ni rf_Ne_Ni xsL.

Lemma rf_nob_pos_zero (p : positive) :
  Lean.eq (Inat_of_bin (INpos (pe p))) Lean.Nat_zero -> Logic.eq (nat_of_bin (Npos p)) O.
Proof.
  intro h.
  have H1 := rf_trans _ _ _ (rf_nat_of_bin_ex (Npos p)) h.
  have H2 := f_equal ni (rf_to_coq H1). by rewrite rf_ni_ne in H2.
Qed.

Definition rf_false_to_target (H : Logic.False) : I.False := match H return I.False with end.
Definition rf_target_false_to_strict (H : I.False) : StrictlyInhabited Logic.False := match H with end.

(** [iotaTsuccN] (a [Prop]) *)
Lemma rf_iota_T_N_ex a n :
  Lean.eq (lex Ne_ (Rf.iota_T a n))
    (I.Prosa_Implementation_Refinements_Refinements_iota_T IN I.Prosa_Implementation_Refinements_Refinements_one_N
       I.Prosa_Implementation_Refinements_Refinements_add_N (Ne_ a) (ne n)).
Proof.
  revert a; induction n as [|n IH]; intro a; cbn [Rf.iota_T lex].
  - exact (rf_refl _).
  - refine (rf_congr (Icons IN (Ne_ a)) _ _ _).
    exact (rf_trans _ _ _ (IH _)
      (rf_congr (fun z => I.Prosa_Implementation_Refinements_Refinements_iota_T IN
         I.Prosa_Implementation_Refinements_Refinements_one_N I.Prosa_Implementation_Refinements_Refinements_add_N z (ne n))
        _ _ (rf_N_add_ex a (Npos xH)))).
Qed.

Lemma rf_iotaTsuccN_lhs a p :
  Lean.eq (lex Ne_ (Rf.iota_T a (nat_of_bin (N.succ (Pos.pred_N p)))))
    (I.Prosa_Implementation_Refinements_Refinements_iota_T IN I.Prosa_Implementation_Refinements_Refinements_one_N
       I.Prosa_Implementation_Refinements_Refinements_add_N (Ne_ a)
       (Inat_of_bin (INsucc (IPpred_N (pe p))))).
Proof.
  refine (rf_trans _ _ _ (rf_iota_T_N_ex _ _) _).
  refine (rf_congr (I.Prosa_Implementation_Refinements_Refinements_iota_T IN I.Prosa_Implementation_Refinements_Refinements_one_N
       I.Prosa_Implementation_Refinements_Refinements_add_N (Ne_ a)) _ _ _).
  exact (rf_trans _ _ _ (rf_nat_of_bin_ex _)
    (rf_congr Inat_of_bin _ _ (rf_trans _ _ _ (rf_N_succ_ex _) (rf_congr INsucc _ _ (rf_pred_N_ex p))))).
Qed.

Lemma rf_iotaTsuccN_rhs a p :
  Lean.eq (lex Ne_ (a :: Rf.iota_T (succN a) (nat_of_bin (Pos.pred_N p))))
    (Icons IN (Ne_ a) (I.Prosa_Implementation_Refinements_Refinements_iota_T IN I.Prosa_Implementation_Refinements_Refinements_one_N
       I.Prosa_Implementation_Refinements_Refinements_add_N (I.Prosa_Implementation_Refinements_Refinements_succN (Ne_ a))
       (Inat_of_bin (IPpred_N (pe p))))).
Proof.
  refine (rf_congr (Icons IN (Ne_ a)) _ _ _).
  refine (rf_trans _ _ _ (rf_iota_T_N_ex _ _) _).
  refine (rf_congr2 (I.Prosa_Implementation_Refinements_Refinements_iota_T IN I.Prosa_Implementation_Refinements_Refinements_one_N
       I.Prosa_Implementation_Refinements_Refinements_add_N) _ _ _ _ _ _).
  - exact (rf_N_add_ex (Npos xH) a).
  - exact (rf_trans _ _ _ (rf_nat_of_bin_ex _) (rf_congr Inat_of_bin _ _ (rf_pred_N_ex p))).
Qed.

(** [refine_shift_points_pos], [refine_shift_points_neg] *)
Lemma rf_spp_T_N_ex xs s :
  Lean.eq (lex Ne_ (Rf.shift_points_pos_T xs s))
    (I.Prosa_Implementation_Refinements_Refinements_shift_points_pos_T IN I.Prosa_Implementation_Refinements_Refinements_add_N
       (lex Ne_ xs) (Ne_ s)).
Proof. exact (rf_map_ex Ne_ Ne_ _ (fun x => INadd (Ne_ s) x) (fun x => rf_N_add_ex s x) xs). Qed.

Lemma rf_spn_T_N_ex xs s :
  Lean.eq (lex Ne_ (Rf.shift_points_neg_T xs s))
    (I.Prosa_Implementation_Refinements_Refinements_shift_points_neg_T IN I.Prosa_Implementation_Refinements_Refinements_sub_N
       I.Prosa_Implementation_Refinements_Refinements_leq_N (lex Ne_ xs) (Ne_ s)).
Proof.
  unfold Rf.shift_points_neg_T, I.Prosa_Implementation_Refinements_Refinements_shift_points_neg_T. cbv zeta.
  have Hf := rf_filter_ex Ne_ (fun x => N.leb s x)
    (fun xL => Ileq_op IN I.Prosa_Implementation_Refinements_Refinements_leq_N (Ne_ s) xL)
    (fun x => rf_N_leb_ex s x) xs.
  rf_rw Hf.
  exact (rf_map_ex Ne_ Ne_ _ (fun x => INsub x (Ne_ s)) (fun x => rf_N_sub_ex x s) _).
Qed.

Definition rf_corr_lsl (f : seq nat -> nat -> seq nat) (g : seq N -> N -> seq N)
    (fL : IList LN -> LN -> IList LN) (gL : IList IN -> IN -> IList IN)
    (Hf : forall xs s, Lean.eq (lex ne (f xs s)) (fL (lex ne xs) (ne s)))
    (Hg : forall xs s, Lean.eq (lex Ne_ (g xs s)) (gL (lex Ne_ xs) (Ne_ s))) :
  TypeCorrespondence (refines (hrespectful (list_R Rnat) (hrespectful Rnat (list_R Rnat))) f g)
    (Iref (IList LN -> LN -> IList LN) (IList IN -> IN -> IList IN)
       (Ihr (IList LN) (IList IN) (LN -> IList LN) (IN -> IList IN) (IlR LN IN IRnat)
          (Ihr LN IN (IList LN) (IList IN) IRnat (IlR LN IN IRnat))) fL gL).
Proof.
  split.
  - intro s. apply Iref_mk. intros xsL xs'L rx sL s'L rs.
    have o := lrnat_fw _ _ (rf_ref_out s (lim ni xsL) (lim Ni xs'L) (lrnat_bw _ _ rx) (ni sL) (Ni s'L) (rnat_bw _ _ rs)).
    refine (rf_tr2 (IlR LN IN IRnat) _ _ o).
    + exact (rf_trans _ _ _ (Hf _ _) (rf_congr2 fL _ _ _ _ (rf_lne_lni xsL) (rf_ne_ni sL))).
    + exact (rf_trans _ _ _ (Hg _ _) (rf_congr2 gL _ _ _ _ (rf_lNe_lNi xs'L) (rf_Ne_Ni s'L))).
  - intro t. apply rf_ref_in. intros xs xs' rx s s' rs.
    have o := Iref_rel _ _ _ _ _ t (lex ne xs) (lex Ne_ xs') (lrnat_fw _ _ rx) (ne s) (Ne_ s') (rnat_fw _ _ rs).
    apply lrnat_bw'.
    exact (rf_tr2 (IlR LN IN IRnat) (rf_sym _ _ (Hf xs s)) (rf_sym _ _ (Hg xs' s')) o).
Defined.

(** [refine_zip] *)
Definition prodR_bw {A A' B B' C C' D D' : Type} (iA : C -> A) (iA' : C' -> A') (iB : D -> B) (iB' : D' -> B')
    (RA : A -> A' -> Type) (RAL : C -> C' -> Type) (RB : B -> B' -> Type) (RBL : D -> D' -> Type)
    (hA : forall c c', RAL c c' -> RA (iA c) (iA' c')) (hB : forall d d', RBL d d' -> RB (iB d) (iB' d'))
    (x : IProd C D) (x' : IProd C' D') (H : IpR C C' RAL D D' RBL x x') : prod_R RA RB (pri iA iB x) (pri iA' iB' x') :=
  match H in IpR _ _ _ _ _ _ x x' return prod_R RA RB (pri iA iB x) (pri iA' iB' x') with
  | I.Prosa_Implementation_Refinements_Refinements_prod_R_pair_R a a' ha b b' hb =>
      @pair_R _ _ RA _ _ RB _ _ (hA _ _ ha) _ _ (hB _ _ hb)
  end.

Abbreviation pRR := (prod_R Rnat Rnat).
Abbreviation IpRR := (IpR LN IN IRnat LN IN IRnat).
Definition prr_fw x x' (H : pRR x x') : IpRR (pre ne ne x) (pre Ne_ Ne_ x') :=
  prodR_fw ne Ne_ ne Ne_ Rnat IRnat Rnat IRnat rnat_fw rnat_fw x x' H.
Definition prr_bw x x' (H : IpRR x x') : pRR (pri ni ni x) (pri Ni Ni x') :=
  prodR_bw ni Ni ni Ni Rnat IRnat Rnat IRnat rnat_bw rnat_bw x x' H.
Lemma rf_pri_pre_n x : pri ni ni (pre ne ne x) = x.
Proof. by case: x => a b; rewrite /pri /pre /= !rf_ni_ne. Qed.
Lemma rf_pri_pre_N x : pri Ni Ni (pre Ne_ Ne_ x) = x.
Proof. by case: x => a b; rewrite /pri /pre /= !rf_Ni_Ne. Qed.
Lemma rf_pre_pri_n x : Lean.eq (pre ne ne (pri ni ni x)) x.
Proof. exact (rf_pair_eq _ _ _ _ (rf_ne_ni _) (rf_ne_ni _)). Qed.
Lemma rf_pre_pri_N x : Lean.eq (pre Ne_ Ne_ (pri Ni Ni x)) x.
Proof. exact (rf_pair_eq _ _ _ _ (rf_Ne_Ni _) (rf_Ne_Ni _)). Qed.

(** ** Generic statements: element types and relations are shared, lists are related elementwise by identity *)
Definition rf_idr_rt {A : Type} (a : A) : Logic.eq (idr (idr a)) a := Logic.eq_refl.
Definition rf_idr_rtL {A : Type} (a : A) : Lean.eq (idr (idr a)) a := rf_refl a.
Definition rf_lid_rt {A : Type} (xs : IList A) : Lean.eq (lex idr (lim idr xs)) xs := rf_lex_lim idr idr rf_idr_rtL xs.
Definition rf_lid_rtR {A : Type} (xs : seq A) : Logic.eq (lim idr (lex idr xs)) xs := rf_lim_lex idr idr rf_idr_rt xs.
Definition lid_fw {A A' : Type} (rA : A -> A' -> Type) xs xs' (H : list_R rA xs xs') : IlR A A' rA (lex idr xs) (lex idr xs') :=
  listR_fw idr idr rA rA (fun _ _ h => h) xs xs' H.
Definition lid_bw {A A' : Type} (rA : A -> A' -> Type) xs xs' (H : IlR A A' rA xs xs') : list_R rA (lim idr xs) (lim idr xs') :=
  listR_bw idr idr rA rA (fun _ _ h => h) xs xs' H.
Definition lid_bw' {A A' : Type} (rA : A -> A' -> Type) xs xs' (H : IlR A A' rA (lex idr xs) (lex idr xs')) : list_R rA xs xs'.
Proof. have H' := lid_bw rA _ _ H. by rewrite !rf_lid_rtR in H'. Defined.

(** [refine_size] *)
Lemma rf_size_T_N_ex {C : Type} (s : seq C) :
  Lean.eq (Ne_ (Rf.size_T s))
    (I.Prosa_Implementation_Refinements_Refinements_size_T IN I.Prosa_Implementation_Refinements_Refinements_zero_N
       I.Prosa_Implementation_Refinements_Refinements_one_N I.Prosa_Implementation_Refinements_Refinements_add_N C (lex idr s)).
Proof.
  induction s as [|x s IH]; cbn [Rf.size_T lex].
  - exact (rf_refl _).
  - exact (rf_trans _ _ _ (rf_N_add_ex (Npos xH) _) (rf_congr (INadd (INpos IxH)) _ _ IH)).
Qed.

(** [refine_foldr], [refine_uncond_foldr], [refine_foldr_max] *)
Lemma rf_fold_add_N_ex {T2 : Type} (F' : T2 -> N) (F'L : T2 -> IN) (HF : forall x, Lean.eq (Ne_ (F' x)) (F'L x)) (ys : seq T2) :
  Lean.eq (Ne_ (foldr N.add N0 (map F' ys)))
    (I.List_foldr_inst3 IN IN INadd IN0 (I.List_map_inst3 T2 IN F'L (lex idr ys))).
Proof.
  refine (rf_trans _ _ _ (rf_foldr_ex Ne_ Ne_ N.add INadd rf_N_add_ex N0 _) _).
  exact (rf_congr (I.List_foldr_inst3 IN IN INadd IN0) _ _ (rf_map_ex idr Ne_ F' F'L HF ys)).
Qed.

Lemma rf_fold_max_N_ex {T2 : Type} (F' : T2 -> N) (F'L : T2 -> IN) (HF : forall x, Lean.eq (Ne_ (F' x)) (F'L x)) (ys : seq T2) :
  Lean.eq (Ne_ (foldr Rf.maxn_T N0 (map F' ys)))
    (I.List_foldr_inst3 IN IN
       (I.Prosa_Implementation_Refinements_Refinements_maxn_T IN I.Prosa_Implementation_Refinements_Refinements_lt_N)
       IN0 (I.List_map_inst3 T2 IN F'L (lex idr ys))).
Proof.
  refine (rf_trans _ _ _ (rf_foldr_ex Ne_ Ne_ Rf.maxn_T _ rf_maxn_T_N_ex N0 _) _).
  exact (rf_congr (I.List_foldr_inst3 IN IN _ IN0) _ _ (rf_map_ex idr Ne_ F' F'L HF ys)).
Qed.