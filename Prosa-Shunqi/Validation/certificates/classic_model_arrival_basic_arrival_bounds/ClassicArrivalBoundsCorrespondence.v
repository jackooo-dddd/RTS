From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq path bigop div.
From prosa Require Import classic.model.time classic.util.div_mod classic.model.arrival.basic.arrival_sequence
  classic.model.arrival.basic.task_arrival classic.model.arrival.basic.arrival_bounds.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedClassicArrivalBounds.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence ClassicArrivalBoundsNatSub ClassicArrivalBoundsOps
  ClassicArrivalBoundsBase ClassicArrivalBoundsList.

Module I := ImportedClassicArrivalBounds.
Local Open Scope nat_scope.

(** Certificates for [classic/model/arrival/basic/arrival_bounds.v] (ProsaBuddy classic, commit f692cb7).

    Inputs: the job and task types are [eqType]s, identified, with the Lean
    [DecidableEq] instances given by the eqTypes' decision procedures
    ([ct_decidable_eq]); [job_task] and jobs identified; times by [SubNatRel];
    job/task parameters [X -> time] pointwise through [SubNatRel]; job sequences
    elementwise; arrival sequences pointwise on related times; all with two-way
    totals.

    Computation: the arrival-sequence, [TaskArrival] and sorting relations are
    those of the accepted classic task_arrival certificate, re-stated for this
    export (the stable-sort characterisation of [List.mergeSort] through the
    exported kernel-checked [ClassicArrivalBoundsInterface.mergeSort_isChain] /
    [mergeSort_filter_class], and the uniqueness of a sorted sequence with given
    key-class filters, proved here); [div_ceil] and the Nat operations through the
    accepted operation-level bridge [certificates/common/DivModCorrespondence.v],
    re-bound to this export ([ClassicArrivalBoundsOps], bound by the exported
    [DivModInterface] equations as for the accepted classic div_mod certificate).

    Statements: the source side is the exact elaborated type of the pinned lemma
    (via [type of]; the source proof is not used).  For the lemmas whose Rocq
    and Lean binder lists put [task_period : Task -> time] before the job type,
    the job type is fixed as an [eqType] with its canonical Lean instance and
    [task_period] stays universally quantified on both sides. *)

Ltac type_of_term t := let T := type of t in exact T.
Notation cid := (fun z => z).

(* ------------------------------------------------------------------ *)
(** * Generic covers and helpers *)

Lemma cta_forall_cover (A B : Type) (Rel : A -> B -> SProp) (toB : A -> B) (toA : B -> A)
    (HB : forall a, Rel a (toB a)) (HA : forall b, Rel (toA b) b) (PR : A -> Prop) (PL : B -> SProp) :
  (forall a b, Rel a b -> PropSPropRel (PR a) (PL b)) -> PropSPropRel (forall a, PR a) (forall b, PL b).
Proof.
  intro H. apply prop_sprop_rel_intro.
  - intros HR b. exact (prop_to_sprop _ _ (H _ _ (HA b)) (HR _)).
  - intro HL. apply strictly_inhabits. intro a. exact (sprop_to_prop _ _ (H _ _ (HB a)) (HL _)).
Qed.

Lemma cta_false_rel : PropSPropRel Logic.False I.False.
Proof.
  apply prop_sprop_rel_intro.
  - exact ct_coq_false_to_target.
  - exact ct_target_false_to_strict.
Qed.

Lemma cta_ne (T : Type) (x y : T) : PropSPropRel (x <> y) (I.Ne T x y).
Proof. exact (ct_imp _ _ _ _ (ct_eq_rel T x y) cta_false_rel). Qed.

Lemma cta_mem (T : eqType) x s sL : ClListRel cid s sL ->
  PropSPropRel (x \in s) (I.Membership_mem T (I.List T) (I.List_instMembership T) sL x).
Proof. exact (cl_mem_rel_list T T cid cid (fun _ => Logic.eq_refl _) x s sL). Qed.

Lemma cta_uniq (T : eqType) s sL : ClListRel cid s sL -> PropSPropRel (uniq s) (I.List_Nodup T sL).
Proof. exact (cl_uniq_rel_list T T cid cid (fun _ => Logic.eq_refl _) (fun _ => Logic.eq_refl _) s sL). Qed.

Lemma cta_unmap_rel (T : Type) (l : I.List T) : ClListRel cid (cl_unmap cid l) l.
Proof. apply: coq_eq_to_imported_eq. exact (cl_map_unmap cid cid (fun _ => Logic.eq_refl _) l). Qed.

Lemma cta_cl_map_inj (T : Type) (s1 s2 : seq T) : Logic.eq (cl_map cid s1) (cl_map cid s2) -> Logic.eq s1 s2.
Proof.
  intro E. rewrite -(cl_unmap_map cid cid (fun _ => Logic.eq_refl _) s1) -(cl_unmap_map cid cid (fun _ => Logic.eq_refl _) s2).
  by rewrite E.
Qed.

Lemma cta_getD (T : Type) (s : seq T) sL (Hs : ClListRel cid s sL) (x0 : T) nR nL (Hn : SubNatRel nR nL) :
  Logic.eq (I.List_getD T sL nL x0) (nth x0 s nR).
Proof.
  rewrite (cl_list_logic _ _ _ Hs) (cl_nat_logic _ _ Hn). exact (Logic.eq_sym (cl_nth cid x0 s nR)).
Qed.

Lemma cta_succ_rel nR nL : SubNatRel nR nL ->
  SubNatRel nR.+1 (I.HAdd_hAdd_inst7 Lean.Nat Lean.Nat Lean.Nat (I.instHAdd_inst1 Lean.Nat I.instAddNat) nL
                     (I.OfNat_ofNat_inst1 Lean.Nat 1 (I.instOfNatNat 1))).
Proof. intro Hn. exact (sub_imported_eq_congr Lean.Nat_succ _ _ Hn). Qed.

Lemma cta_pred_rel nR nL : SubNatRel nR nL ->
  SubNatRel nR.-1 (ct_sub nL (I.OfNat_ofNat_inst1 Lean.Nat 1 (I.instOfNatNat 1))).
Proof.
  intro Hn. apply: coq_eq_to_imported_eq. rewrite -subn1.
  exact (imported_eq_to_coq_eq _ _ (ct_sub_rel _ _ _ _ Hn (sub_nat_rel_canonical 1))).
Qed.

(* ------------------------------------------------------------------ *)
(** * Big concatenation over a half-open interval (as in the accepted arrival_sequence certificate) *)

Fixpoint cta_natl (s : seq nat) : I.List_inst1 Lean.Nat :=
  match s with [::] => I.List_nil_inst1 _ | x :: s' => I.List_cons_inst1 _ (sub_nat_to_imported x) (cta_natl s') end.

Definition cta_one : Lean.Nat := I.OfNat_ofNat_inst1 Lean.Nat 1 (I.instOfNatNat 1).

Lemma cta_iota_range : forall n s,
  Logic.eq (I.List_range' (sub_nat_to_imported s) (sub_nat_to_imported n) cta_one) (cta_natl (iota s n)).
Proof.
  elim => [|n IH] s; first reflexivity.
  change (Logic.eq (I.List_cons_inst1 _ (sub_nat_to_imported s)
      (I.List_range' (sub_nat_to_imported (S s)) (sub_nat_to_imported n) cta_one))
    (I.List_cons_inst1 _ (sub_nat_to_imported s) (cta_natl (iota (S s) n)))).
  by rewrite IH.
Qed.

Lemma cta_map_natl {B : Type} (f : Lean.Nat -> B) : forall s,
  Logic.eq (I.List_map_inst1 Lean.Nat B f (cta_natl s)) (cl_map (fun k => f (sub_nat_to_imported k)) s).
Proof.
  elim => [|k s IH] //=.
  change (Logic.eq (I.List_cons B (f (sub_nat_to_imported k)) (I.List_map_inst1 Lean.Nat B f (cta_natl s)))
                   (I.List_cons B (f (sub_nat_to_imported k)) (cl_map (fun k => f (sub_nat_to_imported k)) s))).
  by rewrite IH.
Qed.

Lemma cta_cl_map_comp {A B C : Type} (f : A -> B) (g : B -> C) : forall s : seq A,
  Logic.eq (cl_map (fun x => g (f x)) s) (cl_map g (map f s)).
Proof. elim => [|x s IH] //=. by rewrite IH. Qed.

Lemma cta_cl_map_ext {A B : Type} (f g : A -> B) (H : forall x, Logic.eq (f x) (g x)) : forall s : seq A,
  Logic.eq (cl_map f s) (cl_map g s).
Proof. elim => [|x s IH] //=. by rewrite H IH. Qed.

Lemma cta_flatten {A : Type} : forall L : seq (seq A),
  Logic.eq (I.List_flatten A (cl_map (cl_map cid) L)) (cl_map cid (flatten L)).
Proof.
  elim => [|s L IH] //=.
  change (Logic.eq (I.List_append A (cl_map cid s) (I.List_flatten A (cl_map (cl_map cid) L))) (cl_map cid (s ++ flatten L))).
  rewrite IH cl_cat. reflexivity.
Qed.

Lemma cta_big_seq {A : Type} (F : nat -> seq A) : forall s : seq nat,
  Logic.eq (\big[cat/[::]]_(i <- s) F i) (flatten (map F s)).
Proof. elim => [|x s IH]; first by rewrite big_nil. by rewrite big_cons IH. Qed.

Definition CtaFamRel (A : Type) (fR : nat -> seq A) (fL : Lean.Nat -> I.List A) : SProp :=
  forall nR nL, SubNatRel nR nL -> ClListRel cid (fR nR) (fL nL).

Lemma cta_bigcat_rel (A : Type) fR fL (Hf : CtaFamRel A fR fL) mR mL nR nL :
  SubNatRel mR mL -> SubNatRel nR nL ->
  ClListRel cid (\big[cat/[::]]_(mR <= t < nR) fR t) (I.Prosa_Util_Notation_bigCat A mL nL fL).
Proof.
  intros Hm Hn. have E1 := cl_nat_logic _ _ Hm. have E2 := cl_nat_logic _ _ Hn. subst mL nL.
  apply: coq_eq_to_imported_eq. apply: Logic.eq_sym.
  rewrite (imported_eq_to_coq_eq _ _ (I.Prosa_Validation_ClassicArrivalBoundsInterface_bigCat_range'
             A (sub_nat_to_imported mR) (sub_nat_to_imported nR) fL)).
  have Hd : Logic.eq (I.HSub_hSub_inst7 Lean.Nat Lean.Nat Lean.Nat (I.instHSub_inst1 Lean.Nat I.instSubNat)
                       (sub_nat_to_imported nR) (sub_nat_to_imported mR)) (sub_nat_to_imported (nR - mR)) :=
    ct_sub_canonical nR mR.
  rewrite Hd.
  change (I.OfNat_ofNat_inst1 Lean.Nat 0 (I.instOfNatNat 0)) with (sub_nat_to_imported 0).
  rewrite (cta_iota_range (nR - mR) 0) cta_map_natl. cbv beta.
  have Hpt : forall k, Logic.eq
      (fL (I.HAdd_hAdd_inst7 Lean.Nat Lean.Nat Lean.Nat (I.instHAdd_inst1 Lean.Nat I.instAddNat)
             (sub_nat_to_imported mR) (sub_nat_to_imported k)))
      (cl_map cid (fR (mR + k))).
  { intro k. exact (cl_list_logic _ _ _ (Hf _ _ (sub_add_correspondence mR _ k _
       (sub_nat_rel_canonical mR) (sub_nat_rel_canonical k)))). }
  rewrite (cta_cl_map_ext _ _ Hpt) (cta_cl_map_comp (fun k => fR (mR + k)) (cl_map cid)) cta_flatten.
  have Hi : Logic.eq (iota mR (nR - mR)) (map (addn mR) (iota 0 (nR - mR))) by rewrite -iotaDl addn0.
  rewrite cta_big_seq /index_iota Hi -map_comp.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(** * Stable sorting: MathComp [sort] against the core [List.mergeSort] *)

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
          end (I.Prosa_Validation_ClassicArrivalBoundsInterface_mergeSort_isChain T fL sL))).
  have Fu : forall x, filter (fun y => f y == f x) u = filter (fun y => f y == f x) s.
  { intro x. apply: cta_cl_map_inj.
    have Hp : forall y, CtBoolRel (f y == f x) (clsL x y) := fun y => ct_decide_eq_nat _ _ _ _ (Hf y) (Hf x).
    refine (Logic.eq_trans (cl_filter cid (fun y => f y == f x) (clsL x) Hp u)
              (Logic.eq_trans _ (Logic.eq_sym (cl_filter cid (fun y => f y == f x) (clsL x) Hp s)))).
    refine (Logic.eq_trans (f_equal (I.List_filter T (clsL x)) (Logic.eq_sym (cl_list_logic _ _ _ Hu)))
              (Logic.eq_trans _ (f_equal (I.List_filter T (clsL x)) (cl_list_logic _ _ _ Hs)))).
    exact (imported_eq_to_coq_eq _ _ (I.Prosa_Validation_ClassicArrivalBoundsInterface_mergeSort_filter_class T fL x sL)). }
  have E := cta_sort_unique T f u s Su Fu.
  apply: coq_eq_to_imported_eq. rewrite -E. exact (Logic.eq_sym (cl_list_logic _ _ _ Hu)).
Qed.
End Sort.

(* ------------------------------------------------------------------ *)
(** * Arrival sequences and parameters *)

Section Rel.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).
Notation LArr := (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrival_sequence Job dJ).

Definition CtaArrRel (aR : ArrivalSequence.arrival_sequence Job) (aL : LArr) : SProp :=
  forall tR tL, SubNatRel tR tL -> ClListRel cid (aR tR) (aL tL).

Definition cta_arr_to_target (aR : ArrivalSequence.arrival_sequence Job) : LArr :=
  fun tL => cl_map cid (aR (sub_nat_to_rocq tL)).

Definition cta_arr_to_source (aL : LArr) : ArrivalSequence.arrival_sequence Job :=
  fun tR => cl_unmap cid (aL (sub_nat_to_imported tR)).

Lemma cta_arr_canonical aR : CtaArrRel aR (cta_arr_to_target aR).
Proof.
  intros tR tL Ht. have E := cl_nat_logic _ _ Ht. subst tL.
  apply: coq_eq_to_imported_eq. rewrite /cta_arr_to_target sub_nat_rocq_roundtrip. reflexivity.
Qed.

Lemma cta_arr_surjective aL : CtaArrRel (cta_arr_to_source aL) aL.
Proof.
  intros tR tL Ht. have E := cl_nat_logic _ _ Ht. subst tL.
  apply: coq_eq_to_imported_eq. exact (cl_map_unmap cid cid (fun _ => Logic.eq_refl _) _).
Qed.

Lemma cta_forall_arr (PR : ArrivalSequence.arrival_sequence Job -> Prop) (PL : LArr -> SProp) :
  (forall aR aL, CtaArrRel aR aL -> PropSPropRel (PR aR) (PL aL)) -> PropSPropRel (forall a, PR a) (forall a, PL a).
Proof. exact (cta_forall_cover _ _ CtaArrRel cta_arr_to_target cta_arr_to_source cta_arr_canonical cta_arr_surjective PR PL). Qed.
End Rel.

Definition CtaParRel (T : Type) (pR : T -> nat) (pL : T -> Lean.Nat) : SProp := forall x, SubNatRel (pR x) (pL x).

Lemma cta_forall_par (T : Type) (PR : (T -> nat) -> Prop) (PL : (T -> Lean.Nat) -> SProp) :
  (forall pR pL, CtaParRel T pR pL -> PropSPropRel (PR pR) (PL pL)) -> PropSPropRel (forall p, PR p) (forall p, PL p).
Proof.
  exact (cta_forall_cover _ _ (CtaParRel T) (fun pR j => sub_nat_to_imported (pR j)) (fun pL j => sub_nat_to_rocq (pL j))
           (fun pR j => sub_nat_rel_canonical (pR j)) (fun pL j => sub_nat_rel_surjective (pL j)) PR PL).
Qed.

(** The imported [ArrivalSequence] definitions this file's statements mention, related on related inputs. *)
Section ArrivalDefs.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).

Lemma cta_jobs_arrived_between aR aL (Ha : CtaArrRel Job aR aL) t1R t1L t2R t2L
    (H1 : SubNatRel t1R t1L) (H2 : SubNatRel t2R t2L) :
  ClListRel cid (ArrivalSequence.jobs_arrived_between aR t1R t2R)
    (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_jobs_arrived_between Job dJ aL t1L t2L).
Proof. exact (cta_bigcat_rel Job (fun t => aR t) (fun t => aL t) Ha t1R t1L t2R t2L H1 H2). Qed.

Lemma cta_arrives_in aR aL (Ha : CtaArrRel Job aR aL) j :
  PropSPropRel (ArrivalSequence.arrives_in aR j)
    (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrives_in Job dJ aL j).
Proof. apply: ct_exists_nat => tR tL Ht. exact (cta_mem Job j _ _ (Ha tR tL Ht)). Qed.

Lemma cta_consistent pR pL (Hp : CtaParRel Job pR pL) aR aL (Ha : CtaArrRel Job aR aL) :
  PropSPropRel (ArrivalSequence.arrival_times_are_consistent pR aR)
    (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrival_times_are_consistent Job dJ pL aL).
Proof.
  apply: ct_forall_identity => j. apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (ct_bool_truth _ _ (ct_decide_bool _ _ _ (cta_mem Job j _ _ (Ha tR tL Ht)))).
  exact (sub_nat_eq_correspondence _ _ _ _ (Hp j) Ht).
Qed.

Lemma cta_is_a_set aR aL (Ha : CtaArrRel Job aR aL) :
  PropSPropRel (ArrivalSequence.arrival_sequence_is_a_set aR)
    (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrival_sequence_is_a_set Job dJ aL).
Proof. apply: ct_forall_nat => tR tL Ht. exact (cta_uniq Job _ _ (Ha tR tL Ht)). Qed.
End ArrivalDefs.

(* ------------------------------------------------------------------ *)
(** * Definitions *)

Section Defs.
Variables (Task Job : eqType).
Notation dT := (ct_decidable_eq Task).
Notation dJ := (ct_decidable_eq Job).

Lemma cab_TaskArrival_sporadic_task_model_correspondence tpR tpL (Htp : CtaParRel Task tpR tpL)
    jaR jaL (Hja : CtaParRel Job jaR jaL) (job_task : Job -> Task) aR aL (Ha : CtaArrRel Job aR aL) :
  PropSPropRel (TaskArrival.sporadic_task_model tpR jaR job_task aR)
    (I.Prosa_Classic_Model_Arrival_Basic_TaskArrival_TaskArrival_sporadic_task_model Task dT tpL Job dJ jaL job_task aL).
Proof.
  apply: ct_forall_identity => j. apply: ct_forall_identity => j'.
  apply: ct_imp; first exact (cta_ne Job j j').
  apply: ct_imp; first exact (cta_arrives_in Job aR aL Ha j).
  apply: ct_imp; first exact (cta_arrives_in Job aR aL Ha j').
  apply: ct_imp; first exact (ct_eq_rel Task (job_task j) (job_task j')).
  apply: ct_imp; first exact (sub_nat_le_correspondence _ _ _ _ (Hja j) (Hja j')).
  exact (sub_nat_le_correspondence _ _ _ _ (sub_add_correspondence _ _ _ _ (Hja j) (Htp (job_task j))) (Hja j')).
Qed.

Lemma cab_TaskArrival_is_job_of_task_correspondence (job_task : Job -> Task) tsk j :
  CtBoolRel (TaskArrival.is_job_of_task job_task tsk j)
    (I.Prosa_Classic_Model_Arrival_Basic_TaskArrival_TaskArrival_is_job_of_task Task Job dT dJ job_task tsk j).
Proof. exact (ct_decide_eq Task (job_task j) tsk). Qed.

Lemma cab_TaskArrival_arrivals_of_task_between_correspondence (job_task : Job -> Task) aR aL (Ha : CtaArrRel Job aR aL) tsk
    t1R t1L t2R t2L (H1 : SubNatRel t1R t1L) (H2 : SubNatRel t2R t2L) :
  ClListRel cid (TaskArrival.arrivals_of_task_between job_task aR tsk t1R t2R)
    (I.Prosa_Classic_Model_Arrival_Basic_TaskArrival_TaskArrival_arrivals_of_task_between Task Job dT dJ job_task aL tsk t1L t2L).
Proof.
  apply: coq_eq_to_imported_eq.
  refine (Logic.eq_trans (cl_filter cid _ (I.Prosa_Classic_Model_Arrival_Basic_TaskArrival_TaskArrival_is_job_of_task Task Job dT dJ job_task tsk)
                            (cab_TaskArrival_is_job_of_task_correspondence job_task tsk) _) _).
  exact (f_equal (I.List_filter Job (I.Prosa_Classic_Model_Arrival_Basic_TaskArrival_TaskArrival_is_job_of_task Task Job dT dJ job_task tsk))
           (Logic.eq_sym (cl_list_logic _ _ _ (cta_jobs_arrived_between Job aR aL Ha _ _ _ _ H1 H2)))).
Qed.


Lemma cab_TaskArrival_num_arrivals_of_task_correspondence (job_task : Job -> Task) aR aL (Ha : CtaArrRel Job aR aL) tsk
    t1R t1L t2R t2L (H1 : SubNatRel t1R t1L) (H2 : SubNatRel t2R t2L) :
  SubNatRel (TaskArrival.num_arrivals_of_task job_task aR tsk t1R t2R)
    (I.Prosa_Classic_Model_Arrival_Basic_TaskArrival_TaskArrival_num_arrivals_of_task Task Job dT dJ job_task aL tsk t1L t2L).
Proof.
  have H := cab_TaskArrival_arrivals_of_task_between_correspondence job_task aR aL Ha tsk _ _ _ _ H1 H2.
  change (SubNatRel (size (TaskArrival.arrivals_of_task_between job_task aR tsk t1R t2R))
    (I.List_length Job (I.Prosa_Classic_Model_Arrival_Basic_TaskArrival_TaskArrival_arrivals_of_task_between Task Job dT dJ job_task aL tsk t1L t2L))).
  exact (match H in Lean.eq _ z
               return SubNatRel (size (TaskArrival.arrivals_of_task_between job_task aR tsk t1R t2R)) (I.List_length Job z) with
         | Lean.eq_refl => cl_size cid _
         end).
Qed.
End Defs.

(** The sorted arrivals of [tsk] in [[t1, t2)] and their elements. *)
Section Sorted.
Variables (Task Job : eqType).
Notation dT := (ct_decidable_eq Task).
Notation dJ := (ct_decidable_eq Job).

Lemma cta_sorted_rel jaR jaL (Hja : CtaParRel Job jaR jaL) (job_task : Job -> Task) aR aL (Ha : CtaArrRel Job aR aL) tsk
    t1R t1L t2R t2L (H1 : SubNatRel t1R t1L) (H2 : SubNatRel t2R t2L) :
  ClListRel cid (sort (fun j j' => jaR j <= jaR j') (TaskArrival.arrivals_of_task_between job_task aR tsk t1R t2R))
    (I.List_mergeSort Job (I.Prosa_Classic_Model_Arrival_Basic_TaskArrival_TaskArrival_arrivals_of_task_between Task Job dT dJ job_task aL tsk t1L t2L)
       (fun j j' => I.Decidable_decide (I.LE_le_inst1 Lean.Nat I.instLENat (jaL j) (jaL j')) (I.Nat_decLe (jaL j) (jaL j')))).
Proof. exact (cta_sort_rel Job jaR jaL Hja _ _ (cab_TaskArrival_arrivals_of_task_between_correspondence Task Job job_task aR aL Ha tsk _ _ _ _ H1 H2)). Qed.
End Sorted.


(* ------------------------------------------------------------------ *)
(** * Statements *)

Notation num := cab_TaskArrival_num_arrivals_of_task_correspondence.
Notation cab_sorted := cta_sorted_rel.

Lemma cab_div_ceil_rel xR xL yR yL : SubNatRel xR xL -> SubNatRel yR yL ->
  SubNatRel (div_mod.div_ceil xR yR) (I.Prosa_Classic_Util_DivMod_div_ceil xL yL).
Proof. exact (dm_div_ceil_correspondence xR xL yR yL). Qed.

Lemma cab_bound (Task : Type) tpR tpL (Htp : CtaParRel Task tpR tpL) (tsk : Task) t1R t1L t2R t2L (H1 : SubNatRel t1R t1L) (H2 : SubNatRel t2R t2L) :
  SubNatRel (div_mod.div_ceil (t2R - t1R) (tpR tsk))
    (I.Prosa_Classic_Util_DivMod_div_ceil
       (I.HSub_hSub_inst7 Lean.Nat Lean.Nat Lean.Nat (I.instHSub_inst1 Lean.Nat I.instSubNat) t2L t1L) (tpL tsk)).
Proof. exact (cab_div_ceil_rel _ _ _ _ (dm_sub_correspondence _ _ _ _ H2 H1) (Htp tsk)). Qed.

(** The common hypotheses of the sporadic-task lemmas. *)
Lemma cab_hyps (Task Job : eqType) tpR tpL (Htp : CtaParRel Task tpR tpL) jaR jaL (Hja : CtaParRel Job jaR jaL)
    (job_task : Job -> Task) aR aL (Ha : CtaArrRel Job aR aL) (PR : Prop) (PL : SProp) :
  PropSPropRel PR PL ->
  PropSPropRel (ArrivalSequence.arrival_times_are_consistent jaR aR ->
                ArrivalSequence.arrival_sequence_is_a_set aR ->
                TaskArrival.sporadic_task_model tpR jaR job_task aR -> PR)
    (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrival_times_are_consistent Job (ct_decidable_eq Job) jaL aL ->
     I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrival_sequence_is_a_set Job (ct_decidable_eq Job) aL ->
     I.Prosa_Classic_Model_Arrival_Basic_TaskArrival_TaskArrival_sporadic_task_model Task (ct_decidable_eq Task) tpL Job (ct_decidable_eq Job) jaL job_task aL -> PL).
Proof.
  intro H.
  apply: ct_imp; first exact (cta_consistent Job jaR jaL Hja aR aL Ha).
  apply: ct_imp; first exact (cta_is_a_set Job aR aL Ha).
  apply: ct_imp; first exact (cab_TaskArrival_sporadic_task_model_correspondence Task Job tpR tpL Htp jaR jaL Hja job_task aR aL Ha).
  exact H.
Qed.

Definition src_sporadic_arrival_bound_no_jobs (Task Job : eqType) : Prop :=
  forall task_period : Task -> Time.time,
    ltac:(type_of_term (@ArrivalBounds.sporadic_arrival_bound_no_jobs Task task_period Job)).
Definition tgt_sporadic_arrival_bound_no_jobs (Task Job : eqType) : SProp :=
  forall task_period : Task -> Lean.Nat,
    ltac:(type_of_term (I.Prosa_Classic_Model_Arrival_Basic_ArrivalBounds_ArrivalBounds_sporadic_arrival_bound_no_jobs
                          Task (ct_decidable_eq Task) task_period Job (ct_decidable_eq Job))).
Theorem ArrivalBounds_sporadic_arrival_bound_no_jobs_correspondence (Task Job : eqType) :
  PropSPropRel (src_sporadic_arrival_bound_no_jobs Task Job) (tgt_sporadic_arrival_bound_no_jobs Task Job).
Proof.
  unfold src_sporadic_arrival_bound_no_jobs, tgt_sporadic_arrival_bound_no_jobs.
  apply: cta_forall_par => tpR tpL Htp. apply: ct_forall_identity => job_task. apply: cta_forall_arr => aR aL Ha.
  apply: ct_forall_nat => t1R t1L H1. apply: ct_forall_nat => t2R t2L H2. apply: ct_forall_identity => tsk.
  have Hn := num Task Job job_task aR aL Ha tsk _ _ _ _ H1 H2.
  apply: ct_imp; first exact (sub_nat_eq_correspondence _ _ _ _ Hn (sub_nat_rel_canonical 0)).
  exact (sub_nat_le_correspondence _ _ _ _ Hn (cab_bound Task tpR tpL Htp tsk _ _ _ _ H1 H2)).
Qed.

Definition src_sporadic_arrival_bound_more_than_one_point (Task Job : eqType) : Prop :=
  ltac:(type_of_term (@ArrivalBounds.sporadic_arrival_bound_more_than_one_point Task Job)).
Definition tgt_sporadic_arrival_bound_more_than_one_point (Task Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Model_Arrival_Basic_ArrivalBounds_ArrivalBounds_sporadic_arrival_bound_more_than_one_point
                        Task Job (ct_decidable_eq Task) (ct_decidable_eq Job))).
Theorem ArrivalBounds_sporadic_arrival_bound_more_than_one_point_correspondence (Task Job : eqType) :
  PropSPropRel (src_sporadic_arrival_bound_more_than_one_point Task Job) (tgt_sporadic_arrival_bound_more_than_one_point Task Job).
Proof.
  unfold src_sporadic_arrival_bound_more_than_one_point, tgt_sporadic_arrival_bound_more_than_one_point.
  apply: cta_forall_par => jaR jaL Hja. apply: ct_forall_identity => job_task. apply: cta_forall_arr => aR aL Ha.
  apply: ct_imp; first exact (cta_consistent Job jaR jaL Hja aR aL Ha).
  apply: ct_forall_nat => t1R t1L H1. apply: ct_forall_nat => t2R t2L H2. apply: ct_forall_identity => tsk.
  apply: ct_imp; first exact (sub_nat_lt_correspondence _ _ _ _ (sub_nat_rel_canonical 0) (num Task Job job_task aR aL Ha tsk _ _ _ _ H1 H2)).
  exact (sub_nat_lt_correspondence _ _ _ _ H1 H2).
Qed.

Definition src_sporadic_arrival_bound_one_job (Task Job : eqType) : Prop :=
  forall task_period : Task -> Time.time,
    ltac:(type_of_term (@ArrivalBounds.sporadic_arrival_bound_one_job Task task_period Job)).
Definition tgt_sporadic_arrival_bound_one_job (Task Job : eqType) : SProp :=
  forall task_period : Task -> Lean.Nat,
    ltac:(type_of_term (I.Prosa_Classic_Model_Arrival_Basic_ArrivalBounds_ArrivalBounds_sporadic_arrival_bound_one_job
                          Task (ct_decidable_eq Task) task_period Job (ct_decidable_eq Job))).
Theorem ArrivalBounds_sporadic_arrival_bound_one_job_correspondence (Task Job : eqType) :
  PropSPropRel (src_sporadic_arrival_bound_one_job Task Job) (tgt_sporadic_arrival_bound_one_job Task Job).
Proof.
  unfold src_sporadic_arrival_bound_one_job, tgt_sporadic_arrival_bound_one_job.
  apply: cta_forall_par => tpR tpL Htp. apply: cta_forall_par => jaR jaL Hja. apply: ct_forall_identity => job_task.
  apply: cta_forall_arr => aR aL Ha.
  apply: ct_imp; first exact (cta_consistent Job jaR jaL Hja aR aL Ha).
  apply: ct_forall_nat => t1R t1L H1. apply: ct_forall_nat => t2R t2L H2. apply: ct_forall_identity => tsk.
  have Hn := num Task Job job_task aR aL Ha tsk _ _ _ _ H1 H2.
  apply: ct_imp; first exact (sub_nat_lt_correspondence _ _ _ _ (sub_nat_rel_canonical 0) (Htp tsk)).
  apply: ct_imp; first exact (sub_nat_eq_correspondence _ _ _ _ Hn (sub_nat_rel_canonical 1)).
  exact (sub_nat_le_correspondence _ _ _ _ Hn (cab_bound Task tpR tpL Htp tsk _ _ _ _ H1 H2)).
Qed.

Definition src_sporadic_arrival_bound_properties_of_nth (Task Job : eqType) : Prop :=
  ltac:(type_of_term (@ArrivalBounds.sporadic_arrival_bound_properties_of_nth Task Job)).
Definition tgt_sporadic_arrival_bound_properties_of_nth (Task Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Model_Arrival_Basic_ArrivalBounds_ArrivalBounds_sporadic_arrival_bound_properties_of_nth
                        Task Job (ct_decidable_eq Task) (ct_decidable_eq Job))).
Theorem ArrivalBounds_sporadic_arrival_bound_properties_of_nth_correspondence (Task Job : eqType) :
  PropSPropRel (src_sporadic_arrival_bound_properties_of_nth Task Job) (tgt_sporadic_arrival_bound_properties_of_nth Task Job).
Proof.
  unfold src_sporadic_arrival_bound_properties_of_nth, tgt_sporadic_arrival_bound_properties_of_nth.
  apply: cta_forall_par => jaR jaL Hja. apply: ct_forall_identity => job_task. apply: cta_forall_arr => aR aL Ha.
  apply: ct_imp; first exact (cta_consistent Job jaR jaL Hja aR aL Ha).
  apply: ct_forall_nat => t1R t1L H1. apply: ct_forall_nat => t2R t2L H2. apply: ct_forall_identity => tsk.
  apply: ct_forall_identity => elem. apply: ct_forall_nat => iR iL Hi.
  have Hn := num Task Job job_task aR aL Ha tsk _ _ _ _ H1 H2.
  apply: ct_imp; first exact (sub_nat_lt_correspondence _ _ _ _ Hi Hn).
  rewrite (cta_getD _ _ _ (cab_sorted Task Job jaR jaL Hja job_task aR aL Ha tsk _ _ _ _ H1 H2) elem _ _ Hi).
  set x := nth elem _ iR.
  apply: ct_and; first exact (ct_bool_truth _ _ (ct_bool_and _ _ _ _ (ct_decide_le _ _ _ _ H1 (Hja x)) (ct_decide_lt _ _ _ _ (Hja x) H2))).
  apply: ct_and; first exact (ct_eq_rel Task (job_task x) tsk).
  exact (cta_arrives_in Job aR aL Ha x).
Qed.

Definition src_sporadic_arrival_bound_distance_between_first_and_last (Task Job : eqType) : Prop :=
  forall task_period : Task -> Time.time,
    ltac:(type_of_term (@ArrivalBounds.sporadic_arrival_bound_distance_between_first_and_last Task task_period Job)).
Definition tgt_sporadic_arrival_bound_distance_between_first_and_last (Task Job : eqType) : SProp :=
  forall task_period : Task -> Lean.Nat,
    ltac:(type_of_term (I.Prosa_Classic_Model_Arrival_Basic_ArrivalBounds_ArrivalBounds_sporadic_arrival_bound_distance_between_first_and_last
                          Task (ct_decidable_eq Task) task_period Job (ct_decidable_eq Job))).
Theorem ArrivalBounds_sporadic_arrival_bound_distance_between_first_and_last_correspondence (Task Job : eqType) :
  PropSPropRel (src_sporadic_arrival_bound_distance_between_first_and_last Task Job)
    (tgt_sporadic_arrival_bound_distance_between_first_and_last Task Job).
Proof.
  unfold src_sporadic_arrival_bound_distance_between_first_and_last, tgt_sporadic_arrival_bound_distance_between_first_and_last.
  apply: cta_forall_par => tpR tpL Htp. apply: cta_forall_par => jaR jaL Hja. apply: ct_forall_identity => job_task.
  apply: cta_forall_arr => aR aL Ha. apply: (cab_hyps Task Job tpR tpL Htp jaR jaL Hja job_task aR aL Ha).
  apply: ct_forall_nat => t1R t1L H1. apply: ct_forall_nat => t2R t2L H2. apply: ct_forall_identity => tsk.
  have Hn := num Task Job job_task aR aL Ha tsk _ _ _ _ H1 H2.
  apply: ct_imp; first exact (sub_nat_lt_correspondence _ _ _ _ (sub_nat_rel_canonical 1) Hn).
  apply: ct_forall_identity => elem.
  have Hs := cab_sorted Task Job jaR jaL Hja job_task aR aL Ha tsk _ _ _ _ H1 H2.
  have Hm1 := ct_sub_rel _ _ _ _ Hn (sub_nat_rel_canonical 1).
  rewrite (cta_getD _ _ _ Hs elem _ _ (sub_nat_rel_canonical 0)) (cta_getD _ _ _ Hs elem _ _ (cta_pred_rel _ _ Hn)).
  exact (sub_nat_le_correspondence _ _ _ _
           (sub_add_correspondence _ _ _ _ (Hja _) (sub_mul_correspondence _ _ _ _ Hm1 (Htp tsk))) (Hja _)).
Qed.

Definition src_sporadic_arrival_bound_last_job_too_far (Task Job : eqType) : Prop :=
  forall task_period : Task -> Time.time,
    ltac:(type_of_term (@ArrivalBounds.sporadic_arrival_bound_last_job_too_far Task task_period Job)).
Definition tgt_sporadic_arrival_bound_last_job_too_far (Task Job : eqType) : SProp :=
  forall task_period : Task -> Lean.Nat,
    ltac:(type_of_term (I.Prosa_Classic_Model_Arrival_Basic_ArrivalBounds_ArrivalBounds_sporadic_arrival_bound_last_job_too_far
                          Task (ct_decidable_eq Task) task_period Job (ct_decidable_eq Job))).
Theorem ArrivalBounds_sporadic_arrival_bound_last_job_too_far_correspondence (Task Job : eqType) :
  PropSPropRel (src_sporadic_arrival_bound_last_job_too_far Task Job) (tgt_sporadic_arrival_bound_last_job_too_far Task Job).
Proof.
  unfold src_sporadic_arrival_bound_last_job_too_far, tgt_sporadic_arrival_bound_last_job_too_far.
  apply: cta_forall_par => tpR tpL Htp. apply: cta_forall_par => jaR jaL Hja. apply: ct_forall_identity => job_task.
  apply: cta_forall_arr => aR aL Ha. apply: (cab_hyps Task Job tpR tpL Htp jaR jaL Hja job_task aR aL Ha).
  apply: ct_forall_nat => t1R t1L H1. apply: ct_forall_nat => t2R t2L H2. apply: ct_forall_identity => tsk.
  have Hn := num Task Job job_task aR aL Ha tsk _ _ _ _ H1 H2.
  apply: ct_imp; first exact (sub_nat_lt_correspondence _ _ _ _ (sub_nat_rel_canonical 0) (Htp tsk)).
  apply: ct_imp; first exact (sub_nat_lt_correspondence _ _ _ _ (sub_nat_rel_canonical 1) Hn).
  apply: ct_imp; first exact (sub_nat_lt_correspondence _ _ _ _ (cab_bound Task tpR tpL Htp tsk _ _ _ _ H1 H2) Hn).
  apply: ct_forall_identity => elem.
  have Hs := cab_sorted Task Job jaR jaL Hja job_task aR aL Ha tsk _ _ _ _ H1 H2.
  rewrite (cta_getD _ _ _ Hs elem _ _ (sub_nat_rel_canonical 0)) (cta_getD _ _ _ Hs elem _ _ (cta_pred_rel _ _ Hn)).
  exact (sub_nat_le_correspondence _ _ _ _
           (dm_sub_correspondence _ _ _ _ (sub_add_correspondence _ _ _ _ (Hja _) H2) H1) (Hja _)).
Qed.

Definition src_sporadic_arrival_bound_last_arrives_too_late (Task Job : eqType) : Prop :=
  forall task_period : Task -> Time.time,
    ltac:(type_of_term (@ArrivalBounds.sporadic_arrival_bound_last_arrives_too_late Task task_period Job)).
Definition tgt_sporadic_arrival_bound_last_arrives_too_late (Task Job : eqType) : SProp :=
  forall task_period : Task -> Lean.Nat,
    ltac:(type_of_term (I.Prosa_Classic_Model_Arrival_Basic_ArrivalBounds_ArrivalBounds_sporadic_arrival_bound_last_arrives_too_late
                          Task (ct_decidable_eq Task) task_period Job (ct_decidable_eq Job))).
Theorem ArrivalBounds_sporadic_arrival_bound_last_arrives_too_late_correspondence (Task Job : eqType) :
  PropSPropRel (src_sporadic_arrival_bound_last_arrives_too_late Task Job) (tgt_sporadic_arrival_bound_last_arrives_too_late Task Job).
Proof.
  unfold src_sporadic_arrival_bound_last_arrives_too_late, tgt_sporadic_arrival_bound_last_arrives_too_late.
  apply: cta_forall_par => tpR tpL Htp. apply: cta_forall_par => jaR jaL Hja. apply: ct_forall_identity => job_task.
  apply: cta_forall_arr => aR aL Ha. apply: (cab_hyps Task Job tpR tpL Htp jaR jaL Hja job_task aR aL Ha).
  apply: ct_forall_nat => t1R t1L H1. apply: ct_forall_nat => t2R t2L H2. apply: ct_forall_identity => tsk.
  have Hn := num Task Job job_task aR aL Ha tsk _ _ _ _ H1 H2.
  apply: ct_imp; first exact (sub_nat_lt_correspondence _ _ _ _ (sub_nat_rel_canonical 0) (Htp tsk)).
  apply: ct_imp; first exact (sub_nat_lt_correspondence _ _ _ _ (sub_nat_rel_canonical 1) Hn).
  apply: ct_imp; first exact (sub_nat_lt_correspondence _ _ _ _ (cab_bound Task tpR tpL Htp tsk _ _ _ _ H1 H2) Hn).
  apply: ct_forall_identity => elem.
  have Hs := cab_sorted Task Job jaR jaL Hja job_task aR aL Ha tsk _ _ _ _ H1 H2.
  rewrite (cta_getD _ _ _ Hs elem _ _ (cta_pred_rel _ _ Hn)).
  exact (sub_nat_le_correspondence _ _ _ _ H2 (Hja _)).
Qed.

Definition src_sporadic_arrival_bound_case_3_contradiction (Task Job : eqType) : Prop :=
  forall task_period : Task -> Time.time,
    ltac:(type_of_term (@ArrivalBounds.sporadic_arrival_bound_case_3_contradiction Task task_period Job)).
Definition tgt_sporadic_arrival_bound_case_3_contradiction (Task Job : eqType) : SProp :=
  forall task_period : Task -> Lean.Nat,
    ltac:(type_of_term (I.Prosa_Classic_Model_Arrival_Basic_ArrivalBounds_ArrivalBounds_sporadic_arrival_bound_case_3_contradiction
                          Task (ct_decidable_eq Task) task_period Job (ct_decidable_eq Job))).
Theorem ArrivalBounds_sporadic_arrival_bound_case_3_contradiction_correspondence (Task Job : eqType) :
  PropSPropRel (src_sporadic_arrival_bound_case_3_contradiction Task Job) (tgt_sporadic_arrival_bound_case_3_contradiction Task Job).
Proof.
  unfold src_sporadic_arrival_bound_case_3_contradiction, tgt_sporadic_arrival_bound_case_3_contradiction.
  apply: cta_forall_par => tpR tpL Htp. apply: cta_forall_par => jaR jaL Hja. apply: ct_forall_identity => job_task.
  apply: cta_forall_arr => aR aL Ha. apply: (cab_hyps Task Job tpR tpL Htp jaR jaL Hja job_task aR aL Ha).
  apply: ct_forall_nat => t1R t1L H1. apply: ct_forall_nat => t2R t2L H2. apply: ct_forall_identity => tsk.
  have Hn := num Task Job job_task aR aL Ha tsk _ _ _ _ H1 H2.
  apply: ct_imp; first exact (sub_nat_lt_correspondence _ _ _ _ (sub_nat_rel_canonical 0) (Htp tsk)).
  apply: ct_imp; first exact (sub_nat_lt_correspondence _ _ _ _ (sub_nat_rel_canonical 1) Hn).
  apply: ct_imp; first exact (sub_nat_lt_correspondence _ _ _ _ (cab_bound Task tpR tpL Htp tsk _ _ _ _ H1 H2) Hn).
  apply: ct_forall_identity => elem. exact cta_false_rel.
Qed.

Definition src_sporadic_task_arrival_bound_at_least_two_jobs (Task Job : eqType) : Prop :=
  forall task_period : Task -> Time.time,
    ltac:(type_of_term (@ArrivalBounds.sporadic_task_arrival_bound_at_least_two_jobs Task task_period Job)).
Definition tgt_sporadic_task_arrival_bound_at_least_two_jobs (Task Job : eqType) : SProp :=
  forall task_period : Task -> Lean.Nat,
    ltac:(type_of_term (I.Prosa_Classic_Model_Arrival_Basic_ArrivalBounds_ArrivalBounds_sporadic_task_arrival_bound_at_least_two_jobs
                          Task (ct_decidable_eq Task) task_period Job (ct_decidable_eq Job))).
Theorem ArrivalBounds_sporadic_task_arrival_bound_at_least_two_jobs_correspondence (Task Job : eqType) :
  PropSPropRel (src_sporadic_task_arrival_bound_at_least_two_jobs Task Job) (tgt_sporadic_task_arrival_bound_at_least_two_jobs Task Job).
Proof.
  unfold src_sporadic_task_arrival_bound_at_least_two_jobs, tgt_sporadic_task_arrival_bound_at_least_two_jobs.
  apply: cta_forall_par => tpR tpL Htp. apply: cta_forall_par => jaR jaL Hja. apply: ct_forall_identity => job_task.
  apply: cta_forall_arr => aR aL Ha. apply: (cab_hyps Task Job tpR tpL Htp jaR jaL Hja job_task aR aL Ha).
  apply: ct_forall_nat => t1R t1L H1. apply: ct_forall_nat => t2R t2L H2. apply: ct_forall_identity => tsk.
  have Hn := num Task Job job_task aR aL Ha tsk _ _ _ _ H1 H2.
  apply: ct_imp; first exact (sub_nat_lt_correspondence _ _ _ _ (sub_nat_rel_canonical 0) (Htp tsk)).
  apply: ct_imp; first exact (sub_nat_lt_correspondence _ _ _ _ (sub_nat_rel_canonical 1) Hn).
  exact (sub_nat_le_correspondence _ _ _ _ Hn (cab_bound Task tpR tpL Htp tsk _ _ _ _ H1 H2)).
Qed.

Definition src_sporadic_task_arrival_bound (Task Job : eqType) : Prop :=
  forall task_period : Task -> Time.time,
    ltac:(type_of_term (@ArrivalBounds.sporadic_task_arrival_bound Task task_period Job)).
Definition tgt_sporadic_task_arrival_bound (Task Job : eqType) : SProp :=
  forall task_period : Task -> Lean.Nat,
    ltac:(type_of_term (I.Prosa_Classic_Model_Arrival_Basic_ArrivalBounds_ArrivalBounds_sporadic_task_arrival_bound
                          Task (ct_decidable_eq Task) task_period Job (ct_decidable_eq Job))).
Theorem ArrivalBounds_sporadic_task_arrival_bound_correspondence (Task Job : eqType) :
  PropSPropRel (src_sporadic_task_arrival_bound Task Job) (tgt_sporadic_task_arrival_bound Task Job).
Proof.
  unfold src_sporadic_task_arrival_bound, tgt_sporadic_task_arrival_bound.
  apply: cta_forall_par => tpR tpL Htp. apply: cta_forall_par => jaR jaL Hja. apply: ct_forall_identity => job_task.
  apply: cta_forall_arr => aR aL Ha. apply: (cab_hyps Task Job tpR tpL Htp jaR jaL Hja job_task aR aL Ha).
  apply: ct_forall_nat => t1R t1L H1. apply: ct_forall_nat => t2R t2L H2. apply: ct_forall_identity => tsk.
  have Hn := num Task Job job_task aR aL Ha tsk _ _ _ _ H1 H2.
  apply: ct_imp; first exact (sub_nat_lt_correspondence _ _ _ _ (sub_nat_rel_canonical 0) (Htp tsk)).
  exact (sub_nat_le_correspondence _ _ _ _ Hn (cab_bound Task tpR tpL Htp tsk _ _ _ _ H1 H2)).
Qed.
