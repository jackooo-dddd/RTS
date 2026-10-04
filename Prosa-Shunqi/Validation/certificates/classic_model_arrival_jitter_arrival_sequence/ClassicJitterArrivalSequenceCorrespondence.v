From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq bigop.
From prosa Require Import classic.model.time classic.model.arrival.basic.arrival_sequence classic.model.arrival.jitter.arrival_sequence.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedClassicJitterArrivalSequence.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence ClassicJitterArrivalSequenceBase ClassicJitterArrivalSequenceList.

Module I := ImportedClassicJitterArrivalSequence.
Local Open Scope nat_scope.

(** Certificates for [classic/model/arrival/jitter/arrival_sequence.v] (ProsaBuddy classic, commit f692cb7).

    Inputs: the job type is an [eqType], identified, with the Lean [DecidableEq] instance given by the eqType's
    decision procedure ([ct_decidable_eq]); times by [SubNatRel]; job parameters [Job -> time] pointwise through
    [SubNatRel]; job sequences elementwise ([ClListRel]); arrival sequences pointwise on related times (as in the
    accepted classic arrival_sequence certificate); all with two-way totals.

    Computation: [\cat_(t1 <= t < t2) F t] against [Prosa.Util.Notation.bigCat] through the exported kernel-checked
    [ClassicJitterArrivalSequenceInterface.bigCat_range'] (a restatement of the accepted
    [ClassicArrivalSequenceInterface.bigCat_range'], used as a propositional equation); [[seq j <- s | p j]] against
    [List.filter] ([cl_filter]); Boolean range tests against [decide] of the Nat orders.

    Statements: the source side is the exact elaborated type of the pinned lemma (via [type of]; the source proof
    is not used). *)

Ltac type_of_term t := let T := type of t in exact T.
Notation cid := (fun z => z).

(* ------------------------------------------------------------------ *)
(** * Helpers (re-bound to this export from the accepted classic certificates) *)

(* ------------------------------------------------------------------ *)
(** * Generic covers and helpers *)

Lemma cja_forall_cover (A B : Type) (Rel : A -> B -> SProp) (toB : A -> B) (toA : B -> A)
    (HB : forall a, Rel a (toB a)) (HA : forall b, Rel (toA b) b) (PR : A -> Prop) (PL : B -> SProp) :
  (forall a b, Rel a b -> PropSPropRel (PR a) (PL b)) -> PropSPropRel (forall a, PR a) (forall b, PL b).
Proof.
  intro H. apply prop_sprop_rel_intro.
  - intros HR b. exact (prop_to_sprop _ _ (H _ _ (HA b)) (HR _)).
  - intro HL. apply strictly_inhabits. intro a. exact (sprop_to_prop _ _ (H _ _ (HB a)) (HL _)).
Qed.

Lemma cja_false_rel : PropSPropRel Logic.False I.False.
Proof.
  apply prop_sprop_rel_intro.
  - exact ct_coq_false_to_target.
  - exact ct_target_false_to_strict.
Qed.

Lemma cja_ne (T : Type) (x y : T) : PropSPropRel (x <> y) (I.Ne T x y).
Proof. exact (ct_imp _ _ _ _ (ct_eq_rel T x y) cja_false_rel). Qed.

Lemma cja_mem (T : eqType) x s sL : ClListRel cid s sL ->
  PropSPropRel (x \in s) (I.Membership_mem T (I.List T) (I.List_instMembership T) sL x).
Proof. exact (cl_mem_rel_list T T cid cid (fun _ => Logic.eq_refl _) x s sL). Qed.

Lemma cja_uniq (T : eqType) s sL : ClListRel cid s sL -> PropSPropRel (uniq s) (I.List_Nodup T sL).
Proof. exact (cl_uniq_rel_list T T cid cid (fun _ => Logic.eq_refl _) (fun _ => Logic.eq_refl _) s sL). Qed.

Lemma cja_unmap_rel (T : Type) (l : I.List T) : ClListRel cid (cl_unmap cid l) l.
Proof. apply: coq_eq_to_imported_eq. exact (cl_map_unmap cid cid (fun _ => Logic.eq_refl _) l). Qed.

Lemma cja_cl_map_inj (T : Type) (s1 s2 : seq T) : Logic.eq (cl_map cid s1) (cl_map cid s2) -> Logic.eq s1 s2.
Proof.
  intro E. rewrite -(cl_unmap_map cid cid (fun _ => Logic.eq_refl _) s1) -(cl_unmap_map cid cid (fun _ => Logic.eq_refl _) s2).
  by rewrite E.
Qed.

Lemma cja_succ_rel nR nL : SubNatRel nR nL ->
  SubNatRel nR.+1 (I.HAdd_hAdd_inst7 Lean.Nat Lean.Nat Lean.Nat (I.instHAdd_inst1 Lean.Nat I.instAddNat) nL
                     (I.OfNat_ofNat_inst1 Lean.Nat 1 (I.instOfNatNat 1))).
Proof. intro Hn. exact (sub_imported_eq_congr Lean.Nat_succ _ _ Hn). Qed.

(* ------------------------------------------------------------------ *)
(** * Big concatenation over a half-open interval (as in the accepted arrival_sequence certificate) *)

Fixpoint cja_natl (s : seq nat) : I.List_inst1 Lean.Nat :=
  match s with [::] => I.List_nil_inst1 _ | x :: s' => I.List_cons_inst1 _ (sub_nat_to_imported x) (cja_natl s') end.

Definition cja_one : Lean.Nat := I.OfNat_ofNat_inst1 Lean.Nat 1 (I.instOfNatNat 1).

Lemma cja_iota_range : forall n s,
  Logic.eq (I.List_range' (sub_nat_to_imported s) (sub_nat_to_imported n) cja_one) (cja_natl (iota s n)).
Proof.
  elim => [|n IH] s; first reflexivity.
  change (Logic.eq (I.List_cons_inst1 _ (sub_nat_to_imported s)
      (I.List_range' (sub_nat_to_imported (S s)) (sub_nat_to_imported n) cja_one))
    (I.List_cons_inst1 _ (sub_nat_to_imported s) (cja_natl (iota (S s) n)))).
  by rewrite IH.
Qed.

Lemma cja_map_natl {B : Type} (f : Lean.Nat -> B) : forall s,
  Logic.eq (I.List_map_inst1 Lean.Nat B f (cja_natl s)) (cl_map (fun k => f (sub_nat_to_imported k)) s).
Proof.
  elim => [|k s IH] //=.
  change (Logic.eq (I.List_cons B (f (sub_nat_to_imported k)) (I.List_map_inst1 Lean.Nat B f (cja_natl s)))
                   (I.List_cons B (f (sub_nat_to_imported k)) (cl_map (fun k => f (sub_nat_to_imported k)) s))).
  by rewrite IH.
Qed.

Lemma cja_cl_map_comp {A B C : Type} (f : A -> B) (g : B -> C) : forall s : seq A,
  Logic.eq (cl_map (fun x => g (f x)) s) (cl_map g (map f s)).
Proof. elim => [|x s IH] //=. by rewrite IH. Qed.

Lemma cja_cl_map_ext {A B : Type} (f g : A -> B) (H : forall x, Logic.eq (f x) (g x)) : forall s : seq A,
  Logic.eq (cl_map f s) (cl_map g s).
Proof. elim => [|x s IH] //=. by rewrite H IH. Qed.

Lemma cja_flatten {A : Type} : forall L : seq (seq A),
  Logic.eq (I.List_flatten A (cl_map (cl_map cid) L)) (cl_map cid (flatten L)).
Proof.
  elim => [|s L IH] //=.
  change (Logic.eq (I.List_append A (cl_map cid s) (I.List_flatten A (cl_map (cl_map cid) L))) (cl_map cid (s ++ flatten L))).
  rewrite IH cl_cat. reflexivity.
Qed.

Lemma cja_big_seq {A : Type} (F : nat -> seq A) : forall s : seq nat,
  Logic.eq (\big[cat/[::]]_(i <- s) F i) (flatten (map F s)).
Proof. elim => [|x s IH]; first by rewrite big_nil. by rewrite big_cons IH. Qed.

Definition CjaFamRel (A : Type) (fR : nat -> seq A) (fL : Lean.Nat -> I.List A) : SProp :=
  forall nR nL, SubNatRel nR nL -> ClListRel cid (fR nR) (fL nL).

Lemma cja_bigcat_rel (A : Type) fR fL (Hf : CjaFamRel A fR fL) mR mL nR nL :
  SubNatRel mR mL -> SubNatRel nR nL ->
  ClListRel cid (\big[cat/[::]]_(mR <= t < nR) fR t) (I.Prosa_Util_Notation_bigCat A mL nL fL).
Proof.
  intros Hm Hn. have E1 := cl_nat_logic _ _ Hm. have E2 := cl_nat_logic _ _ Hn. subst mL nL.
  apply: coq_eq_to_imported_eq. apply: Logic.eq_sym.
  rewrite (imported_eq_to_coq_eq _ _ (I.Prosa_Validation_ClassicJitterArrivalSequenceInterface_bigCat_range'
             A (sub_nat_to_imported mR) (sub_nat_to_imported nR) fL)).
  have Hd : Logic.eq (I.HSub_hSub_inst7 Lean.Nat Lean.Nat Lean.Nat (I.instHSub_inst1 Lean.Nat I.instSubNat)
                       (sub_nat_to_imported nR) (sub_nat_to_imported mR)) (sub_nat_to_imported (nR - mR)) :=
    ct_sub_canonical nR mR.
  rewrite Hd.
  change (I.OfNat_ofNat_inst1 Lean.Nat 0 (I.instOfNatNat 0)) with (sub_nat_to_imported 0).
  rewrite (cja_iota_range (nR - mR) 0) cja_map_natl. cbv beta.
  have Hpt : forall k, Logic.eq
      (fL (I.HAdd_hAdd_inst7 Lean.Nat Lean.Nat Lean.Nat (I.instHAdd_inst1 Lean.Nat I.instAddNat)
             (sub_nat_to_imported mR) (sub_nat_to_imported k)))
      (cl_map cid (fR (mR + k))).
  { intro k. exact (cl_list_logic _ _ _ (Hf _ _ (sub_add_correspondence mR _ k _
       (sub_nat_rel_canonical mR) (sub_nat_rel_canonical k)))). }
  rewrite (cja_cl_map_ext _ _ Hpt) (cja_cl_map_comp (fun k => fR (mR + k)) (cl_map cid)) cja_flatten.
  have Hi : Logic.eq (iota mR (nR - mR)) (map (addn mR) (iota 0 (nR - mR))) by rewrite -iotaDl addn0.
  rewrite cja_big_seq /index_iota Hi -map_comp.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(** * Arrival sequences and parameters *)

Section Rel.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).
Notation LArr := (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrival_sequence Job dJ).

Definition CjaArrRel (aR : ArrivalSequence.arrival_sequence Job) (aL : LArr) : SProp :=
  forall tR tL, SubNatRel tR tL -> ClListRel cid (aR tR) (aL tL).

Definition cja_arr_to_target (aR : ArrivalSequence.arrival_sequence Job) : LArr :=
  fun tL => cl_map cid (aR (sub_nat_to_rocq tL)).

Definition cja_arr_to_source (aL : LArr) : ArrivalSequence.arrival_sequence Job :=
  fun tR => cl_unmap cid (aL (sub_nat_to_imported tR)).

Lemma cja_arr_canonical aR : CjaArrRel aR (cja_arr_to_target aR).
Proof.
  intros tR tL Ht. have E := cl_nat_logic _ _ Ht. subst tL.
  apply: coq_eq_to_imported_eq. rewrite /cja_arr_to_target sub_nat_rocq_roundtrip. reflexivity.
Qed.

Lemma cja_arr_surjective aL : CjaArrRel (cja_arr_to_source aL) aL.
Proof.
  intros tR tL Ht. have E := cl_nat_logic _ _ Ht. subst tL.
  apply: coq_eq_to_imported_eq. exact (cl_map_unmap cid cid (fun _ => Logic.eq_refl _) _).
Qed.

Lemma cja_forall_arr (PR : ArrivalSequence.arrival_sequence Job -> Prop) (PL : LArr -> SProp) :
  (forall aR aL, CjaArrRel aR aL -> PropSPropRel (PR aR) (PL aL)) -> PropSPropRel (forall a, PR a) (forall a, PL a).
Proof. exact (cja_forall_cover _ _ CjaArrRel cja_arr_to_target cja_arr_to_source cja_arr_canonical cja_arr_surjective PR PL). Qed.

End Rel.

Definition CjaParRel (T : Type) (pR : T -> nat) (pL : T -> Lean.Nat) : SProp := forall x, SubNatRel (pR x) (pL x).

Lemma cja_forall_par (T : Type) (PR : (T -> nat) -> Prop) (PL : (T -> Lean.Nat) -> SProp) :
  (forall pR pL, CjaParRel T pR pL -> PropSPropRel (PR pR) (PL pL)) -> PropSPropRel (forall p, PR p) (forall p, PL p).
Proof.
  exact (cja_forall_cover _ _ (CjaParRel T) (fun pR j => sub_nat_to_imported (pR j)) (fun pL j => sub_nat_to_rocq (pL j))
           (fun pR j => sub_nat_rel_canonical (pR j)) (fun pL j => sub_nat_rel_surjective (pL j)) PR PL).
Qed.

(** The imported [ArrivalSequence] definitions this file's statements mention, related on related inputs. *)
Section ArrivalDefs.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).

Lemma cja_jobs_arrived_between aR aL (Ha : CjaArrRel Job aR aL) t1R t1L t2R t2L
    (H1 : SubNatRel t1R t1L) (H2 : SubNatRel t2R t2L) :
  ClListRel cid (ArrivalSequence.jobs_arrived_between aR t1R t2R)
    (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_jobs_arrived_between Job dJ aL t1L t2L).
Proof. exact (cja_bigcat_rel Job (fun t => aR t) (fun t => aL t) Ha t1R t1L t2R t2L H1 H2). Qed.

Lemma cja_arrives_in aR aL (Ha : CjaArrRel Job aR aL) j :
  PropSPropRel (ArrivalSequence.arrives_in aR j)
    (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrives_in Job dJ aL j).
Proof. apply: ct_exists_nat => tR tL Ht. exact (cja_mem Job j _ _ (Ha tR tL Ht)). Qed.

Lemma cja_consistent pR pL (Hp : CjaParRel Job pR pL) aR aL (Ha : CjaArrRel Job aR aL) :
  PropSPropRel (ArrivalSequence.arrival_times_are_consistent pR aR)
    (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrival_times_are_consistent Job dJ pL aL).
Proof.
  apply: ct_forall_identity => j. apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (ct_bool_truth _ _ (ct_decide_bool _ _ _ (cja_mem Job j _ _ (Ha tR tL Ht)))).
  exact (sub_nat_eq_correspondence _ _ _ _ (Hp j) Ht).
Qed.

Lemma cja_is_a_set aR aL (Ha : CjaArrRel Job aR aL) :
  PropSPropRel (ArrivalSequence.arrival_sequence_is_a_set aR)
    (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrival_sequence_is_a_set Job dJ aL).
Proof. apply: ct_forall_nat => tR tL Ht. exact (cja_uniq Job _ _ (Ha tR tL Ht)). Qed.

End ArrivalDefs.

Section ArrivalDefs2.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).

Lemma cja_jobs_arrived_before aR aL (Ha : CjaArrRel Job aR aL) tR tL (Ht : SubNatRel tR tL) :
  ClListRel cid (ArrivalSequence.jobs_arrived_before aR tR)
    (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_jobs_arrived_before Job dJ aL tL).
Proof. exact (cja_jobs_arrived_between Job aR aL Ha 0 _ tR tL (sub_nat_rel_canonical 0) Ht). Qed.

Lemma cja_arrives_at aR aL (Ha : CjaArrRel Job aR aL) j tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (ArrivalSequence.arrives_at aR j tR)
    (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrives_at Job dJ aL j tL).
Proof. exact (ct_decide_bool _ _ _ (cja_mem Job j _ _ (Ha tR tL Ht))). Qed.

End ArrivalDefs2.



(* ------------------------------------------------------------------ *)
(** * Definitions *)

Section Defs.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).

Theorem ArrivalSequenceWithJitter_actual_arrival_correspondence pR pL (Hp : CjaParRel Job pR pL) qR qL (Hq : CjaParRel Job qR qL) j :
  SubNatRel (ArrivalSequenceWithJitter.actual_arrival pR qR j) (I.Prosa_Classic_Model_Arrival_Jitter_ArrivalSequence_ArrivalSequenceWithJitter_actual_arrival Job dJ pL qL j).
Proof. exact (sub_add_correspondence _ _ _ _ (Hp j) (Hq j)). Qed.

Notation AA := ArrivalSequenceWithJitter_actual_arrival_correspondence.

Theorem ArrivalSequenceWithJitter_jitter_has_passed_correspondence pR pL (Hp : CjaParRel Job pR pL) qR qL (Hq : CjaParRel Job qR qL) j
    tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (ArrivalSequenceWithJitter.jitter_has_passed pR qR j tR) (I.Prosa_Classic_Model_Arrival_Jitter_ArrivalSequence_ArrivalSequenceWithJitter_jitter_has_passed Job dJ pL qL j tL).
Proof. exact (ct_decide_le _ _ _ _ (AA pR pL Hp qR qL Hq j) Ht). Qed.

Theorem ArrivalSequenceWithJitter_actual_arrival_before_correspondence pR pL (Hp : CjaParRel Job pR pL) qR qL (Hq : CjaParRel Job qR qL) j
    tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (ArrivalSequenceWithJitter.actual_arrival_before pR qR j tR) (I.Prosa_Classic_Model_Arrival_Jitter_ArrivalSequence_ArrivalSequenceWithJitter_actual_arrival_before Job dJ pL qL j tL).
Proof. exact (ct_decide_lt _ _ _ _ (AA pR pL Hp qR qL Hq j) Ht). Qed.

Theorem ArrivalSequenceWithJitter_actual_arrival_between_correspondence pR pL (Hp : CjaParRel Job pR pL) qR qL (Hq : CjaParRel Job qR qL) j
    t1R t1L (H1 : SubNatRel t1R t1L) t2R t2L (H2 : SubNatRel t2R t2L) :
  CtBoolRel (ArrivalSequenceWithJitter.actual_arrival_between pR qR j t1R t2R) (I.Prosa_Classic_Model_Arrival_Jitter_ArrivalSequence_ArrivalSequenceWithJitter_actual_arrival_between Job dJ pL qL j t1L t2L).
Proof.
  exact (ct_bool_and _ _ _ _ (ct_decide_le _ _ _ _ H1 (AA pR pL Hp qR qL Hq j))
                             (ct_decide_lt _ _ _ _ (AA pR pL Hp qR qL Hq j) H2)).
Qed.

Theorem ArrivalSequenceWithJitter_actual_arrivals_between_correspondence pR pL (Hp : CjaParRel Job pR pL) qR qL (Hq : CjaParRel Job qR qL)
    aR aL (Ha : CjaArrRel Job aR aL) t1R t1L (H1 : SubNatRel t1R t1L) t2R t2L (H2 : SubNatRel t2R t2L) :
  ClListRel cid (ArrivalSequenceWithJitter.actual_arrivals_between pR qR aR t1R t2R) (I.Prosa_Classic_Model_Arrival_Jitter_ArrivalSequence_ArrivalSequenceWithJitter_actual_arrivals_between Job dJ pL qL aL t1L t2L).
Proof.
  apply: coq_eq_to_imported_eq.
  have E := cl_list_logic _ _ _ (cja_jobs_arrived_before Job aR aL Ha t2R t2L H2).
  have F := cl_filter cid _ (fun j => I.Prosa_Classic_Model_Arrival_Jitter_ArrivalSequence_ArrivalSequenceWithJitter_actual_arrival_between Job dJ pL qL j t1L t2L) (fun j => ArrivalSequenceWithJitter_actual_arrival_between_correspondence pR pL Hp qR qL Hq j _ _ H1 _ _ H2)
              (ArrivalSequence.jobs_arrived_before aR t2R).
  rewrite -E in F. exact F.
Qed.

Notation AB := ArrivalSequenceWithJitter_actual_arrivals_between_correspondence.

Theorem ArrivalSequenceWithJitter_actual_arrivals_up_to_correspondence pR pL (Hp : CjaParRel Job pR pL) qR qL (Hq : CjaParRel Job qR qL)
    aR aL (Ha : CjaArrRel Job aR aL) tR tL (Ht : SubNatRel tR tL) :
  ClListRel cid (ArrivalSequenceWithJitter.actual_arrivals_up_to pR qR aR tR) (I.Prosa_Classic_Model_Arrival_Jitter_ArrivalSequence_ArrivalSequenceWithJitter_actual_arrivals_up_to Job dJ pL qL aL tL).
Proof. exact (AB pR pL Hp qR qL Hq aR aL Ha 0 _ (sub_nat_rel_canonical 0) tR.+1 _ (cja_succ_rel tR tL Ht)). Qed.

Theorem ArrivalSequenceWithJitter_actual_arrivals_before_correspondence pR pL (Hp : CjaParRel Job pR pL) qR qL (Hq : CjaParRel Job qR qL)
    aR aL (Ha : CjaArrRel Job aR aL) tR tL (Ht : SubNatRel tR tL) :
  ClListRel cid (ArrivalSequenceWithJitter.actual_arrivals_before pR qR aR tR) (I.Prosa_Classic_Model_Arrival_Jitter_ArrivalSequence_ArrivalSequenceWithJitter_actual_arrivals_before Job dJ pL qL aL tL).
Proof. exact (AB pR pL Hp qR qL Hq aR aL Ha 0 _ (sub_nat_rel_canonical 0) tR tL Ht). Qed.
End Defs.

(* ------------------------------------------------------------------ *)
(** * Statements *)

Notation AB := ArrivalSequenceWithJitter_actual_arrivals_between_correspondence.
Notation AA := ArrivalSequenceWithJitter_actual_arrival_correspondence.

Ltac cja_params :=
  apply: cja_forall_par => pR pL Hp; apply: cja_forall_par => qR qL Hq; apply: cja_forall_arr => aR aL Ha.

Definition src_actual_arrivals_between_mem_cat (Job : eqType) : Prop :=
  ltac:(type_of_term (@ArrivalSequenceWithJitter.actual_arrivals_between_mem_cat Job)).
Definition tgt_actual_arrivals_between_mem_cat (Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Model_Arrival_Jitter_ArrivalSequence_ArrivalSequenceWithJitter_actual_arrivals_between_mem_cat Job (ct_decidable_eq Job))).

Theorem ArrivalSequenceWithJitter_actual_arrivals_between_mem_cat_correspondence (Job : eqType) :
  PropSPropRel (src_actual_arrivals_between_mem_cat Job) (tgt_actual_arrivals_between_mem_cat Job).
Proof.
  unfold src_actual_arrivals_between_mem_cat, tgt_actual_arrivals_between_mem_cat. cja_params.
  apply: ct_imp; first exact (cja_consistent Job pR pL Hp aR aL Ha).
  apply: ct_forall_identity => j.
  apply: ct_forall_nat => t1R t1L H1. apply: ct_forall_nat => tR tL Ht. apply: ct_forall_nat => t2R t2L H2.
  apply: ct_imp; first exact (sub_nat_le_correspondence _ _ _ _ H1 Ht).
  apply: ct_imp; first exact (sub_nat_le_correspondence _ _ _ _ Ht H2).
  apply: ct_bool_eq.
  - exact (ct_decide_bool _ _ _ (cja_mem Job j _ _ (AB Job pR pL Hp qR qL Hq aR aL Ha _ _ H1 _ _ H2))).
  - apply: ct_decide_bool. apply: cja_mem. apply: coq_eq_to_imported_eq.
    rewrite (cl_cat cid). rewrite (cl_list_logic _ _ _ (AB Job pR pL Hp qR qL Hq aR aL Ha _ _ H1 _ _ Ht))
      (cl_list_logic _ _ _ (AB Job pR pL Hp qR qL Hq aR aL Ha _ _ Ht _ _ H2)).
    reflexivity.
Qed.

Definition src_actual_arrivals_between_sub (Job : eqType) : Prop :=
  ltac:(type_of_term (@ArrivalSequenceWithJitter.actual_arrivals_between_sub Job)).
Definition tgt_actual_arrivals_between_sub (Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Model_Arrival_Jitter_ArrivalSequence_ArrivalSequenceWithJitter_actual_arrivals_between_sub Job (ct_decidable_eq Job))).

Theorem ArrivalSequenceWithJitter_actual_arrivals_between_sub_correspondence (Job : eqType) :
  PropSPropRel (src_actual_arrivals_between_sub Job) (tgt_actual_arrivals_between_sub Job).
Proof.
  unfold src_actual_arrivals_between_sub, tgt_actual_arrivals_between_sub. cja_params.
  apply: ct_imp; first exact (cja_consistent Job pR pL Hp aR aL Ha).
  apply: ct_forall_identity => j.
  apply: ct_forall_nat => t1R t1L H1. apply: ct_forall_nat => t1'R t1'L H1'.
  apply: ct_forall_nat => t2R t2L H2. apply: ct_forall_nat => t2'R t2'L H2'.
  apply: ct_imp; first exact (sub_nat_le_correspondence _ _ _ _ H1' H1).
  apply: ct_imp; first exact (sub_nat_le_correspondence _ _ _ _ H2 H2').
  apply: ct_imp; first exact (cja_mem Job j _ _ (AB Job pR pL Hp qR qL Hq aR aL Ha _ _ H1 _ _ H2)).
  exact (cja_mem Job j _ _ (AB Job pR pL Hp qR qL Hq aR aL Ha _ _ H1' _ _ H2')).
Qed.

Definition src_in_actual_arrivals_between_implies_arrived (Job : eqType) : Prop :=
  ltac:(type_of_term (@ArrivalSequenceWithJitter.in_actual_arrivals_between_implies_arrived Job)).
Definition tgt_in_actual_arrivals_between_implies_arrived (Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Model_Arrival_Jitter_ArrivalSequence_ArrivalSequenceWithJitter_in_actual_arrivals_between_implies_arrived Job (ct_decidable_eq Job))).

Theorem ArrivalSequenceWithJitter_in_actual_arrivals_between_implies_arrived_correspondence (Job : eqType) :
  PropSPropRel (src_in_actual_arrivals_between_implies_arrived Job) (tgt_in_actual_arrivals_between_implies_arrived Job).
Proof.
  unfold src_in_actual_arrivals_between_implies_arrived, tgt_in_actual_arrivals_between_implies_arrived. cja_params.
  apply: ct_forall_identity => j.
  apply: ct_forall_nat => t1R t1L H1. apply: ct_forall_nat => t2R t2L H2.
  apply: ct_imp; first exact (cja_mem Job j _ _ (AB Job pR pL Hp qR qL Hq aR aL Ha _ _ H1 _ _ H2)).
  exact (cja_arrives_in Job aR aL Ha j).
Qed.

Definition src_in_actual_arrivals_before_implies_arrived (Job : eqType) : Prop :=
  ltac:(type_of_term (@ArrivalSequenceWithJitter.in_actual_arrivals_before_implies_arrived Job)).
Definition tgt_in_actual_arrivals_before_implies_arrived (Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Model_Arrival_Jitter_ArrivalSequence_ArrivalSequenceWithJitter_in_actual_arrivals_before_implies_arrived Job (ct_decidable_eq Job))).

Theorem ArrivalSequenceWithJitter_in_actual_arrivals_before_implies_arrived_correspondence (Job : eqType) :
  PropSPropRel (src_in_actual_arrivals_before_implies_arrived Job) (tgt_in_actual_arrivals_before_implies_arrived Job).
Proof.
  unfold src_in_actual_arrivals_before_implies_arrived, tgt_in_actual_arrivals_before_implies_arrived. cja_params.
  apply: ct_forall_identity => j. apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (cja_mem Job j _ _ (ArrivalSequenceWithJitter_actual_arrivals_before_correspondence Job pR pL Hp qR qL Hq aR aL Ha _ _ Ht)).
  exact (cja_arrives_in Job aR aL Ha j).
Qed.

Definition src_in_actual_arrivals_implies_arrived_before (Job : eqType) : Prop :=
  ltac:(type_of_term (@ArrivalSequenceWithJitter.in_actual_arrivals_implies_arrived_before Job)).
Definition tgt_in_actual_arrivals_implies_arrived_before (Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Model_Arrival_Jitter_ArrivalSequence_ArrivalSequenceWithJitter_in_actual_arrivals_implies_arrived_before Job (ct_decidable_eq Job))).

Theorem ArrivalSequenceWithJitter_in_actual_arrivals_implies_arrived_before_correspondence (Job : eqType) :
  PropSPropRel (src_in_actual_arrivals_implies_arrived_before Job) (tgt_in_actual_arrivals_implies_arrived_before Job).
Proof.
  unfold src_in_actual_arrivals_implies_arrived_before, tgt_in_actual_arrivals_implies_arrived_before. cja_params.
  apply: ct_forall_identity => j. apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (cja_mem Job j _ _ (ArrivalSequenceWithJitter_actual_arrivals_before_correspondence Job pR pL Hp qR qL Hq aR aL Ha _ _ Ht)).
  exact (ct_bool_truth _ _ (ArrivalSequenceWithJitter_actual_arrival_before_correspondence Job pR pL Hp qR qL Hq j _ _ Ht)).
Qed.

Definition src_in_actual_arrivals_implies_arrived_between (Job : eqType) : Prop :=
  ltac:(type_of_term (@ArrivalSequenceWithJitter.in_actual_arrivals_implies_arrived_between Job)).
Definition tgt_in_actual_arrivals_implies_arrived_between (Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Model_Arrival_Jitter_ArrivalSequence_ArrivalSequenceWithJitter_in_actual_arrivals_implies_arrived_between Job (ct_decidable_eq Job))).

Theorem ArrivalSequenceWithJitter_in_actual_arrivals_implies_arrived_between_correspondence (Job : eqType) :
  PropSPropRel (src_in_actual_arrivals_implies_arrived_between Job) (tgt_in_actual_arrivals_implies_arrived_between Job).
Proof.
  unfold src_in_actual_arrivals_implies_arrived_between, tgt_in_actual_arrivals_implies_arrived_between. cja_params.
  apply: ct_forall_identity => j.
  apply: ct_forall_nat => t1R t1L H1. apply: ct_forall_nat => t2R t2L H2.
  apply: ct_imp; first exact (cja_mem Job j _ _ (AB Job pR pL Hp qR qL Hq aR aL Ha _ _ H1 _ _ H2)).
  exact (ct_bool_truth _ _ (ArrivalSequenceWithJitter_actual_arrival_between_correspondence Job pR pL Hp qR qL Hq j _ _ H1 _ _ H2)).
Qed.

Definition src_arrived_between_implies_in_actual_arrivals (Job : eqType) : Prop :=
  ltac:(type_of_term (@ArrivalSequenceWithJitter.arrived_between_implies_in_actual_arrivals Job)).
Definition tgt_arrived_between_implies_in_actual_arrivals (Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Model_Arrival_Jitter_ArrivalSequence_ArrivalSequenceWithJitter_arrived_between_implies_in_actual_arrivals Job (ct_decidable_eq Job))).

Theorem ArrivalSequenceWithJitter_arrived_between_implies_in_actual_arrivals_correspondence (Job : eqType) :
  PropSPropRel (src_arrived_between_implies_in_actual_arrivals Job) (tgt_arrived_between_implies_in_actual_arrivals Job).
Proof.
  unfold src_arrived_between_implies_in_actual_arrivals, tgt_arrived_between_implies_in_actual_arrivals. cja_params.
  apply: ct_imp; first exact (cja_consistent Job pR pL Hp aR aL Ha).
  apply: ct_forall_identity => j.
  apply: ct_forall_nat => t1R t1L H1. apply: ct_forall_nat => t2R t2L H2.
  apply: ct_imp; first exact (cja_arrives_in Job aR aL Ha j).
  apply: ct_imp; first exact (ct_bool_truth _ _ (ArrivalSequenceWithJitter_actual_arrival_between_correspondence Job pR pL Hp qR qL Hq j _ _ H1 _ _ H2)).
  exact (cja_mem Job j _ _ (AB Job pR pL Hp qR qL Hq aR aL Ha _ _ H1 _ _ H2)).
Qed.

Definition src_actual_arrivals_uniq (Job : eqType) : Prop :=
  ltac:(type_of_term (@ArrivalSequenceWithJitter.actual_arrivals_uniq Job)).
Definition tgt_actual_arrivals_uniq (Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Model_Arrival_Jitter_ArrivalSequence_ArrivalSequenceWithJitter_actual_arrivals_uniq Job (ct_decidable_eq Job))).

Theorem ArrivalSequenceWithJitter_actual_arrivals_uniq_correspondence (Job : eqType) :
  PropSPropRel (src_actual_arrivals_uniq Job) (tgt_actual_arrivals_uniq Job).
Proof.
  unfold src_actual_arrivals_uniq, tgt_actual_arrivals_uniq. cja_params.
  apply: ct_imp; first exact (cja_consistent Job pR pL Hp aR aL Ha).
  apply: ct_imp; first exact (cja_is_a_set Job aR aL Ha).
  apply: ct_forall_nat => t1R t1L H1. apply: ct_forall_nat => t2R t2L H2.
  exact (cja_uniq Job _ _ (AB Job pR pL Hp qR qL Hq aR aL Ha _ _ H1 _ _ H2)).
Qed.
