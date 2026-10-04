From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq bigop.
From prosa Require Import classic.model.arrival.basic.arrival_sequence.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedClassicArrivalSequence.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence ClassicArrivalSequenceBase ClassicArrivalSequenceList.

Module I := ImportedClassicArrivalSequence.
Local Open Scope nat_scope.

(** Certificates for [classic/model/arrival/basic/arrival_sequence.v] (ProsaBuddy classic,
    commit f692cb7).

    Inputs: the job type is an [eqType], identified, with the Lean [DecidableEq]
    instance given by the eqType's decision procedure ([ct_decidable_eq]); times by
    [SubNatRel]; job sequences elementwise ([ClListRel]); arrival sequences
    [time -> seq Job] pointwise on related times ([CaArrRel]); arrival-time functions
    [Job -> time] pointwise through [SubNatRel] ([CaParRel]); all with two-way totals.

    Computation: [\cat_(t1 <= t < t2) F t] is a flattening of [F] mapped over
    [iota t1 (t2 - t1)] (MathComp [big_nil]/[big_cons], [iotaDl]); the Lean
    [Prosa.Util.Notation.bigCat t1 t2 F] is rewritten by the exported kernel-checked
    equation [ClassicArrivalSequenceInterface.bigCat_range'] (used as a propositional
    equation) into a flattening over [List.range' 0 (t2 - t1)]; the two are related
    structurally.  Membership tests [decide (j ∈ s)] are related through the
    propositional correspondence of membership ([ct_decide_bool]); the Lean decision
    procedures are never unfolded.

    Statements: the source side is the exact elaborated type of the pinned lemma (via
    [type of]; the source proof is not used). *)

Ltac type_of_term t := let T := type of t in exact T.
Notation cid := (fun z => z).

(* ------------------------------------------------------------------ *)
(** * Generic covers and list helpers *)

Lemma ca_forall_cover (A B : Type) (Rel : A -> B -> SProp) (toB : A -> B) (toA : B -> A)
    (HB : forall a, Rel a (toB a)) (HA : forall b, Rel (toA b) b) (PR : A -> Prop) (PL : B -> SProp) :
  (forall a b, Rel a b -> PropSPropRel (PR a) (PL b)) -> PropSPropRel (forall a, PR a) (forall b, PL b).
Proof.
  intro H. apply prop_sprop_rel_intro.
  - intros HR b. exact (prop_to_sprop _ _ (H _ _ (HA b)) (HR _)).
  - intro HL. apply strictly_inhabits. intro a. exact (sprop_to_prop _ _ (H _ _ (HB a)) (HL _)).
Qed.

Lemma ca_list_eq (T : Type) s1 l1 s2 l2 :
  ClListRel (B := T) cid s1 l1 -> ClListRel (B := T) cid s2 l2 -> PropSPropRel (Logic.eq s1 s2) (Lean.eq l1 l2).
Proof.
  intros H1 H2. rewrite (cl_list_logic _ _ _ H1) (cl_list_logic _ _ _ H2). clear H1 H2.
  apply prop_sprop_rel_intro.
  - intro E. rewrite E. exact (@Lean.eq_refl _ _).
  - intro E. apply strictly_inhabits. have E' := imported_eq_to_coq_eq _ _ E. clear E.
    rewrite -(cl_unmap_map cid cid (fun _ => Logic.eq_refl _) s1) -(cl_unmap_map cid cid (fun _ => Logic.eq_refl _) s2).
    by rewrite E'.
Qed.

Lemma ca_cat_rel (T : Type) s1 l1 s2 l2 :
  ClListRel (B := T) cid s1 l1 -> ClListRel (B := T) cid s2 l2 ->
  ClListRel cid (s1 ++ s2)
    (I.HAppend_hAppend (I.List T) (I.List T) (I.List T) (I.instHAppendOfAppend (I.List T) (I.List_instAppend T)) l1 l2).
Proof.
  intros H1 H2. apply: coq_eq_to_imported_eq.
  rewrite (cl_list_logic _ _ _ H1) (cl_list_logic _ _ _ H2). exact (cl_cat cid s1 s2).
Qed.

Lemma ca_mem (T : eqType) x s sL : ClListRel cid s sL ->
  PropSPropRel (x \in s) (I.Membership_mem T (I.List T) (I.List_instMembership T) sL x).
Proof. exact (cl_mem_rel_list T T cid cid (fun _ => Logic.eq_refl _) x s sL). Qed.

Lemma ca_uniq (T : eqType) s sL : ClListRel cid s sL -> PropSPropRel (uniq s) (I.List_Nodup T sL).
Proof. exact (cl_uniq_rel_list T T cid cid (fun _ => Logic.eq_refl _) (fun _ => Logic.eq_refl _) s sL). Qed.

(* ------------------------------------------------------------------ *)
(** * Big concatenation over a half-open interval *)

Fixpoint ca_natl (s : seq nat) : I.List_inst1 Lean.Nat :=
  match s with [::] => I.List_nil_inst1 _ | x :: s' => I.List_cons_inst1 _ (sub_nat_to_imported x) (ca_natl s') end.

Definition ca_one : Lean.Nat := I.OfNat_ofNat_inst1 Lean.Nat 1 (I.instOfNatNat 1).

Lemma ca_iota_range : forall n s,
  Logic.eq (I.List_range' (sub_nat_to_imported s) (sub_nat_to_imported n) ca_one) (ca_natl (iota s n)).
Proof.
  elim => [|n IH] s; first reflexivity.
  change (Logic.eq (I.List_cons_inst1 _ (sub_nat_to_imported s)
      (I.List_range' (sub_nat_to_imported (S s)) (sub_nat_to_imported n) ca_one))
    (I.List_cons_inst1 _ (sub_nat_to_imported s) (ca_natl (iota (S s) n)))).
  by rewrite IH.
Qed.

Lemma ca_map_natl {B : Type} (f : Lean.Nat -> B) : forall s,
  Logic.eq (I.List_map_inst1 Lean.Nat B f (ca_natl s)) (cl_map (fun k => f (sub_nat_to_imported k)) s).
Proof.
  elim => [|k s IH] //=.
  change (Logic.eq (I.List_cons B (f (sub_nat_to_imported k)) (I.List_map_inst1 Lean.Nat B f (ca_natl s)))
                   (I.List_cons B (f (sub_nat_to_imported k)) (cl_map (fun k => f (sub_nat_to_imported k)) s))).
  by rewrite IH.
Qed.

Lemma ca_cl_map_comp {A B C : Type} (f : A -> B) (g : B -> C) : forall s : seq A,
  Logic.eq (cl_map (fun x => g (f x)) s) (cl_map g (map f s)).
Proof. elim => [|x s IH] //=. by rewrite IH. Qed.

Lemma ca_cl_map_ext {A B : Type} (f g : A -> B) (H : forall x, Logic.eq (f x) (g x)) : forall s : seq A,
  Logic.eq (cl_map f s) (cl_map g s).
Proof. elim => [|x s IH] //=. by rewrite H IH. Qed.

Lemma ca_flatten {A : Type} : forall L : seq (seq A),
  Logic.eq (I.List_flatten A (cl_map (cl_map cid) L)) (cl_map cid (flatten L)).
Proof.
  elim => [|s L IH] //=.
  change (Logic.eq (I.List_append A (cl_map cid s) (I.List_flatten A (cl_map (cl_map cid) L))) (cl_map cid (s ++ flatten L))).
  rewrite IH cl_cat. reflexivity.
Qed.

Lemma ca_big_seq {A : Type} (F : nat -> seq A) : forall s : seq nat,
  Logic.eq (\big[cat/[::]]_(i <- s) F i) (flatten (map F s)).
Proof. elim => [|x s IH]; first by rewrite big_nil. by rewrite big_cons IH. Qed.

Definition CaFamRel (A : Type) (fR : nat -> seq A) (fL : Lean.Nat -> I.List A) : SProp :=
  forall nR nL, SubNatRel nR nL -> ClListRel cid (fR nR) (fL nL).

Lemma ca_bigcat_rel (A : Type) fR fL (Hf : CaFamRel A fR fL) mR mL nR nL :
  SubNatRel mR mL -> SubNatRel nR nL ->
  ClListRel cid (\big[cat/[::]]_(mR <= t < nR) fR t) (I.Prosa_Util_Notation_bigCat A mL nL fL).
Proof.
  intros Hm Hn. have E1 := cl_nat_logic _ _ Hm. have E2 := cl_nat_logic _ _ Hn. subst mL nL.
  apply: coq_eq_to_imported_eq. apply: Logic.eq_sym.
  rewrite (imported_eq_to_coq_eq _ _ (I.Prosa_Validation_ClassicArrivalSequenceInterface_bigCat_range'
             A (sub_nat_to_imported mR) (sub_nat_to_imported nR) fL)).
  have Hd : Logic.eq (I.HSub_hSub_inst7 Lean.Nat Lean.Nat Lean.Nat (I.instHSub_inst1 Lean.Nat I.instSubNat)
                       (sub_nat_to_imported nR) (sub_nat_to_imported mR)) (sub_nat_to_imported (nR - mR)) :=
    ct_sub_canonical nR mR.
  rewrite Hd.
  change (I.OfNat_ofNat_inst1 Lean.Nat 0 (I.instOfNatNat 0)) with (sub_nat_to_imported 0).
  rewrite (ca_iota_range (nR - mR) 0) ca_map_natl. cbv beta.
  have Hpt : forall k, Logic.eq
      (fL (I.HAdd_hAdd_inst7 Lean.Nat Lean.Nat Lean.Nat (I.instHAdd_inst1 Lean.Nat I.instAddNat)
             (sub_nat_to_imported mR) (sub_nat_to_imported k)))
      (cl_map cid (fR (mR + k))).
  { intro k. exact (cl_list_logic _ _ _ (Hf _ _ (sub_add_correspondence mR _ k _
       (sub_nat_rel_canonical mR) (sub_nat_rel_canonical k)))). }
  rewrite (ca_cl_map_ext _ _ Hpt) (ca_cl_map_comp (fun k => fR (mR + k)) (cl_map cid)) ca_flatten.
  have Hi : Logic.eq (iota mR (nR - mR)) (map (addn mR) (iota 0 (nR - mR))) by rewrite -iotaDl addn0.
  rewrite ca_big_seq /index_iota Hi -map_comp.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(** * Arrival sequences and arrival-time functions *)

Section Rel.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).
Notation LArr := (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrival_sequence Job dJ).

Definition CaArrRel (aR : ArrivalSequence.arrival_sequence Job) (aL : LArr) : SProp :=
  forall tR tL, SubNatRel tR tL -> ClListRel cid (aR tR) (aL tL).

Definition ca_arr_to_target (aR : ArrivalSequence.arrival_sequence Job) : LArr :=
  fun tL => cl_map cid (aR (sub_nat_to_rocq tL)).

Definition ca_arr_to_source (aL : LArr) : ArrivalSequence.arrival_sequence Job :=
  fun tR => cl_unmap cid (aL (sub_nat_to_imported tR)).

Lemma ca_arr_canonical aR : CaArrRel aR (ca_arr_to_target aR).
Proof.
  intros tR tL Ht. have E := cl_nat_logic _ _ Ht. subst tL.
  apply: coq_eq_to_imported_eq. rewrite /ca_arr_to_target sub_nat_rocq_roundtrip. reflexivity.
Qed.

Lemma ca_arr_surjective aL : CaArrRel (ca_arr_to_source aL) aL.
Proof.
  intros tR tL Ht. have E := cl_nat_logic _ _ Ht. subst tL.
  apply: coq_eq_to_imported_eq. exact (cl_map_unmap cid cid (fun _ => Logic.eq_refl _) _).
Qed.

Lemma ca_forall_arr (PR : ArrivalSequence.arrival_sequence Job -> Prop) (PL : LArr -> SProp) :
  (forall aR aL, CaArrRel aR aL -> PropSPropRel (PR aR) (PL aL)) -> PropSPropRel (forall a, PR a) (forall a, PL a).
Proof. exact (ca_forall_cover _ _ CaArrRel ca_arr_to_target ca_arr_to_source ca_arr_canonical ca_arr_surjective PR PL). Qed.

Definition CaParRel (pR : Job -> nat) (pL : Job -> Lean.Nat) : SProp := forall j, SubNatRel (pR j) (pL j).

Lemma ca_forall_par (PR : (Job -> nat) -> Prop) (PL : (Job -> Lean.Nat) -> SProp) :
  (forall pR pL, CaParRel pR pL -> PropSPropRel (PR pR) (PL pL)) -> PropSPropRel (forall p, PR p) (forall p, PL p).
Proof.
  exact (ca_forall_cover _ _ CaParRel (fun pR j => sub_nat_to_imported (pR j)) (fun pL j => sub_nat_to_rocq (pL j))
           (fun pR j => sub_nat_rel_canonical (pR j)) (fun pL j => sub_nat_rel_surjective (pL j)) PR PL).
Qed.
End Rel.

(* ------------------------------------------------------------------ *)
(** * Definitions *)

Section Defs.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).

Theorem ArrivalSequence_arrival_sequence_correspondence :
  And (forall aR : ArrivalSequence.arrival_sequence Job, CaArrRel Job aR (ca_arr_to_target Job aR))
      (forall aL : I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrival_sequence Job dJ,
         CaArrRel Job (ca_arr_to_source Job aL) aL).
Proof. exact (And_intro _ _ (ca_arr_canonical Job) (ca_arr_surjective Job)). Qed.

Theorem ArrivalSequence_jobs_arriving_at_correspondence aR aL (Ha : CaArrRel Job aR aL) tR tL (Ht : SubNatRel tR tL) :
  ClListRel cid (ArrivalSequence.jobs_arriving_at aR tR)
    (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_jobs_arriving_at Job dJ aL tL).
Proof. exact (Ha tR tL Ht). Qed.

Theorem ArrivalSequence_arrives_at_correspondence aR aL (Ha : CaArrRel Job aR aL) j tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (ArrivalSequence.arrives_at aR j tR)
    (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrives_at Job dJ aL j tL).
Proof. exact (ct_decide_bool _ _ _ (ca_mem Job j _ _ (Ha tR tL Ht))). Qed.

Theorem ArrivalSequence_arrives_in_correspondence aR aL (Ha : CaArrRel Job aR aL) j :
  PropSPropRel (ArrivalSequence.arrives_in aR j)
    (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrives_in Job dJ aL j).
Proof. apply: ct_exists_nat => tR tL Ht. exact (ca_mem Job j _ _ (Ha tR tL Ht)). Qed.

Theorem ArrivalSequence_arrival_times_are_consistent_correspondence pR pL (Hp : CaParRel Job pR pL) aR aL (Ha : CaArrRel Job aR aL) :
  PropSPropRel (ArrivalSequence.arrival_times_are_consistent pR aR)
    (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrival_times_are_consistent Job dJ pL aL).
Proof.
  apply: ct_forall_identity => j. apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (ct_bool_truth _ _ (ArrivalSequence_arrives_at_correspondence aR aL Ha j tR tL Ht)).
  exact (sub_nat_eq_correspondence _ _ _ _ (Hp j) Ht).
Qed.

Theorem ArrivalSequence_arrival_sequence_is_a_set_correspondence aR aL (Ha : CaArrRel Job aR aL) :
  PropSPropRel (ArrivalSequence.arrival_sequence_is_a_set aR)
    (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrival_sequence_is_a_set Job dJ aL).
Proof. apply: ct_forall_nat => tR tL Ht. exact (ca_uniq Job _ _ (Ha tR tL Ht)). Qed.

Theorem ArrivalSequence_has_arrived_correspondence pR pL (Hp : CaParRel Job pR pL) j tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (ArrivalSequence.has_arrived pR j tR)
    (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_has_arrived Job dJ pL j tL).
Proof. exact (ct_decide_le _ _ _ _ (Hp j) Ht). Qed.

Theorem ArrivalSequence_arrived_before_correspondence pR pL (Hp : CaParRel Job pR pL) j tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (ArrivalSequence.arrived_before pR j tR)
    (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrived_before Job dJ pL j tL).
Proof. exact (ct_decide_lt _ _ _ _ (Hp j) Ht). Qed.

Theorem ArrivalSequence_arrived_between_correspondence pR pL (Hp : CaParRel Job pR pL) j t1R t1L t2R t2L
    (H1 : SubNatRel t1R t1L) (H2 : SubNatRel t2R t2L) :
  CtBoolRel (ArrivalSequence.arrived_between pR j t1R t2R)
    (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrived_between Job dJ pL j t1L t2L).
Proof. exact (ct_bool_and _ _ _ _ (ct_decide_le _ _ _ _ H1 (Hp j)) (ct_decide_lt _ _ _ _ (Hp j) H2)). Qed.

Theorem ArrivalSequence_jobs_arrived_between_correspondence aR aL (Ha : CaArrRel Job aR aL) t1R t1L t2R t2L
    (H1 : SubNatRel t1R t1L) (H2 : SubNatRel t2R t2L) :
  ClListRel cid (ArrivalSequence.jobs_arrived_between aR t1R t2R)
    (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_jobs_arrived_between Job dJ aL t1L t2L).
Proof. exact (ca_bigcat_rel Job (fun t => aR t) (fun t => aL t) Ha t1R t1L t2R t2L H1 H2). Qed.

Lemma ca_succ_rel tR tL : SubNatRel tR tL ->
  SubNatRel tR.+1 (I.HAdd_hAdd_inst7 Lean.Nat Lean.Nat Lean.Nat (I.instHAdd_inst1 Lean.Nat I.instAddNat) tL ca_one).
Proof. intro Ht. exact (sub_imported_eq_congr Lean.Nat_succ _ _ Ht). Qed.

Theorem ArrivalSequence_jobs_arrived_up_to_correspondence aR aL (Ha : CaArrRel Job aR aL) tR tL (Ht : SubNatRel tR tL) :
  ClListRel cid (ArrivalSequence.jobs_arrived_up_to aR tR)
    (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_jobs_arrived_up_to Job dJ aL tL).
Proof.
  exact (ArrivalSequence_jobs_arrived_between_correspondence aR aL Ha 0 _ tR.+1 _
           (sub_nat_rel_canonical 0) (ca_succ_rel tR tL Ht)).
Qed.

Theorem ArrivalSequence_jobs_arrived_before_correspondence aR aL (Ha : CaArrRel Job aR aL) tR tL (Ht : SubNatRel tR tL) :
  ClListRel cid (ArrivalSequence.jobs_arrived_before aR tR)
    (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_jobs_arrived_before Job dJ aL tL).
Proof. exact (ArrivalSequence_jobs_arrived_between_correspondence aR aL Ha 0 _ tR tL (sub_nat_rel_canonical 0) Ht). Qed.
End Defs.

(* ------------------------------------------------------------------ *)
(** * Statements *)

Notation jab := ArrivalSequence_jobs_arrived_between_correspondence.

Definition src_job_arrived_between_cat (Job : eqType) : Prop :=
  ltac:(type_of_term (@ArrivalSequence.job_arrived_between_cat Job)).
Definition tgt_job_arrived_between_cat (Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_job_arrived_between_cat Job (ct_decidable_eq Job))).

Theorem ArrivalSequence_job_arrived_between_cat_correspondence (Job : eqType) :
  PropSPropRel (src_job_arrived_between_cat Job) (tgt_job_arrived_between_cat Job).
Proof.
  unfold src_job_arrived_between_cat, tgt_job_arrived_between_cat.
  apply: ca_forall_arr => aR aL Ha.
  apply: ct_forall_nat => t1R t1L H1. apply: ct_forall_nat => tR tL Ht. apply: ct_forall_nat => t2R t2L H2.
  apply: ct_imp; first exact (sub_nat_le_correspondence _ _ _ _ H1 Ht).
  apply: ct_imp; first exact (sub_nat_le_correspondence _ _ _ _ Ht H2).
  apply: ca_list_eq; first exact (jab Job _ _ Ha _ _ _ _ H1 H2).
  exact (ca_cat_rel Job _ _ _ _ (jab Job _ _ Ha _ _ _ _ H1 Ht) (jab Job _ _ Ha _ _ _ _ Ht H2)).
Qed.

Definition src_jobs_arrived_between_mem_cat (Job : eqType) : Prop :=
  ltac:(type_of_term (@ArrivalSequence.jobs_arrived_between_mem_cat Job)).
Definition tgt_jobs_arrived_between_mem_cat (Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_jobs_arrived_between_mem_cat Job (ct_decidable_eq Job))).

Theorem ArrivalSequence_jobs_arrived_between_mem_cat_correspondence (Job : eqType) :
  PropSPropRel (src_jobs_arrived_between_mem_cat Job) (tgt_jobs_arrived_between_mem_cat Job).
Proof.
  unfold src_jobs_arrived_between_mem_cat, tgt_jobs_arrived_between_mem_cat.
  apply: ca_forall_arr => aR aL Ha. apply: ct_forall_identity => j.
  apply: ct_forall_nat => t1R t1L H1. apply: ct_forall_nat => tR tL Ht. apply: ct_forall_nat => t2R t2L H2.
  apply: ct_imp; first exact (sub_nat_le_correspondence _ _ _ _ H1 Ht).
  apply: ct_imp; first exact (sub_nat_le_correspondence _ _ _ _ Ht H2).
  apply: ct_bool_eq.
  - exact (ct_decide_bool _ _ _ (ca_mem Job j _ _ (jab Job _ _ Ha _ _ _ _ H1 H2))).
  - exact (ct_decide_bool _ _ _ (ca_mem Job j _ _
      (ca_cat_rel Job _ _ _ _ (jab Job _ _ Ha _ _ _ _ H1 Ht) (jab Job _ _ Ha _ _ _ _ Ht H2)))).
Qed.

Definition src_jobs_arrived_between_sub (Job : eqType) : Prop :=
  ltac:(type_of_term (@ArrivalSequence.jobs_arrived_between_sub Job)).
Definition tgt_jobs_arrived_between_sub (Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_jobs_arrived_between_sub Job (ct_decidable_eq Job))).

Theorem ArrivalSequence_jobs_arrived_between_sub_correspondence (Job : eqType) :
  PropSPropRel (src_jobs_arrived_between_sub Job) (tgt_jobs_arrived_between_sub Job).
Proof.
  unfold src_jobs_arrived_between_sub, tgt_jobs_arrived_between_sub.
  apply: ca_forall_arr => aR aL Ha. apply: ct_forall_identity => j.
  apply: ct_forall_nat => t1R t1L H1. apply: ct_forall_nat => t1'R t1'L H1'.
  apply: ct_forall_nat => t2R t2L H2. apply: ct_forall_nat => t2'R t2'L H2'.
  apply: ct_imp; first exact (sub_nat_le_correspondence _ _ _ _ H1' H1).
  apply: ct_imp; first exact (sub_nat_le_correspondence _ _ _ _ H2 H2').
  apply: ct_imp; first exact (ca_mem Job j _ _ (jab Job _ _ Ha _ _ _ _ H1 H2)).
  exact (ca_mem Job j _ _ (jab Job _ _ Ha _ _ _ _ H1' H2')).
Qed.

Definition src_in_arrivals_implies_arrived (Job : eqType) : Prop :=
  ltac:(type_of_term (@ArrivalSequence.in_arrivals_implies_arrived Job)).
Definition tgt_in_arrivals_implies_arrived (Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_in_arrivals_implies_arrived Job (ct_decidable_eq Job))).

Theorem ArrivalSequence_in_arrivals_implies_arrived_correspondence (Job : eqType) :
  PropSPropRel (src_in_arrivals_implies_arrived Job) (tgt_in_arrivals_implies_arrived Job).
Proof.
  unfold src_in_arrivals_implies_arrived, tgt_in_arrivals_implies_arrived.
  apply: ca_forall_arr => aR aL Ha. apply: ct_forall_identity => j.
  apply: ct_forall_nat => t1R t1L H1. apply: ct_forall_nat => t2R t2L H2.
  apply: ct_imp; first exact (ca_mem Job j _ _ (jab Job _ _ Ha _ _ _ _ H1 H2)).
  exact (ArrivalSequence_arrives_in_correspondence Job aR aL Ha j).
Qed.

Definition src_in_arrivals_implies_arrived_between (Job : eqType) : Prop :=
  ltac:(type_of_term (@ArrivalSequence.in_arrivals_implies_arrived_between Job)).
Definition tgt_in_arrivals_implies_arrived_between (Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_in_arrivals_implies_arrived_between Job (ct_decidable_eq Job))).

Theorem ArrivalSequence_in_arrivals_implies_arrived_between_correspondence (Job : eqType) :
  PropSPropRel (src_in_arrivals_implies_arrived_between Job) (tgt_in_arrivals_implies_arrived_between Job).
Proof.
  unfold src_in_arrivals_implies_arrived_between, tgt_in_arrivals_implies_arrived_between.
  apply: ca_forall_par => pR pL Hp. apply: ca_forall_arr => aR aL Ha.
  apply: ct_imp; first exact (ArrivalSequence_arrival_times_are_consistent_correspondence Job pR pL Hp aR aL Ha).
  apply: ct_forall_identity => j.
  apply: ct_forall_nat => t1R t1L H1. apply: ct_forall_nat => t2R t2L H2.
  apply: ct_imp; first exact (ca_mem Job j _ _ (jab Job _ _ Ha _ _ _ _ H1 H2)).
  exact (ct_bool_truth _ _ (ArrivalSequence_arrived_between_correspondence Job pR pL Hp j _ _ _ _ H1 H2)).
Qed.

Definition src_in_arrivals_implies_arrived_before (Job : eqType) : Prop :=
  ltac:(type_of_term (@ArrivalSequence.in_arrivals_implies_arrived_before Job)).
Definition tgt_in_arrivals_implies_arrived_before (Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_in_arrivals_implies_arrived_before Job (ct_decidable_eq Job))).

Theorem ArrivalSequence_in_arrivals_implies_arrived_before_correspondence (Job : eqType) :
  PropSPropRel (src_in_arrivals_implies_arrived_before Job) (tgt_in_arrivals_implies_arrived_before Job).
Proof.
  unfold src_in_arrivals_implies_arrived_before, tgt_in_arrivals_implies_arrived_before.
  apply: ca_forall_par => pR pL Hp. apply: ca_forall_arr => aR aL Ha.
  apply: ct_imp; first exact (ArrivalSequence_arrival_times_are_consistent_correspondence Job pR pL Hp aR aL Ha).
  apply: ct_forall_identity => j. apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (ca_mem Job j _ _ (ArrivalSequence_jobs_arrived_before_correspondence Job aR aL Ha tR tL Ht)).
  exact (ct_bool_truth _ _ (ArrivalSequence_arrived_before_correspondence Job pR pL Hp j tR tL Ht)).
Qed.

Definition src_arrived_between_implies_in_arrivals (Job : eqType) : Prop :=
  ltac:(type_of_term (@ArrivalSequence.arrived_between_implies_in_arrivals Job)).
Definition tgt_arrived_between_implies_in_arrivals (Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrived_between_implies_in_arrivals Job (ct_decidable_eq Job))).

Theorem ArrivalSequence_arrived_between_implies_in_arrivals_correspondence (Job : eqType) :
  PropSPropRel (src_arrived_between_implies_in_arrivals Job) (tgt_arrived_between_implies_in_arrivals Job).
Proof.
  unfold src_arrived_between_implies_in_arrivals, tgt_arrived_between_implies_in_arrivals.
  apply: ca_forall_par => pR pL Hp. apply: ca_forall_arr => aR aL Ha.
  apply: ct_imp; first exact (ArrivalSequence_arrival_times_are_consistent_correspondence Job pR pL Hp aR aL Ha).
  apply: ct_forall_identity => j.
  apply: ct_forall_nat => t1R t1L H1. apply: ct_forall_nat => t2R t2L H2.
  apply: ct_imp; first exact (ArrivalSequence_arrives_in_correspondence Job aR aL Ha j).
  apply: ct_imp; first exact (ct_bool_truth _ _ (ArrivalSequence_arrived_between_correspondence Job pR pL Hp j _ _ _ _ H1 H2)).
  exact (ca_mem Job j _ _ (jab Job _ _ Ha _ _ _ _ H1 H2)).
Qed.

Definition src_arrivals_uniq (Job : eqType) : Prop :=
  ltac:(type_of_term (@ArrivalSequence.arrivals_uniq Job)).
Definition tgt_arrivals_uniq (Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrivals_uniq Job (ct_decidable_eq Job))).

Theorem ArrivalSequence_arrivals_uniq_correspondence (Job : eqType) :
  PropSPropRel (src_arrivals_uniq Job) (tgt_arrivals_uniq Job).
Proof.
  unfold src_arrivals_uniq, tgt_arrivals_uniq.
  apply: ca_forall_par => pR pL Hp. apply: ca_forall_arr => aR aL Ha.
  apply: ct_imp; first exact (ArrivalSequence_arrival_times_are_consistent_correspondence Job pR pL Hp aR aL Ha).
  apply: ct_imp; first exact (ArrivalSequence_arrival_sequence_is_a_set_correspondence Job aR aL Ha).
  apply: ct_forall_nat => t1R t1L H1. apply: ct_forall_nat => t2R t2L H2.
  exact (ca_uniq Job _ _ (jab Job _ _ Ha _ _ _ _ H1 H2)).
Qed.
