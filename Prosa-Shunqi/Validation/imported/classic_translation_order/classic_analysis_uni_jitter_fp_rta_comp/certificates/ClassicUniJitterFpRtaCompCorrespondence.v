From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq fintype bigop div.
From prosa Require Import classic.util.notation util.sum classic.util.div_mod classic.model.time classic.model.arrival.basic.arrival_sequence classic.model.arrival.basic.task classic.model.arrival.basic.job classic.model.arrival.basic.task_arrival classic.model.arrival.jitter.arrival_sequence classic.model.priority classic.model.schedule.uni.schedule classic.model.schedule.uni.response_time classic.model.schedule.uni.jitter.schedule classic.model.schedule.uni.jitter.platform classic.analysis.uni.jitter.workload_bound_fp classic.util.fixedpoint classic.model.arrival.jitter.job classic.model.schedule.uni.schedulability classic.analysis.uni.jitter.fp_rta_theory classic.analysis.uni.jitter.fp_rta_comp.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedClassicUniJitterFpRtaComp.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence ClassicUniJitterFpRtaCompBase ClassicUniJitterFpRtaCompList.

Module I := ImportedClassicUniJitterFpRtaComp.
Local Open Scope nat_scope.

(** Certificates for [classic/analysis/uni/jitter/fp_rta_comp.v] (ProsaBuddy classic, commit f692cb7).

    Inputs: the job and task types are [eqType]s, identified, with the Lean [DecidableEq] instances given by the
    eqTypes' decision procedures ([ct_decidable_eq]); [job_task] identified; times by [SubNatRel]; job/task parameters
    (including jitters) pointwise through [SubNatRel]; task sequences elementwise; FP policies pointwise on Booleans;
    arrival sequences pointwise on related times; uniprocessor schedules pointwise through the option map; all with two-way
    totals.  Computed results: [option nat] through the canonical Nat map ([cjc_onat]); (task, response-time) pairs by
    their components ([cjc_pair], two-way totals through [cjc_unpair]); [option (seq _)] elementwise ([cjc_olist]).
    [iter_fixpoint] over [nat] against its Lean counterpart by induction, one Lean step at a time by conversion;
    [all]/[pmap] against [List.all]/[List.filterMap] by induction (one step by conversion); the section-local
    [is_valid_bound] against its Lean counterpart by case analysis; [\In] against [optIn].  The jitter-aware FP workload
    bound, platform, schedule and response-time notions as in the accepted classic certificates (re-bound below).

    Statements: the source side is the exact elaborated type of the pinned lemma (via [type of]; the source proof is not
    used); every input is quantified and covered in both directions. *)

Ltac type_of_term t := let T := type of t in exact T.
Notation cid := (fun z => z).

(* ------------------------------------------------------------------ *)
(** * Helpers (re-bound to this export from the accepted classic certificates) *)

(** Base definitions (as in the accepted classic base library), provided here when this export's library lacks them. *)

(* ------------------------------------------------------------------ *)
(** * Generic covers and helpers *)

Lemma cjc_forall_cover (A B : Type) (Rel : A -> B -> SProp) (toB : A -> B) (toA : B -> A)
    (HB : forall a, Rel a (toB a)) (HA : forall b, Rel (toA b) b) (PR : A -> Prop) (PL : B -> SProp) :
  (forall a b, Rel a b -> PropSPropRel (PR a) (PL b)) -> PropSPropRel (forall a, PR a) (forall b, PL b).
Proof.
  intro H. apply prop_sprop_rel_intro.
  - intros HR b. exact (prop_to_sprop _ _ (H _ _ (HA b)) (HR _)).
  - intro HL. apply strictly_inhabits. intro a. exact (sprop_to_prop _ _ (H _ _ (HB a)) (HL _)).
Qed.

Lemma cjc_false_rel : PropSPropRel Logic.False I.False.
Proof.
  apply prop_sprop_rel_intro.
  - exact ct_coq_false_to_target.
  - exact ct_target_false_to_strict.
Qed.

Lemma cjc_ne (T : Type) (x y : T) : PropSPropRel (x <> y) (I.Ne T x y).
Proof. exact (ct_imp _ _ _ _ (ct_eq_rel T x y) cjc_false_rel). Qed.

Lemma cjc_mem (T : eqType) x s sL : ClListRel cid s sL ->
  PropSPropRel (x \in s) (I.Membership_mem T (I.List T) (I.List_instMembership T) sL x).
Proof. exact (cl_mem_rel_list T T cid cid (fun _ => Logic.eq_refl _) x s sL). Qed.

Lemma cjc_uniq (T : eqType) s sL : ClListRel cid s sL -> PropSPropRel (uniq s) (I.List_Nodup T sL).
Proof. exact (cl_uniq_rel_list T T cid cid (fun _ => Logic.eq_refl _) (fun _ => Logic.eq_refl _) s sL). Qed.

Lemma cjc_unmap_rel (T : Type) (l : I.List T) : ClListRel cid (cl_unmap cid l) l.
Proof. apply: coq_eq_to_imported_eq. exact (cl_map_unmap cid cid (fun _ => Logic.eq_refl _) l). Qed.

Lemma cjc_cl_map_inj (T : Type) (s1 s2 : seq T) : Logic.eq (cl_map cid s1) (cl_map cid s2) -> Logic.eq s1 s2.
Proof.
  intro E. rewrite -(cl_unmap_map cid cid (fun _ => Logic.eq_refl _) s1) -(cl_unmap_map cid cid (fun _ => Logic.eq_refl _) s2).
  by rewrite E.
Qed.

Lemma cjc_succ_rel nR nL : SubNatRel nR nL ->
  SubNatRel nR.+1 (I.HAdd_hAdd_inst7 Lean.Nat Lean.Nat Lean.Nat (I.instHAdd_inst1 Lean.Nat I.instAddNat) nL
                     (I.OfNat_ofNat_inst1 Lean.Nat 1 (I.instOfNatNat 1))).
Proof. intro Hn. exact (sub_imported_eq_congr Lean.Nat_succ _ _ Hn). Qed.

(* ------------------------------------------------------------------ *)
(** * Big concatenation over a half-open interval (as in the accepted arrival_sequence certificate) *)

Lemma cjc_forall_list (T : Type) (PR : seq T -> Prop) (PL : I.List T -> SProp) :
  (forall sR sL, ClListRel (B := T) cid sR sL -> PropSPropRel (PR sR) (PL sL)) -> PropSPropRel (forall s, PR s) (forall s, PL s).
Proof.
  exact (cjc_forall_cover _ _ (fun sR sL => ClListRel (B := T) cid sR sL) (cl_map cid) (cl_unmap cid)
           (fun s => @Lean.eq_refl _ _) (fun l => cjc_unmap_rel T l) PR PL).
Qed.

Definition CjcParRel (T : Type) (pR : T -> nat) (pL : T -> Lean.Nat) : SProp := forall x, SubNatRel (pR x) (pL x).

Lemma cjc_forall_par (T : Type) (PR : (T -> nat) -> Prop) (PL : (T -> Lean.Nat) -> SProp) :
  (forall pR pL, CjcParRel T pR pL -> PropSPropRel (PR pR) (PL pL)) -> PropSPropRel (forall p, PR p) (forall p, PL p).
Proof.
  exact (cjc_forall_cover _ _ (CjcParRel T) (fun pR j => sub_nat_to_imported (pR j)) (fun pL j => sub_nat_to_rocq (pL j))
           (fun pR j => sub_nat_rel_canonical (pR j)) (fun pL j => sub_nat_rel_surjective (pL j)) PR PL).
Qed.

Fixpoint cjc_natl (s : seq nat) : I.List_inst1 Lean.Nat :=
  match s with [::] => I.List_nil_inst1 _ | x :: s' => I.List_cons_inst1 _ (sub_nat_to_imported x) (cjc_natl s') end.

Definition cjc_one : Lean.Nat := I.OfNat_ofNat_inst1 Lean.Nat 1 (I.instOfNatNat 1).

Lemma cjc_iota_range : forall n s,
  Logic.eq (I.List_range' (sub_nat_to_imported s) (sub_nat_to_imported n) cjc_one) (cjc_natl (iota s n)).
Proof.
  elim => [|n IH] s; first reflexivity.
  change (Logic.eq (I.List_cons_inst1 _ (sub_nat_to_imported s)
      (I.List_range' (sub_nat_to_imported (S s)) (sub_nat_to_imported n) cjc_one))
    (I.List_cons_inst1 _ (sub_nat_to_imported s) (cjc_natl (iota (S s) n)))).
  by rewrite IH.
Qed.

Lemma cjc_map_natl {B : Type} (f : Lean.Nat -> B) : forall s,
  Logic.eq (I.List_map_inst1 Lean.Nat B f (cjc_natl s)) (cl_map (fun k => f (sub_nat_to_imported k)) s).
Proof.
  elim => [|k s IH] //=.
  change (Logic.eq (I.List_cons B (f (sub_nat_to_imported k)) (I.List_map_inst1 Lean.Nat B f (cjc_natl s)))
                   (I.List_cons B (f (sub_nat_to_imported k)) (cl_map (fun k => f (sub_nat_to_imported k)) s))).
  by rewrite IH.
Qed.

Lemma cjc_cl_map_comp {A B C : Type} (f : A -> B) (g : B -> C) : forall s : seq A,
  Logic.eq (cl_map (fun x => g (f x)) s) (cl_map g (map f s)).
Proof. elim => [|x s IH] //=. by rewrite IH. Qed.

Lemma cjc_cl_map_ext {A B : Type} (f g : A -> B) (H : forall x, Logic.eq (f x) (g x)) : forall s : seq A,
  Logic.eq (cl_map f s) (cl_map g s).
Proof. elim => [|x s IH] //=. by rewrite H IH. Qed.

Lemma cjc_cl_append {A : Type} : forall s1 s2 : seq A,
  Logic.eq (cl_map cid (s1 ++ s2)) (I.List_append A (cl_map cid s1) (cl_map cid s2)).
Proof.
  elim => [|x s1 IH] s2; first reflexivity.
  change (Logic.eq (I.List_cons A x (cl_map cid (s1 ++ s2))) (I.List_cons A x (I.List_append A (cl_map cid s1) (cl_map cid s2)))).
  by rewrite IH.
Qed.

Lemma cjc_flatten {A : Type} : forall L : seq (seq A),
  Logic.eq (I.List_flatten A (cl_map (cl_map cid) L)) (cl_map cid (flatten L)).
Proof.
  elim => [|s L IH] //=.
  change (Logic.eq (I.List_append A (cl_map cid s) (I.List_flatten A (cl_map (cl_map cid) L))) (cl_map cid (s ++ flatten L))).
  rewrite IH cjc_cl_append. reflexivity.
Qed.

Lemma cjc_big_seq {A : Type} (F : nat -> seq A) : forall s : seq nat,
  Logic.eq (\big[cat/[::]]_(i <- s) F i) (flatten (map F s)).
Proof. elim => [|x s IH]; first by rewrite big_nil. by rewrite big_cons IH. Qed.

Definition CjcFamRel (A : Type) (fR : nat -> seq A) (fL : Lean.Nat -> I.List A) : SProp :=
  forall nR nL, SubNatRel nR nL -> ClListRel cid (fR nR) (fL nL).

Lemma cjc_bigcat_rel (A : Type) fR fL (Hf : CjcFamRel A fR fL) mR mL nR nL :
  SubNatRel mR mL -> SubNatRel nR nL ->
  ClListRel cid (\big[cat/[::]]_(mR <= t < nR) fR t) (I.Prosa_Util_Notation_bigCat A mL nL fL).
Proof.
  intros Hm Hn. have E1 := cl_nat_logic _ _ Hm. have E2 := cl_nat_logic _ _ Hn. subst mL nL.
  apply: coq_eq_to_imported_eq. apply: Logic.eq_sym.
  rewrite (imported_eq_to_coq_eq _ _ (I.Prosa_Validation_ClassicUniJitterFpRtaCompInterface_bigCat_range'
             A (sub_nat_to_imported mR) (sub_nat_to_imported nR) fL)).
  have Hd : Logic.eq (I.HSub_hSub_inst7 Lean.Nat Lean.Nat Lean.Nat (I.instHSub_inst1 Lean.Nat I.instSubNat)
                       (sub_nat_to_imported nR) (sub_nat_to_imported mR)) (sub_nat_to_imported (nR - mR)) :=
    ct_sub_canonical nR mR.
  rewrite Hd.
  change (I.OfNat_ofNat_inst1 Lean.Nat 0 (I.instOfNatNat 0)) with (sub_nat_to_imported 0).
  rewrite (cjc_iota_range (nR - mR) 0) cjc_map_natl. cbv beta.
  have Hpt : forall k, Logic.eq
      (fL (I.HAdd_hAdd_inst7 Lean.Nat Lean.Nat Lean.Nat (I.instHAdd_inst1 Lean.Nat I.instAddNat)
             (sub_nat_to_imported mR) (sub_nat_to_imported k)))
      (cl_map cid (fR (mR + k))).
  { intro k. exact (cl_list_logic _ _ _ (Hf _ _ (sub_add_correspondence mR _ k _
       (sub_nat_rel_canonical mR) (sub_nat_rel_canonical k)))). }
  rewrite (cjc_cl_map_ext _ _ Hpt) (cjc_cl_map_comp (fun k => fR (mR + k)) (cl_map cid)) cjc_flatten.
  have Hi : Logic.eq (iota mR (nR - mR)) (map (addn mR) (iota 0 (nR - mR))) by rewrite -iotaDl addn0.
  rewrite cjc_big_seq /index_iota Hi -map_comp.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(** * Arrival sequences and parameters *)

Section Rel.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).
Notation LArr := (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrival_sequence Job dJ).

Definition CjcArrRel (aR : ArrivalSequence.arrival_sequence Job) (aL : LArr) : SProp :=
  forall tR tL, SubNatRel tR tL -> ClListRel cid (aR tR) (aL tL).

Definition cjc_arr_to_target (aR : ArrivalSequence.arrival_sequence Job) : LArr :=
  fun tL => cl_map cid (aR (sub_nat_to_rocq tL)).

Definition cjc_arr_to_source (aL : LArr) : ArrivalSequence.arrival_sequence Job :=
  fun tR => cl_unmap cid (aL (sub_nat_to_imported tR)).

Lemma cjc_arr_canonical aR : CjcArrRel aR (cjc_arr_to_target aR).
Proof.
  intros tR tL Ht. have E := cl_nat_logic _ _ Ht. subst tL.
  apply: coq_eq_to_imported_eq. rewrite /cjc_arr_to_target sub_nat_rocq_roundtrip. reflexivity.
Qed.

Lemma cjc_arr_surjective aL : CjcArrRel (cjc_arr_to_source aL) aL.
Proof.
  intros tR tL Ht. have E := cl_nat_logic _ _ Ht. subst tL.
  apply: coq_eq_to_imported_eq. exact (cl_map_unmap cid cid (fun _ => Logic.eq_refl _) _).
Qed.

Lemma cjc_forall_arr (PR : ArrivalSequence.arrival_sequence Job -> Prop) (PL : LArr -> SProp) :
  (forall aR aL, CjcArrRel aR aL -> PropSPropRel (PR aR) (PL aL)) -> PropSPropRel (forall a, PR a) (forall a, PL a).
Proof. exact (cjc_forall_cover _ _ CjcArrRel cjc_arr_to_target cjc_arr_to_source cjc_arr_canonical cjc_arr_surjective PR PL). Qed.

End Rel.

(** The imported [ArrivalSequence] definitions this file's statements mention, related on related inputs. *)
Section ArrivalDefs.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).

Lemma cjc_arrives_in aR aL (Ha : CjcArrRel Job aR aL) j :
  PropSPropRel (ArrivalSequence.arrives_in aR j)
    (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrives_in Job dJ aL j).
Proof. apply: ct_exists_nat => tR tL Ht. exact (cjc_mem Job j _ _ (Ha tR tL Ht)). Qed.

Lemma cjc_consistent pR pL (Hp : CjcParRel Job pR pL) aR aL (Ha : CjcArrRel Job aR aL) :
  PropSPropRel (ArrivalSequence.arrival_times_are_consistent pR aR)
    (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrival_times_are_consistent Job dJ pL aL).
Proof.
  apply: ct_forall_identity => j. apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (ct_bool_truth _ _ (ct_decide_bool _ _ _ (cjc_mem Job j _ _ (Ha tR tL Ht)))).
  exact (sub_nat_eq_correspondence _ _ _ _ (Hp j) Ht).
Qed.

Lemma cjc_is_a_set aR aL (Ha : CjcArrRel Job aR aL) :
  PropSPropRel (ArrivalSequence.arrival_sequence_is_a_set aR)
    (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrival_sequence_is_a_set Job dJ aL).
Proof. apply: ct_forall_nat => tR tL Ht. exact (cjc_uniq Job _ _ (Ha tR tL Ht)). Qed.

End ArrivalDefs.

Section ArrivalDefs2.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).

Lemma cjc_arrives_at aR aL (Ha : CjcArrRel Job aR aL) j tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (ArrivalSequence.arrives_at aR j tR)
    (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrives_at Job dJ aL j tL).
Proof. exact (ct_decide_bool _ _ _ (cjc_mem Job j _ _ (Ha tR tL Ht))). Qed.

End ArrivalDefs2.

Fixpoint cjc_snatl (s : seq nat) : I.List_inst1 Lean.Nat :=
  match s with [::] => I.List_nil_inst1 _ | x :: s' => I.List_cons_inst1 _ (sub_nat_to_imported x) (cjc_snatl s') end.

Lemma cjc_siota_range : forall n s,
  Logic.eq (I.List_range' (sub_nat_to_imported s) (sub_nat_to_imported n) (Lean.Nat_succ Lean.Nat_zero)) (cjc_snatl (iota s n)).
Proof.
  elim => [|n IH] s; first reflexivity.
  change (Logic.eq (I.List_cons_inst1 _ (sub_nat_to_imported s)
      (I.List_range' (sub_nat_to_imported (S s)) (sub_nat_to_imported n) (Lean.Nat_succ Lean.Nat_zero)))
    (I.List_cons_inst1 _ (sub_nat_to_imported s) (cjc_snatl (iota (S s) n)))).
  by rewrite IH.
Qed.

Lemma cjc_foldr_add (f : Lean.Nat -> Lean.Nat) (g : nat -> nat) (Hf : forall k, Logic.eq (f (sub_nat_to_imported k)) (sub_nat_to_imported (g k))) :
  forall s, Logic.eq (I.List_foldr_inst3 Lean.Nat Lean.Nat Lean.Nat_add Lean.Nat_zero (I.List_map_inst3 Lean.Nat Lean.Nat f (cjc_snatl s)))
                     (sub_nat_to_imported (foldr addn 0 (map g s))).
Proof.
  elim => [|k s IH] //=.
  change (Logic.eq (Lean.Nat_add (f (sub_nat_to_imported k))
            (I.List_foldr_inst3 Lean.Nat Lean.Nat Lean.Nat_add Lean.Nat_zero (I.List_map_inst3 Lean.Nat Lean.Nat f (cjc_snatl s))))
         (sub_nat_to_imported (g k + foldr addn 0 (map g s)))).
  rewrite IH Hf. exact (imported_eq_to_coq_eq _ _ (sub_add_canonical _ _)).
Qed.

Lemma cjc_big_fold (xs : seq nat) (F : nat -> nat) : Logic.eq (\sum_(i <- xs) F i) (foldr addn 0 (map F xs)).
Proof. elim: xs => [|x xs IH]; first by rewrite big_nil. by rewrite big_cons IH. Qed.

Definition CjcFunRel (FR : nat -> nat) (FL : Lean.Nat -> Lean.Nat) : SProp :=
  forall kR kL, SubNatRel kR kL -> SubNatRel (FR kR) (FL kL).

Lemma cjc_fun_canonical FR FL (HF : CjcFunRel FR FL) k : Logic.eq (FL (sub_nat_to_imported k)) (sub_nat_to_imported (FR k)).
Proof. exact (cl_nat_logic _ _ (HF _ _ (sub_nat_rel_canonical k))). Qed.

Lemma cjc_nat_sub_canonical (a b : nat) :
  Logic.eq (I.Nat_sub (sub_nat_to_imported a) (sub_nat_to_imported b)) (sub_nat_to_imported (a - b)).
Proof.
  elim: b => [|b IH]; first by rewrite subn0.
  change (Logic.eq (I.Nat_pred (I.Nat_sub (sub_nat_to_imported a) (sub_nat_to_imported b))) (sub_nat_to_imported (a - b.+1))).
  rewrite IH subnS. case: (a - b) => [|k]; reflexivity.
Qed.

Lemma cjc_ico mR mL nR nL FR FL (Hm : SubNatRel mR mL) (Hn : SubNatRel nR nL) (HF : CjcFunRel FR FL) :
  SubNatRel (\sum_(mR <= i < nR) FR i)
    (I.List_foldr_inst3 Lean.Nat Lean.Nat Lean.Nat_add Lean.Nat_zero
       (I.List_map_inst3 Lean.Nat Lean.Nat FL (I.List_range' mL (I.Nat_sub nL mL) (Lean.Nat_succ Lean.Nat_zero)))).
Proof.
  rewrite (cl_nat_logic _ _ Hm) (cl_nat_logic _ _ Hn).
  have -> : Logic.eq (I.Nat_sub (sub_nat_to_imported nR) (sub_nat_to_imported mR)) (sub_nat_to_imported (nR - mR))
    := cjc_nat_sub_canonical nR mR.
  rewrite cjc_siota_range.
  apply: coq_eq_to_imported_eq. apply: Logic.eq_sym. rewrite (cjc_foldr_add FL FR (cjc_fun_canonical FR FL HF)).
  by rewrite cjc_big_fold.
Qed.

(* ------------------------------------------------------------------ *)
(** * Options and uniprocessor schedules *)

(** Transport along the target equality (definitional UIP), as in the accepted global schedule certificate. *)
Definition cjc_tr {A : Type} {x y : A} (E : Lean.eq x y) (P : A -> Type) (h : P x) : P y :=
  match E in Lean.eq _ z return P z with Lean.eq_refl => h end.

Definition cjc_trs {A : Type} {x y : A} (E : Lean.eq x y) (P : A -> SProp) (h : P x) : P y :=
  match E in Lean.eq _ z return P z with Lean.eq_refl => h end.

Lemma cjc_opt_inj (A : Type) (o1 o2 : option A) : Logic.eq (cl_opt o1) (cl_opt o2) -> Logic.eq o1 o2.
Proof. intro E. by rewrite -(cl_unopt_opt o1) -(cl_unopt_opt o2) E. Qed.

Lemma cjc_opt_eqb_rel (A : eqType) (o1 o2 : option A) :
  PropSPropRel (is_true (o1 == o2)) (Lean.eq (cl_opt o1) (cl_opt o2)).
Proof.
  apply prop_sprop_rel_intro.
  - move=> /eqP E. rewrite E. exact (@Lean.eq_refl _ _).
  - intro E. apply strictly_inhabits. apply/eqP. exact (cjc_opt_inj A o1 o2 (imported_eq_to_coq_eq _ _ E)).
Qed.

Section Sched.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).
Notation LSched := (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job dJ).

Definition CjcSchedRel (sR : UniprocessorSchedule.schedule Job) (sL : LSched) : SProp :=
  forall tR tL, SubNatRel tR tL -> Lean.eq (cl_opt (sR tR)) (sL tL).

Definition cjc_sched_to_target (sR : UniprocessorSchedule.schedule Job) : LSched := fun tL => cl_opt (sR (sub_nat_to_rocq tL)).
Definition cjc_sched_to_source (sL : LSched) : UniprocessorSchedule.schedule Job := fun tR => cl_unopt (sL (sub_nat_to_imported tR)).

Lemma cjc_sched_canonical sR : CjcSchedRel sR (cjc_sched_to_target sR).
Proof. intros tR tL Ht. apply: coq_eq_to_imported_eq. by rewrite /cjc_sched_to_target (cl_nat_input _ _ Ht). Qed.

Lemma cjc_sched_surjective sL : CjcSchedRel (cjc_sched_to_source sL) sL.
Proof.
  intros tR tL Ht. apply: coq_eq_to_imported_eq. rewrite /cjc_sched_to_source cl_opt_unopt.
  by rewrite (cl_nat_logic _ _ Ht).
Qed.

Lemma cjc_forall_sched (PR : UniprocessorSchedule.schedule Job -> Prop) (PL : LSched -> SProp) :
  (forall sR sL, CjcSchedRel sR sL -> PropSPropRel (PR sR) (PL sL)) -> PropSPropRel (forall s, PR s) (forall s, PL s).
Proof. exact (cjc_forall_cover _ _ CjcSchedRel cjc_sched_to_target cjc_sched_to_source cjc_sched_canonical cjc_sched_surjective PR PL). Qed.

End Sched.

(* ------------------------------------------------------------------ *)
(** * Definitions *)

Lemma cjc_US_schedule (Job : eqType) :
  And (forall sR : UniprocessorSchedule.schedule Job, CjcSchedRel Job sR (cjc_sched_to_target Job sR))
      (forall sL : I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job (ct_decidable_eq Job), CjcSchedRel Job (cjc_sched_to_source Job sL) sL).
Proof. exact (And_intro _ _ (cjc_sched_canonical Job) (cjc_sched_surjective Job)). Qed.

Section USchedDefs.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).
Variables (sR : UniprocessorSchedule.schedule Job) (sL : I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job dJ).
Hypothesis Hs : CjcSchedRel Job sR sL.

Lemma cjc_US_scheduled_at j tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (UniprocessorSchedule.scheduled_at sR j tR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_scheduled_at Job dJ sL j tL).
Proof.
  apply: ct_decide_bool.
  exact (cjc_tr (Hs tR tL Ht) (fun z => PropSPropRel (sR tR == Some j) (Lean.eq z (cl_opt (Some j))))
           (cjc_opt_eqb_rel Job (sR tR) (Some j))).
Qed.

Lemma cjc_US_service_at j tR tL (Ht : SubNatRel tR tL) :
  SubNatRel (UniprocessorSchedule.service_at sR j tR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_service_at Job dJ sL j tL).
Proof. exact (ct_bool_to_nat _ _ (cjc_US_scheduled_at j tR tL Ht)). Qed.

Lemma cjc_service_at_fun j : CjcFunRel (fun t => UniprocessorSchedule.service_at sR j t) (fun t => I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_service_at Job dJ sL j t).
Proof. intros kR kL Hk. exact (cjc_US_service_at j kR kL Hk). Qed.

Lemma cjc_US_service_during j t1R t1L (H1 : SubNatRel t1R t1L) t2R t2L (H2 : SubNatRel t2R t2L) :
  SubNatRel (UniprocessorSchedule.service_during sR j t1R t2R) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_service_during Job dJ sL j t1L t2L).
Proof. exact (cjc_ico _ _ _ _ _ _ H1 H2 (cjc_service_at_fun j)). Qed.

Lemma cjc_US_service j tR tL (Ht : SubNatRel tR tL) :
  SubNatRel (UniprocessorSchedule.service sR j tR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_service Job dJ sL j tL).
Proof. exact (cjc_US_service_during j 0 _ (sub_nat_rel_canonical 0) tR tL Ht). Qed.

Lemma cjc_US_completed_by cR cL (Hc : CjcParRel Job cR cL) j tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (UniprocessorSchedule.completed_by cR sR j tR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_completed_by Job dJ cL sL j tL).
Proof. exact (ct_decide_le _ _ _ _ (Hc j) (cjc_US_service j tR tL Ht)). Qed.

Lemma cjc_US_jobs_come_from_arrival_sequence arrR arrL (Harr : CjcArrRel Job arrR arrL) :
  PropSPropRel (UniprocessorSchedule.jobs_come_from_arrival_sequence sR arrR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_jobs_come_from_arrival_sequence Job dJ sL arrL).
Proof.
  apply: ct_forall_identity => j. apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (ct_bool_truth _ _ (cjc_US_scheduled_at j tR tL Ht)).
  exact (cjc_arrives_in Job arrR arrL Harr j).
Qed.

Lemma cjc_US_completed_jobs_dont_execute cR cL (Hc : CjcParRel Job cR cL) :
  PropSPropRel (UniprocessorSchedule.completed_jobs_dont_execute cR sR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_completed_jobs_dont_execute Job dJ cL sL).
Proof.
  apply: ct_forall_identity => j. apply: ct_forall_nat => tR tL Ht.
  exact (sub_nat_le_correspondence _ _ _ _ (cjc_US_service j tR tL Ht) (Hc j)).
Qed.

End USchedDefs.

(* ------------------------------------------------------------------ *)
(** * Sequence sums against [sumSeq] / [sumFiltered] (as in the accepted v0.6 request-bound-function certificates) *)

Section SeqSums.
Variable X : Type.
Variable FR : X -> nat.
Variable FL : X -> Lean.Nat.
Hypothesis HF : forall x, SubNatRel (FR x) (FL x).

Lemma cjc_sum_canonical (xs : seq X) :
  SubNatRel (\sum_(x <- xs) FR x) (I.Prosa_Util_Sum_sumSeq X (cl_map cid xs) FL).
Proof.
  induction xs as [|x xs IH].
  - rewrite big_nil.
    exact (sub_imported_eq_sym _ _ (I.Prosa_Validation_ClassicUniJitterFpRtaCompInterface_production_sumSeq_nil X FL)).
  - rewrite big_cons. cbn [cl_map].
    refine (sub_imported_eq_trans _ _ _ _ (sub_imported_eq_sym _ _
      (I.Prosa_Validation_ClassicUniJitterFpRtaCompInterface_production_sumSeq_cons X FL x (cl_map cid xs)))).
    exact (sub_add_correspondence _ _ _ _ (HF x) IH).
Qed.

Lemma cjc_sum_rel xsR xsL : ClListRel cid xsR xsL ->
  SubNatRel (\sum_(x <- xsR) FR x) (I.Prosa_Util_Sum_sumSeq X xsL FL).
Proof.
  intro Hxs.
  exact (sub_imported_eq_trans _ _ _ (cjc_sum_canonical xsR)
    (sub_imported_eq_congr (fun l => I.Prosa_Util_Sum_sumSeq X l FL) _ _ Hxs)).
Qed.

Variable PR : X -> bool.
Variable PL : X -> I.Bool.
Hypothesis HP : forall x, CtBoolRel (PR x) (PL x).

Lemma cjc_sum_filtered_canonical (xs : seq X) :
  SubNatRel (\sum_(x <- xs | PR x) FR x) (I.Prosa_Util_Sum_sumFiltered X (cl_map cid xs) PL FL).
Proof.
  induction xs as [|x xs IH].
  - rewrite big_nil.
    exact (sub_imported_eq_sym _ _ (I.Prosa_Validation_ClassicUniJitterFpRtaCompInterface_production_sumFiltered_nil X PL FL)).
  - rewrite big_cons. cbn [cl_map].
    have Hx := HP x. unfold CtBoolRel in Hx.
    destruct (PR x).
    + refine (sub_imported_eq_trans _ _ _ _ (sub_imported_eq_sym _ _
        (I.Prosa_Validation_ClassicUniJitterFpRtaCompInterface_production_sumFiltered_cons_true
          X PL FL x (cl_map cid xs) (sub_imported_eq_sym _ _ Hx)))).
      exact (sub_add_correspondence _ _ _ _ (HF x) IH).
    + exact (sub_imported_eq_trans _ _ _ IH (sub_imported_eq_sym _ _
        (I.Prosa_Validation_ClassicUniJitterFpRtaCompInterface_production_sumFiltered_cons_false
          X PL FL x (cl_map cid xs) (sub_imported_eq_sym _ _ Hx)))).
Qed.

Lemma cjc_sum_filtered_rel xsR xsL : ClListRel cid xsR xsL ->
  SubNatRel (\sum_(x <- xsR | PR x) FR x) (I.Prosa_Util_Sum_sumFiltered X xsL PL FL).
Proof.
  intro Hxs.
  exact (sub_imported_eq_trans _ _ _ (cjc_sum_filtered_canonical xsR)
    (sub_imported_eq_congr (fun l => I.Prosa_Util_Sum_sumFiltered X l PL FL) _ _ Hxs)).
Qed.

End SeqSums.

Definition CjcPredRel (T : Type) (pR : T -> bool) (pL : T -> I.Bool) : SProp := forall x, CtBoolRel (pR x) (pL x).

Lemma cjc_forall_pred (T : Type) (PR : (T -> bool) -> Prop) (PL : (T -> I.Bool) -> SProp) :
  (forall pR pL, CjcPredRel T pR pL -> PropSPropRel (PR pR) (PL pL)) -> PropSPropRel (forall p, PR p) (forall p, PL p).
Proof.
  exact (cjc_forall_cover _ _ (CjcPredRel T) (fun pR x => ct_b2l (pR x)) (fun pL x => ct_l2b (pL x))
           (fun pR x => ct_bool_canonical _) (fun pL x => ct_bool_surjective _) PR PL).
Qed.

(** Priority relations (as in the accepted classic priority certificate). *)
Definition CjcRelRel (T : Type) (rR : T -> T -> bool) (rL : T -> T -> I.Bool) : SProp :=
  forall a b, CtBoolRel (rR a b) (rL a b).

Lemma cjc_rel_canonical (T : Type) (rR : T -> T -> bool) : CjcRelRel T rR (fun a b => ct_b2l (rR a b)).
Proof. intros a b. exact (ct_bool_canonical _). Qed.

Lemma cjc_rel_surjective (T : Type) (rL : T -> T -> I.Bool) : CjcRelRel T (fun a b => ct_l2b (rL a b)) rL.
Proof. intros a b. exact (ct_bool_surjective _). Qed.

Lemma cjc_forall_rel (T : Type) (PR : (T -> T -> bool) -> Prop) (PL : (T -> T -> I.Bool) -> SProp) :
  (forall rR rL, CjcRelRel T rR rL -> PropSPropRel (PR rR) (PL rL)) -> PropSPropRel (forall r, PR r) (forall r, PL r).
Proof.
  exact (cjc_forall_cover _ _ (CjcRelRel T) (fun rR a b => ct_b2l (rR a b)) (fun rL a b => ct_l2b (rL a b))
           (cjc_rel_canonical T) (cjc_rel_surjective T) PR PL).
Qed.

Definition CjcJldpRel (T : Type) (rR : nat -> T -> T -> bool) (rL : Lean.Nat -> T -> T -> I.Bool) : SProp :=
  forall tR tL, SubNatRel tR tL -> CjcRelRel T (rR tR) (rL tL).

Lemma cjc_jldp_canonical (T : Type) (rR : nat -> T -> T -> bool) :
  CjcJldpRel T rR (fun tL a b => ct_b2l (rR (sub_nat_to_rocq tL) a b)).
Proof.
  intros tR tL Ht a b. have E := cl_nat_logic _ _ Ht. subst tL. rewrite sub_nat_rocq_roundtrip.
  exact (ct_bool_canonical _).
Qed.

Lemma cjc_jldp_surjective (T : Type) (rL : Lean.Nat -> T -> T -> I.Bool) :
  CjcJldpRel T (fun tR a b => ct_l2b (rL (sub_nat_to_imported tR) a b)) rL.
Proof. intros tR tL Ht a b. have E := cl_nat_logic _ _ Ht. subst tL. exact (ct_bool_surjective _). Qed.

(* ------------------------------------------------------------------ *)
(** * Arrival sequences *)

Lemma cjc_forall_jldp (T : Type) (PR : (nat -> T -> T -> bool) -> Prop) (PL : (Lean.Nat -> T -> T -> I.Bool) -> SProp) :
  (forall rR rL, CjcJldpRel T rR rL -> PropSPropRel (PR rR) (PL rL)) -> PropSPropRel (forall r, PR r) (forall r, PL r).
Proof.
  exact (cjc_forall_cover _ _ (CjcJldpRel T) (fun rR tL a b => ct_b2l (rR (sub_nat_to_rocq tL) a b))
           (fun rL tR a b => ct_l2b (rL (sub_nat_to_imported tR) a b)) (cjc_jldp_canonical T) (cjc_jldp_surjective T) PR PL).
Qed.

Section PriodefsDefs.
Variables (Task Job : eqType).
Notation dT := (ct_decidable_eq Task).
Notation dJ := (ct_decidable_eq Job).

Lemma cjc_PR_FP_policy :
  And (forall rR : Priority.FP_policy Task, CjcRelRel Task rR (fun a b => ct_b2l (rR a b)))
      (forall rL : I.Prosa_Classic_Model_Priority_Priority_FP_policy Task dT, CjcRelRel Task (fun a b => ct_l2b (rL a b)) rL).
Proof. exact (And_intro _ _ (cjc_rel_canonical Task) (cjc_rel_surjective Task)). Qed.

Lemma cjc_reflexive (T : Type) rR rL (Hr : CjcRelRel T rR rL) :
  PropSPropRel (reflexive rR) (I.Prosa_Classic_Model_Priority_Priority_reflexiveB T rL).
Proof. apply: ct_forall_identity => x. exact (ct_bool_truth _ _ (Hr x x)). Qed.

Lemma cjc_transitive (T : Type) rR rL (Hr : CjcRelRel T rR rL) :
  PropSPropRel (transitive rR) (I.Prosa_Classic_Model_Priority_Priority_transitiveB T rL).
Proof.
  apply: ct_forall_identity => y. apply: ct_forall_identity => x. apply: ct_forall_identity => z.
  apply: ct_imp; first exact (ct_bool_truth _ _ (Hr x y)).
  apply: ct_imp; first exact (ct_bool_truth _ _ (Hr y z)).
  exact (ct_bool_truth _ _ (Hr x z)).
Qed.

Lemma cjc_PR_FP_is_reflexive rR rL (Hr : CjcRelRel Task rR rL) :
  PropSPropRel (Priority.FP_is_reflexive rR) (I.Prosa_Classic_Model_Priority_Priority_FP_is_reflexive Task dT rL).
Proof. exact (cjc_reflexive Task rR rL Hr). Qed.

Lemma cjc_PR_FP_is_transitive rR rL (Hr : CjcRelRel Task rR rL) :
  PropSPropRel (Priority.FP_is_transitive rR) (I.Prosa_Classic_Model_Priority_Priority_FP_is_transitive Task dT rL).
Proof. exact (cjc_transitive Task rR rL Hr). Qed.

End PriodefsDefs.

Section TaskDefsP.
Variables (Task : eqType).
Notation dT := (ct_decidable_eq Task).
Notation c0 := (sub_nat_rel_canonical 0).

End TaskDefsP.

(** The imported [Job] definitions (as in the accepted classic job certificate). *)
Section JobDefs.
Notation c0 := (sub_nat_rel_canonical 0).
Variables (Task Job : eqType).
Notation dT := (ct_decidable_eq Task).
Notation dJ := (ct_decidable_eq Job).

End JobDefs.

(** The imported [TaskArrival] definitions (as in the accepted classic task_arrival certificate). *)
Section TaskArrivalDefs.
Variables (Task Job : eqType).
Notation dT := (ct_decidable_eq Task).
Notation dJ := (ct_decidable_eq Job).

Lemma cjc_TA_sporadic_task_model tpR tpL (Htp : CjcParRel Task tpR tpL)
    jaR jaL (Hja : CjcParRel Job jaR jaL) (job_task : Job -> Task) aR aL (Ha : CjcArrRel Job aR aL) :
  PropSPropRel (TaskArrival.sporadic_task_model tpR jaR job_task aR)
    (I.Prosa_Classic_Model_Arrival_Basic_TaskArrival_TaskArrival_sporadic_task_model Task dT tpL Job dJ jaL job_task aL).
Proof.
  apply: ct_forall_identity => j. apply: ct_forall_identity => j'.
  apply: ct_imp; first exact (cjc_ne Job j j').
  apply: ct_imp; first exact (cjc_arrives_in Job aR aL Ha j).
  apply: ct_imp; first exact (cjc_arrives_in Job aR aL Ha j').
  apply: ct_imp; first exact (ct_eq_rel Task (job_task j) (job_task j')).
  apply: ct_imp; first exact (sub_nat_le_correspondence _ _ _ _ (Hja j) (Hja j')).
  exact (sub_nat_le_correspondence _ _ _ _ (sub_add_correspondence _ _ _ _ (Hja j) (Htp (job_task j))) (Hja j')).
Qed.

End TaskArrivalDefs.

Section UplatDefs.
Variables (Task Job : eqType).
Notation dT := (ct_decidable_eq Task).
Notation dJ := (ct_decidable_eq Job).
Variables (sR : UniprocessorSchedule.schedule Job) (sL : I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job dJ).
Hypothesis Hs : CjcSchedRel Job sR sL.

End UplatDefs.

Section UrtDefs.
Variables (Task Job : eqType).
Notation dT := (ct_decidable_eq Task).
Notation dJ := (ct_decidable_eq Job).
Variables (sR : UniprocessorSchedule.schedule Job) (sL : I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job dJ).
Hypothesis Hs : CjcSchedRel Job sR sL.

Lemma cjc_RT_is_response_time_bound_of_job aR aL (Ha : CjcParRel Job aR aL) cR cL (Hc : CjcParRel Job cR cL)
    j rR rL (Hr : SubNatRel rR rL) :
  CtBoolRel (ResponseTime.is_response_time_bound_of_job aR cR sR j rR) (I.Prosa_Classic_Model_Schedule_Uni_ResponseTime_ResponseTime_is_response_time_bound_of_job Job dJ aL cL sL j rL).
Proof. exact (cjc_US_completed_by Job sR sL Hs cR cL Hc j _ _ (sub_add_correspondence _ _ _ _ (Ha j) Hr)). Qed.

Lemma cjc_RT_is_response_time_bound_of_task aR aL (Ha : CjcParRel Job aR aL) cR cL (Hc : CjcParRel Job cR cL)
    (job_task : Job -> Task) arrR arrL (Harr : CjcArrRel Job arrR arrL) tsk rR rL (Hr : SubNatRel rR rL) :
  PropSPropRel (ResponseTime.is_response_time_bound_of_task aR cR job_task arrR sR tsk rR)
    (I.Prosa_Classic_Model_Schedule_Uni_ResponseTime_ResponseTime_is_response_time_bound_of_task Task dT Job dJ aL cL job_task arrL sL tsk rL).
Proof.
  apply: ct_forall_identity => j.
  apply: ct_imp; first exact (cjc_arrives_in Job arrR arrL Harr j).
  apply: ct_imp; first exact (ct_eq_rel Task (job_task j) tsk).
  exact (ct_bool_truth _ _ (cjc_RT_is_response_time_bound_of_job aR aL Ha cR cL Hc j rR rL Hr)).
Qed.

End UrtDefs.

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

(** The imported [ArrivalSequenceWithJitter] definitions (as in the accepted classic jitter arrival_sequence certificate). *)
Section JitterArrDefs.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).

Lemma cjc_AJ_actual_arrival pR pL (Hp : CjcParRel Job pR pL) qR qL (Hq : CjcParRel Job qR qL) j :
  SubNatRel (ArrivalSequenceWithJitter.actual_arrival pR qR j) (I.Prosa_Classic_Model_Arrival_Jitter_ArrivalSequence_ArrivalSequenceWithJitter_actual_arrival Job dJ pL qL j).
Proof. exact (sub_add_correspondence _ _ _ _ (Hp j) (Hq j)). Qed.

Lemma cjc_AJ_jitter_has_passed pR pL (Hp : CjcParRel Job pR pL) qR qL (Hq : CjcParRel Job qR qL) j
    tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (ArrivalSequenceWithJitter.jitter_has_passed pR qR j tR) (I.Prosa_Classic_Model_Arrival_Jitter_ArrivalSequence_ArrivalSequenceWithJitter_jitter_has_passed Job dJ pL qL j tL).
Proof. exact (ct_decide_le _ _ _ _ (cjc_AJ_actual_arrival pR pL Hp qR qL Hq j) Ht). Qed.

End JitterArrDefs.

Section UjschedDefs.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).
Variables (sR : UniprocessorSchedule.schedule Job) (sL : I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job dJ).
Hypothesis Hs : CjcSchedRel Job sR sL.

Lemma cjc_UJ_pending aR aL (Ha : CjcParRel Job aR aL) cR cL (Hc : CjcParRel Job cR cL)
    jjR jjL (Hjj : CjcParRel Job jjR jjL) j tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (UniprocessorScheduleWithJitter.pending aR cR jjR sR j tR) (I.Prosa_Classic_Model_Schedule_Uni_Jitter_Schedule_UniprocessorScheduleWithJitter_pending Job dJ aL cL jjL sL j tL).
Proof.
  exact (ct_bool_and _ _ _ _ (cjc_AJ_jitter_has_passed Job aR aL Ha jjR jjL Hjj j tR tL Ht)
           (ct_bool_not _ _ (cjc_US_completed_by Job sR sL Hs cR cL Hc j tR tL Ht))).
Qed.

Lemma cjc_UJ_backlogged aR aL (Ha : CjcParRel Job aR aL) cR cL (Hc : CjcParRel Job cR cL)
    jjR jjL (Hjj : CjcParRel Job jjR jjL) j tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (UniprocessorScheduleWithJitter.backlogged aR cR jjR sR j tR) (I.Prosa_Classic_Model_Schedule_Uni_Jitter_Schedule_UniprocessorScheduleWithJitter_backlogged Job dJ aL cL jjL sL j tL).
Proof.
  exact (ct_bool_and _ _ _ _ (cjc_UJ_pending aR aL Ha cR cL Hc jjR jjL Hjj j tR tL Ht)
           (ct_bool_not _ _ (cjc_US_scheduled_at Job sR sL Hs j tR tL Ht))).
Qed.

Lemma cjc_UJ_jobs_execute_after_jitter aR aL (Ha : CjcParRel Job aR aL) jjR jjL (Hjj : CjcParRel Job jjR jjL) :
  PropSPropRel (UniprocessorScheduleWithJitter.jobs_execute_after_jitter aR jjR sR) (I.Prosa_Classic_Model_Schedule_Uni_Jitter_Schedule_UniprocessorScheduleWithJitter_jobs_execute_after_jitter Job dJ aL jjL sL).
Proof.
  apply: ct_forall_identity => j. apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (ct_bool_truth _ _ (cjc_US_scheduled_at Job sR sL Hs j tR tL Ht)).
  exact (ct_bool_truth _ _ (cjc_AJ_jitter_has_passed Job aR aL Ha jjR jjL Hjj j tR tL Ht)).
Qed.

End UjschedDefs.

Section UjplatDefs.
Variables (Task Job : eqType).
Notation dT := (ct_decidable_eq Task).
Notation dJ := (ct_decidable_eq Job).
Variables (sR : UniprocessorSchedule.schedule Job) (sL : I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job dJ).
Hypothesis Hs : CjcSchedRel Job sR sL.
Variables (aR : Job -> nat) (aL : Job -> Lean.Nat) (cR : Job -> nat) (cL : Job -> Lean.Nat) (jjR : Job -> nat) (jjL : Job -> Lean.Nat).
Hypotheses (Ha : CjcParRel Job aR aL) (Hc : CjcParRel Job cR cL) (Hjj : CjcParRel Job jjR jjL).
Variables (arrR : ArrivalSequence.arrival_sequence Job)
  (arrL : I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrival_sequence Job dJ).
Hypothesis Harr : CjcArrRel Job arrR arrL.

Notation BL := (cjc_UJ_backlogged Job sR sL Hs aR aL Ha cR cL Hc jjR jjL Hjj).
Notation SA := (cjc_US_scheduled_at Job sR sL Hs).

Lemma cjc_UJP_work_conserving :
  PropSPropRel (Platform.work_conserving aR cR jjR arrR sR) (I.Prosa_Classic_Model_Schedule_Uni_Jitter_Platform_Platform_work_conserving Job dJ aL cL jjL arrL sL).
Proof.
  apply: ct_forall_identity => j. apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (cjc_arrives_in Job arrR arrL Harr j).
  apply: ct_imp; first exact (ct_bool_truth _ _ (BL j tR tL Ht)).
  apply: ct_exists_identity => j_other.
  exact (ct_bool_truth _ _ (SA j_other tR tL Ht)).
Qed.

Lemma cjc_UJP_respects_FP_policy (job_task : Job -> Task) hR hL (Hh : CjcRelRel Task hR hL) :
  PropSPropRel (Platform.respects_FP_policy aR cR jjR job_task arrR sR hR)
    (I.Prosa_Classic_Model_Schedule_Uni_Jitter_Platform_Platform_respects_FP_policy Task dT Job dJ aL cL jjL job_task arrL sL hL).
Proof.
  apply: ct_forall_identity => j. apply: ct_forall_identity => j_hp. apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (cjc_arrives_in Job arrR arrL Harr j).
  apply: ct_imp; first exact (ct_bool_truth _ _ (BL j tR tL Ht)).
  apply: ct_imp; first exact (ct_bool_truth _ _ (SA j_hp tR tL Ht)).
  exact (ct_bool_truth _ _ (Hh (job_task j_hp) (job_task j))).
Qed.

End UjplatDefs.



(* ------------------------------------------------------------------ *)
(** * Definitions *)

Section Defs.
Variable Task : eqType.
Notation dT := (ct_decidable_eq Task).

Lemma cjc_W_max_jobs_correspondence pR pL (Hp : CjcParRel Task pR pL) jR jL (Hj : CjcParRel Task jR jL) tsk dR dL (Hd : SubNatRel dR dL) :
  SubNatRel (WorkloadBoundFP.max_jobs pR jR tsk dR) (I.Prosa_Classic_Analysis_Uni_Jitter_WorkloadBoundFp_WorkloadBoundFP_max_jobs Task dT pL jL tsk dL).
Proof. exact (dm_div_ceil_correspondence _ _ _ _ (sub_add_correspondence _ _ _ _ Hd (Hj tsk)) (Hp tsk)). Qed.

Lemma cjc_W_task_workload_bound_FP_correspondence cR cL (Hc : CjcParRel Task cR cL) pR pL (Hp : CjcParRel Task pR pL)
    jR jL (Hj : CjcParRel Task jR jL) tsk dR dL (Hd : SubNatRel dR dL) :
  SubNatRel (WorkloadBoundFP.task_workload_bound_FP cR pR jR tsk dR) (I.Prosa_Classic_Analysis_Uni_Jitter_WorkloadBoundFp_WorkloadBoundFP_task_workload_bound_FP Task dT cL pL jL tsk dL).
Proof. exact (sub_mul_correspondence _ _ _ _ (cjc_W_max_jobs_correspondence pR pL Hp jR jL Hj tsk dR dL Hd) (Hc tsk)). Qed.

Lemma cjc_W_total_workload_bound_fp_correspondence cR cL (Hc : CjcParRel Task cR cL) pR pL (Hp : CjcParRel Task pR pL)
    jR jL (Hj : CjcParRel Task jR jL) hR hL (Hh : CjcRelRel Task hR hL) tsR tsL (Hts : ClListRel cid tsR tsL) tsk dR dL (Hd : SubNatRel dR dL) :
  SubNatRel (WorkloadBoundFP.total_workload_bound_fp cR pR jR hR tsR tsk dR) (I.Prosa_Classic_Analysis_Uni_Jitter_WorkloadBoundFp_WorkloadBoundFP_total_workload_bound_fp Task dT cL pL jL hL tsL tsk dL).
Proof.
  exact (cjc_sum_filtered_rel Task _ _ (fun x => cjc_W_task_workload_bound_FP_correspondence cR cL Hc pR pL Hp jR jL Hj x dR dL Hd)
           _ _ (fun x => Hh x tsk) _ _ Hts).
Qed.
End Defs.



(* ------------------------------------------------------------------ *)
(** * Options, pairs and the response-time iteration *)

Lemma cjc_ite_bool (A : Type) bR bL (Hb : CtBoolRel bR bL) (a b : A) :
  Logic.eq (I.ite A (Lean.eq bL I.Bool_true) (I.instDecidableEqBool bL I.Bool_true) a b) (if bR then a else b).
Proof. rewrite (ct_bool_rel_logic _ _ Hb). clear Hb. by case: bR. Qed.

Lemma cjc_ite_dec (A : Type) (P : SProp) (dec : I.Decidable P) bR (Hb : CtBoolRel bR (I.Decidable_decide P dec)) (a b : A) :
  Logic.eq (I.ite A P dec a b) (if bR then a else b).
Proof.
  have E := ct_bool_rel_logic _ _ Hb. clear Hb. move: E.
  case: dec => [h|h] E; destruct bR; try reflexivity; discriminate E.
Qed.

Definition cjc_onat (o : option nat) : I.Option_inst1 Lean.Nat :=
  match o with Some n => I.Option_some_inst1 Lean.Nat (sub_nat_to_imported n) | None => I.Option_none_inst1 Lean.Nat end.

Lemma cjc_iter_canonical fR fL (Hf : forall a aL, SubNatRel a aL -> SubNatRel (fR a) (fL aL)) : forall n x,
  Logic.eq (cjc_onat (iter_fixpoint fR n x))
    (I.Prosa_Classic_Util_Fixedpoint_iter_fixpoint_inst1 Lean.Nat I.instDecidableEqNat fL (sub_nat_to_imported n) (sub_nat_to_imported x)).
Proof.
  elim => [|n IH] x; first reflexivity.
  have E := cl_nat_logic _ _ (Hf x _ (sub_nat_rel_canonical x)).
  have -> : Logic.eq (I.Prosa_Classic_Util_Fixedpoint_iter_fixpoint_inst1 Lean.Nat I.instDecidableEqNat fL (sub_nat_to_imported n.+1) (sub_nat_to_imported x))
      (match I.Decidable_decide (Lean.eq (sub_nat_to_imported x) (fL (sub_nat_to_imported x)))
               (I.instDecidableEqNat (sub_nat_to_imported x) (fL (sub_nat_to_imported x))) with
       | I.Bool_true => I.Option_some_inst1 Lean.Nat (sub_nat_to_imported x)
       | I.Bool_false => I.Prosa_Classic_Util_Fixedpoint_iter_fixpoint_inst1 Lean.Nat I.instDecidableEqNat fL (sub_nat_to_imported n) (fL (sub_nat_to_imported x)) end).
  { cbn. destruct (I.instDecidableEqNat (sub_nat_to_imported x) (fL (sub_nat_to_imported x))); reflexivity. }
  rewrite E (ct_bool_rel_logic _ _ (ct_decide_eq_nat _ _ _ _ (sub_nat_rel_canonical x) (sub_nat_rel_canonical (fR x)))) -IH /=.
  by case: (x == fR x).
Qed.

Lemma cjc_iter fR fL (Hf : forall a aL, SubNatRel a aL -> SubNatRel (fR a) (fL aL)) nR nL (Hn : SubNatRel nR nL) xR xL (Hx : SubNatRel xR xL) :
  Logic.eq (cjc_onat (iter_fixpoint fR nR xR)) (I.Prosa_Classic_Util_Fixedpoint_iter_fixpoint_inst1 Lean.Nat I.instDecidableEqNat fL nL xL).
Proof. rewrite (cl_nat_logic _ _ Hn) (cl_nat_logic _ _ Hx). exact (cjc_iter_canonical fR fL Hf nR xR). Qed.

Section Pairs.
Variable Task : eqType.
Notation PT := (I.Prod_inst2 Task Lean.Nat).
Notation PO := (I.Prod_inst2 Task (I.Option_inst1 Lean.Nat)).

Definition cjc_pair (p : Task * nat) : PT := I.Prod_mk_inst2 Task Lean.Nat p.1 (sub_nat_to_imported p.2).
Definition cjc_unpair (q : PT) : Task * nat := match q with I.Prod_mk_inst2 a b => (a, sub_nat_to_rocq b) end.
Lemma cjc_unpair_pair p : Logic.eq (cjc_unpair (cjc_pair p)) p.
Proof. case: p => a b. rewrite /cjc_unpair /cjc_pair /=. by rewrite sub_nat_rocq_roundtrip. Qed.
Lemma cjc_pair_unpair q : Logic.eq (cjc_pair (cjc_unpair q)) q.
Proof. case: q => a b. rewrite /cjc_unpair /cjc_pair /=. by rewrite (imported_eq_to_coq_eq _ _ (sub_nat_imported_roundtrip b)). Qed.
Definition cjc_pairo (p : Task * option nat) : PO := I.Prod_mk_inst2 Task (I.Option_inst1 Lean.Nat) p.1 (cjc_onat p.2).
Definition cjc_opair (o : option (Task * nat)) : I.Option PT := match o with Some p => I.Option_some PT (cjc_pair p) | None => I.Option_none PT end.
Definition cjc_olist (o : option (seq (Task * nat))) : I.Option (I.List PT) :=
  match o with Some l => I.Option_some (I.List PT) (cl_map cjc_pair l) | None => I.Option_none (I.List PT) end.

Lemma cjc_all_step (P : PO -> I.Bool) a l : Logic.eq (I.List_all PO (I.List_cons PO a l) P) (I.Bool_and (P a) (I.List_all PO l P)).
Proof. reflexivity. Qed.

Lemma cjc_filterMap_step (f : PO -> I.Option PT) a l :
  Logic.eq (I.List_filterMap PO PT f (I.List_cons PO a l))
    (match f a with I.Option_none => I.List_filterMap PO PT f l | I.Option_some b => I.List_cons PT b (I.List_filterMap PO PT f l) end).
Proof. reflexivity. Qed.

Lemma cjc_all_pmap (vR : Task * option nat -> option (Task * nat)) (vL : PO -> I.Option PT)
    (Hv : forall p, Logic.eq (cjc_opair (vR p)) (vL (cjc_pairo p))) s :
  Logic.eq (cjc_olist (if all (fun p => isSome (vR p)) s then Some (pmap vR s) else None))
    (I.ite (I.Option (I.List PT))
       (Lean.eq (I.List_all PO (cl_map cjc_pairo s) (fun p => I.Option_isSome PT (vL p))) I.Bool_true)
       (I.instDecidableEqBool (I.List_all PO (cl_map cjc_pairo s) (fun p => I.Option_isSome PT (vL p))) I.Bool_true)
       (I.Option_some (I.List PT) (I.List_filterMap PO PT vL (cl_map cjc_pairo s)))
       (I.Option_none (I.List PT))).
Proof.
  have Eall : Logic.eq (I.List_all PO (cl_map cjc_pairo s) (fun p => I.Option_isSome PT (vL p))) (ct_b2l (all (fun p => isSome (vR p)) s)).
  { elim: s => [|x s IH]; first reflexivity.
    rewrite [cl_map _ _]/= [all _ (_ :: _)]/= cjc_all_step IH -(Hv x). case: (vR x) => [p|]; reflexivity. }
  have Epm : Logic.eq (I.List_filterMap PO PT vL (cl_map cjc_pairo s)) (cl_map cjc_pair (pmap vR s)).
  { clear Eall. elim: s => [|x s IH]; first reflexivity.
    rewrite [cl_map cjc_pairo _]/= [pmap _ (_ :: _)]/= cjc_filterMap_step IH -(Hv x). case: (vR x) => [p|]; reflexivity. }
  rewrite Eall Epm. by case: (all _ s).
Qed.

Lemma cjc_cl_map_pair_inj (s1 s2 : seq (Task * nat)) : Logic.eq (cl_map cjc_pair s1) (cl_map cjc_pair s2) -> Logic.eq s1 s2.
Proof.
  intro E. have E' := f_equal (cl_unmap cjc_unpair) E.
  by rewrite !(cl_unmap_map cjc_pair cjc_unpair cjc_unpair_pair) in E'.
Qed.

Lemma cjc_fcb_eq oR oL (Ho : Logic.eq (cjc_olist oR) oL) rbR rbL (Hrb : ClListRel cjc_pair rbR rbL) :
  PropSPropRel (Logic.eq oR (Some rbR)) (Lean.eq oL (I.Option_some (I.List PT) rbL)).
Proof.
  subst oL. rewrite (cl_list_logic _ _ _ Hrb). apply prop_sprop_rel_intro.
  - intros ->. exact (@Lean.eq_refl _ _).
  - intro E. apply strictly_inhabits. have E' := imported_eq_to_coq_eq _ _ E. clear E.
    case: oR E' => [l|] /= E'; last discriminate E'.
    injection E' => E''. by rewrite (cjc_cl_map_pair_inj _ _ E'').
Qed.

Lemma cjc_mem_pair tsk RR RL (HR : SubNatRel RR RL) rbR rbL (Hrb : ClListRel cjc_pair rbR rbL) :
  PropSPropRel ((tsk, RR) \in rbR) (I.List_Mem PT (I.Prod_mk_inst2 Task Lean.Nat tsk RL) rbL).
Proof. destruct HR. exact (cl_mem_rel_list _ _ cjc_pair cjc_unpair cjc_unpair_pair (tsk, RR) _ _ Hrb). Qed.

Lemma cjc_forall_bounds (PR : seq (Task * nat) -> Prop) (PL : I.List PT -> SProp) :
  (forall sR sL, ClListRel cjc_pair sR sL -> PropSPropRel (PR sR) (PL sL)) -> PropSPropRel (forall s, PR s) (forall s, PL s).
Proof. exact (cl_forall_list cjc_pair cjc_unpair cjc_pair_unpair PR PL). Qed.
End Pairs.

(* ------------------------------------------------------------------ *)
(** * Definitions *)

Section Defs.
Variable Task : eqType.
Notation dT := (ct_decidable_eq Task).
Variables (tcR tpR tdR tjR : Task -> nat) (tcL tpL tdL tjL : Task -> Lean.Nat).
Hypotheses (Htc : CjcParRel Task tcR tcL) (Htp : CjcParRel Task tpR tpL) (Htd : CjcParRel Task tdR tdL) (Htj : CjcParRel Task tjR tjL).
Variables (hR : Task -> Task -> bool) (hL : Task -> Task -> I.Bool).
Hypothesis Hh : CjcRelRel Task hR hL.

Theorem ResponseTimeIterationFP_max_steps_correspondence tsk :
  SubNatRel (@ResponseTimeIterationFP.max_steps Task tcR tdR tsk) (I.Prosa_Classic_Analysis_Uni_Jitter_FpRtaComp_ResponseTimeIterationFP_max_steps Task dT tcL tdL tsk).
Proof. exact (sub_add_correspondence _ _ _ _ (ct_sub_rel _ _ _ _ (Htd tsk) (Htc tsk)) (sub_nat_rel_canonical 1)). Qed.

Theorem ResponseTimeIterationFP_per_task_rta_correspondence tsR tsL (Hts : ClListRel cid tsR tsL) tsk :
  Logic.eq (cjc_onat (@ResponseTimeIterationFP.per_task_rta Task tcR tpR tdR tjR hR tsR tsk)) (I.Prosa_Classic_Analysis_Uni_Jitter_FpRtaComp_ResponseTimeIterationFP_per_task_rta Task dT tcL tpL tdL tjL hL tsL tsk).
Proof.
  rewrite /ResponseTimeIterationFP.per_task_rta. unfold I.Prosa_Classic_Analysis_Uni_Jitter_FpRtaComp_ResponseTimeIterationFP_per_task_rta.
  exact (cjc_iter _ _ (fun a aL Ha => cjc_W_total_workload_bound_fp_correspondence Task tcR tcL Htc tpR tpL Htp tjR tjL Htj hR hL Hh tsR tsL Hts tsk a aL Ha)
           _ _ (ResponseTimeIterationFP_max_steps_correspondence tsk) _ _ (Htc tsk)).
Qed.

Theorem ResponseTimeIterationFP_fp_claimed_bounds_correspondence tsR tsL (Hts : ClListRel cid tsR tsL) :
  Logic.eq (cjc_olist Task (@ResponseTimeIterationFP.fp_claimed_bounds Task tcR tpR tdR tjR hR tsR)) (I.Prosa_Classic_Analysis_Uni_Jitter_FpRtaComp_ResponseTimeIterationFP_fp_claimed_bounds Task dT tcL tpL tdL tjL hL tsL).
Proof.
  rewrite /ResponseTimeIterationFP.fp_claimed_bounds. unfold I.Prosa_Classic_Analysis_Uni_Jitter_FpRtaComp_ResponseTimeIterationFP_fp_claimed_bounds. cbv zeta.
  rewrite (cl_list_logic _ _ _ Hts).
  rewrite -(cl_map_op cid (cjc_pairo Task) (fun tsk => (tsk, @ResponseTimeIterationFP.per_task_rta Task tcR tpR tdR tjR hR tsR tsk))
              (fun tsk => I.Prod_mk_inst2 Task (I.Option_inst1 Lean.Nat) tsk (I.Prosa_Classic_Analysis_Uni_Jitter_FpRtaComp_ResponseTimeIterationFP_per_task_rta Task dT tcL tpL tdL tjL hL (cl_map cid tsR) tsk))
              (fun tsk => _) tsR).
  - intro tsk. rewrite /cjc_pairo /= -(ResponseTimeIterationFP_per_task_rta_correspondence _ _ (@Lean.eq_refl _ _) tsk). reflexivity.
  - apply: cjc_all_pmap => - [tsk [R|]]; last reflexivity.
    cbv beta iota zeta. rewrite [cjc_pairo _ _]/cjc_pairo [cjc_onat _]/cjc_onat. unfold I.Prosa_Classic_Analysis_Uni_Jitter_FpRtaComp_ResponseTimeIterationFP_is_valid_bound.
    rewrite [I.Prosa_Classic_Analysis_Uni_Jitter_FpRtaComp_ResponseTimeIterationFP_is_valid_bound_match_1 _ _ _ _ _]/=.
    rewrite (cjc_ite_dec _ _ _ _ (ct_decide_le _ _ _ _ (sub_add_correspondence _ _ _ _ (Htj tsk) (sub_nat_rel_canonical R)) (Htd tsk))).
    by case: (_ <= _).
Qed.

Notation FCB := ResponseTimeIterationFP_fp_claimed_bounds_correspondence.

Theorem ResponseTimeIterationFP_fp_schedulable_correspondence tsR tsL (Hts : ClListRel cid tsR tsL) :
  CtBoolRel (@ResponseTimeIterationFP.fp_schedulable Task tcR tpR tdR tjR hR tsR) (I.Prosa_Classic_Analysis_Uni_Jitter_FpRtaComp_ResponseTimeIterationFP_fp_schedulable Task dT tcL tpL tdL tjL hL tsL).
Proof.
  apply: coq_eq_to_imported_eq. rewrite /ResponseTimeIterationFP.fp_schedulable. unfold I.Prosa_Classic_Analysis_Uni_Jitter_FpRtaComp_ResponseTimeIterationFP_fp_schedulable.
  rewrite -(FCB tsR tsL Hts). by case: (@ResponseTimeIterationFP.fp_claimed_bounds Task tcR tpR tdR tjR hR tsR).
Qed.
End Defs.

Notation FCB := ResponseTimeIterationFP_fp_claimed_bounds_correspondence.
Notation PTR := ResponseTimeIterationFP_per_task_rta_correspondence.
Notation FS := ResponseTimeIterationFP_fp_schedulable_correspondence.
Notation TWc := cjc_W_total_workload_bound_fp_correspondence.


Lemma cjc_onat_eq oR oL (Ho : Logic.eq (cjc_onat oR) oL) RR RL (HR : SubNatRel RR RL) :
  PropSPropRel (Logic.eq oR (Some RR)) (Lean.eq oL (I.Option_some_inst1 Lean.Nat RL)).
Proof.
  subst oL. rewrite (cl_nat_logic _ _ HR). apply prop_sprop_rel_intro.
  - intros ->. exact (@Lean.eq_refl _ _).
  - intro E. apply strictly_inhabits. have E' := imported_eq_to_coq_eq _ _ E. clear E.
    case: oR E' => [x|] /= E'; last discriminate E'.
    injection E' => E''. have := f_equal sub_nat_to_rocq E''. by rewrite !sub_nat_rocq_roundtrip => ->.
Qed.

(** [x \In o] against [optIn x o]. *)
Lemma cjc_optIn (Task : eqType) tsk RR RL (HR : SubNatRel RR RL) oR oL (Ho : Logic.eq (cjc_olist Task oR) oL) dP :
  CtBoolRel ((tsk, RR) \In oR)
    (I.Prosa_Classic_Util_Notation_optIn (I.Prod_inst2 Task Lean.Nat) dP (I.Prod_mk_inst2 Task Lean.Nat tsk RL) oL).
Proof.
  subst oL. destruct oR as [l|].
  - exact (ct_decide_bool _ _ _ (cjc_mem_pair Task tsk RR RL HR l _ (@Lean.eq_refl _ _))).
  - exact (ct_bool_canonical false).
Qed.

(** Schedulability (as in the accepted classic uniprocessor schedulability certificate). *)
Section Sched.
Variables (Task Job : eqType).
Notation dT := (ct_decidable_eq Task).
Notation dJ := (ct_decidable_eq Job).
Variables (sR : UniprocessorSchedule.schedule Job) (sL : I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job dJ).
Hypothesis Hs : CjcSchedRel Job sR sL.
Variables (aR : Job -> nat) (aL : Job -> Lean.Nat) (cR : Job -> nat) (cL : Job -> Lean.Nat) (dR : Job -> nat) (dL : Job -> Lean.Nat).
Hypotheses (Ha : CjcParRel Job aR aL) (Hc : CjcParRel Job cR cL) (Hd : CjcParRel Job dR dL).
Lemma cjc_job_misses_no_deadline j :
  PropSPropRel (Schedulability.job_misses_no_deadline aR cR dR sR j)
    (I.Prosa_Classic_Model_Schedule_Uni_Schedulability_Schedulability_job_misses_no_deadline Job dJ aL cL dL sL j).
Proof. exact (ct_bool_truth _ _ (cjc_US_completed_by Job sR sL Hs cR cL Hc j _ _ (sub_add_correspondence _ _ _ _ (Ha j) (Hd j)))). Qed.
Lemma cjc_task_misses_no_deadline (job_task : Job -> Task) arrR arrL (Harr : CjcArrRel Job arrR arrL) tsk :
  PropSPropRel (Schedulability.task_misses_no_deadline aR cR dR job_task arrR sR tsk)
    (I.Prosa_Classic_Model_Schedule_Uni_Schedulability_Schedulability_task_misses_no_deadline Job dJ aL cL dL Task dT job_task arrL sL tsk).
Proof.
  apply: ct_forall_identity => j.
  apply: ct_imp; first exact (cjc_arrives_in Job arrR arrL Harr j).
  apply: ct_imp; first exact (ct_eq_rel Task (job_task j) tsk).
  exact (cjc_job_misses_no_deadline j).
Qed.
End Sched.

(* ------------------------------------------------------------------ *)
(** * Statements *)

Definition src_fp_claimed_bounds_for_every_task (Task : eqType) : Prop :=
  ltac:(type_of_term (@ResponseTimeIterationFP.fp_claimed_bounds_for_every_task Task)).
Definition tgt_fp_claimed_bounds_for_every_task (Task : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Analysis_Uni_Jitter_FpRtaComp_ResponseTimeIterationFP_fp_claimed_bounds_for_every_task Task (ct_decidable_eq Task))).
Theorem ResponseTimeIterationFP_fp_claimed_bounds_for_every_task_correspondence (Task : eqType) :
  PropSPropRel (src_fp_claimed_bounds_for_every_task Task) (tgt_fp_claimed_bounds_for_every_task Task).
Proof.
  unfold src_fp_claimed_bounds_for_every_task, tgt_fp_claimed_bounds_for_every_task.
  apply: cjc_forall_par => tcR tcL Htc. apply: cjc_forall_par => tpR tpL Htp. apply: cjc_forall_par => tdR tdL Htd. apply: cjc_forall_par => tjR tjL Htj.
  apply: (cjc_forall_rel Task) => hR hL Hh.
  apply: (cjc_forall_list Task) => tsR tsL Hts.
  apply: (cjc_forall_bounds Task) => rbR rbL Hrb.
  apply: ct_imp; first exact (cjc_fcb_eq Task _ _ (FCB Task tcR tpR tdR tjR tcL tpL tdL tjL Htc Htp Htd Htj hR hL Hh tsR tsL Hts) rbR rbL Hrb).
  apply: ct_forall_identity => tsk.
  apply: ct_imp; first exact (cjc_mem Task tsk _ _ Hts).
  apply: ct_exists_nat => RR RL HR. exact (cjc_mem_pair Task tsk RR RL HR rbR rbL Hrb).
Qed.

Definition src_fp_claimed_bounds_from_taskset (Task : eqType) : Prop :=
  ltac:(type_of_term (@ResponseTimeIterationFP.fp_claimed_bounds_from_taskset Task)).
Definition tgt_fp_claimed_bounds_from_taskset (Task : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Analysis_Uni_Jitter_FpRtaComp_ResponseTimeIterationFP_fp_claimed_bounds_from_taskset Task (ct_decidable_eq Task))).
Theorem ResponseTimeIterationFP_fp_claimed_bounds_from_taskset_correspondence (Task : eqType) :
  PropSPropRel (src_fp_claimed_bounds_from_taskset Task) (tgt_fp_claimed_bounds_from_taskset Task).
Proof.
  unfold src_fp_claimed_bounds_from_taskset, tgt_fp_claimed_bounds_from_taskset.
  apply: cjc_forall_par => tcR tcL Htc. apply: cjc_forall_par => tpR tpL Htp. apply: cjc_forall_par => tdR tdL Htd. apply: cjc_forall_par => tjR tjL Htj.
  apply: (cjc_forall_rel Task) => hR hL Hh.
  apply: (cjc_forall_list Task) => tsR tsL Hts.
  apply: (cjc_forall_bounds Task) => rbR rbL Hrb.
  apply: ct_imp; first exact (cjc_fcb_eq Task _ _ (FCB Task tcR tpR tdR tjR tcL tpL tdL tjL Htc Htp Htd Htj hR hL Hh tsR tsL Hts) rbR rbL Hrb).
  apply: ct_forall_identity => tsk.
  apply: ct_forall_nat => RR RL HR.
  apply: ct_imp; first exact (cjc_mem_pair Task tsk RR RL HR rbR rbL Hrb).
  exact (cjc_mem Task tsk _ _ Hts).
Qed.

Definition src_fp_claimed_bounds_computes_iteration (Task : eqType) : Prop :=
  ltac:(type_of_term (@ResponseTimeIterationFP.fp_claimed_bounds_computes_iteration Task)).
Definition tgt_fp_claimed_bounds_computes_iteration (Task : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Analysis_Uni_Jitter_FpRtaComp_ResponseTimeIterationFP_fp_claimed_bounds_computes_iteration Task (ct_decidable_eq Task))).
Theorem ResponseTimeIterationFP_fp_claimed_bounds_computes_iteration_correspondence (Task : eqType) :
  PropSPropRel (src_fp_claimed_bounds_computes_iteration Task) (tgt_fp_claimed_bounds_computes_iteration Task).
Proof.
  unfold src_fp_claimed_bounds_computes_iteration, tgt_fp_claimed_bounds_computes_iteration.
  apply: cjc_forall_par => tcR tcL Htc. apply: cjc_forall_par => tpR tpL Htp. apply: cjc_forall_par => tdR tdL Htd. apply: cjc_forall_par => tjR tjL Htj.
  apply: (cjc_forall_rel Task) => hR hL Hh.
  apply: (cjc_forall_list Task) => tsR tsL Hts.
  apply: (cjc_forall_bounds Task) => rbR rbL Hrb.
  apply: ct_imp; first exact (cjc_fcb_eq Task _ _ (FCB Task tcR tpR tdR tjR tcL tpL tdL tjL Htc Htp Htd Htj hR hL Hh tsR tsL Hts) rbR rbL Hrb).
  apply: ct_forall_identity => tsk.
  apply: ct_forall_nat => RR RL HR.
  apply: ct_imp; first exact (cjc_mem_pair Task tsk RR RL HR rbR rbL Hrb).
  exact (cjc_onat_eq _ _ (PTR Task tcR tpR tdR tjR tcL tpL tdL tjL Htc Htp Htd Htj hR hL Hh tsR tsL Hts tsk) _ _ HR).
Qed.

Definition src_fp_claimed_bounds_yields_fixed_point (Task : eqType) : Prop :=
  ltac:(type_of_term (@ResponseTimeIterationFP.fp_claimed_bounds_yields_fixed_point Task)).
Definition tgt_fp_claimed_bounds_yields_fixed_point (Task : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Analysis_Uni_Jitter_FpRtaComp_ResponseTimeIterationFP_fp_claimed_bounds_yields_fixed_point Task (ct_decidable_eq Task))).
Theorem ResponseTimeIterationFP_fp_claimed_bounds_yields_fixed_point_correspondence (Task : eqType) :
  PropSPropRel (src_fp_claimed_bounds_yields_fixed_point Task) (tgt_fp_claimed_bounds_yields_fixed_point Task).
Proof.
  unfold src_fp_claimed_bounds_yields_fixed_point, tgt_fp_claimed_bounds_yields_fixed_point.
  cbv zeta.
  apply: cjc_forall_par => tcR tcL Htc. apply: cjc_forall_par => tpR tpL Htp. apply: cjc_forall_par => tdR tdL Htd. apply: cjc_forall_par => tjR tjL Htj.
  apply: (cjc_forall_rel Task) => hR hL Hh.
  apply: (cjc_forall_list Task) => tsR tsL Hts.
  apply: (cjc_forall_bounds Task) => rbR rbL Hrb.
  apply: ct_imp; first exact (cjc_fcb_eq Task _ _ (FCB Task tcR tpR tdR tjR tcL tpL tdL tjL Htc Htp Htd Htj hR hL Hh tsR tsL Hts) rbR rbL Hrb).
  apply: ct_forall_identity => tsk.
  apply: ct_forall_nat => RR RL HR.
  apply: ct_imp; first exact (cjc_mem_pair Task tsk RR RL HR rbR rbL Hrb).
  exact (sub_nat_eq_correspondence _ _ _ _ HR (TWc Task tcR tcL Htc tpR tpL Htp tjR tjL Htj hR hL Hh tsR tsL Hts tsk _ _ HR)).
Qed.

Definition src_fp_claimed_bounds_le_deadline (Task : eqType) : Prop :=
  ltac:(type_of_term (@ResponseTimeIterationFP.fp_claimed_bounds_le_deadline Task)).
Definition tgt_fp_claimed_bounds_le_deadline (Task : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Analysis_Uni_Jitter_FpRtaComp_ResponseTimeIterationFP_fp_claimed_bounds_le_deadline Task (ct_decidable_eq Task))).
Theorem ResponseTimeIterationFP_fp_claimed_bounds_le_deadline_correspondence (Task : eqType) :
  PropSPropRel (src_fp_claimed_bounds_le_deadline Task) (tgt_fp_claimed_bounds_le_deadline Task).
Proof.
  unfold src_fp_claimed_bounds_le_deadline, tgt_fp_claimed_bounds_le_deadline.
  apply: cjc_forall_par => tcR tcL Htc. apply: cjc_forall_par => tpR tpL Htp. apply: cjc_forall_par => tdR tdL Htd. apply: cjc_forall_par => tjR tjL Htj.
  apply: (cjc_forall_rel Task) => hR hL Hh.
  apply: (cjc_forall_list Task) => tsR tsL Hts.
  apply: (cjc_forall_bounds Task) => rbR rbL Hrb.
  apply: ct_imp; first exact (cjc_fcb_eq Task _ _ (FCB Task tcR tpR tdR tjR tcL tpL tdL tjL Htc Htp Htd Htj hR hL Hh tsR tsL Hts) rbR rbL Hrb).
  apply: ct_forall_identity => tsk.
  apply: ct_forall_nat => RR RL HR.
  apply: ct_imp; first exact (cjc_mem_pair Task tsk RR RL HR rbR rbL Hrb).
  exact (sub_nat_le_correspondence _ _ _ _ (sub_add_correspondence _ _ _ _ (Htj tsk) HR) (Htd tsk)).
Qed.

Definition src_fp_claimed_bounds_ge_cost (Task : eqType) : Prop :=
  ltac:(type_of_term (@ResponseTimeIterationFP.fp_claimed_bounds_ge_cost Task)).
Definition tgt_fp_claimed_bounds_ge_cost (Task : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Analysis_Uni_Jitter_FpRtaComp_ResponseTimeIterationFP_fp_claimed_bounds_ge_cost Task (ct_decidable_eq Task))).
Theorem ResponseTimeIterationFP_fp_claimed_bounds_ge_cost_correspondence (Task : eqType) :
  PropSPropRel (src_fp_claimed_bounds_ge_cost Task) (tgt_fp_claimed_bounds_ge_cost Task).
Proof.
  unfold src_fp_claimed_bounds_ge_cost, tgt_fp_claimed_bounds_ge_cost.
  apply: cjc_forall_par => tcR tcL Htc. apply: cjc_forall_par => tpR tpL Htp. apply: cjc_forall_par => tdR tdL Htd. apply: cjc_forall_par => tjR tjL Htj.
  apply: (cjc_forall_rel Task) => hR hL Hh.
  apply: (cjc_forall_list Task) => tsR tsL Hts.
  apply: (cjc_forall_bounds Task) => rbR rbL Hrb.
  apply: ct_imp; first exact (cjc_fcb_eq Task _ _ (FCB Task tcR tpR tdR tjR tcL tpL tdL tjL Htc Htp Htd Htj hR hL Hh tsR tsL Hts) rbR rbL Hrb).
  apply: ct_forall_identity => tsk.
  apply: ct_forall_nat => RR RL HR.
  apply: ct_imp; first exact (cjc_mem_pair Task tsk RR RL HR rbR rbL Hrb).
  apply: ct_imp; first exact (cjc_PR_FP_is_reflexive Task hR hL Hh).
  apply: ct_imp; first exact (sub_nat_lt_correspondence _ _ _ _ (sub_nat_rel_canonical 0) (Htc tsk)).
  apply: ct_imp.
  { apply: ct_forall_identity => x. apply: ct_imp; first exact (cjc_mem Task x _ _ Hts).
    exact (sub_nat_lt_correspondence _ _ _ _ (sub_nat_rel_canonical 0) (Htp x)). }
  exact (sub_nat_le_correspondence _ _ _ _ (Htc tsk) HR).
Qed.

Definition src_fp_claimed_bounds_gt_zero (Task : eqType) : Prop :=
  ltac:(type_of_term (@ResponseTimeIterationFP.fp_claimed_bounds_gt_zero Task)).
Definition tgt_fp_claimed_bounds_gt_zero (Task : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Analysis_Uni_Jitter_FpRtaComp_ResponseTimeIterationFP_fp_claimed_bounds_gt_zero Task (ct_decidable_eq Task))).
Theorem ResponseTimeIterationFP_fp_claimed_bounds_gt_zero_correspondence (Task : eqType) :
  PropSPropRel (src_fp_claimed_bounds_gt_zero Task) (tgt_fp_claimed_bounds_gt_zero Task).
Proof.
  unfold src_fp_claimed_bounds_gt_zero, tgt_fp_claimed_bounds_gt_zero.
  apply: cjc_forall_par => tcR tcL Htc. apply: cjc_forall_par => tpR tpL Htp. apply: cjc_forall_par => tdR tdL Htd. apply: cjc_forall_par => tjR tjL Htj.
  apply: (cjc_forall_rel Task) => hR hL Hh.
  apply: (cjc_forall_list Task) => tsR tsL Hts.
  apply: (cjc_forall_bounds Task) => rbR rbL Hrb.
  apply: ct_imp; first exact (cjc_fcb_eq Task _ _ (FCB Task tcR tpR tdR tjR tcL tpL tdL tjL Htc Htp Htd Htj hR hL Hh tsR tsL Hts) rbR rbL Hrb).
  apply: ct_forall_identity => tsk.
  apply: ct_forall_nat => RR RL HR.
  apply: ct_imp; first exact (cjc_mem_pair Task tsk RR RL HR rbR rbL Hrb).
  apply: ct_imp; first exact (cjc_PR_FP_is_reflexive Task hR hL Hh).
  apply: ct_imp; first exact (sub_nat_lt_correspondence _ _ _ _ (sub_nat_rel_canonical 0) (Htc tsk)).
  apply: ct_imp.
  { apply: ct_forall_identity => x. apply: ct_imp; first exact (cjc_mem Task x _ _ Hts).
    exact (sub_nat_lt_correspondence _ _ _ _ (sub_nat_rel_canonical 0) (Htp x)). }
  exact (sub_nat_lt_correspondence _ _ _ _ (sub_nat_rel_canonical 0) HR).
Qed.

Definition src_fp_analysis_yields_response_time_bounds (Task Job : eqType) : Prop :=
  forall task_cost task_period task_deadline task_jitter : Task -> Time.time,
    ltac:(type_of_term (@ResponseTimeIterationFP.fp_analysis_yields_response_time_bounds Task task_cost task_period task_deadline task_jitter Job)).
Definition tgt_fp_analysis_yields_response_time_bounds (Task Job : eqType) : SProp :=
  forall task_cost task_period task_deadline task_jitter : Task -> Lean.Nat,
    ltac:(type_of_term (I.Prosa_Classic_Analysis_Uni_Jitter_FpRtaComp_ResponseTimeIterationFP_fp_analysis_yields_response_time_bounds Task (ct_decidable_eq Task) task_cost task_period task_deadline task_jitter Job (ct_decidable_eq Job))).
Theorem ResponseTimeIterationFP_fp_analysis_yields_response_time_bounds_correspondence (Task Job : eqType) :
  PropSPropRel (src_fp_analysis_yields_response_time_bounds Task Job) (tgt_fp_analysis_yields_response_time_bounds Task Job).
Proof.
  unfold src_fp_analysis_yields_response_time_bounds, tgt_fp_analysis_yields_response_time_bounds.
  apply: cjc_forall_par => tcR tcL Htc. apply: cjc_forall_par => tpR tpL Htp. apply: cjc_forall_par => tdR tdL Htd. apply: cjc_forall_par => tjR tjL Htj.
  apply: cjc_forall_par => jaR jaL Hja. apply: cjc_forall_par => cR cL Hc.
  apply: cjc_forall_par => jjR jjL Hjj. apply: ct_forall_identity => job_task.
  apply: (cjc_forall_list Task) => tsR tsL Hts.
  apply: ct_imp.
  { apply: ct_forall_identity => x. apply: ct_imp; first exact (cjc_mem Task x _ _ Hts).
    exact (sub_nat_lt_correspondence _ _ _ _ (sub_nat_rel_canonical 0) (Htc x)). }
  apply: ct_imp.
  { apply: ct_forall_identity => x. apply: ct_imp; first exact (cjc_mem Task x _ _ Hts).
    exact (sub_nat_lt_correspondence _ _ _ _ (sub_nat_rel_canonical 0) (Htp x)). }
  apply: (cjc_forall_arr Job) => aR aL Ha.
  apply: ct_imp; first exact (cjc_consistent Job jaR jaL Hja aR aL Ha).
  apply: ct_imp; first exact (cjc_is_a_set Job aR aL Ha).
  apply: ct_imp.
  { apply: ct_forall_identity => j. apply: ct_imp; first exact (cjc_arrives_in Job aR aL Ha j).
    exact (cjc_mem Task (job_task j) _ _ Hts). }
  apply: ct_imp; first exact (cjc_TA_sporadic_task_model Task Job tpR tpL Htp jaR jaL Hja job_task aR aL Ha).
  apply: ct_imp.
  { apply: ct_forall_identity => j. apply: ct_imp; first exact (cjc_arrives_in Job aR aL Ha j).
    exact (sub_nat_le_correspondence _ _ _ _ (Hc j) (Htc (job_task j))). }
  apply: ct_imp.
  { apply: ct_forall_identity => j. apply: ct_imp; first exact (cjc_arrives_in Job aR aL Ha j).
    exact (sub_nat_le_correspondence _ _ _ _ (Hjj j) (Htj (job_task j))). }
  apply: (cjc_forall_rel Task) => hR hL Hh.
  apply: ct_imp; first exact (cjc_PR_FP_is_reflexive Task hR hL Hh).
  apply: ct_imp; first exact (cjc_PR_FP_is_transitive Task hR hL Hh).
  apply: (cjc_forall_sched Job) => sR sL Hs.
  apply: ct_imp; first exact (cjc_US_jobs_come_from_arrival_sequence Job sR sL Hs aR aL Ha).
  apply: ct_imp; first exact (cjc_UJ_jobs_execute_after_jitter Job sR sL Hs jaR jaL Hja jjR jjL Hjj).
  apply: ct_imp; first exact (cjc_US_completed_jobs_dont_execute Job sR sL Hs cR cL Hc).
  apply: ct_imp; first exact (cjc_UJP_work_conserving Job sR sL Hs jaR jaL cR cL jjR jjL Hja Hc Hjj aR aL Ha).
  apply: ct_imp; first exact (cjc_UJP_respects_FP_policy Task Job sR sL Hs jaR jaL cR cL jjR jjL Hja Hc Hjj aR aL Ha job_task hR hL Hh).
  apply: ct_forall_identity => tsk.
  apply: ct_forall_nat => RR RL HR.
  apply: ct_imp; first exact (ct_bool_truth _ _ (cjc_optIn Task tsk RR RL HR _ _ (FCB Task tcR tpR tdR tjR tcL tpL tdL tjL Htc Htp Htd Htj hR hL Hh tsR tsL Hts) _)).
  exact (cjc_RT_is_response_time_bound_of_task Task Job sR sL Hs jaR jaL Hja cR cL Hc job_task aR aL Ha tsk _ _ (sub_add_correspondence _ _ _ _ (Htj tsk) HR)).
Qed.

Definition src_taskset_schedulable_by_fp_rta (Task Job : eqType) : Prop :=
  forall task_cost task_period task_deadline task_jitter : Task -> Time.time,
    ltac:(type_of_term (@ResponseTimeIterationFP.taskset_schedulable_by_fp_rta Task task_cost task_period task_deadline task_jitter Job)).
Definition tgt_taskset_schedulable_by_fp_rta (Task Job : eqType) : SProp :=
  forall task_cost task_period task_deadline task_jitter : Task -> Lean.Nat,
    ltac:(type_of_term (I.Prosa_Classic_Analysis_Uni_Jitter_FpRtaComp_ResponseTimeIterationFP_taskset_schedulable_by_fp_rta Task (ct_decidable_eq Task) task_cost task_period task_deadline task_jitter Job (ct_decidable_eq Job))).
Theorem ResponseTimeIterationFP_taskset_schedulable_by_fp_rta_correspondence (Task Job : eqType) :
  PropSPropRel (src_taskset_schedulable_by_fp_rta Task Job) (tgt_taskset_schedulable_by_fp_rta Task Job).
Proof.
  unfold src_taskset_schedulable_by_fp_rta, tgt_taskset_schedulable_by_fp_rta.
  apply: cjc_forall_par => tcR tcL Htc. apply: cjc_forall_par => tpR tpL Htp. apply: cjc_forall_par => tdR tdL Htd. apply: cjc_forall_par => tjR tjL Htj.
  apply: cjc_forall_par => jaR jaL Hja. apply: cjc_forall_par => cR cL Hc. apply: cjc_forall_par => jdR jdL Hjd.
  apply: cjc_forall_par => jjR jjL Hjj. apply: ct_forall_identity => job_task.
  apply: (cjc_forall_list Task) => tsR tsL Hts.
  apply: ct_imp.
  { apply: ct_forall_identity => x. apply: ct_imp; first exact (cjc_mem Task x _ _ Hts).
    exact (sub_nat_lt_correspondence _ _ _ _ (sub_nat_rel_canonical 0) (Htc x)). }
  apply: ct_imp.
  { apply: ct_forall_identity => x. apply: ct_imp; first exact (cjc_mem Task x _ _ Hts).
    exact (sub_nat_lt_correspondence _ _ _ _ (sub_nat_rel_canonical 0) (Htp x)). }
  apply: (cjc_forall_arr Job) => aR aL Ha.
  apply: ct_imp; first exact (cjc_consistent Job jaR jaL Hja aR aL Ha).
  apply: ct_imp; first exact (cjc_is_a_set Job aR aL Ha).
  apply: ct_imp.
  { apply: ct_forall_identity => j. apply: ct_imp; first exact (cjc_arrives_in Job aR aL Ha j).
    exact (cjc_mem Task (job_task j) _ _ Hts). }
  apply: ct_imp; first exact (cjc_TA_sporadic_task_model Task Job tpR tpL Htp jaR jaL Hja job_task aR aL Ha).
  apply: ct_imp.
  { apply: ct_forall_identity => j. apply: ct_imp; first exact (cjc_arrives_in Job aR aL Ha j).
    exact (sub_nat_le_correspondence _ _ _ _ (Hc j) (Htc (job_task j))). }
  apply: ct_imp.
  { apply: ct_forall_identity => j. apply: ct_imp; first exact (cjc_arrives_in Job aR aL Ha j).
    exact (sub_nat_le_correspondence _ _ _ _ (Hjj j) (Htj (job_task j))). }
  apply: ct_imp.
  { apply: ct_forall_identity => j. apply: ct_imp; first exact (cjc_arrives_in Job aR aL Ha j).
    exact (sub_nat_eq_correspondence _ _ _ _ (Hjd j) (Htd (job_task j))). }
  apply: (cjc_forall_rel Task) => hR hL Hh.
  apply: ct_imp; first exact (cjc_PR_FP_is_reflexive Task hR hL Hh).
  apply: ct_imp; first exact (cjc_PR_FP_is_transitive Task hR hL Hh).
  apply: (cjc_forall_sched Job) => sR sL Hs.
  apply: ct_imp; first exact (cjc_US_jobs_come_from_arrival_sequence Job sR sL Hs aR aL Ha).
  apply: ct_imp; first exact (cjc_UJ_jobs_execute_after_jitter Job sR sL Hs jaR jaL Hja jjR jjL Hjj).
  apply: ct_imp; first exact (cjc_US_completed_jobs_dont_execute Job sR sL Hs cR cL Hc).
  apply: ct_imp; first exact (cjc_UJP_work_conserving Job sR sL Hs jaR jaL cR cL jjR jjL Hja Hc Hjj aR aL Ha).
  apply: ct_imp; first exact (cjc_UJP_respects_FP_policy Task Job sR sL Hs jaR jaL cR cL jjR jjL Hja Hc Hjj aR aL Ha job_task hR hL Hh).
  apply: ct_imp; first exact (ct_bool_truth _ _ (FS Task tcR tpR tdR tjR tcL tpL tdL tjL Htc Htp Htd Htj hR hL Hh tsR tsL Hts)).
  apply: ct_forall_identity => tsk.
  apply: ct_imp; first exact (cjc_mem Task tsk _ _ Hts).
  exact (cjc_task_misses_no_deadline Task Job sR sL Hs jaR jaL cR cL jdR jdL Hja Hc Hjd job_task aR aL Ha tsk).
Qed.

Definition src_jobs_schedulable_by_fp_rta (Task Job : eqType) : Prop :=
  forall task_cost task_period task_deadline task_jitter : Task -> Time.time,
    ltac:(type_of_term (@ResponseTimeIterationFP.jobs_schedulable_by_fp_rta Task task_cost task_period task_deadline task_jitter Job)).
Definition tgt_jobs_schedulable_by_fp_rta (Task Job : eqType) : SProp :=
  forall task_cost task_period task_deadline task_jitter : Task -> Lean.Nat,
    ltac:(type_of_term (I.Prosa_Classic_Analysis_Uni_Jitter_FpRtaComp_ResponseTimeIterationFP_jobs_schedulable_by_fp_rta Task (ct_decidable_eq Task) task_cost task_period task_deadline task_jitter Job (ct_decidable_eq Job))).
Theorem ResponseTimeIterationFP_jobs_schedulable_by_fp_rta_correspondence (Task Job : eqType) :
  PropSPropRel (src_jobs_schedulable_by_fp_rta Task Job) (tgt_jobs_schedulable_by_fp_rta Task Job).
Proof.
  unfold src_jobs_schedulable_by_fp_rta, tgt_jobs_schedulable_by_fp_rta.
  apply: cjc_forall_par => tcR tcL Htc. apply: cjc_forall_par => tpR tpL Htp. apply: cjc_forall_par => tdR tdL Htd. apply: cjc_forall_par => tjR tjL Htj.
  apply: cjc_forall_par => jaR jaL Hja. apply: cjc_forall_par => cR cL Hc. apply: cjc_forall_par => jdR jdL Hjd.
  apply: cjc_forall_par => jjR jjL Hjj. apply: ct_forall_identity => job_task.
  apply: (cjc_forall_list Task) => tsR tsL Hts.
  apply: ct_imp.
  { apply: ct_forall_identity => x. apply: ct_imp; first exact (cjc_mem Task x _ _ Hts).
    exact (sub_nat_lt_correspondence _ _ _ _ (sub_nat_rel_canonical 0) (Htc x)). }
  apply: ct_imp.
  { apply: ct_forall_identity => x. apply: ct_imp; first exact (cjc_mem Task x _ _ Hts).
    exact (sub_nat_lt_correspondence _ _ _ _ (sub_nat_rel_canonical 0) (Htp x)). }
  apply: (cjc_forall_arr Job) => aR aL Ha.
  apply: ct_imp; first exact (cjc_consistent Job jaR jaL Hja aR aL Ha).
  apply: ct_imp; first exact (cjc_is_a_set Job aR aL Ha).
  apply: ct_imp.
  { apply: ct_forall_identity => j. apply: ct_imp; first exact (cjc_arrives_in Job aR aL Ha j).
    exact (cjc_mem Task (job_task j) _ _ Hts). }
  apply: ct_imp; first exact (cjc_TA_sporadic_task_model Task Job tpR tpL Htp jaR jaL Hja job_task aR aL Ha).
  apply: ct_imp.
  { apply: ct_forall_identity => j. apply: ct_imp; first exact (cjc_arrives_in Job aR aL Ha j).
    exact (sub_nat_le_correspondence _ _ _ _ (Hc j) (Htc (job_task j))). }
  apply: ct_imp.
  { apply: ct_forall_identity => j. apply: ct_imp; first exact (cjc_arrives_in Job aR aL Ha j).
    exact (sub_nat_le_correspondence _ _ _ _ (Hjj j) (Htj (job_task j))). }
  apply: ct_imp.
  { apply: ct_forall_identity => j. apply: ct_imp; first exact (cjc_arrives_in Job aR aL Ha j).
    exact (sub_nat_eq_correspondence _ _ _ _ (Hjd j) (Htd (job_task j))). }
  apply: (cjc_forall_rel Task) => hR hL Hh.
  apply: ct_imp; first exact (cjc_PR_FP_is_reflexive Task hR hL Hh).
  apply: ct_imp; first exact (cjc_PR_FP_is_transitive Task hR hL Hh).
  apply: (cjc_forall_sched Job) => sR sL Hs.
  apply: ct_imp; first exact (cjc_US_jobs_come_from_arrival_sequence Job sR sL Hs aR aL Ha).
  apply: ct_imp; first exact (cjc_UJ_jobs_execute_after_jitter Job sR sL Hs jaR jaL Hja jjR jjL Hjj).
  apply: ct_imp; first exact (cjc_US_completed_jobs_dont_execute Job sR sL Hs cR cL Hc).
  apply: ct_imp; first exact (cjc_UJP_work_conserving Job sR sL Hs jaR jaL cR cL jjR jjL Hja Hc Hjj aR aL Ha).
  apply: ct_imp; first exact (cjc_UJP_respects_FP_policy Task Job sR sL Hs jaR jaL cR cL jjR jjL Hja Hc Hjj aR aL Ha job_task hR hL Hh).
  apply: ct_imp; first exact (ct_bool_truth _ _ (FS Task tcR tpR tdR tjR tcL tpL tdL tjL Htc Htp Htd Htj hR hL Hh tsR tsL Hts)).
  apply: ct_forall_identity => j. apply: ct_imp; first exact (cjc_arrives_in Job aR aL Ha j).
  exact (cjc_job_misses_no_deadline Job sR sL Hs jaR jaL cR cL jdR jdL Hja Hc Hjd j).
Qed.
