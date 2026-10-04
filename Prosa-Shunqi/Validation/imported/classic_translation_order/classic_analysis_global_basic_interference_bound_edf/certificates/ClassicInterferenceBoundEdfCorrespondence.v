From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq path fintype bigop div.
From prosa Require Import util.seqset util.div_mod classic.model.time classic.util.notation classic.model.arrival.basic.arrival_sequence classic.model.arrival.basic.task classic.model.arrival.basic.job classic.model.arrival.basic.task_arrival classic.model.priority classic.model.schedule.global.basic.schedule classic.model.schedule.global.response_time classic.model.schedule.global.basic.interference classic.model.schedule.global.basic.platform classic.analysis.global.basic.workload_bound classic.analysis.global.basic.interference_bound classic.analysis.global.basic.interference_bound_edf.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedClassicInterferenceBoundEdf.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence ClassicInterferenceBoundEdfNatSub ClassicInterferenceBoundEdfOps ClassicInterferenceBoundEdfBase ClassicInterferenceBoundEdfList ClassicInterferenceBoundEdfOrd.

Module I := ImportedClassicInterferenceBoundEdf.
Local Open Scope nat_scope.

(** Certificates for [classic/analysis/global/basic/interference_bound_edf.v] (ProsaBuddy classic, commit f692cb7).

    Inputs, relations and computation as in the accepted classic schedule, task, task_arrival, priority, global interference and platform, response_time, workload_bound and interference_bound_fp
    certificates (re-stated below for this export): eqTypes identified with their
    canonical Lean [DecidableEq] instances; times and [num_cpus] by [SubNatRel];
    processors by their values; schedules pointwise ([CsSchedRel]); job and task
    parameters pointwise; arrival sequences pointwise on related times; task sets
    by their underlying sequences ([CtsRel]); sequences of (task, time) pairs
    elementwise by the pair conversion ([cibfp_pair]); FP policies pointwise; all
    with two-way totals.  The interference sums through kernel-guarded [rfl] body
    projections; [div_floor] and the Nat operations through the accepted
    operation-level bridge [DivModCorrespondence], re-bound to this export.

    Statements: the source side is the exact elaborated type of the pinned lemma
    (via [type of]; the source proof is not used).  All lemmas of this file put the
    task parameters before the job type in their Rocq and Lean binder lists; as in
    the accepted classic workload_bound certificates, the job type is fixed as an
    [eqType] with its canonical Lean instance and the task parameters stay
    universally quantified on both sides.  Each statement is proved by the relation
    search [crel] below. *)

Ltac type_of_term t := let T := type of t in exact T.

Lemma cs_forall_cover (A B : Type) (Rel : A -> B -> SProp) (toB : A -> B) (toA : B -> A)
    (HB : forall a, Rel a (toB a)) (HA : forall b, Rel (toA b) b) (PR : A -> Prop) (PL : B -> SProp) :
  (forall a b, Rel a b -> PropSPropRel (PR a) (PL b)) -> PropSPropRel (forall a, PR a) (forall b, PL b).
Proof.
  intro H. apply prop_sprop_rel_intro.
  - intros HR b. exact (prop_to_sprop _ _ (H _ _ (HA b)) (HR _)).
  - intro HL. apply strictly_inhabits. intro a. exact (sprop_to_prop _ _ (H _ _ (HB a)) (HL _)).
Qed.

Lemma cs_mem (T : eqType) x s sL : ClListRel cid s sL ->
  PropSPropRel (x \in s) (I.Membership_mem T (I.List T) (I.List_instMembership T) sL x).
Proof. exact (cl_mem_rel_list T T cid cid (fun _ => Logic.eq_refl _) x s sL). Qed.

Lemma cs_uniq (T : eqType) s sL : ClListRel cid s sL -> PropSPropRel (uniq s) (I.List_Nodup T sL).
Proof. exact (cl_uniq_rel_list T T cid cid (fun _ => Logic.eq_refl _) (fun _ => Logic.eq_refl _) s sL). Qed.

Lemma cs_list_size (T : Type) s sL : ClListRel (B := T) cid s sL -> SubNatRel (size s) (I.List_length T sL).
Proof. intro H. destruct H. exact (cl_size cid s). Qed.

Lemma cs_lean_eq_logic (A : Type) (x y : A) : Lean.eq x y -> Logic.eq x y.
Proof. exact (imported_eq_to_coq_eq x y). Qed.

Definition cs_tr {A : Type} {x y : A} (E : Lean.eq x y) (P : A -> Type) (h : P x) : P y :=
  match E in Lean.eq _ z return P z with Lean.eq_refl => h end.

Definition cs_trs {A : Type} {x y : A} (E : Lean.eq x y) (P : A -> SProp) (h : P x) : P y :=
  match E in Lean.eq _ z return P z with Lean.eq_refl => h end.

Lemma cs_opt_inj (A : Type) (o1 o2 : option A) : Logic.eq (cl_opt o1) (cl_opt o2) -> Logic.eq o1 o2.
Proof. intro E. by rewrite -(cl_unopt_opt o1) -(cl_unopt_opt o2) E. Qed.

Lemma cs_opt_eq_rel (A : Type) (o1 o2 : option A) :
  PropSPropRel (Logic.eq o1 o2) (Lean.eq (cl_opt o1) (cl_opt o2)).
Proof.
  apply prop_sprop_rel_intro.
  - intro E. rewrite E. exact (@Lean.eq_refl _ _).
  - intro E. apply strictly_inhabits. exact (cs_opt_inj A o1 o2 (imported_eq_to_coq_eq _ _ E)).
Qed.

Lemma cs_opt_eqb_rel (A : eqType) (o1 o2 : option A) :
  PropSPropRel (is_true (o1 == o2)) (Lean.eq (cl_opt o1) (cl_opt o2)).
Proof.
  apply prop_sprop_rel_intro.
  - move=> /eqP E. rewrite E. exact (@Lean.eq_refl _ _).
  - intro E. apply strictly_inhabits. apply/eqP. exact (cs_opt_inj A o1 o2 (imported_eq_to_coq_eq _ _ E)).
Qed.

Fixpoint cs_natl (s : seq nat) : I.List_inst1 Lean.Nat :=
  match s with [::] => I.List_nil_inst1 _ | x :: s' => I.List_cons_inst1 _ (sub_nat_to_imported x) (cs_natl s') end.

Lemma cs_iota_range : forall n s,
  Logic.eq (I.List_range' (sub_nat_to_imported s) (sub_nat_to_imported n) (Lean.Nat_succ Lean.Nat_zero)) (cs_natl (iota s n)).
Proof.
  elim => [|n IH] s; first reflexivity.
  change (Logic.eq (I.List_cons_inst1 _ (sub_nat_to_imported s)
      (I.List_range' (sub_nat_to_imported (S s)) (sub_nat_to_imported n) (Lean.Nat_succ Lean.Nat_zero)))
    (I.List_cons_inst1 _ (sub_nat_to_imported s) (cs_natl (iota (S s) n)))).
  by rewrite IH.
Qed.

Lemma cs_foldr_add (f : Lean.Nat -> Lean.Nat) (g : nat -> nat) (Hf : forall k, Logic.eq (f (sub_nat_to_imported k)) (sub_nat_to_imported (g k))) :
  forall s, Logic.eq (I.List_foldr_inst3 Lean.Nat Lean.Nat Lean.Nat_add Lean.Nat_zero (I.List_map_inst3 Lean.Nat Lean.Nat f (cs_natl s)))
                     (sub_nat_to_imported (foldr addn 0 (map g s))).
Proof.
  elim => [|k s IH] //=.
  change (Logic.eq (Lean.Nat_add (f (sub_nat_to_imported k))
            (I.List_foldr_inst3 Lean.Nat Lean.Nat Lean.Nat_add Lean.Nat_zero (I.List_map_inst3 Lean.Nat Lean.Nat f (cs_natl s))))
         (sub_nat_to_imported (g k + foldr addn 0 (map g s)))).
  rewrite IH Hf. exact (imported_eq_to_coq_eq _ _ (sub_add_canonical _ _)).
Qed.

Lemma cs_big_fold (xs : seq nat) (F : nat -> nat) : Logic.eq (\sum_(i <- xs) F i) (foldr addn 0 (map F xs)).
Proof. elim: xs => [|x xs IH]; first by rewrite big_nil. by rewrite big_cons IH. Qed.

Definition CsFunRel (FR : nat -> nat) (FL : Lean.Nat -> Lean.Nat) : SProp :=
  forall kR kL, SubNatRel kR kL -> SubNatRel (FR kR) (FL kL).

Lemma cs_fun_canonical FR FL (HF : CsFunRel FR FL) k : Logic.eq (FL (sub_nat_to_imported k)) (sub_nat_to_imported (FR k)).
Proof. exact (co_nat_logic _ _ (HF _ _ (sub_nat_rel_canonical k))). Qed.

Lemma cs_ico mR mL nR nL FR FL (Hm : SubNatRel mR mL) (Hn : SubNatRel nR nL) (HF : CsFunRel FR FL) :
  SubNatRel (\sum_(mR <= i < nR) FR i)
    (I.List_foldr_inst3 Lean.Nat Lean.Nat Lean.Nat_add Lean.Nat_zero
       (I.List_map_inst3 Lean.Nat Lean.Nat FL (I.List_range' mL (I.Nat_sub nL mL) (Lean.Nat_succ Lean.Nat_zero)))).
Proof.
  rewrite (co_nat_logic _ _ Hm) (co_nat_logic _ _ Hn).
  have -> : Logic.eq (I.Nat_sub (sub_nat_to_imported nR) (sub_nat_to_imported mR)) (sub_nat_to_imported (nR - mR))
    := ct_sub_canonical nR mR.
  rewrite cs_iota_range.
  apply: coq_eq_to_imported_eq. apply: Logic.eq_sym. rewrite (cs_foldr_add FL FR (cs_fun_canonical FR FL HF)).
  by rewrite cs_big_fold.
Qed.

Definition CsParRel (T : Type) (pR : T -> nat) (pL : T -> Lean.Nat) : SProp := forall x, SubNatRel (pR x) (pL x).

Lemma cs_forall_par (T : Type) (PR : (T -> nat) -> Prop) (PL : (T -> Lean.Nat) -> SProp) :
  (forall pR pL, CsParRel T pR pL -> PropSPropRel (PR pR) (PL pL)) -> PropSPropRel (forall p, PR p) (forall p, PL p).
Proof.
  exact (cs_forall_cover _ _ (CsParRel T) (fun pR j => sub_nat_to_imported (pR j)) (fun pL j => sub_nat_to_rocq (pL j))
           (fun pR j => sub_nat_rel_canonical (pR j)) (fun pL j => sub_nat_rel_surjective (pL j)) PR PL).
Qed.

Section Sched.
Variables (Job : eqType) (nR : nat) (nL : Lean.Nat).
Hypothesis Hn : SubNatRel nR nL.
Notation dJ := (ct_decidable_eq Job).
Notation LSched := (I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_schedule Job dJ nL).

Definition CsSchedRel (sR : Schedule.schedule Job nR) (sL : LSched) : SProp :=
  forall oR oL, CoOrdRel nR nL oR oL -> forall tR tL, SubNatRel tR tL -> Lean.eq (cl_opt (sR oR tR)) (sL oL tL).

Definition cs_sched_to_target (sR : Schedule.schedule Job nR) : LSched :=
  fun oL tL => cl_opt (sR (co_fin_to_ord nR nL Hn oL) (sub_nat_to_rocq tL)).

Definition cs_sched_to_source (sL : LSched) : Schedule.schedule Job nR :=
  fun oR tR => cl_unopt (sL (co_ord_to_fin nR nL Hn oR) (sub_nat_to_imported tR)).

Lemma cs_sched_canonical sR : CsSchedRel sR (cs_sched_to_target sR).
Proof.
  intros oR oL Ho tR tL Ht. apply: coq_eq_to_imported_eq. rewrite /cs_sched_to_target (co_nat_input _ _ Ht).
  by rewrite (co_ord_eq _ _ _ _ _ Ho (co_ord_surjective nR nL Hn oL)).
Qed.

Lemma cs_sched_surjective sL : CsSchedRel (cs_sched_to_source sL) sL.
Proof.
  intros oR oL Ho tR tL Ht. apply: coq_eq_to_imported_eq. rewrite /cs_sched_to_source cl_opt_unopt.
  rewrite (co_nat_logic _ _ Ht). by rewrite (co_fin_rel_eq _ _ _ _ _ (co_ord_canonical nR nL Hn oR) Ho).
Qed.

Lemma cs_forall_sched (PR : Schedule.schedule Job nR -> Prop) (PL : LSched -> SProp) :
  (forall sR sL, CsSchedRel sR sL -> PropSPropRel (PR sR) (PL sL)) -> PropSPropRel (forall s, PR s) (forall s, PL s).
Proof. exact (cs_forall_cover _ _ CsSchedRel cs_sched_to_target cs_sched_to_source cs_sched_canonical cs_sched_surjective PR PL). Qed.
End Sched.

Section Arr.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).
Notation LArr := (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrival_sequence Job dJ).

Definition CsArrRel (aR : ArrivalSequence.arrival_sequence Job) (aL : LArr) : SProp :=
  forall tR tL, SubNatRel tR tL -> ClListRel cid (aR tR) (aL tL).

Definition cs_arr_to_target (aR : ArrivalSequence.arrival_sequence Job) : LArr :=
  fun tL => cl_map cid (aR (sub_nat_to_rocq tL)).

Definition cs_arr_to_source (aL : LArr) : ArrivalSequence.arrival_sequence Job :=
  fun tR => cl_unmap cid (aL (sub_nat_to_imported tR)).

Lemma cs_arr_canonical aR : CsArrRel aR (cs_arr_to_target aR).
Proof.
  intros tR tL Ht. have E := co_nat_logic _ _ Ht. subst tL.
  apply: coq_eq_to_imported_eq. rewrite /cs_arr_to_target sub_nat_rocq_roundtrip. reflexivity.
Qed.

Lemma cs_arr_surjective aL : CsArrRel (cs_arr_to_source aL) aL.
Proof.
  intros tR tL Ht. have E := co_nat_logic _ _ Ht. subst tL.
  apply: coq_eq_to_imported_eq. exact (cl_map_unmap cid cid (fun _ => Logic.eq_refl _) _).
Qed.

Lemma cs_arrives_in aR aL (Ha : CsArrRel aR aL) j :
  PropSPropRel (ArrivalSequence.arrives_in aR j)
    (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrives_in Job dJ aL j).
Proof. apply: ct_exists_nat => tR tL Ht. exact (cs_mem Job j _ _ (Ha tR tL Ht)). Qed.
End Arr.

Lemma cs_map_natl {B : Type} (f : Lean.Nat -> B) : forall s,
  Logic.eq (I.List_map_inst1 Lean.Nat B f (cs_natl s)) (cl_map (fun k => f (sub_nat_to_imported k)) s).
Proof.
  elim => [|k s IH] //=.
  change (Logic.eq (I.List_cons B (f (sub_nat_to_imported k)) (I.List_map_inst1 Lean.Nat B f (cs_natl s)))
                   (I.List_cons B (f (sub_nat_to_imported k)) (cl_map (fun k => f (sub_nat_to_imported k)) s))).
  by rewrite IH.
Qed.

Lemma cs_big_seq {A : Type} (F : nat -> seq A) : forall s : seq nat,
  Logic.eq (\big[cat/[::]]_(i <- s) F i) (flatten (map F s)).
Proof. elim => [|x s IH]; first by rewrite big_nil. by rewrite big_cons IH. Qed.

Definition CsNatFamRel (A : Type) (fR : nat -> seq A) (fL : Lean.Nat -> I.List A) : SProp :=
  forall nR nL, SubNatRel nR nL -> ClListRel cid (fR nR) (fL nL).

Lemma cs_bigcat_nat_rel (A : Type) fR fL (Hf : CsNatFamRel A fR fL) mR mL nR nL :
  SubNatRel mR mL -> SubNatRel nR nL ->
  ClListRel cid (\big[cat/[::]]_(mR <= t < nR) fR t) (I.Prosa_Util_Notation_bigCat A mL nL fL).
Proof.
  intros Hm Hn. have E1 := co_nat_logic _ _ Hm. have E2 := co_nat_logic _ _ Hn. subst mL nL.
  apply: coq_eq_to_imported_eq. apply: Logic.eq_sym.
  rewrite (imported_eq_to_coq_eq _ _ (I.Prosa_Validation_ClassicInterferenceBoundEdfInterface_bigCat_range'
             A (sub_nat_to_imported mR) (sub_nat_to_imported nR) fL)).
  have Hd : Logic.eq (I.HSub_hSub_inst7 Lean.Nat Lean.Nat Lean.Nat (I.instHSub_inst1 Lean.Nat I.instSubNat)
                       (sub_nat_to_imported nR) (sub_nat_to_imported mR)) (sub_nat_to_imported (nR - mR)) :=
    ct_sub_canonical nR mR.
  rewrite Hd.
  change (I.OfNat_ofNat_inst1 Lean.Nat 0 (I.instOfNatNat 0)) with (sub_nat_to_imported 0).
  rewrite (co_iota_range (nR - mR) 0) co_map_inst1. cbv beta.
  have Hpt : forall k, Logic.eq
      (fL (I.HAdd_hAdd_inst7 Lean.Nat Lean.Nat Lean.Nat (I.instHAdd_inst1 Lean.Nat I.instAddNat)
             (sub_nat_to_imported mR) (sub_nat_to_imported k)))
      (cl_map cid (fR (mR + k))).
  { intro k. exact (cl_list_logic _ _ _ (Hf _ _ (sub_add_correspondence mR _ k _
       (sub_nat_rel_canonical mR) (sub_nat_rel_canonical k)))). }
  rewrite (co_cl_map_ext _ _ Hpt) (co_cl_map_comp (fun k => fR (mR + k)) (cl_map cid)) co_flatten.
  have Hi : Logic.eq (iota mR (nR - mR)) (map (addn mR) (iota 0 (nR - mR))) by rewrite -iotaDl addn0.
  rewrite cs_big_seq /index_iota Hi -map_comp.
  reflexivity.
Qed.

Lemma cs_notin_target (T : eqType) x s : Logic.eq (x \in s) false ->
  I.Not (I.Membership_mem T (I.List T) (I.List_instMembership T) (cl_map cid s) x).
Proof.
  intros Hx H. apply: ct_coq_false_to_target.
  have Hm := sprop_to_prop _ _ (cs_mem T x s _ (cl_lean_eq _ _ _ (Logic.eq_refl _))) H.
  rewrite Hx in Hm. discriminate.
Qed.

Lemma cs_undup_rel (T : eqType) : forall s sL, ClListRel cid s sL ->
  ClListRel cid (undup s) (I.List_dedup T (ct_decidable_eq T) sL).
Proof.
  intros s sL Hs. have E := cl_list_logic _ _ _ Hs. subst sL. apply: coq_eq_to_imported_eq. clear Hs.
  elim: s => [|x s IH].
  - exact (Logic.eq_sym (imported_eq_to_coq_eq _ _ (I.Prosa_Validation_ClassicInterferenceBoundEdfInterface_dedup_nil T (ct_decidable_eq T)))).
  - change (Logic.eq (cl_map cid (if x \in s then undup s else x :: undup s))
      (I.List_dedup T (ct_decidable_eq T) (I.List_cons T x (cl_map cid s)))).
    case Hx: (x \in s).
    + rewrite (imported_eq_to_coq_eq _ _ (I.Prosa_Validation_ClassicInterferenceBoundEdfInterface_dedup_cons_mem
                 T (ct_decidable_eq T) x (cl_map cid s)
                 (prop_to_sprop _ _ (cs_mem T x s _ (cl_lean_eq _ _ _ (Logic.eq_refl _))) Hx))).
      exact IH.
    + rewrite (imported_eq_to_coq_eq _ _ (I.Prosa_Validation_ClassicInterferenceBoundEdfInterface_dedup_cons_not_mem
                 T (ct_decidable_eq T) x (cl_map cid s) (cs_notin_target T x s Hx))).
      change (Logic.eq (I.List_cons T x (cl_map cid (undup s))) (I.List_cons T x (I.List_dedup T (ct_decidable_eq T) (cl_map cid s)))).
      by rewrite IH.
Qed.

Section Defs.
Variables (Job : eqType) (nR : nat) (nL : Lean.Nat).
Hypothesis Hn : SubNatRel nR nL.
Notation dJ := (ct_decidable_eq Job).
Variables (sR : Schedule.schedule Job nR)
  (sL : I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_schedule Job dJ nL).
Hypothesis Hs : CsSchedRel Job nR nL sR sL.

Lemma cf_Schedule_scheduled_on j oR oL (Ho : CoOrdRel nR nL oR oL) tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (Schedule.scheduled_on sR j oR tR)
    (I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_scheduled_on Job dJ nL sL j oL tL).
Proof.
  apply: ct_decide_bool.
  exact (cs_tr (Hs oR oL Ho tR tL Ht) (fun z => PropSPropRel (sR oR tR == Some j) (Lean.eq z (cl_opt (Some j))))
           (cs_opt_eqb_rel Job (sR oR tR) (Some j))).
Qed.

Lemma cf_Schedule_scheduled j tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (Schedule.scheduled sR j tR)
    (I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_scheduled Job dJ nL sL j tL).
Proof.
  apply: (co_exists_rel nR nL Hn). intros oR oL Ho. exact (cf_Schedule_scheduled_on j oR oL Ho tR tL Ht).
Qed.

Lemma cf_Schedule_service_at j tR tL (Ht : SubNatRel tR tL) :
  SubNatRel (Schedule.service_at sR j tR)
    (I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_service_at Job dJ nL sL j tL).
Proof.
  apply: coq_eq_to_imported_eq.
  rewrite (imported_eq_to_coq_eq _ _ (I.Prosa_Validation_ClassicInterferenceBoundEdfInterface_service_at_sum Job dJ nL sL j tL)).
  apply: imported_eq_to_coq_eq.
  rewrite /Schedule.service_at big_mkcond /=.
  apply: (co_sum_rel nR nL Hn). intros oR oL Ho.
  have H := cf_Schedule_scheduled_on j oR oL Ho tR tL Ht.
  rewrite (ct_bool_rel_logic _ _ H). destruct (Schedule.scheduled_on sR j oR tR).
  - exact (sub_nat_rel_canonical 1).
  - exact (sub_nat_rel_canonical 0).
Qed.

Lemma cs_service_at_fun j : CsFunRel (fun t => Schedule.service_at sR j t)
    (fun t => I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_service_at Job dJ nL sL j t).
Proof. intros kR kL Hk. exact (cf_Schedule_service_at j kR kL Hk). Qed.

Lemma cf_Schedule_service j tR tL (Ht : SubNatRel tR tL) :
  SubNatRel (Schedule.service sR j tR)
    (I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_service Job dJ nL sL j tL).
Proof. exact (cs_ico 0 _ tR tL _ _ (sub_nat_rel_canonical 0) Ht (cs_service_at_fun j)). Qed.

Lemma cf_Schedule_completed cR cL (Hc : CsParRel Job cR cL) j tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (Schedule.completed cR sR j tR)
    (I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_completed Job dJ cL nL sL j tL).
Proof. exact (ct_decide_le _ _ _ _ (Hc j) (cf_Schedule_service j tR tL Ht)). Qed.

Lemma cf_Schedule_pending aR aL (Ha : CsParRel Job aR aL) cR cL (Hc : CsParRel Job cR cL) j tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (Schedule.pending aR cR sR j tR)
    (I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_pending Job dJ aL cL nL sL j tL).
Proof.
  exact (ct_bool_and _ _ _ _ (ct_decide_le _ _ _ _ (Ha j) Ht)
           (ct_bool_not _ _ (cf_Schedule_completed cR cL Hc j tR tL Ht))).
Qed.

Lemma cf_Schedule_backlogged aR aL (Ha : CsParRel Job aR aL) cR cL (Hc : CsParRel Job cR cL) j tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (Schedule.backlogged aR cR sR j tR)
    (I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_backlogged Job dJ aL cL nL sL j tL).
Proof.
  exact (ct_bool_and _ _ _ _ (cf_Schedule_pending aR aL Ha cR cL Hc j tR tL Ht)
           (ct_bool_not _ _ (cf_Schedule_scheduled j tR tL Ht))).
Qed.

Lemma cs_make_sequence (o : option Job) :
  ClListRel cid (make_sequence o) (I.Prosa_Classic_Util_Notation_make_sequence Job (cl_opt o)).
Proof. destruct o as [x|]; exact (@Lean.eq_refl _ _). Qed.

Lemma cf_Schedule_jobs_scheduled_at tR tL (Ht : SubNatRel tR tL) :
  ClListRel cid (Schedule.jobs_scheduled_at sR tR)
    (I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_jobs_scheduled_at Job dJ nL sL tL).
Proof.
  apply: (co_bigcat_rel Job nR nL Hn). intros oR oL Ho.
  exact (cs_trs (Hs oR oL Ho tR tL Ht)
           (fun z => ClListRel cid (make_sequence (sR oR tR)) (I.Prosa_Classic_Util_Notation_make_sequence Job z))
           (cs_make_sequence (sR oR tR))).
Qed.

Lemma cf_Schedule_jobs_scheduled_between t1R t1L t2R t2L (H1 : SubNatRel t1R t1L) (H2 : SubNatRel t2R t2L) :
  ClListRel cid (Schedule.jobs_scheduled_between sR t1R t2R)
    (I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_jobs_scheduled_between Job dJ nL sL t1L t2L).
Proof.
  apply: cs_undup_rel. apply: (cs_bigcat_nat_rel Job (fun t => Schedule.jobs_scheduled_at sR t) _ _ _ _ _ _ H1 H2).
  intros kR kL Hk. exact (cf_Schedule_jobs_scheduled_at kR kL Hk).
Qed.

Lemma cf_Schedule_sequential_jobs :
  PropSPropRel (Schedule.sequential_jobs sR)
    (I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_sequential_jobs Job dJ nL sL).
Proof.
  apply: ct_forall_identity => j. apply: ct_forall_nat => tR tL Ht.
  apply: (co_forall_ord nR nL Hn) => o1R o1L H1. apply: (co_forall_ord nR nL Hn) => o2R o2L H2.
  apply: ct_imp.
  { exact (cs_tr (Hs o1R o1L H1 tR tL Ht) (fun z => PropSPropRel (sR o1R tR = Some j) (Lean.eq z (cl_opt (Some j))))
             (cs_opt_eq_rel Job (sR o1R tR) (Some j))). }
  apply: ct_imp.
  { exact (cs_tr (Hs o2R o2L H2 tR tL Ht) (fun z => PropSPropRel (sR o2R tR = Some j) (Lean.eq z (cl_opt (Some j))))
             (cs_opt_eq_rel Job (sR o2R tR) (Some j))). }
  exact (co_ord_eq_rel _ _ _ _ _ _ H1 H2).
Qed.

Lemma cf_Schedule_jobs_must_arrive_to_execute aR aL (Ha : CsParRel Job aR aL) :
  PropSPropRel (Schedule.jobs_must_arrive_to_execute aR sR)
    (I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_jobs_must_arrive_to_execute Job dJ aL nL sL).
Proof.
  apply: ct_forall_identity => j. apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (ct_bool_truth _ _ (cf_Schedule_scheduled j tR tL Ht)).
  exact (ct_bool_truth _ _ (ct_decide_le _ _ _ _ (Ha j) Ht)).
Qed.

Lemma cf_Schedule_completed_jobs_dont_execute cR cL (Hc : CsParRel Job cR cL) :
  PropSPropRel (Schedule.completed_jobs_dont_execute cR sR)
    (I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_completed_jobs_dont_execute Job dJ cL nL sL).
Proof.
  apply: ct_forall_identity => j. apply: ct_forall_nat => tR tL Ht.
  exact (sub_nat_le_correspondence _ _ _ _ (cf_Schedule_service j tR tL Ht) (Hc j)).
Qed.

Lemma cf_Schedule_jobs_come_from_arrival_sequence arrR arrL (Harr : CsArrRel Job arrR arrL) :
  PropSPropRel (Schedule.jobs_come_from_arrival_sequence sR arrR)
    (I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_jobs_come_from_arrival_sequence Job dJ nL sL arrL).
Proof.
  apply: ct_forall_identity => j. apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (ct_bool_truth _ _ (cf_Schedule_scheduled j tR tL Ht)).
  exact (cs_arrives_in Job arrR arrL Harr j).
Qed.
End Defs.

Section TaskDefs.
Variables (Task Job : eqType) (nR : nat) (nL : Lean.Nat).
Hypothesis Hn : SubNatRel nR nL.
Notation dT := (ct_decidable_eq Task).
Notation dJ := (ct_decidable_eq Job).
Variables (sR : Schedule.schedule Job nR)
  (sL : I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_schedule Job dJ nL).
Hypothesis Hs : CsSchedRel Job nR nL sR sL.
Variable job_task : Job -> Task.

Lemma cf_ScheduleOfSporadicTask_task_scheduled_on tsk oR oL (Ho : CoOrdRel nR nL oR oL) tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (ScheduleOfSporadicTask.task_scheduled_on job_task sR tsk oR tR)
    (I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_ScheduleOfSporadicTask_task_scheduled_on Task Job dT dJ job_task nL sL tsk oL tL).
Proof.
  refine (cs_trs (Hs oR oL Ho tR tL Ht)
            (fun z => CtBoolRel (ScheduleOfSporadicTask.task_scheduled_on job_task sR tsk oR tR)
                        (match z with
                         | I.Option_some j => I.Decidable_decide (Lean.eq (job_task j) tsk) (dT (job_task j) tsk)
                         | I.Option_none => I.Bool_false end)) _).
  rewrite /ScheduleOfSporadicTask.task_scheduled_on. destruct (sR oR tR) as [x|].
  - exact (ct_decide_eq Task (job_task x) tsk).
  - exact (ct_bool_canonical false).
Qed.
End TaskDefs.

Lemma cs_forall_ncpus_sched (Job : eqType)
    (PR : forall n : nat, Schedule.schedule Job n -> Prop)
    (PL : forall n : Lean.Nat, I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_schedule Job (ct_decidable_eq Job) n -> SProp) :
  (forall nR nL (Hn : SubNatRel nR nL) sR sL, CsSchedRel Job nR nL sR sL -> PropSPropRel (PR nR sR) (PL nL sL)) ->
  PropSPropRel (forall n s, PR n s) (forall n s, PL n s).
Proof.
  intro H. apply: ct_forall_nat => nR nL Hn. exact (cs_forall_sched Job nR nL Hn _ _ (H nR nL Hn)).
Qed.

(* ------------------------------------------------------------------ *)
(** * Interference (as in the accepted classic global interference certificate) *)

Lemma cai_sum_map (T : Type) FR FL (HF : forall x, SubNatRel (FR x) (FL x)) : forall l,
  SubNatRel (\sum_(i <- l) FR i)
    (I.List_sum_inst1 Lean.Nat I.instAddNat (I.MulZeroClass_toZero_inst1 Lean.Nat I.Nat_instMulZeroClass)
       (I.List_map_inst2 T Lean.Nat FL (cl_map cid l))).
Proof.
  intro l. induction l as [|x l IH]; first by rewrite big_nil; exact (sub_nat_rel_canonical 0).
  rewrite big_cons. exact (sub_add_correspondence _ _ _ _ (HF x) IH).
Qed.

Lemma cai_sumFiltered (T : Type) (PR : T -> bool) PL (HP : forall x, CtBoolRel (PR x) (PL x)) FR FL
    (HF : forall x, SubNatRel (FR x) (FL x)) : forall l,
  SubNatRel (\sum_(i <- l | PR i) FR i) (I.Prosa_Util_Sum_sumFiltered T (cl_map cid l) PL FL).
Proof.
  intro l. rewrite -big_filter.
  refine (cs_trs (cl_lean_eq _ _ _ (cl_filter cid PR PL HP l))
            (fun z => SubNatRel (\sum_(i <- filter PR l) FR i)
                        (I.List_sum_inst1 Lean.Nat I.instAddNat (I.MulZeroClass_toZero_inst1 Lean.Nat I.Nat_instMulZeroClass)
                           (I.List_map_inst2 T Lean.Nat FL z))) _).
  exact (cai_sum_map T FR FL HF (filter PR l)).
Qed.

Lemma cai_sumFiltered_rel (T : Type) (PR : T -> bool) PL (HP : forall x, CtBoolRel (PR x) (PL x)) FR FL
    (HF : forall x, SubNatRel (FR x) (FL x)) l L : ClListRel (B := T) cid l L ->
  SubNatRel (\sum_(i <- l | PR i) FR i) (I.Prosa_Util_Sum_sumFiltered T L PL FL).
Proof.
  intro H. exact (cs_trs H (fun z => SubNatRel (\sum_(i <- l | PR i) FR i) (I.Prosa_Util_Sum_sumFiltered T z PL FL))
                    (cai_sumFiltered T PR PL HP FR FL HF l)).
Qed.

Section IntDefs.
Variables (Task Job : eqType) (nR : nat) (nL : Lean.Nat).
Hypothesis Hn : SubNatRel nR nL.
Notation dT := (ct_decidable_eq Task).
Notation dJ := (ct_decidable_eq Job).
Variables (sR : Schedule.schedule Job nR)
  (sL : I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_schedule Job dJ nL).
Hypothesis Hs : CsSchedRel Job nR nL sR sL.
Variables (jaR : Job -> nat) (jaL : Job -> Lean.Nat) (cR : Job -> nat) (cL : Job -> Lean.Nat).
Hypotheses (Hja : CsParRel Job jaR jaL) (Hc : CsParRel Job cR cL).
Variable job_task : Job -> Task.

Notation bl := (cf_Schedule_backlogged Job nR nL Hn sR sL Hs jaR jaL Hja cR cL Hc).

Theorem Interference_job_interference_correspondence j j_other t1R t1L t2R t2L (H1 : SubNatRel t1R t1L) (H2 : SubNatRel t2R t2L) :
  SubNatRel (Interference.job_interference jaR cR sR j j_other t1R t2R)
    (I.Prosa_Classic_Model_Schedule_Global_Basic_Interference_Interference_job_interference Job dJ jaL cL nL sL j j_other t1L t2L).
Proof.
  apply: (cs_ico _ _ _ _ _ _ H1 H2) => tR tL Ht.
  apply: (co_sum_rel nR nL Hn) => oR oL Ho.
  exact (ct_bool_to_nat _ _ (ct_bool_and _ _ _ _ (bl j tR tL Ht)
           (cf_Schedule_scheduled_on Job nR nL sR sL Hs j_other oR oL Ho tR tL Ht))).
Qed.

Theorem Interference_task_interference_correspondence j tsk_other t1R t1L t2R t2L (H1 : SubNatRel t1R t1L) (H2 : SubNatRel t2R t2L) :
  SubNatRel (Interference.task_interference jaR cR job_task sR j tsk_other t1R t2R)
    (I.Prosa_Classic_Model_Schedule_Global_Basic_Interference_Interference_task_interference Task Job dT dJ jaL cL job_task nL sL j tsk_other t1L t2L).
Proof.
  apply: (cs_ico _ _ _ _ _ _ H1 H2) => tR tL Ht.
  apply: (co_sum_rel nR nL Hn) => oR oL Ho.
  exact (ct_bool_to_nat _ _ (ct_bool_and _ _ _ _ (bl j tR tL Ht)
           (cf_ScheduleOfSporadicTask_task_scheduled_on Task Job nR nL sR sL Hs job_task tsk_other oR oL Ho tR tL Ht))).
Qed.

End IntDefs.

(* ------------------------------------------------------------------ *)
(** * Policies and platform (as in the accepted classic priority and global platform certificates) *)

Definition CpRelRel (T : Type) (rR : T -> T -> bool) (rL : T -> T -> I.Bool) : SProp :=
  forall a b, CtBoolRel (rR a b) (rL a b).

Lemma cp_forall_rel (T : Type) (PR : (T -> T -> bool) -> Prop) (PL : (T -> T -> I.Bool) -> SProp) :
  (forall rR rL, CpRelRel T rR rL -> PropSPropRel (PR rR) (PL rL)) -> PropSPropRel (forall r, PR r) (forall r, PL r).
Proof.
  exact (cs_forall_cover _ _ (CpRelRel T) (fun rR a b => ct_b2l (rR a b)) (fun rL a b => ct_l2b (rL a b))
           (fun rR a b => ct_bool_canonical _) (fun rL a b => ct_bool_surjective _) PR PL).
Qed.

Definition CpJldpRel (T : Type) (rR : nat -> T -> T -> bool) (rL : Lean.Nat -> T -> T -> I.Bool) : SProp :=
  forall tR tL, SubNatRel tR tL -> CpRelRel T (rR tR) (rL tL).

Section PlatDefs.
Variables (Task Job : eqType) (nR : nat) (nL : Lean.Nat).
Hypothesis Hn : SubNatRel nR nL.
Notation dT := (ct_decidable_eq Task).
Notation dJ := (ct_decidable_eq Job).
Variables (sR : Schedule.schedule Job nR) (sL : I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_schedule Job dJ nL).
Hypothesis Hs : CsSchedRel Job nR nL sR sL.
Variables (jaR : Job -> nat) (jaL : Job -> Lean.Nat) (cR : Job -> nat) (cL : Job -> Lean.Nat).
Hypotheses (Hja : CsParRel Job jaR jaL) (Hc : CsParRel Job cR cL).
Variable job_task : Job -> Task.
Variables (aR : ArrivalSequence.arrival_sequence Job) (aL : I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrival_sequence Job dJ).
Hypothesis Ha : CsArrRel Job aR aL.
Notation bl := (cf_Schedule_backlogged Job nR nL Hn sR sL Hs jaR jaL Hja cR cL Hc).
Notation son := (cf_Schedule_scheduled_on Job nR nL sR sL Hs).
Notation sch := (cf_Schedule_scheduled Job nR nL Hn sR sL Hs).

Theorem Platform_respects_JLFP_policy_correspondence hpR hpL (Hhp : CpRelRel Job hpR hpL) :
  PropSPropRel (Platform.respects_JLFP_policy jaR cR aR sR hpR) (I.Prosa_Classic_Model_Schedule_Global_Basic_Platform_Platform_respects_JLFP_policy Job dJ jaL cL aL nL sL hpL).
Proof.
  apply: ct_forall_identity => j. apply: ct_forall_identity => j_hp. apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (cs_arrives_in Job aR aL Ha j).
  apply: ct_imp; first exact (ct_bool_truth _ _ (bl j tR tL Ht)).
  apply: ct_imp; first exact (ct_bool_truth _ _ (sch j_hp tR tL Ht)).
  exact (ct_bool_truth _ _ (Hhp j_hp j)).
Qed.
End PlatDefs.

(* ------------------------------------------------------------------ *)
(** * Response-time bounds (as in the accepted classic response_time certificate) *)


(* ------------------------------------------------------------------ *)
(** * Task model, job validity and sequence sums (as in the accepted classic task_arrival and workload_bound certificates) *)

Lemma cta_false_rel : PropSPropRel Logic.False I.False.
Proof.
  apply prop_sprop_rel_intro.
  - exact ct_coq_false_to_target.
  - exact ct_target_false_to_strict.
Qed.

Lemma cta_ne (T : Type) (x y : T) : PropSPropRel (x <> y) (I.Ne T x y).
Proof. exact (ct_imp _ _ _ _ (ct_eq_rel T x y) cta_false_rel). Qed.

Lemma cta_succ_rel nR nL : SubNatRel nR nL ->
  SubNatRel nR.+1 (I.HAdd_hAdd_inst7 Lean.Nat Lean.Nat Lean.Nat (I.instHAdd_inst1 Lean.Nat I.instAddNat) nL
                     (I.OfNat_ofNat_inst1 Lean.Nat 1 (I.instOfNatNat 1))).
Proof. intro Hn. exact (sub_imported_eq_congr Lean.Nat_succ _ _ Hn). Qed.

Lemma cwb_forall_arr (Job : eqType) PR PL :
  (forall aR aL, CsArrRel Job aR aL -> PropSPropRel (PR aR) (PL aL)) -> PropSPropRel (forall a, PR a) (forall a, PL a).
Proof. exact (cs_forall_cover _ _ (CsArrRel Job) (cs_arr_to_target Job) (cs_arr_to_source Job) (cs_arr_canonical Job) (cs_arr_surjective Job) PR PL). Qed.

Lemma cwb_valid_sporadic_job (Task Job : eqType) tcR tcL (Htc : CsParRel Task tcR tcL) tdR tdL (Htd : CsParRel Task tdR tdL)
    cR cL (Hc : CsParRel Job cR cL) dR dL (Hd : CsParRel Job dR dL) (job_task : Job -> Task) j :
  PropSPropRel (Job.valid_sporadic_job tcR tdR cR dR job_task j)
    (I.Prosa_Classic_Model_Arrival_Basic_Job_Job_valid_sporadic_job Task (ct_decidable_eq Task) tcL tdL Job (ct_decidable_eq Job) cL dL job_task j).
Proof.
  apply: ct_and.
  { apply: ct_and; first exact (ct_bool_truth _ _ (ct_decide_lt _ _ _ _ (sub_nat_rel_canonical 0) (Hc j))).
    apply: ct_and; first exact (ct_bool_truth _ _ (ct_decide_le _ _ _ _ (Hc j) (Hd j))).
    exact (ct_bool_truth _ _ (ct_decide_lt _ _ _ _ (sub_nat_rel_canonical 0) (Hd j))). }
  apply: ct_and; first exact (ct_bool_truth _ _ (ct_decide_le _ _ _ _ (Hc j) (Htc (job_task j)))).
  exact (sub_nat_eq_correspondence _ _ _ _ (Hd j) (Htd (job_task j))).
Qed.

Lemma cwb_sporadic_task_model (Task Job : eqType) tpR tpL (Htp : CsParRel Task tpR tpL) jaR jaL (Hja : CsParRel Job jaR jaL)
    (job_task : Job -> Task) aR aL (Ha : CsArrRel Job aR aL) :
  PropSPropRel (TaskArrival.sporadic_task_model tpR jaR job_task aR)
    (I.Prosa_Classic_Model_Arrival_Basic_TaskArrival_TaskArrival_sporadic_task_model Task (ct_decidable_eq Task) tpL Job (ct_decidable_eq Job) jaL job_task aL).
Proof.
  apply: ct_forall_identity => j. apply: ct_forall_identity => j'.
  apply: ct_imp; first exact (cta_ne Job j j').
  apply: ct_imp; first exact (cs_arrives_in Job aR aL Ha j).
  apply: ct_imp; first exact (cs_arrives_in Job aR aL Ha j').
  apply: ct_imp; first exact (ct_eq_rel Task (job_task j) (job_task j')).
  apply: ct_imp; first exact (sub_nat_le_correspondence _ _ _ _ (Hja j) (Hja j')).
  exact (sub_nat_le_correspondence _ _ _ _ (sub_add_correspondence _ _ _ _ (Hja j) (Htp (job_task j))) (Hja j')).
Qed.

Lemma cwb_valid_sporadic_task (Task : eqType) cR cL (Hc : CsParRel Task cR cL) pR pL (Hp : CsParRel Task pR pL)
    dR dL (Hd : CsParRel Task dR dL) tsk :
  PropSPropRel (SporadicTask.is_valid_sporadic_task cR pR dR tsk)
    (I.Prosa_Classic_Model_Arrival_Basic_Task_SporadicTask_is_valid_sporadic_task Task (ct_decidable_eq Task) cL pL dL tsk).
Proof.
  apply: ct_and; first exact (ct_bool_truth _ _ (ct_decide_lt _ _ _ _ (sub_nat_rel_canonical 0) (Hc tsk))).
  apply: ct_and; first exact (ct_bool_truth _ _ (ct_decide_lt _ _ _ _ (sub_nat_rel_canonical 0) (Hp tsk))).
  apply: ct_and; first exact (ct_bool_truth _ _ (ct_decide_lt _ _ _ _ (sub_nat_rel_canonical 0) (Hd tsk))).
  apply: ct_and; first exact (ct_bool_truth _ _ (ct_decide_le _ _ _ _ (Hc tsk) (Hd tsk))).
  exact (ct_bool_truth _ _ (ct_decide_le _ _ _ _ (Hc tsk) (Hp tsk))).
Qed.

Lemma cai_sumSeq (T : Type) (FR : T -> nat) (FL : T -> Lean.Nat) (HF : forall x, SubNatRel (FR x) (FL x)) : forall l,
  SubNatRel (\sum_(i <- l) FR i) (I.Prosa_Util_Sum_sumSeq T (cl_map cid l) FL).
Proof.
  intro l. induction l as [|x l IH]; first by rewrite big_nil; exact (sub_nat_rel_canonical 0).
  rewrite big_cons.
  change (SubNatRel (FR x + \sum_(j <- l) FR j) (Lean.Nat_add (FL x) (I.Prosa_Util_Sum_sumSeq T (cl_map cid l) FL))).
  exact (sub_add_correspondence _ _ _ _ (HF x) IH).
Qed.

Lemma cwb_sumSeq_rel (T : Type) FR FL (HF : forall x, SubNatRel (FR x) (FL x)) l L : ClListRel (B := T) cid l L ->
  SubNatRel (\sum_(i <- l) FR i) (I.Prosa_Util_Sum_sumSeq T L FL).
Proof. intro H. exact (cs_trs H (fun z => SubNatRel (\sum_(i <- l) FR i) (I.Prosa_Util_Sum_sumSeq T z FL)) (cai_sumSeq T FR FL HF l)). Qed.

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

Lemma cta_pred_rel nR nL : SubNatRel nR nL ->
  SubNatRel nR.-1 (ct_sub nL (I.OfNat_ofNat_inst1 Lean.Nat 1 (I.instOfNatNat 1))).
Proof.
  intro Hn. apply: coq_eq_to_imported_eq. rewrite -subn1.
  exact (imported_eq_to_coq_eq _ _ (ct_sub_rel _ _ _ _ Hn (sub_nat_rel_canonical 1))).
Qed.

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
          end (I.Prosa_Validation_ClassicInterferenceBoundEdfInterface_mergeSort_isChain T fL sL))).
  have Fu : forall x, filter (fun y => f y == f x) u = filter (fun y => f y == f x) s.
  { intro x. apply: cta_cl_map_inj.
    have Hp : forall y, CtBoolRel (f y == f x) (clsL x y) := fun y => ct_decide_eq_nat _ _ _ _ (Hf y) (Hf x).
    refine (Logic.eq_trans (cl_filter cid (fun y => f y == f x) (clsL x) Hp u)
              (Logic.eq_trans _ (Logic.eq_sym (cl_filter cid (fun y => f y == f x) (clsL x) Hp s)))).
    refine (Logic.eq_trans (f_equal (I.List_filter T (clsL x)) (Logic.eq_sym (cl_list_logic _ _ _ Hu)))
              (Logic.eq_trans _ (f_equal (I.List_filter T (clsL x)) (cl_list_logic _ _ _ Hs)))).
    exact (imported_eq_to_coq_eq _ _ (I.Prosa_Validation_ClassicInterferenceBoundEdfInterface_mergeSort_filter_class T fL x sL)). }
  have E := cta_sort_unique T f u s Su Fu.
  apply: coq_eq_to_imported_eq. rewrite -E. exact (Logic.eq_sym (cl_list_logic _ _ _ Hu)).
Qed.
End Sort.

Lemma cwb_add2 nR nL : SubNatRel nR nL ->
  SubNatRel nR.+2 (I.HAdd_hAdd_inst7 Lean.Nat Lean.Nat Lean.Nat (I.instHAdd_inst1 Lean.Nat I.instAddNat) nL
                     (I.OfNat_ofNat_inst1 Lean.Nat 2 (I.instOfNatNat 2))).
Proof.
  intro H. apply: coq_eq_to_imported_eq. rewrite -addn2.
  exact (imported_eq_to_coq_eq _ _ (sub_add_correspondence _ _ 2 _ H (sub_nat_rel_canonical 2))).
Qed.

(* ------------------------------------------------------------------ *)
(** * Workload and interference bounds (as in the accepted classic interference_bound_fp certificate) *)

Lemma cib_max_jobs (Task : eqType) cR cL (Hc : CsParRel Task cR cL) pR pL (Hp : CsParRel Task pR pL) tsk
    RR RL (HR : SubNatRel RR RL) dR dL (Hd : SubNatRel dR dL) :
  SubNatRel (WorkloadBound.max_jobs cR pR tsk RR dR) (I.Prosa_Classic_Analysis_Global_Basic_WorkloadBound_WorkloadBound_max_jobs Task (ct_decidable_eq Task) cL pL tsk RL dL).
Proof.
  exact (dm_div_floor_correspondence _ _ _ _ (dm_sub_correspondence _ _ _ _ (dm_add_correspondence _ _ _ _ Hd HR) (Hc tsk)) (Hp tsk)).
Qed.

Lemma cib_W (Task : eqType) cR cL (Hc : CsParRel Task cR cL) pR pL (Hp : CsParRel Task pR pL) tsk
    RR RL (HR : SubNatRel RR RL) dR dL (Hd : SubNatRel dR dL) :
  SubNatRel (WorkloadBound.W cR pR tsk RR dR) (I.Prosa_Classic_Analysis_Global_Basic_WorkloadBound_WorkloadBound_W Task (ct_decidable_eq Task) cL pL tsk RL dL).
Proof.
  have Hm := cib_max_jobs Task cR cL Hc pR pL Hp tsk RR RL HR dR dL Hd.
  exact (dm_add_correspondence _ _ _ _
           (ct_min_rel _ _ _ _ (Hc tsk)
              (dm_sub_correspondence _ _ _ _ (dm_sub_correspondence _ _ _ _ (dm_add_correspondence _ _ _ _ Hd HR) (Hc tsk))
                 (dm_mul_correspondence _ _ _ _ Hm (Hp tsk))))
           (dm_mul_correspondence _ _ _ _ Hm (Hc tsk))).
Qed.

Definition cibfp_pair (T : Type) (p : T * nat) : I.Prod_inst2 T Lean.Nat := I.Prod_mk_inst2 T Lean.Nat p.1 (sub_nat_to_imported p.2).

Lemma cib_generic (Task : eqType) cR cL (Hc : CsParRel Task cR cL) pR pL (Hp : CsParRel Task pR pL) tsk dR dL (Hd : SubNatRel dR dL)
    (p : Task * nat) :
  SubNatRel (InterferenceBoundGeneric.interference_bound_generic cR pR tsk dR p)
    (I.Prosa_Classic_Analysis_Global_Basic_InterferenceBound_InterferenceBoundGeneric_interference_bound_generic Task (ct_decidable_eq Task) cL pL tsk dL (cibfp_pair Task p)).
Proof.
  exact (ct_min_rel _ _ _ _ (cib_W Task cR cL Hc pR pL Hp p.1 _ _ (sub_nat_rel_canonical p.2) _ _ Hd)
           (dm_add_correspondence _ _ _ _ (dm_sub_correspondence _ _ _ _ Hd (Hc tsk)) (sub_nat_rel_canonical 1))).
Qed.

Definition cibfp_trs {A : Type} {x y : A} (E : Lean.eq x y) (P : A -> SProp) (h : P x) : P y :=
  match E in Lean.eq _ z return P z with Lean.eq_refl => h end.

Lemma cibfp_sum_map (A B : Type) (c : A -> B) FR FL (HF : forall x, SubNatRel (FR x) (FL (c x))) : forall l,
  SubNatRel (\sum_(i <- l) FR i)
    (I.List_sum_inst1 Lean.Nat I.instAddNat (I.MulZeroClass_toZero_inst1 Lean.Nat I.Nat_instMulZeroClass)
       (I.List_map_inst2 B Lean.Nat FL (cl_map c l))).
Proof.
  intro l. induction l as [|x l IH]; first by rewrite big_nil; exact (sub_nat_rel_canonical 0).
  rewrite big_cons. exact (sub_add_correspondence _ _ _ _ (HF x) IH).
Qed.

Lemma cibfp_sumSeq_rel (A B : Type) FR (c : A -> B) FL (HF : forall x, SubNatRel (FR x) (FL (c x))) l L :
  ClListRel c l L -> SubNatRel (\sum_(i <- l) FR i) (I.Prosa_Util_Sum_sumSeq B L FL).
Proof.
  intro H. refine (cibfp_trs H (fun z => SubNatRel (\sum_(i <- l) FR i) (I.Prosa_Util_Sum_sumSeq B z FL)) _).
  exact (cibfp_sum_map A B c FR FL HF l).
Qed.

Lemma cibfp_sumFiltered_rel (A B : Type) (PR : A -> bool) FR (c : A -> B) PL FL
    (HP : forall x, CtBoolRel (PR x) (PL (c x))) (HF : forall x, SubNatRel (FR x) (FL (c x))) l L :
  ClListRel c l L -> SubNatRel (\sum_(i <- l | PR i) FR i) (I.Prosa_Util_Sum_sumFiltered B L PL FL).
Proof.
  intro H.
  refine (cibfp_trs H (fun z => SubNatRel (\sum_(i <- l | PR i) FR i) (I.Prosa_Util_Sum_sumFiltered B z PL FL)) _).
  rewrite -big_filter.
  refine (cibfp_trs (cl_lean_eq _ _ _ (cl_filter c PR PL HP l))
            (fun z => SubNatRel (\sum_(i <- filter PR l) FR i)
                        (I.List_sum_inst1 Lean.Nat I.instAddNat (I.MulZeroClass_toZero_inst1 Lean.Nat I.Nat_instMulZeroClass)
                           (I.List_map_inst2 B Lean.Nat FL z))) _).
  exact (cibfp_sum_map A B c FR FL HF (filter PR l)).
Qed.

(* ------------------------------------------------------------------ *)
(** * Task sets, filters, counts and (task, time) pair sequences *)

(** [taskset_of Task] is the accepted sequence-set type; task sets are related through their
    underlying sequences, elementwise by identity, with two-way totals (as the accepted
    classic task certificate's [RocqSeqSetRel], here through the re-bound list library). *)
Section Ts.
Variable Task : eqType.
Notation dT := (ct_decidable_eq Task).
Notation LTs := (I.Prosa_Classic_Model_Arrival_Basic_Task_SporadicTaskset_taskset_of Task dT).
Notation LVal := (I.Prosa_Util_Seqset_set_val Task dT).

Definition CtsRel (tsR : SporadicTaskset.taskset_of Task) (tsL : LTs) : SProp :=
  ClListRel cid (@prosa.util.seqset._set_seq _ tsR) (LVal tsL).

Lemma cts_id (x : Task) : Logic.eq x x.
Proof. reflexivity. Qed.

Definition cts_to_target (tsR : SporadicTaskset.taskset_of Task) : LTs :=
  I.Prosa_Util_Seqset_set_mk Task dT (cl_map cid (@prosa.util.seqset._set_seq _ tsR))
    (prop_to_sprop _ _ (cl_uniq_rel _ _ cid cid cts_id cts_id _) (@prosa.util.seqset.set_uniq _ tsR)).

Definition cts_to_source (tsL : LTs) : SporadicTaskset.taskset_of Task :=
  @prosa.util.seqset.Build_set _ (cl_unmap cid (LVal tsL))
    (interpret_strict _ (cl_uniq_backward _ _ cid cid cts_id _ (@I.nodup1 Task dT tsL))).

Lemma cts_canonical tsR : CtsRel tsR (cts_to_target tsR).
Proof. exact (@Lean.eq_refl _ _). Qed.

Lemma cts_surjective tsL : CtsRel (cts_to_source tsL) tsL.
Proof. apply: coq_eq_to_imported_eq. exact (cl_map_unmap cid cid cts_id _). Qed.

Lemma cts_forall (PR : SporadicTaskset.taskset_of Task -> Prop) (PL : LTs -> SProp) :
  (forall tsR tsL, CtsRel tsR tsL -> PropSPropRel (PR tsR) (PL tsL)) -> PropSPropRel (forall ts, PR ts) (forall ts, PL ts).
Proof. exact (cs_forall_cover _ _ CtsRel cts_to_target cts_to_source cts_canonical cts_surjective PR PL). Qed.

Lemma cts_mem tsR tsL (Hts : CtsRel tsR tsL) x :
  PropSPropRel (x \in tsR)
    (I.Membership_mem Task LTs (I.Prosa_Util_Seqset_instMembershipSet Task dT) tsL x).
Proof. exact (cl_mem_rel_list _ _ cid cid cts_id x _ _ Hts). Qed.
End Ts.

(** [valid_sporadic_taskset] over related task sequences (as in the accepted classic task certificate). *)
Lemma cts_valid_taskset (Task : eqType) cR cL (Hc : CsParRel Task cR cL) pR pL (Hp : CsParRel Task pR pL)
    dR dL (Hd : CsParRel Task dR dL) (s : seq Task) sL (Hs : ClListRel cid s sL) :
  PropSPropRel (SporadicTaskset.valid_sporadic_taskset cR pR dR s)
    (I.Prosa_Classic_Model_Arrival_Basic_Task_SporadicTaskset_valid_sporadic_taskset Task (ct_decidable_eq Task) cL pL dL sL).
Proof.
  apply: ct_forall_identity => tsk.
  exact (ct_imp _ _ _ _ (cl_mem_rel_list Task Task cid cid (fun _ => Logic.eq_refl _) tsk s sL Hs)
           (cwb_valid_sporadic_task Task cR cL Hc pR pL Hp dR dL Hd tsk)).
Qed.

(** [[seq x <- s | P x]] against [List.filter]. *)
Lemma cts_filter (Task : eqType) (PR : Task -> bool) PL (Hp : forall x, CtBoolRel (PR x) (PL x)) s sL :
  ClListRel cid s sL -> ClListRel cid [seq x <- s | PR x] (I.List_filter Task PL sL).
Proof.
  intro H. refine (cs_trs H (fun z => ClListRel cid [seq x <- s | PR x] (I.List_filter Task PL z)) _).
  apply: coq_eq_to_imported_eq. exact (cl_filter cid PR PL Hp s).
Qed.

(** [count P s] against [List.countP P l] by structural induction through [countP.go] and its
    accumulator (as in the accepted classic counting certificate). *)
Lemma ccount_go (T : Type) (pR : T -> bool) (pL : T -> I.Bool) (Hp : forall x, CtBoolRel (pR x) (pL x)) :
  forall (s : seq T) n,
  Logic.eq (I.List_countP_go T pL (cl_map cid s) (sub_nat_to_imported n)) (sub_nat_to_imported (n + count pR s)).
Proof.
  elim => [|x s IH] n.
  - by rewrite addn0.
  - have -> : Logic.eq (I.List_countP_go T pL (cl_map cid (x :: s)) (sub_nat_to_imported n))
        (match pL x with
         | I.Bool_true => I.List_countP_go T pL (cl_map cid s) (sub_nat_to_imported n.+1)
         | I.Bool_false => I.List_countP_go T pL (cl_map cid s) (sub_nat_to_imported n) end).
    { cbn. destruct (pL x); reflexivity. }
    rewrite (ct_bool_rel_logic _ _ (Hp x)) (IH n.+1) (IH n).
    change (count pR (x :: s)) with (pR x + count pR s).
    case: (pR x).
    + by rewrite addSnnS add1n.
    + by rewrite add0n.
Qed.

Lemma ccount_rel (T : Type) pR pL (Hp : forall x, CtBoolRel (pR x) (pL x)) s sL : ClListRel (B := T) cid s sL ->
  SubNatRel (count pR s) (I.List_countP T pL sL).
Proof.
  intro H. refine (cs_trs H (fun z => SubNatRel (count pR s) (I.List_countP T pL z)) _).
  apply: coq_eq_to_imported_eq. apply: Logic.eq_sym. exact (ccount_go T pR pL Hp s 0).
Qed.

(** Sequences of (task, time) pairs: elementwise by [cibfp_pair], with two-way totals. *)
Definition cpair_unpair (T : Type) (p : I.Prod_inst2 T Lean.Nat) : T * nat :=
  match p with I.Prod_mk_inst2 a b => (a, sub_nat_to_rocq b) end.

Lemma cpair_dc (T : Type) (x : T * nat) : Logic.eq (cpair_unpair T (cibfp_pair T x)) x.
Proof.
  destruct x as [a b]. change (Logic.eq (a, sub_nat_to_rocq (sub_nat_to_imported b)) (a, b)).
  by rewrite sub_nat_rocq_roundtrip.
Qed.

Lemma cpair_cd (T : Type) (y : I.Prod_inst2 T Lean.Nat) : Logic.eq (cibfp_pair T (cpair_unpair T y)) y.
Proof.
  destruct y as [a b]. change (Logic.eq (I.Prod_mk_inst2 T Lean.Nat a (sub_nat_to_imported (sub_nat_to_rocq b))) (I.Prod_mk_inst2 T Lean.Nat a b)).
  by rewrite (imported_eq_to_coq_eq _ _ (sub_nat_imported_roundtrip b)).
Qed.

Lemma cpair_forall (T : Type) (PR : seq (T * nat) -> Prop) (PL : I.List (I.Prod_inst2 T Lean.Nat) -> SProp) :
  (forall lR lL, ClListRel (cibfp_pair T) lR lL -> PropSPropRel (PR lR) (PL lL)) -> PropSPropRel (forall l, PR l) (forall l, PL l).
Proof.
  exact (cs_forall_cover _ _ (ClListRel (cibfp_pair T)) (cl_map (cibfp_pair T)) (cl_unmap (cpair_unpair T))
           (fun l => @Lean.eq_refl _ _) (fun L => coq_eq_to_imported_eq _ _ (cl_map_unmap _ _ (cpair_cd T) L)) PR PL).
Qed.

Lemma cpair_mem (T : eqType) a bR bL (Hb : SubNatRel bR bL) (l : seq (T * nat)) L (Hl : ClListRel (cibfp_pair T) l L) :
  PropSPropRel ((a, bR) \in l)
    (I.Membership_mem (I.Prod_inst2 T Lean.Nat) (I.List (I.Prod_inst2 T Lean.Nat)) (I.List_instMembership (I.Prod_inst2 T Lean.Nat))
       L (I.Prod_mk_inst2 T Lean.Nat a bL)).
Proof.
  refine (cs_tr Hb (fun z => PropSPropRel ((a, bR) \in l)
                                (I.Membership_mem (I.Prod_inst2 T Lean.Nat) (I.List (I.Prod_inst2 T Lean.Nat))
                                   (I.List_instMembership (I.Prod_inst2 T Lean.Nat)) L (I.Prod_mk_inst2 T Lean.Nat a z))) _).
  exact (cl_mem_rel_list _ _ (cibfp_pair T) (cpair_unpair T) (cpair_dc T) (a, bR) l L Hl).
Qed.

(* ------------------------------------------------------------------ *)
(** * EDF priority and [different_task] (as in the accepted classic priority certificate) *)

Lemma cpe_edf (Job : eqType) jaR jaL (Hja : CsParRel Job jaR jaL) jdR jdL (Hjd : CsParRel Job jdR jdL) :
  CpRelRel Job (Priority.EDF jaR jdR) (I.Prosa_Classic_Model_Priority_Priority_EDF Job (ct_decidable_eq Job) jaL jdL).
Proof.
  intros a b. exact (ct_decide_le _ _ _ _ (sub_add_correspondence _ _ _ _ (Hja a) (Hjd a))
                                          (sub_add_correspondence _ _ _ _ (Hja b) (Hjd b))).
Qed.

Lemma cpe_different_task (Task : eqType) tsk tsk_other :
  CtBoolRel (Priority.different_task tsk tsk_other)
    (I.Prosa_Classic_Model_Priority_Priority_different_task Task (ct_decidable_eq Task) tsk tsk_other).
Proof. exact (ct_bool_not _ _ (ct_decide_eq Task tsk_other tsk)). Qed.

(* ------------------------------------------------------------------ *)
(** * Definitions *)

Theorem InterferenceBoundEDF_edf_specific_interference_bound_correspondence (Task : eqType)
    cR cL (Hc : CsParRel Task cR cL) pR pL (Hp : CsParRel Task pR pL) dR dL (Hd : CsParRel Task dR dL)
    tsk tsk_other RR RL (HR : SubNatRel RR RL) :
  SubNatRel (InterferenceBoundEDF.edf_specific_interference_bound cR pR dR tsk tsk_other RR)
    (I.Prosa_Classic_Analysis_Global_Basic_InterferenceBoundEdf_InterferenceBoundEDF_edf_specific_interference_bound Task (ct_decidable_eq Task) cL pL dL tsk tsk_other RL).
Proof.
  exact (dm_add_correspondence _ _ _ _
           (dm_mul_correspondence _ _ _ _ (dm_div_floor_correspondence _ _ _ _ (Hd tsk) (Hp tsk_other)) (Hc tsk_other))
           (ct_min_rel _ _ _ _ (Hc tsk_other)
              (dm_sub_correspondence _ _ _ _ (dm_mod_correspondence _ _ _ _ (Hd tsk) (Hp tsk_other))
                 (dm_sub_correspondence _ _ _ _ (Hd tsk_other) HR)))).
Qed.

(** The pair argument is related componentwise: any source pair is [(tsk_other, R)] and any Lean pair is
    [Prod.mk tsk_other R'] (primitive record, eta), with [R] and [R'] related by [SubNatRel]. *)
Theorem InterferenceBoundEDF_interference_bound_edf_correspondence (Task : eqType)
    cR cL (Hc : CsParRel Task cR cL) pR pL (Hp : CsParRel Task pR pL) dR dL (Hd : CsParRel Task dR dL)
    tsk deltaR deltaL (Hdelta : SubNatRel deltaR deltaL) tsk_other RR RL (HR : SubNatRel RR RL) :
  SubNatRel (InterferenceBoundEDF.interference_bound_edf cR pR dR tsk deltaR (tsk_other, RR))
    (I.Prosa_Classic_Analysis_Global_Basic_InterferenceBoundEdf_InterferenceBoundEDF_interference_bound_edf Task (ct_decidable_eq Task) cL pL dL tsk deltaL (I.Prod_mk_inst2 Task Lean.Nat tsk_other RL)).
Proof.
  refine (cs_trs HR (fun z => SubNatRel (InterferenceBoundEDF.interference_bound_edf cR pR dR tsk deltaR (tsk_other, RR))
                                (I.Prosa_Classic_Analysis_Global_Basic_InterferenceBoundEdf_InterferenceBoundEDF_interference_bound_edf Task (ct_decidable_eq Task) cL pL dL tsk deltaL
                                   (I.Prod_mk_inst2 Task Lean.Nat tsk_other z))) _).
  exact (ct_min_rel _ _ _ _ (cib_generic Task cR cL Hc pR pL Hp tsk deltaR deltaL Hdelta (tsk_other, RR))
           (InterferenceBoundEDF_edf_specific_interference_bound_correspondence Task cR cL Hc pR pL Hp dR dL Hd
              tsk tsk_other RR _ (sub_nat_rel_canonical RR))).
Qed.

Theorem InterferenceBoundEDF_total_interference_bound_edf_correspondence (Task : eqType)
    cR cL (Hc : CsParRel Task cR cL) pR pL (Hp : CsParRel Task pR pL) dR dL (Hd : CsParRel Task dR dL)
    tsk (Rp : seq (Task * nat)) RpL (HRp : ClListRel (cibfp_pair Task) Rp RpL) deltaR deltaL (Hdelta : SubNatRel deltaR deltaL) :
  SubNatRel (InterferenceBoundEDF.total_interference_bound_edf cR pR dR tsk Rp deltaR)
    (I.Prosa_Classic_Analysis_Global_Basic_InterferenceBoundEdf_InterferenceBoundEDF_total_interference_bound_edf Task (ct_decidable_eq Task) cL pL dL tsk RpL deltaL).
Proof.
  rewrite /InterferenceBoundEDF.total_interference_bound_edf.
  unfold I.Prosa_Classic_Analysis_Global_Basic_InterferenceBoundEdf_InterferenceBoundEDF_total_interference_bound_edf.
  refine (cibfp_sumFiltered_rel (Task * nat) _ _ _ (cibfp_pair Task) _ _ _ _ _ _ HRp).
  - intros [a b]. exact (cpe_different_task Task tsk a).
  - intros [a b]. exact (InterferenceBoundEDF_interference_bound_edf_correspondence Task cR cL Hc pR pL Hp dR dL Hd
                           tsk deltaR deltaL Hdelta a b _ (sub_nat_rel_canonical b)).
Qed.

(** Membership in related sequences (as in the accepted classic task certificate). *)
Lemma cmem_list (T : eqType) x (s : seq T) sL : ClListRel cid s sL ->
  PropSPropRel (x \in s) (I.Membership_mem T (I.List T) (I.List_instMembership T) sL x).
Proof. exact (cl_mem_rel_list T T cid cid (fun _ => Logic.eq_refl _) x s sL). Qed.

(* ------------------------------------------------------------------ *)
(** * Statement relation search

    [crel] proves a [PropSPropRel P PL] (and the [SubNatRel], [CtBoolRel] and
    [ClListRel] goals it generates) by the structure of the source side [P]: each
    binder by the cover lemma of its type's relation (above), each connective by
    its [LogicalRelation]/base lemma, and each atom by the definition
    correspondence lemma of its head (above), whose remaining relation premises
    are hypotheses introduced by the binders.  It only chains lemmas proved in this
    file or its imports; a goal it cannot close makes the
    proof fail. *)

Ltac crel_hyp :=
  match goal with
  | |- SubNatRel (?f ?x) (?g ?x) => match goal with H : CsParRel _ f g |- _ => exact (H x) end
  | |- CtBoolRel (?f ?x ?y) (?g ?x ?y) => match goal with H : CpRelRel _ f g |- _ => exact (H x y) end
  end.

Ltac crel_isnat T := first [ unify T nat | unify T Lean.Nat ].

Ltac crel_intro_defs T :=
  lazymatch T with
  | ArrivalSequence.arrival_sequence _ => apply: cwb_forall_arr; intros ? ? ?
  | Schedule.schedule _ ?n => match goal with Hn : SubNatRel n _ |- _ => apply: (cs_forall_sched _ _ _ Hn); intros ? ? ? end
  | Priority.FP_policy _ => apply: cp_forall_rel; intros ? ? ?
  | SporadicTaskset.taskset_of _ => apply: cts_forall; intros ? ? ?
  | seq (_ * _) => apply: cpair_forall; intros ? ? ?
  | _ => apply: ct_forall_identity; intro
  end.

Ltac crel_intro T :=
  tryif crel_isnat T then (apply: ct_forall_nat; intros ? ? ?) else
  lazymatch T with
  | ?A -> ?B => tryif crel_isnat B then (apply: cs_forall_par; intros ? ? ?) else crel_intro_defs T
  | _ => crel_intro_defs T
  end.

Ltac crel :=
  first
  [ assumption
  | crel_hyp
  | crel_nth; crel
  | lazymatch goal with
    | |- forall x : prod _ _, _ => intros [? ?]; cbv beta iota; crel
    | |- forall _, _ => intro; crel
    | |- CsFunRel _ _ => intros ? ? ?; cbv beta; crel
    | |- CpRelRel _ _ _ => crel_cp_defs
    | |- SubNatRel ?a _ => crel_n a
    | |- CtBoolRel ?b _ => crel_b b
    | |- ClListRel _ ?l _ => crel_l l
    | |- PropSPropRel ?P _ => crel_p P
    end ]
with crel_n a :=
  lazymatch a with
  | addn _ _ => eapply sub_add_correspondence; crel
  | subn _ _ => first [ eapply dm_sub_correspondence; crel | eapply ct_sub_rel; crel ]
  | muln _ _ => first [ eapply dm_mul_correspondence; crel | eapply sub_mul_correspondence; crel ]
  | minn _ _ => eapply ct_min_rel; crel
  | modn _ _ => eapply dm_mod_correspondence; crel
  | predn _ => eapply cta_pred_rel; crel
  | S (S _) => first [ eapply cwb_add2; crel | eapply cta_succ_rel; crel ]
  | S _ => eapply cta_succ_rel; crel
  | _ => first [ exact (sub_nat_rel_canonical _) | crel_n_defs ]
  end
with crel_b b :=
  lazymatch b with
  | andb _ _ => eapply ct_bool_and; crel
  | negb _ => eapply ct_bool_not; crel
  | leq _ _ => first [ eapply ct_decide_lt; crel | eapply ct_decide_le; crel ]
  | @eq_op ?T _ _ => first [ eapply ct_decide_eq_nat; crel | eapply ct_decide_eq; crel ]
  | _ => crel_b_defs
  end
with crel_l l := crel_l_defs
with crel_p P :=
  lazymatch P with
  | forall x : ?T, _ => lazymatch type of T with Prop => eapply ct_imp; crel | _ => crel_intro T; crel end
  | exists x : ?T, _ =>
      tryif crel_isnat T then (apply: ct_exists_nat; intros ? ? ?; crel)
      else (apply: ct_exists_identity; intro; crel)
  | _ /\ _ => eapply ct_and; crel
  | _ <> _ => eapply cta_ne
  | @Logic.eq bool _ _ => eapply ct_bool_eq; crel
  | @Logic.eq ?T _ _ => tryif crel_isnat T then (eapply sub_nat_eq_correspondence; crel) else eapply ct_eq_rel
  | is_true (leq _ _) => first [ eapply sub_nat_lt_correspondence; crel | eapply sub_nat_le_correspondence; crel
                              | eapply ct_bool_truth; crel ]
  | is_true _ => first [ crel_p_defs | eapply ct_bool_truth; crel ]
  | _ => crel_p_defs
  end
with crel_n_defs := first [ eapply InterferenceBoundEDF_edf_specific_interference_bound_correspondence; crel
    | eapply InterferenceBoundEDF_interference_bound_edf_correspondence; crel
    | eapply InterferenceBoundEDF_total_interference_bound_edf_correspondence; crel
    | eapply Interference_job_interference_correspondence; crel
    | eapply Interference_task_interference_correspondence; crel
    | eapply cib_W; crel
    | eapply dm_div_floor_correspondence; crel
    | eapply cs_list_size; crel
    | eapply ccount_rel; crel
    | eapply cwb_sumSeq_rel; crel
    | eapply cai_sumFiltered_rel; crel
    | eapply (cibfp_sumFiltered_rel _ _ _ _ (cibfp_pair _)); crel
    | eapply cs_ico; crel ]
with crel_b_defs := first [ eapply cf_Schedule_completed; crel
    | eapply cf_Schedule_pending; crel
    | eapply cf_Schedule_backlogged; crel
    | eapply cf_Schedule_scheduled; crel
    | eapply cpe_different_task; crel
    | eapply ct_decide_bool; crel ]
with crel_l_defs := first [ eapply cts_filter; crel
    | eapply cta_sort_rel; crel
    | eapply cf_Schedule_jobs_scheduled_between; crel ]
with crel_cp_defs := first [ eapply cpe_edf; crel ]
with crel_p_defs := first [ eapply cs_arrives_in; crel
    | eapply cwb_sporadic_task_model; crel
    | eapply cwb_valid_sporadic_job; crel
    | eapply cts_valid_taskset; crel
    | eapply cts_mem; crel
    | eapply cpair_mem; crel
    | eapply cmem_list; crel
    | eapply Platform_respects_JLFP_policy_correspondence; crel
    | eapply cf_Schedule_jobs_come_from_arrival_sequence; crel
    | eapply cf_Schedule_sequential_jobs; crel
    | eapply cf_Schedule_jobs_must_arrive_to_execute; crel
    | eapply cf_Schedule_completed_jobs_dont_execute; crel ]
with crel_nth :=
  match goal with
  | |- context [I.List_getD ?T ?L ?n ?x0] =>
      match goal with
      | |- context [@nth ?T' ?x0' ?l ?m] =>
          let E := fresh "E" in
          assert (E : Logic.eq (I.List_getD T L n x0) (@nth T' x0' l m)) by (eapply cta_getD; crel);
          rewrite E; clear E
      end
  end.

(** The binder/implication spine of a statement is walked iteratively (each premise closed by [crel]), so the
    search depth is bounded by the largest premise rather than by the whole statement. *)
Ltac crel_spine :=
  repeat lazymatch goal with
  | |- PropSPropRel (forall x : ?T, _) _ =>
      lazymatch type of T with Prop => eapply ct_imp; [ crel | idtac ] | _ => crel_intro T end
  end.

(* ------------------------------------------------------------------ *)
(** * Statements *)

Definition src_interference_bound_edf_use_another_definition (Task Job : eqType) : Prop :=
  ltac:(type_of_term (@InterferenceBoundEDF.interference_bound_edf_use_another_definition Task Job)).
Definition tgt_interference_bound_edf_use_another_definition (Task Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Analysis_Global_Basic_InterferenceBoundEdf_InterferenceBoundEDF_interference_bound_edf_use_another_definition Task (ct_decidable_eq Task) Job (ct_decidable_eq Job))).
Theorem InterferenceBoundEDF_interference_bound_edf_use_another_definition_correspondence (Task Job : eqType) :
  PropSPropRel (src_interference_bound_edf_use_another_definition Task Job) (tgt_interference_bound_edf_use_another_definition Task Job).
Proof. unfold src_interference_bound_edf_use_another_definition, tgt_interference_bound_edf_use_another_definition. crel_spine. crel. Unshelve. all: crel. Qed.

Definition src_interference_bound_edf_simpl_by_filtering_interfering_jobs (Task Job : eqType) : Prop :=
  ltac:(type_of_term (@InterferenceBoundEDF.interference_bound_edf_simpl_by_filtering_interfering_jobs Task Job)).
Definition tgt_interference_bound_edf_simpl_by_filtering_interfering_jobs (Task Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Analysis_Global_Basic_InterferenceBoundEdf_InterferenceBoundEDF_interference_bound_edf_simpl_by_filtering_interfering_jobs Task (ct_decidable_eq Task) Job (ct_decidable_eq Job))).
Theorem InterferenceBoundEDF_interference_bound_edf_simpl_by_filtering_interfering_jobs_correspondence (Task Job : eqType) :
  PropSPropRel (src_interference_bound_edf_simpl_by_filtering_interfering_jobs Task Job) (tgt_interference_bound_edf_simpl_by_filtering_interfering_jobs Task Job).
Proof. unfold src_interference_bound_edf_simpl_by_filtering_interfering_jobs, tgt_interference_bound_edf_simpl_by_filtering_interfering_jobs. crel_spine. crel. Unshelve. all: crel. Qed.

Definition src_interference_bound_edf_simpl_by_sorting_interfering_jobs (Task Job : eqType) : Prop :=
  ltac:(type_of_term (@InterferenceBoundEDF.interference_bound_edf_simpl_by_sorting_interfering_jobs Task Job)).
Definition tgt_interference_bound_edf_simpl_by_sorting_interfering_jobs (Task Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Analysis_Global_Basic_InterferenceBoundEdf_InterferenceBoundEDF_interference_bound_edf_simpl_by_sorting_interfering_jobs Task (ct_decidable_eq Task) Job (ct_decidable_eq Job))).
Theorem InterferenceBoundEDF_interference_bound_edf_simpl_by_sorting_interfering_jobs_correspondence (Task Job : eqType) :
  PropSPropRel (src_interference_bound_edf_simpl_by_sorting_interfering_jobs Task Job) (tgt_interference_bound_edf_simpl_by_sorting_interfering_jobs Task Job).
Proof. unfold src_interference_bound_edf_simpl_by_sorting_interfering_jobs, tgt_interference_bound_edf_simpl_by_sorting_interfering_jobs. crel_spine. crel. Unshelve. all: crel. Qed.

Definition src_interference_bound_edf_job_in_same_sequence (Task Job : eqType) : Prop :=
  ltac:(type_of_term (@InterferenceBoundEDF.interference_bound_edf_job_in_same_sequence Task Job)).
Definition tgt_interference_bound_edf_job_in_same_sequence (Task Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Analysis_Global_Basic_InterferenceBoundEdf_InterferenceBoundEDF_interference_bound_edf_job_in_same_sequence Task (ct_decidable_eq Task) Job (ct_decidable_eq Job))).
Theorem InterferenceBoundEDF_interference_bound_edf_job_in_same_sequence_correspondence (Task Job : eqType) :
  PropSPropRel (src_interference_bound_edf_job_in_same_sequence Task Job) (tgt_interference_bound_edf_job_in_same_sequence Task Job).
Proof. unfold src_interference_bound_edf_job_in_same_sequence, tgt_interference_bound_edf_job_in_same_sequence. crel_spine. crel. Unshelve. all: crel. Qed.

Definition src_interference_bound_edf_all_jobs_from_tsk_k (Task Job : eqType) : Prop :=
  ltac:(type_of_term (@InterferenceBoundEDF.interference_bound_edf_all_jobs_from_tsk_k Task Job)).
Definition tgt_interference_bound_edf_all_jobs_from_tsk_k (Task Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Analysis_Global_Basic_InterferenceBoundEdf_InterferenceBoundEDF_interference_bound_edf_all_jobs_from_tsk_k Task (ct_decidable_eq Task) Job (ct_decidable_eq Job))).
Theorem InterferenceBoundEDF_interference_bound_edf_all_jobs_from_tsk_k_correspondence (Task Job : eqType) :
  PropSPropRel (src_interference_bound_edf_all_jobs_from_tsk_k Task Job) (tgt_interference_bound_edf_all_jobs_from_tsk_k Task Job).
Proof. unfold src_interference_bound_edf_all_jobs_from_tsk_k, tgt_interference_bound_edf_all_jobs_from_tsk_k. crel_spine. crel. Unshelve. all: crel. Qed.

Definition src_interference_bound_edf_jobs_ordered_by_arrival (Task Job : eqType) : Prop :=
  ltac:(type_of_term (@InterferenceBoundEDF.interference_bound_edf_jobs_ordered_by_arrival Task Job)).
Definition tgt_interference_bound_edf_jobs_ordered_by_arrival (Task Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Analysis_Global_Basic_InterferenceBoundEdf_InterferenceBoundEDF_interference_bound_edf_jobs_ordered_by_arrival Task (ct_decidable_eq Task) Job (ct_decidable_eq Job))).
Theorem InterferenceBoundEDF_interference_bound_edf_jobs_ordered_by_arrival_correspondence (Task Job : eqType) :
  PropSPropRel (src_interference_bound_edf_jobs_ordered_by_arrival Task Job) (tgt_interference_bound_edf_jobs_ordered_by_arrival Task Job).
Proof. unfold src_interference_bound_edf_jobs_ordered_by_arrival, tgt_interference_bound_edf_jobs_ordered_by_arrival. crel_spine. crel. Unshelve. all: crel. Qed.

Definition src_interference_bound_edf_interference_le_task_cost (Task Job : eqType) : Prop :=
  forall p1 p2 : Task -> Time.time,
    ltac:(type_of_term (@InterferenceBoundEDF.interference_bound_edf_interference_le_task_cost Task p1 p2 Job)).
Definition tgt_interference_bound_edf_interference_le_task_cost (Task Job : eqType) : SProp :=
  forall p1 p2 : Task -> Lean.Nat,
    ltac:(type_of_term (I.Prosa_Classic_Analysis_Global_Basic_InterferenceBoundEdf_InterferenceBoundEDF_interference_bound_edf_interference_le_task_cost Task (ct_decidable_eq Task) p1 p2 Job (ct_decidable_eq Job))).
Theorem InterferenceBoundEDF_interference_bound_edf_interference_le_task_cost_correspondence (Task Job : eqType) :
  PropSPropRel (src_interference_bound_edf_interference_le_task_cost Task Job) (tgt_interference_bound_edf_interference_le_task_cost Task Job).
Proof. unfold src_interference_bound_edf_interference_le_task_cost, tgt_interference_bound_edf_interference_le_task_cost. crel_spine. crel. Unshelve. all: crel. Qed.

Definition src_interference_bound_edf_holds_for_at_most_n_k_jobs (Task Job : eqType) : Prop :=
  forall p1 p2 p3 : Task -> Time.time,
    ltac:(type_of_term (@InterferenceBoundEDF.interference_bound_edf_holds_for_at_most_n_k_jobs Task p1 p2 p3 Job)).
Definition tgt_interference_bound_edf_holds_for_at_most_n_k_jobs (Task Job : eqType) : SProp :=
  forall p1 p2 p3 : Task -> Lean.Nat,
    ltac:(type_of_term (I.Prosa_Classic_Analysis_Global_Basic_InterferenceBoundEdf_InterferenceBoundEDF_interference_bound_edf_holds_for_at_most_n_k_jobs Task (ct_decidable_eq Task) p1 p2 p3 Job (ct_decidable_eq Job))).
Theorem InterferenceBoundEDF_interference_bound_edf_holds_for_at_most_n_k_jobs_correspondence (Task Job : eqType) :
  PropSPropRel (src_interference_bound_edf_holds_for_at_most_n_k_jobs Task Job) (tgt_interference_bound_edf_holds_for_at_most_n_k_jobs Task Job).
Proof. unfold src_interference_bound_edf_holds_for_at_most_n_k_jobs, tgt_interference_bound_edf_holds_for_at_most_n_k_jobs. crel_spine. crel. Unshelve. all: crel. Qed.

Definition src_interference_bound_edf_at_least_one_job (Task Job : eqType) : Prop :=
  forall p1 p2 : Task -> Time.time,
    ltac:(type_of_term (@InterferenceBoundEDF.interference_bound_edf_at_least_one_job Task p1 p2 Job)).
Definition tgt_interference_bound_edf_at_least_one_job (Task Job : eqType) : SProp :=
  forall p1 p2 : Task -> Lean.Nat,
    ltac:(type_of_term (I.Prosa_Classic_Analysis_Global_Basic_InterferenceBoundEdf_InterferenceBoundEDF_interference_bound_edf_at_least_one_job Task (ct_decidable_eq Task) p1 p2 Job (ct_decidable_eq Job))).
Theorem InterferenceBoundEDF_interference_bound_edf_at_least_one_job_correspondence (Task Job : eqType) :
  PropSPropRel (src_interference_bound_edf_at_least_one_job Task Job) (tgt_interference_bound_edf_at_least_one_job Task Job).
Proof. unfold src_interference_bound_edf_at_least_one_job, tgt_interference_bound_edf_at_least_one_job. crel_spine. crel. Unshelve. all: crel. Qed.

Definition src_interference_bound_edf_j_fst_is_job_of_tsk_k (Task Job : eqType) : Prop :=
  forall p1 p2 : Task -> Time.time,
    ltac:(type_of_term (@InterferenceBoundEDF.interference_bound_edf_j_fst_is_job_of_tsk_k Task p1 p2 Job)).
Definition tgt_interference_bound_edf_j_fst_is_job_of_tsk_k (Task Job : eqType) : SProp :=
  forall p1 p2 : Task -> Lean.Nat,
    ltac:(type_of_term (I.Prosa_Classic_Analysis_Global_Basic_InterferenceBoundEdf_InterferenceBoundEDF_interference_bound_edf_j_fst_is_job_of_tsk_k Task (ct_decidable_eq Task) p1 p2 Job (ct_decidable_eq Job))).
Theorem InterferenceBoundEDF_interference_bound_edf_j_fst_is_job_of_tsk_k_correspondence (Task Job : eqType) :
  PropSPropRel (src_interference_bound_edf_j_fst_is_job_of_tsk_k Task Job) (tgt_interference_bound_edf_j_fst_is_job_of_tsk_k Task Job).
Proof. unfold src_interference_bound_edf_j_fst_is_job_of_tsk_k, tgt_interference_bound_edf_j_fst_is_job_of_tsk_k. crel_spine. crel. Unshelve. all: crel. Qed.

Definition src_interference_bound_edf_j_fst_deadline (Task Job : eqType) : Prop :=
  forall p1 p2 p3 : Task -> Time.time,
    ltac:(type_of_term (@InterferenceBoundEDF.interference_bound_edf_j_fst_deadline Task p1 p2 p3 Job)).
Definition tgt_interference_bound_edf_j_fst_deadline (Task Job : eqType) : SProp :=
  forall p1 p2 p3 : Task -> Lean.Nat,
    ltac:(type_of_term (I.Prosa_Classic_Analysis_Global_Basic_InterferenceBoundEdf_InterferenceBoundEDF_interference_bound_edf_j_fst_deadline Task (ct_decidable_eq Task) p1 p2 p3 Job (ct_decidable_eq Job))).
Theorem InterferenceBoundEDF_interference_bound_edf_j_fst_deadline_correspondence (Task Job : eqType) :
  PropSPropRel (src_interference_bound_edf_j_fst_deadline Task Job) (tgt_interference_bound_edf_j_fst_deadline Task Job).
Proof. unfold src_interference_bound_edf_j_fst_deadline, tgt_interference_bound_edf_j_fst_deadline. crel_spine. crel. Unshelve. all: crel. Qed.

Definition src_interference_bound_edf_j_i_deadline (Task Job : eqType) : Prop :=
  forall p1 p2 : Task -> Time.time,
    ltac:(type_of_term (@InterferenceBoundEDF.interference_bound_edf_j_i_deadline Task p1 p2 Job)).
Definition tgt_interference_bound_edf_j_i_deadline (Task Job : eqType) : SProp :=
  forall p1 p2 : Task -> Lean.Nat,
    ltac:(type_of_term (I.Prosa_Classic_Analysis_Global_Basic_InterferenceBoundEdf_InterferenceBoundEDF_interference_bound_edf_j_i_deadline Task (ct_decidable_eq Task) p1 p2 Job (ct_decidable_eq Job))).
Theorem InterferenceBoundEDF_interference_bound_edf_j_i_deadline_correspondence (Task Job : eqType) :
  PropSPropRel (src_interference_bound_edf_j_i_deadline Task Job) (tgt_interference_bound_edf_j_i_deadline Task Job).
Proof. unfold src_interference_bound_edf_j_i_deadline, tgt_interference_bound_edf_j_i_deadline. crel_spine. crel. Unshelve. all: crel. Qed.

Definition src_interference_bound_edf_j_fst_completion_implies_rt_bound_inside_interval (Task Job : eqType) : Prop :=
  forall p1 p2 : Task -> Time.time,
    ltac:(type_of_term (@InterferenceBoundEDF.interference_bound_edf_j_fst_completion_implies_rt_bound_inside_interval Task p1 p2 Job)).
Definition tgt_interference_bound_edf_j_fst_completion_implies_rt_bound_inside_interval (Task Job : eqType) : SProp :=
  forall p1 p2 : Task -> Lean.Nat,
    ltac:(type_of_term (I.Prosa_Classic_Analysis_Global_Basic_InterferenceBoundEdf_InterferenceBoundEDF_interference_bound_edf_j_fst_completion_implies_rt_bound_inside_interval Task (ct_decidable_eq Task) p1 p2 Job (ct_decidable_eq Job))).
Theorem InterferenceBoundEDF_interference_bound_edf_j_fst_completion_implies_rt_bound_inside_interval_correspondence (Task Job : eqType) :
  PropSPropRel (src_interference_bound_edf_j_fst_completion_implies_rt_bound_inside_interval Task Job) (tgt_interference_bound_edf_j_fst_completion_implies_rt_bound_inside_interval Task Job).
Proof. unfold src_interference_bound_edf_j_fst_completion_implies_rt_bound_inside_interval, tgt_interference_bound_edf_j_fst_completion_implies_rt_bound_inside_interval. crel_spine. crel. Unshelve. all: crel. Qed.

Definition src_interference_bound_edf_simpl_when_there_s_one_job (Task Job : eqType) : Prop :=
  forall p1 p2 p3 : Task -> Time.time,
    ltac:(type_of_term (@InterferenceBoundEDF.interference_bound_edf_simpl_when_there's_one_job Task p1 p2 p3 Job)).
Definition tgt_interference_bound_edf_simpl_when_there_s_one_job (Task Job : eqType) : SProp :=
  forall p1 p2 p3 : Task -> Lean.Nat,
    ltac:(type_of_term (I.Prosa_Classic_Analysis_Global_Basic_InterferenceBoundEdf_InterferenceBoundEDF_interference_bound_edf_simpl_when_there's_one_job Task (ct_decidable_eq Task) p1 p2 p3 Job (ct_decidable_eq Job))).
Theorem InterferenceBoundEDF_interference_bound_edf_simpl_when_there's_one_job_correspondence (Task Job : eqType) :
  PropSPropRel (src_interference_bound_edf_simpl_when_there_s_one_job Task Job) (tgt_interference_bound_edf_simpl_when_there_s_one_job Task Job).
Proof. unfold src_interference_bound_edf_simpl_when_there_s_one_job, tgt_interference_bound_edf_simpl_when_there_s_one_job. crel_spine. crel. Unshelve. all: crel. Qed.

Definition src_interference_bound_edf_holds_for_single_job_that_completes_on_time (Task Job : eqType) : Prop :=
  forall p1 p2 p3 : Task -> Time.time,
    ltac:(type_of_term (@InterferenceBoundEDF.interference_bound_edf_holds_for_single_job_that_completes_on_time Task p1 p2 p3 Job)).
Definition tgt_interference_bound_edf_holds_for_single_job_that_completes_on_time (Task Job : eqType) : SProp :=
  forall p1 p2 p3 : Task -> Lean.Nat,
    ltac:(type_of_term (I.Prosa_Classic_Analysis_Global_Basic_InterferenceBoundEdf_InterferenceBoundEDF_interference_bound_edf_holds_for_single_job_that_completes_on_time Task (ct_decidable_eq Task) p1 p2 p3 Job (ct_decidable_eq Job))).
Theorem InterferenceBoundEDF_interference_bound_edf_holds_for_single_job_that_completes_on_time_correspondence (Task Job : eqType) :
  PropSPropRel (src_interference_bound_edf_holds_for_single_job_that_completes_on_time Task Job) (tgt_interference_bound_edf_holds_for_single_job_that_completes_on_time Task Job).
Proof. unfold src_interference_bound_edf_holds_for_single_job_that_completes_on_time, tgt_interference_bound_edf_holds_for_single_job_that_completes_on_time. crel_spine. crel. Unshelve. all: crel. Qed.

Definition src_interference_bound_edf_response_time_bound_of_j_fst_after_interval (Task Job : eqType) : Prop :=
  forall p1 p2 : Task -> Time.time,
    ltac:(type_of_term (@InterferenceBoundEDF.interference_bound_edf_response_time_bound_of_j_fst_after_interval Task p1 p2 Job)).
Definition tgt_interference_bound_edf_response_time_bound_of_j_fst_after_interval (Task Job : eqType) : SProp :=
  forall p1 p2 : Task -> Lean.Nat,
    ltac:(type_of_term (I.Prosa_Classic_Analysis_Global_Basic_InterferenceBoundEdf_InterferenceBoundEDF_interference_bound_edf_response_time_bound_of_j_fst_after_interval Task (ct_decidable_eq Task) p1 p2 Job (ct_decidable_eq Job))).
Theorem InterferenceBoundEDF_interference_bound_edf_response_time_bound_of_j_fst_after_interval_correspondence (Task Job : eqType) :
  PropSPropRel (src_interference_bound_edf_response_time_bound_of_j_fst_after_interval Task Job) (tgt_interference_bound_edf_response_time_bound_of_j_fst_after_interval Task Job).
Proof. unfold src_interference_bound_edf_response_time_bound_of_j_fst_after_interval, tgt_interference_bound_edf_response_time_bound_of_j_fst_after_interval. crel_spine. crel. Unshelve. all: crel. Qed.

Definition src_interference_bound_edf_holds_for_single_job_with_big_slack (Task Job : eqType) : Prop :=
  forall p1 p2 p3 : Task -> Time.time,
    ltac:(type_of_term (@InterferenceBoundEDF.interference_bound_edf_holds_for_single_job_with_big_slack Task p1 p2 p3 Job)).
Definition tgt_interference_bound_edf_holds_for_single_job_with_big_slack (Task Job : eqType) : SProp :=
  forall p1 p2 p3 : Task -> Lean.Nat,
    ltac:(type_of_term (I.Prosa_Classic_Analysis_Global_Basic_InterferenceBoundEdf_InterferenceBoundEDF_interference_bound_edf_holds_for_single_job_with_big_slack Task (ct_decidable_eq Task) p1 p2 p3 Job (ct_decidable_eq Job))).
Theorem InterferenceBoundEDF_interference_bound_edf_holds_for_single_job_with_big_slack_correspondence (Task Job : eqType) :
  PropSPropRel (src_interference_bound_edf_holds_for_single_job_with_big_slack Task Job) (tgt_interference_bound_edf_holds_for_single_job_with_big_slack Task Job).
Proof. unfold src_interference_bound_edf_holds_for_single_job_with_big_slack, tgt_interference_bound_edf_holds_for_single_job_with_big_slack. crel_spine. crel. Unshelve. all: crel. Qed.

Definition src_interference_bound_edf_holds_for_single_job_with_small_slack (Task Job : eqType) : Prop :=
  forall p1 p2 p3 : Task -> Time.time,
    ltac:(type_of_term (@InterferenceBoundEDF.interference_bound_edf_holds_for_single_job_with_small_slack Task p1 p2 p3 Job)).
Definition tgt_interference_bound_edf_holds_for_single_job_with_small_slack (Task Job : eqType) : SProp :=
  forall p1 p2 p3 : Task -> Lean.Nat,
    ltac:(type_of_term (I.Prosa_Classic_Analysis_Global_Basic_InterferenceBoundEdf_InterferenceBoundEDF_interference_bound_edf_holds_for_single_job_with_small_slack Task (ct_decidable_eq Task) p1 p2 p3 Job (ct_decidable_eq Job))).
Theorem InterferenceBoundEDF_interference_bound_edf_holds_for_single_job_with_small_slack_correspondence (Task Job : eqType) :
  PropSPropRel (src_interference_bound_edf_holds_for_single_job_with_small_slack Task Job) (tgt_interference_bound_edf_holds_for_single_job_with_small_slack Task Job).
Proof. unfold src_interference_bound_edf_holds_for_single_job_with_small_slack, tgt_interference_bound_edf_holds_for_single_job_with_small_slack. crel_spine. crel. Unshelve. all: crel. Qed.

Definition src_interference_bound_edf_interference_of_j_fst_limited_by_slack (Task Job : eqType) : Prop :=
  forall p1 p2 p3 : Task -> Time.time,
    ltac:(type_of_term (@InterferenceBoundEDF.interference_bound_edf_interference_of_j_fst_limited_by_slack Task p1 p2 p3 Job)).
Definition tgt_interference_bound_edf_interference_of_j_fst_limited_by_slack (Task Job : eqType) : SProp :=
  forall p1 p2 p3 : Task -> Lean.Nat,
    ltac:(type_of_term (I.Prosa_Classic_Analysis_Global_Basic_InterferenceBoundEdf_InterferenceBoundEDF_interference_bound_edf_interference_of_j_fst_limited_by_slack Task (ct_decidable_eq Task) p1 p2 p3 Job (ct_decidable_eq Job))).
Theorem InterferenceBoundEDF_interference_bound_edf_interference_of_j_fst_limited_by_slack_correspondence (Task Job : eqType) :
  PropSPropRel (src_interference_bound_edf_interference_of_j_fst_limited_by_slack Task Job) (tgt_interference_bound_edf_interference_of_j_fst_limited_by_slack Task Job).
Proof. unfold src_interference_bound_edf_interference_of_j_fst_limited_by_slack, tgt_interference_bound_edf_interference_of_j_fst_limited_by_slack. crel_spine. crel. Unshelve. all: crel. Qed.

Definition src_interference_bound_edf_holds_for_a_single_job (Task Job : eqType) : Prop :=
  forall p1 p2 p3 : Task -> Time.time,
    ltac:(type_of_term (@InterferenceBoundEDF.interference_bound_edf_holds_for_a_single_job Task p1 p2 p3 Job)).
Definition tgt_interference_bound_edf_holds_for_a_single_job (Task Job : eqType) : SProp :=
  forall p1 p2 p3 : Task -> Lean.Nat,
    ltac:(type_of_term (I.Prosa_Classic_Analysis_Global_Basic_InterferenceBoundEdf_InterferenceBoundEDF_interference_bound_edf_holds_for_a_single_job Task (ct_decidable_eq Task) p1 p2 p3 Job (ct_decidable_eq Job))).
Theorem InterferenceBoundEDF_interference_bound_edf_holds_for_a_single_job_correspondence (Task Job : eqType) :
  PropSPropRel (src_interference_bound_edf_holds_for_a_single_job Task Job) (tgt_interference_bound_edf_holds_for_a_single_job Task Job).
Proof. unfold src_interference_bound_edf_holds_for_a_single_job, tgt_interference_bound_edf_holds_for_a_single_job. crel_spine. crel. Unshelve. all: crel. Qed.

Definition src_interference_bound_edf_j_lst_is_job_of_tsk_k (Task Job : eqType) : Prop :=
  ltac:(type_of_term (@InterferenceBoundEDF.interference_bound_edf_j_lst_is_job_of_tsk_k Task Job)).
Definition tgt_interference_bound_edf_j_lst_is_job_of_tsk_k (Task Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Analysis_Global_Basic_InterferenceBoundEdf_InterferenceBoundEDF_interference_bound_edf_j_lst_is_job_of_tsk_k Task (ct_decidable_eq Task) Job (ct_decidable_eq Job))).
Theorem InterferenceBoundEDF_interference_bound_edf_j_lst_is_job_of_tsk_k_correspondence (Task Job : eqType) :
  PropSPropRel (src_interference_bound_edf_j_lst_is_job_of_tsk_k Task Job) (tgt_interference_bound_edf_j_lst_is_job_of_tsk_k Task Job).
Proof. unfold src_interference_bound_edf_j_lst_is_job_of_tsk_k, tgt_interference_bound_edf_j_lst_is_job_of_tsk_k. crel_spine. crel. Unshelve. all: crel. Qed.

Definition src_interference_bound_edf_j_lst_deadline (Task Job : eqType) : Prop :=
  forall p1 p2 : Task -> Time.time,
    ltac:(type_of_term (@InterferenceBoundEDF.interference_bound_edf_j_lst_deadline Task p1 p2 Job)).
Definition tgt_interference_bound_edf_j_lst_deadline (Task Job : eqType) : SProp :=
  forall p1 p2 : Task -> Lean.Nat,
    ltac:(type_of_term (I.Prosa_Classic_Analysis_Global_Basic_InterferenceBoundEdf_InterferenceBoundEDF_interference_bound_edf_j_lst_deadline Task (ct_decidable_eq Task) p1 p2 Job (ct_decidable_eq Job))).
Theorem InterferenceBoundEDF_interference_bound_edf_j_lst_deadline_correspondence (Task Job : eqType) :
  PropSPropRel (src_interference_bound_edf_j_lst_deadline Task Job) (tgt_interference_bound_edf_j_lst_deadline Task Job).
Proof. unfold src_interference_bound_edf_j_lst_deadline, tgt_interference_bound_edf_j_lst_deadline. crel_spine. crel. Unshelve. all: crel. Qed.

Definition src_interference_bound_edf_j_fst_before_j_lst (Task Job : eqType) : Prop :=
  ltac:(type_of_term (@InterferenceBoundEDF.interference_bound_edf_j_fst_before_j_lst Task Job)).
Definition tgt_interference_bound_edf_j_fst_before_j_lst (Task Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Analysis_Global_Basic_InterferenceBoundEdf_InterferenceBoundEDF_interference_bound_edf_j_fst_before_j_lst Task (ct_decidable_eq Task) Job (ct_decidable_eq Job))).
Theorem InterferenceBoundEDF_interference_bound_edf_j_fst_before_j_lst_correspondence (Task Job : eqType) :
  PropSPropRel (src_interference_bound_edf_j_fst_before_j_lst Task Job) (tgt_interference_bound_edf_j_fst_before_j_lst Task Job).
Proof. unfold src_interference_bound_edf_j_fst_before_j_lst, tgt_interference_bound_edf_j_fst_before_j_lst. crel_spine. crel. Unshelve. all: crel. Qed.

Definition src_interference_bound_edf_last_job_arrives_before_end_of_interval (Task Job : eqType) : Prop :=
  ltac:(type_of_term (@InterferenceBoundEDF.interference_bound_edf_last_job_arrives_before_end_of_interval Task Job)).
Definition tgt_interference_bound_edf_last_job_arrives_before_end_of_interval (Task Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Analysis_Global_Basic_InterferenceBoundEdf_InterferenceBoundEDF_interference_bound_edf_last_job_arrives_before_end_of_interval Task (ct_decidable_eq Task) Job (ct_decidable_eq Job))).
Theorem InterferenceBoundEDF_interference_bound_edf_last_job_arrives_before_end_of_interval_correspondence (Task Job : eqType) :
  PropSPropRel (src_interference_bound_edf_last_job_arrives_before_end_of_interval Task Job) (tgt_interference_bound_edf_last_job_arrives_before_end_of_interval Task Job).
Proof. unfold src_interference_bound_edf_last_job_arrives_before_end_of_interval, tgt_interference_bound_edf_last_job_arrives_before_end_of_interval. crel_spine. crel. Unshelve. all: crel. Qed.

Definition src_interference_bound_edf_j_fst_completed_on_time (Task Job : eqType) : Prop :=
  forall p1 p2 : Task -> Time.time,
    ltac:(type_of_term (@InterferenceBoundEDF.interference_bound_edf_j_fst_completed_on_time Task p1 p2 Job)).
Definition tgt_interference_bound_edf_j_fst_completed_on_time (Task Job : eqType) : SProp :=
  forall p1 p2 : Task -> Lean.Nat,
    ltac:(type_of_term (I.Prosa_Classic_Analysis_Global_Basic_InterferenceBoundEdf_InterferenceBoundEDF_interference_bound_edf_j_fst_completed_on_time Task (ct_decidable_eq Task) p1 p2 Job (ct_decidable_eq Job))).
Theorem InterferenceBoundEDF_interference_bound_edf_j_fst_completed_on_time_correspondence (Task Job : eqType) :
  PropSPropRel (src_interference_bound_edf_j_fst_completed_on_time Task Job) (tgt_interference_bound_edf_j_fst_completed_on_time Task Job).
Proof. unfold src_interference_bound_edf_j_fst_completed_on_time, tgt_interference_bound_edf_j_fst_completed_on_time. crel_spine. crel. Unshelve. all: crel. Qed.

Definition src_interference_bound_edf_many_periods_in_between (Task Job : eqType) : Prop :=
  forall p1 p2 p3 : Task -> Time.time,
    ltac:(type_of_term (@InterferenceBoundEDF.interference_bound_edf_many_periods_in_between Task p1 p2 p3 Job)).
Definition tgt_interference_bound_edf_many_periods_in_between (Task Job : eqType) : SProp :=
  forall p1 p2 p3 : Task -> Lean.Nat,
    ltac:(type_of_term (I.Prosa_Classic_Analysis_Global_Basic_InterferenceBoundEdf_InterferenceBoundEDF_interference_bound_edf_many_periods_in_between Task (ct_decidable_eq Task) p1 p2 p3 Job (ct_decidable_eq Job))).
Theorem InterferenceBoundEDF_interference_bound_edf_many_periods_in_between_correspondence (Task Job : eqType) :
  PropSPropRel (src_interference_bound_edf_many_periods_in_between Task Job) (tgt_interference_bound_edf_many_periods_in_between Task Job).
Proof. unfold src_interference_bound_edf_many_periods_in_between, tgt_interference_bound_edf_many_periods_in_between. crel_spine. crel. Unshelve. all: crel. Qed.

Definition src_interference_bound_edf_n_k_covers_middle_jobs_plus_one (Task Job : eqType) : Prop :=
  forall p1 p2 p3 : Task -> Time.time,
    ltac:(type_of_term (@InterferenceBoundEDF.interference_bound_edf_n_k_covers_middle_jobs_plus_one Task p1 p2 p3 Job)).
Definition tgt_interference_bound_edf_n_k_covers_middle_jobs_plus_one (Task Job : eqType) : SProp :=
  forall p1 p2 p3 : Task -> Lean.Nat,
    ltac:(type_of_term (I.Prosa_Classic_Analysis_Global_Basic_InterferenceBoundEdf_InterferenceBoundEDF_interference_bound_edf_n_k_covers_middle_jobs_plus_one Task (ct_decidable_eq Task) p1 p2 p3 Job (ct_decidable_eq Job))).
Theorem InterferenceBoundEDF_interference_bound_edf_n_k_covers_middle_jobs_plus_one_correspondence (Task Job : eqType) :
  PropSPropRel (src_interference_bound_edf_n_k_covers_middle_jobs_plus_one Task Job) (tgt_interference_bound_edf_n_k_covers_middle_jobs_plus_one Task Job).
Proof. unfold src_interference_bound_edf_n_k_covers_middle_jobs_plus_one, tgt_interference_bound_edf_n_k_covers_middle_jobs_plus_one. crel_spine. crel. Unshelve. all: crel. Qed.

Definition src_interference_bound_edf_holds_for_middle_and_last_jobs (Task Job : eqType) : Prop :=
  forall p1 p2 p3 : Task -> Time.time,
    ltac:(type_of_term (@InterferenceBoundEDF.interference_bound_edf_holds_for_middle_and_last_jobs Task p1 p2 p3 Job)).
Definition tgt_interference_bound_edf_holds_for_middle_and_last_jobs (Task Job : eqType) : SProp :=
  forall p1 p2 p3 : Task -> Lean.Nat,
    ltac:(type_of_term (I.Prosa_Classic_Analysis_Global_Basic_InterferenceBoundEdf_InterferenceBoundEDF_interference_bound_edf_holds_for_middle_and_last_jobs Task (ct_decidable_eq Task) p1 p2 p3 Job (ct_decidable_eq Job))).
Theorem InterferenceBoundEDF_interference_bound_edf_holds_for_middle_and_last_jobs_correspondence (Task Job : eqType) :
  PropSPropRel (src_interference_bound_edf_holds_for_middle_and_last_jobs Task Job) (tgt_interference_bound_edf_holds_for_middle_and_last_jobs Task Job).
Proof. unfold src_interference_bound_edf_holds_for_middle_and_last_jobs, tgt_interference_bound_edf_holds_for_middle_and_last_jobs. crel_spine. crel. Unshelve. all: crel. Qed.

Definition src_interference_bound_edf_n_k_equals_num_mid_jobs_plus_one (Task Job : eqType) : Prop :=
  forall p1 p2 p3 : Task -> Time.time,
    ltac:(type_of_term (@InterferenceBoundEDF.interference_bound_edf_n_k_equals_num_mid_jobs_plus_one Task p1 p2 p3 Job)).
Definition tgt_interference_bound_edf_n_k_equals_num_mid_jobs_plus_one (Task Job : eqType) : SProp :=
  forall p1 p2 p3 : Task -> Lean.Nat,
    ltac:(type_of_term (I.Prosa_Classic_Analysis_Global_Basic_InterferenceBoundEdf_InterferenceBoundEDF_interference_bound_edf_n_k_equals_num_mid_jobs_plus_one Task (ct_decidable_eq Task) p1 p2 p3 Job (ct_decidable_eq Job))).
Theorem InterferenceBoundEDF_interference_bound_edf_n_k_equals_num_mid_jobs_plus_one_correspondence (Task Job : eqType) :
  PropSPropRel (src_interference_bound_edf_n_k_equals_num_mid_jobs_plus_one Task Job) (tgt_interference_bound_edf_n_k_equals_num_mid_jobs_plus_one Task Job).
Proof. unfold src_interference_bound_edf_n_k_equals_num_mid_jobs_plus_one, tgt_interference_bound_edf_n_k_equals_num_mid_jobs_plus_one. crel_spine. crel. Unshelve. all: crel. Qed.

Definition src_interference_bound_edf_remainder_ge_slack (Task Job : eqType) : Prop :=
  forall p1 p2 p3 : Task -> Time.time,
    ltac:(type_of_term (@InterferenceBoundEDF.interference_bound_edf_remainder_ge_slack Task p1 p2 p3 Job)).
Definition tgt_interference_bound_edf_remainder_ge_slack (Task Job : eqType) : SProp :=
  forall p1 p2 p3 : Task -> Lean.Nat,
    ltac:(type_of_term (I.Prosa_Classic_Analysis_Global_Basic_InterferenceBoundEdf_InterferenceBoundEDF_interference_bound_edf_remainder_ge_slack Task (ct_decidable_eq Task) p1 p2 p3 Job (ct_decidable_eq Job))).
Theorem InterferenceBoundEDF_interference_bound_edf_remainder_ge_slack_correspondence (Task Job : eqType) :
  PropSPropRel (src_interference_bound_edf_remainder_ge_slack Task Job) (tgt_interference_bound_edf_remainder_ge_slack Task Job).
Proof. unfold src_interference_bound_edf_remainder_ge_slack, tgt_interference_bound_edf_remainder_ge_slack. crel_spine. crel. Unshelve. all: crel. Qed.

Definition src_interference_bound_edf_simpl_by_moving_to_left_side (Task Job : eqType) : Prop :=
  forall p1 p2 : Task -> Time.time,
    ltac:(type_of_term (@InterferenceBoundEDF.interference_bound_edf_simpl_by_moving_to_left_side Task p1 p2 Job)).
Definition tgt_interference_bound_edf_simpl_by_moving_to_left_side (Task Job : eqType) : SProp :=
  forall p1 p2 : Task -> Lean.Nat,
    ltac:(type_of_term (I.Prosa_Classic_Analysis_Global_Basic_InterferenceBoundEdf_InterferenceBoundEDF_interference_bound_edf_simpl_by_moving_to_left_side Task (ct_decidable_eq Task) p1 p2 Job (ct_decidable_eq Job))).
Theorem InterferenceBoundEDF_interference_bound_edf_simpl_by_moving_to_left_side_correspondence (Task Job : eqType) :
  PropSPropRel (src_interference_bound_edf_simpl_by_moving_to_left_side Task Job) (tgt_interference_bound_edf_simpl_by_moving_to_left_side Task Job).
Proof. unfold src_interference_bound_edf_simpl_by_moving_to_left_side, tgt_interference_bound_edf_simpl_by_moving_to_left_side. crel_spine. crel. Unshelve. all: crel. Qed.

Definition src_interference_bound_edf_interference_of_j_fst_bounded_by_response_time (Task Job : eqType) : Prop :=
  forall p1 p2 : Task -> Time.time,
    ltac:(type_of_term (@InterferenceBoundEDF.interference_bound_edf_interference_of_j_fst_bounded_by_response_time Task p1 p2 Job)).
Definition tgt_interference_bound_edf_interference_of_j_fst_bounded_by_response_time (Task Job : eqType) : SProp :=
  forall p1 p2 : Task -> Lean.Nat,
    ltac:(type_of_term (I.Prosa_Classic_Analysis_Global_Basic_InterferenceBoundEdf_InterferenceBoundEDF_interference_bound_edf_interference_of_j_fst_bounded_by_response_time Task (ct_decidable_eq Task) p1 p2 Job (ct_decidable_eq Job))).
Theorem InterferenceBoundEDF_interference_bound_edf_interference_of_j_fst_bounded_by_response_time_correspondence (Task Job : eqType) :
  PropSPropRel (src_interference_bound_edf_interference_of_j_fst_bounded_by_response_time Task Job) (tgt_interference_bound_edf_interference_of_j_fst_bounded_by_response_time Task Job).
Proof. unfold src_interference_bound_edf_interference_of_j_fst_bounded_by_response_time, tgt_interference_bound_edf_interference_of_j_fst_bounded_by_response_time. crel_spine. crel. Unshelve. all: crel. Qed.

Definition src_interference_bound_edf_bounding_interference_with_interval_lengths (Task Job : eqType) : Prop :=
  forall p1 p2 p3 : Task -> Time.time,
    ltac:(type_of_term (@InterferenceBoundEDF.interference_bound_edf_bounding_interference_with_interval_lengths Task p1 p2 p3 Job)).
Definition tgt_interference_bound_edf_bounding_interference_with_interval_lengths (Task Job : eqType) : SProp :=
  forall p1 p2 p3 : Task -> Lean.Nat,
    ltac:(type_of_term (I.Prosa_Classic_Analysis_Global_Basic_InterferenceBoundEdf_InterferenceBoundEDF_interference_bound_edf_bounding_interference_with_interval_lengths Task (ct_decidable_eq Task) p1 p2 p3 Job (ct_decidable_eq Job))).
Theorem InterferenceBoundEDF_interference_bound_edf_bounding_interference_with_interval_lengths_correspondence (Task Job : eqType) :
  PropSPropRel (src_interference_bound_edf_bounding_interference_with_interval_lengths Task Job) (tgt_interference_bound_edf_bounding_interference_with_interval_lengths Task Job).
Proof. unfold src_interference_bound_edf_bounding_interference_with_interval_lengths, tgt_interference_bound_edf_bounding_interference_with_interval_lengths. crel_spine. crel. Unshelve. all: crel. Qed.

Definition src_interference_bound_edf_simpl_by_concatenation_of_intervals (Task Job : eqType) : Prop :=
  forall p1 p2 : Task -> Time.time,
    ltac:(type_of_term (@InterferenceBoundEDF.interference_bound_edf_simpl_by_concatenation_of_intervals Task p1 p2 Job)).
Definition tgt_interference_bound_edf_simpl_by_concatenation_of_intervals (Task Job : eqType) : SProp :=
  forall p1 p2 : Task -> Lean.Nat,
    ltac:(type_of_term (I.Prosa_Classic_Analysis_Global_Basic_InterferenceBoundEdf_InterferenceBoundEDF_interference_bound_edf_simpl_by_concatenation_of_intervals Task (ct_decidable_eq Task) p1 p2 Job (ct_decidable_eq Job))).
Theorem InterferenceBoundEDF_interference_bound_edf_simpl_by_concatenation_of_intervals_correspondence (Task Job : eqType) :
  PropSPropRel (src_interference_bound_edf_simpl_by_concatenation_of_intervals Task Job) (tgt_interference_bound_edf_simpl_by_concatenation_of_intervals Task Job).
Proof. unfold src_interference_bound_edf_simpl_by_concatenation_of_intervals, tgt_interference_bound_edf_simpl_by_concatenation_of_intervals. crel_spine. crel. Unshelve. all: crel. Qed.

Definition src_interference_bound_edf_interference_of_j_fst_limited_by_remainder_and_slack (Task Job : eqType) : Prop :=
  forall p1 p2 p3 : Task -> Time.time,
    ltac:(type_of_term (@InterferenceBoundEDF.interference_bound_edf_interference_of_j_fst_limited_by_remainder_and_slack Task p1 p2 p3 Job)).
Definition tgt_interference_bound_edf_interference_of_j_fst_limited_by_remainder_and_slack (Task Job : eqType) : SProp :=
  forall p1 p2 p3 : Task -> Lean.Nat,
    ltac:(type_of_term (I.Prosa_Classic_Analysis_Global_Basic_InterferenceBoundEdf_InterferenceBoundEDF_interference_bound_edf_interference_of_j_fst_limited_by_remainder_and_slack Task (ct_decidable_eq Task) p1 p2 p3 Job (ct_decidable_eq Job))).
Theorem InterferenceBoundEDF_interference_bound_edf_interference_of_j_fst_limited_by_remainder_and_slack_correspondence (Task Job : eqType) :
  PropSPropRel (src_interference_bound_edf_interference_of_j_fst_limited_by_remainder_and_slack Task Job) (tgt_interference_bound_edf_interference_of_j_fst_limited_by_remainder_and_slack Task Job).
Proof. unfold src_interference_bound_edf_interference_of_j_fst_limited_by_remainder_and_slack, tgt_interference_bound_edf_interference_of_j_fst_limited_by_remainder_and_slack. crel_spine. crel. Unshelve. all: crel. Qed.

Definition src_interference_bound_edf_holds_for_multiple_jobs (Task Job : eqType) : Prop :=
  forall p1 p2 p3 : Task -> Time.time,
    ltac:(type_of_term (@InterferenceBoundEDF.interference_bound_edf_holds_for_multiple_jobs Task p1 p2 p3 Job)).
Definition tgt_interference_bound_edf_holds_for_multiple_jobs (Task Job : eqType) : SProp :=
  forall p1 p2 p3 : Task -> Lean.Nat,
    ltac:(type_of_term (I.Prosa_Classic_Analysis_Global_Basic_InterferenceBoundEdf_InterferenceBoundEDF_interference_bound_edf_holds_for_multiple_jobs Task (ct_decidable_eq Task) p1 p2 p3 Job (ct_decidable_eq Job))).
Theorem InterferenceBoundEDF_interference_bound_edf_holds_for_multiple_jobs_correspondence (Task Job : eqType) :
  PropSPropRel (src_interference_bound_edf_holds_for_multiple_jobs Task Job) (tgt_interference_bound_edf_holds_for_multiple_jobs Task Job).
Proof. unfold src_interference_bound_edf_holds_for_multiple_jobs, tgt_interference_bound_edf_holds_for_multiple_jobs. crel_spine. crel. Unshelve. all: crel. Qed.

Definition src_interference_bound_edf_bounds_interference (Task Job : eqType) : Prop :=
  forall p1 p2 p3 : Task -> Time.time,
    ltac:(type_of_term (@InterferenceBoundEDF.interference_bound_edf_bounds_interference Task p1 p2 p3 Job)).
Definition tgt_interference_bound_edf_bounds_interference (Task Job : eqType) : SProp :=
  forall p1 p2 p3 : Task -> Lean.Nat,
    ltac:(type_of_term (I.Prosa_Classic_Analysis_Global_Basic_InterferenceBoundEdf_InterferenceBoundEDF_interference_bound_edf_bounds_interference Task (ct_decidable_eq Task) p1 p2 p3 Job (ct_decidable_eq Job))).
Theorem InterferenceBoundEDF_interference_bound_edf_bounds_interference_correspondence (Task Job : eqType) :
  PropSPropRel (src_interference_bound_edf_bounds_interference Task Job) (tgt_interference_bound_edf_bounds_interference Task Job).
Proof. unfold src_interference_bound_edf_bounds_interference, tgt_interference_bound_edf_bounds_interference. crel_spine. crel. Unshelve. all: crel. Qed.

Definition src_interference_bound_edf_monotonic (Task : eqType) : Prop :=
  forall p1 p2 p3 : Task -> Time.time,
    ltac:(type_of_term (@InterferenceBoundEDF.interference_bound_edf_monotonic Task p1 p2 p3)).
Definition tgt_interference_bound_edf_monotonic (Task : eqType) : SProp :=
  forall p1 p2 p3 : Task -> Lean.Nat,
    ltac:(type_of_term (I.Prosa_Classic_Analysis_Global_Basic_InterferenceBoundEdf_InterferenceBoundEDF_interference_bound_edf_monotonic Task (ct_decidable_eq Task) p1 p2 p3)).
Theorem InterferenceBoundEDF_interference_bound_edf_monotonic_correspondence (Task : eqType) :
  PropSPropRel (src_interference_bound_edf_monotonic Task) (tgt_interference_bound_edf_monotonic Task).
Proof. unfold src_interference_bound_edf_monotonic, tgt_interference_bound_edf_monotonic. crel_spine. crel. Unshelve. all: crel. Qed.
