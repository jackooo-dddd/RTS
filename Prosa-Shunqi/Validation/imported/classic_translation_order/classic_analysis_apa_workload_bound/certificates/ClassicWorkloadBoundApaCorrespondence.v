From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq path fintype bigop div.
From prosa Require Import classic.model.time classic.util.div_mod classic.util.notation classic.model.arrival.basic.arrival_sequence
  classic.model.arrival.basic.task classic.model.arrival.basic.job classic.model.arrival.basic.task_arrival
  classic.model.schedule.global.basic.schedule classic.model.schedule.global.workload classic.analysis.apa.workload_bound.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedClassicWorkloadBoundApa.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence ClassicWorkloadBoundApaNatSub ClassicWorkloadBoundApaOps ClassicWorkloadBoundApaBase ClassicWorkloadBoundApaList ClassicWorkloadBoundApaOrd.

Module I := ImportedClassicWorkloadBoundApa.
Local Open Scope nat_scope.

(** Certificates for [classic/analysis/apa/workload_bound.v] (ProsaBuddy classic, commit f692cb7).

    Inputs, relations and computation as in the accepted classic schedule,
    workload, task_arrival and div_mod certificates (re-stated below for this
    export): eqTypes identified with their canonical Lean [DecidableEq]
    instances; times and [num_cpus] by [SubNatRel]; processors by their values;
    schedules pointwise ([CsSchedRel]); job and task parameters pointwise;
    sequences elementwise; arrival sequences pointwise on related times; all with
    two-way totals.  The sorted jobs [sort (fun x y => job_arrival x <= job_arrival y) s]
    against the core [List.mergeSort] through the exported stable-sort facts and
    the uniqueness of a sorted sequence with given key-class filters
    ([cta_sort_rel]); [nth] against [getD]; [workload]/[service]/[service_during]
    through kernel-guarded [rfl] body projections and the four half-open sums of
    the statements through kernel-guarded type normalization, related by
    [cs_ico]; [\sum_(i <- s) F i] against the accepted v0.6 [sumSeq];
    [div_floor] and the Nat operations through the accepted operation-level
    bridge [DivModCorrespondence], re-bound to this export.

    Statements: the source side is the exact elaborated type of the pinned lemma
    (via [type of]; the source proof is not used).  For the lemmas whose Rocq and
    Lean binder lists put task parameters before the job type, the job type is
    fixed as an [eqType] with its canonical Lean instance and the task parameters
    stay universally quantified on both sides. *)

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
  rewrite (imported_eq_to_coq_eq _ _ (I.Prosa_Validation_ClassicWorkloadBoundApaInterface_bigCat_range'
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
  - exact (Logic.eq_sym (imported_eq_to_coq_eq _ _ (I.Prosa_Validation_ClassicWorkloadBoundApaInterface_dedup_nil T (ct_decidable_eq T)))).
  - change (Logic.eq (cl_map cid (if x \in s then undup s else x :: undup s))
      (I.List_dedup T (ct_decidable_eq T) (I.List_cons T x (cl_map cid s)))).
    case Hx: (x \in s).
    + rewrite (imported_eq_to_coq_eq _ _ (I.Prosa_Validation_ClassicWorkloadBoundApaInterface_dedup_cons_mem
                 T (ct_decidable_eq T) x (cl_map cid s)
                 (prop_to_sprop _ _ (cs_mem T x s _ (cl_lean_eq _ _ _ (Logic.eq_refl _))) Hx))).
      exact IH.
    + rewrite (imported_eq_to_coq_eq _ _ (I.Prosa_Validation_ClassicWorkloadBoundApaInterface_dedup_cons_not_mem
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
  rewrite (imported_eq_to_coq_eq _ _ (I.Prosa_Validation_ClassicWorkloadBoundApaInterface_service_at_sum Job dJ nL sL j tL)).
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

Lemma cf_Schedule_service_during j t1R t1L t2R t2L (H1 : SubNatRel t1R t1L) (H2 : SubNatRel t2R t2L) :
  SubNatRel (Schedule.service_during sR j t1R t2R)
    (I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_service_during Job dJ nL sL j t1L t2L).
Proof. exact (cs_ico _ _ _ _ _ _ H1 H2 (cs_service_at_fun j)). Qed.

Lemma cf_Schedule_completed cR cL (Hc : CsParRel Job cR cL) j tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (Schedule.completed cR sR j tR)
    (I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_completed Job dJ cL nL sL j tL).
Proof. exact (ct_decide_le _ _ _ _ (Hc j) (cf_Schedule_service j tR tL Ht)). Qed.

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

Lemma cf_ScheduleOfSporadicTask_jobs_of_task_scheduled_between tsk t1R t1L t2R t2L
    (H1 : SubNatRel t1R t1L) (H2 : SubNatRel t2R t2L) :
  ClListRel cid (ScheduleOfSporadicTask.jobs_of_task_scheduled_between job_task sR tsk t1R t2R)
    (I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_ScheduleOfSporadicTask_jobs_of_task_scheduled_between
       Task Job dT dJ job_task nL sL tsk t1L t2L).
Proof.
  apply: coq_eq_to_imported_eq.
  refine (Logic.eq_trans (cl_filter cid (fun j => job_task j == tsk)
                            (fun j => I.Decidable_decide (Lean.eq (job_task j) tsk) (dT (job_task j) tsk))
                            (fun j => ct_decide_eq Task (job_task j) tsk) _) _).
  exact (f_equal (I.List_filter Job (fun j => I.Decidable_decide (Lean.eq (job_task j) tsk) (dT (job_task j) tsk)))
           (Logic.eq_sym (cl_list_logic _ _ _ (cf_Schedule_jobs_scheduled_between Job nR nL Hn sR sL Hs _ _ _ _ H1 H2)))).
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
(** * Stable sorting and lists (as in the accepted classic task_arrival certificate) *)

Lemma cta_false_rel : PropSPropRel Logic.False I.False.
Proof.
  apply prop_sprop_rel_intro.
  - exact ct_coq_false_to_target.
  - exact ct_target_false_to_strict.
Qed.

Lemma cta_ne (T : Type) (x y : T) : PropSPropRel (x <> y) (I.Ne T x y).
Proof. exact (ct_imp _ _ _ _ (ct_eq_rel T x y) cta_false_rel). Qed.

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
          end (I.Prosa_Validation_ClassicWorkloadBoundApaInterface_mergeSort_isChain T fL sL))).
  have Fu : forall x, filter (fun y => f y == f x) u = filter (fun y => f y == f x) s.
  { intro x. apply: cta_cl_map_inj.
    have Hp : forall y, CtBoolRel (f y == f x) (clsL x y) := fun y => ct_decide_eq_nat _ _ _ _ (Hf y) (Hf x).
    refine (Logic.eq_trans (cl_filter cid (fun y => f y == f x) (clsL x) Hp u)
              (Logic.eq_trans _ (Logic.eq_sym (cl_filter cid (fun y => f y == f x) (clsL x) Hp s)))).
    refine (Logic.eq_trans (f_equal (I.List_filter T (clsL x)) (Logic.eq_sym (cl_list_logic _ _ _ Hu)))
              (Logic.eq_trans _ (f_equal (I.List_filter T (clsL x)) (cl_list_logic _ _ _ Hs)))).
    exact (imported_eq_to_coq_eq _ _ (I.Prosa_Validation_ClassicWorkloadBoundApaInterface_mergeSort_filter_class T fL x sL)). }
  have E := cta_sort_unique T f u s Su Fu.
  apply: coq_eq_to_imported_eq. rewrite -E. exact (Logic.eq_sym (cl_list_logic _ _ _ Hu)).
Qed.
End Sort.


(* ------------------------------------------------------------------ *)
(** * Workload (as in the accepted classic workload certificate) *)

Section Wl.
Variables (Task Job : eqType) (nR : nat) (nL : Lean.Nat).
Hypothesis Hn : SubNatRel nR nL.
Notation dT := (ct_decidable_eq Task).
Notation dJ := (ct_decidable_eq Job).
Variables (sR : Schedule.schedule Job nR)
  (sL : I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_schedule Job dJ nL).
Hypothesis Hs : CsSchedRel Job nR nL sR sL.
Variable job_task : Job -> Task.

Lemma cai_service_of_task tsk (oR : 'I_nR) (oL : Fin nL) (o : option Job) :
  SubNatRel (Workload.service_of_task job_task tsk oR o)
    (I.Prosa_Classic_Model_Schedule_Global_Workload_Workload_service_of_task Task Job dT dJ job_task nL tsk oL (cl_opt o)).
Proof.
  destruct o as [x|].
  - exact (ct_bool_to_nat _ _ (ct_decide_eq Task (job_task x) tsk)).
  - exact (sub_nat_rel_canonical 0).
Qed.

Lemma cai_workload tsk t1R t1L t2R t2L (H1 : SubNatRel t1R t1L) (H2 : SubNatRel t2R t2L) :
  SubNatRel (Workload.workload job_task sR tsk t1R t2R)
    (I.Prosa_Classic_Model_Schedule_Global_Workload_Workload_workload Task Job dT dJ job_task nL sL tsk t1L t2L).
Proof.
  apply: (cs_ico _ _ _ _ _ _ H1 H2) => tR tL Ht.
  apply: (co_sum_rel nR nL Hn) => oR oL Ho.
  exact (cs_trs (Hs oR oL Ho tR tL Ht)
           (fun z => SubNatRel (Workload.service_of_task job_task tsk oR (sR oR tR))
                       (I.Prosa_Classic_Model_Schedule_Global_Workload_Workload_service_of_task Task Job dT dJ job_task nL tsk oL z))
           (cai_service_of_task tsk oR oL (sR oR tR))).
Qed.
End Wl.

(** [\sum_(i <- l) F i] against the accepted v0.6 [sumSeq] (as in the accepted classic sum certificate). *)
Lemma cai_sumSeq (T : Type) (FR : T -> nat) (FL : T -> Lean.Nat) (HF : forall x, SubNatRel (FR x) (FL x)) : forall l,
  SubNatRel (\sum_(i <- l) FR i) (I.Prosa_Util_Sum_sumSeq T (cl_map cid l) FL).
Proof.
  intro l. induction l as [|x l IH]; first by rewrite big_nil; exact (sub_nat_rel_canonical 0).
  rewrite big_cons.
  change (SubNatRel (FR x + \sum_(j <- l) FR j) (Lean.Nat_add (FL x) (I.Prosa_Util_Sum_sumSeq T (cl_map cid l) FL))).
  exact (sub_add_correspondence _ _ _ _ (HF x) IH).
Qed.


(* ------------------------------------------------------------------ *)
(** * The sorted scheduled jobs of the analysed task *)

Notation LSJ Task Job job_task nL sL tsk t1L dL :=
  (I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_ScheduleOfSporadicTask_jobs_of_task_scheduled_between Task Job (ct_decidable_eq Task) (ct_decidable_eq Job) job_task nL sL tsk t1L
     (I.HAdd_hAdd_inst7 Lean.Nat Lean.Nat Lean.Nat (I.instHAdd_inst1 Lean.Nat I.instAddNat) t1L dL)).
Notation LSORT Job jaL l :=
  (I.List_mergeSort Job l (fun x y => I.Decidable_decide (I.LE_le_inst1 Lean.Nat I.instLENat (jaL x) (jaL y)) (I.Nat_decLe (jaL x) (jaL y)))).

Lemma cwb_t2 t1R t1L dR dL (H1 : SubNatRel t1R t1L) (Hd : SubNatRel dR dL) :
  SubNatRel (t1R + dR) (I.HAdd_hAdd_inst7 Lean.Nat Lean.Nat Lean.Nat (I.instHAdd_inst1 Lean.Nat I.instAddNat) t1L dL).
Proof. exact (sub_add_correspondence _ _ _ _ H1 Hd). Qed.

Lemma cwb_sorted (Task Job : eqType) nR nL (Hn : SubNatRel nR nL) sR sL (Hs : CsSchedRel Job nR nL sR sL)
    jaR jaL (Hja : CsParRel Job jaR jaL) (job_task : Job -> Task) tsk t1R t1L dR dL (H1 : SubNatRel t1R t1L) (Hd : SubNatRel dR dL) :
  ClListRel cid (sort (fun x y => jaR x <= jaR y) (ScheduleOfSporadicTask.jobs_of_task_scheduled_between job_task sR tsk t1R (t1R + dR)))
    (LSORT Job jaL (LSJ Task Job job_task nL sL tsk t1L dL)).
Proof.
  exact (cta_sort_rel Job jaR jaL Hja _ _
           (cf_ScheduleOfSporadicTask_jobs_of_task_scheduled_between Task Job nR nL Hn sR sL Hs job_task tsk _ _ _ _ H1 (cwb_t2 _ _ _ _ H1 Hd))).
Qed.

Lemma cwb_add2 nR nL : SubNatRel nR nL ->
  SubNatRel nR.+2 (I.HAdd_hAdd_inst7 Lean.Nat Lean.Nat Lean.Nat (I.instHAdd_inst1 Lean.Nat I.instAddNat) nL
                     (I.OfNat_ofNat_inst1 Lean.Nat 2 (I.instOfNatNat 2))).
Proof.
  intro H. apply: coq_eq_to_imported_eq. rewrite -addn2.
  exact (imported_eq_to_coq_eq _ _ (sub_add_correspondence _ _ 2 _ H (sub_nat_rel_canonical 2))).
Qed.

Lemma cwb_sumSeq_rel (T : Type) FR FL (HF : forall x, SubNatRel (FR x) (FL x)) l L : ClListRel (B := T) cid l L ->
  SubNatRel (\sum_(i <- l) FR i) (I.Prosa_Util_Sum_sumSeq T L FL).
Proof. intro H. exact (cs_trs H (fun z => SubNatRel (\sum_(i <- l) FR i) (I.Prosa_Util_Sum_sumSeq T z FL)) (cai_sumSeq T FR FL HF l)). Qed.

(* ------------------------------------------------------------------ *)
(** * Task, job and arrival-model relations (as in the accepted classic task, job and task_arrival certificates) *)

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

Lemma cwb_valid_params (Task Job : eqType) tcR tcL (Htc : CsParRel Task tcR tcL) tdR tdL (Htd : CsParRel Task tdR tdL)
    cR cL (Hc : CsParRel Job cR cL) dR dL (Hd : CsParRel Job dR dL) (job_task : Job -> Task) aR aL (Ha : CsArrRel Job aR aL) :
  PropSPropRel (forall j, ArrivalSequence.arrives_in aR j -> Job.valid_sporadic_job tcR tdR cR dR job_task j)
    (forall j, I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrives_in Job (ct_decidable_eq Job) aL j ->
       I.Prosa_Classic_Model_Arrival_Basic_Job_Job_valid_sporadic_job Task (ct_decidable_eq Task) tcL tdL Job (ct_decidable_eq Job) cL dL job_task j).
Proof.
  apply: ct_forall_identity => j.
  exact (ct_imp _ _ _ _ (cs_arrives_in Job aR aL Ha j) (cwb_valid_sporadic_job Task Job tcR tcL Htc tdR tdL Htd cR cL Hc dR dL Hd job_task j)).
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

Lemma cwb_rt_bound (Task Job : eqType) nR nL (Hn : SubNatRel nR nL) sR sL (Hs : CsSchedRel Job nR nL sR sL)
    jaR jaL (Hja : CsParRel Job jaR jaL) cR cL (Hc : CsParRel Job cR cL) (job_task : Job -> Task) aR aL (Ha : CsArrRel Job aR aL)
    tsk t1R t1L dR dL RR RL (H1 : SubNatRel t1R t1L) (Hd : SubNatRel dR dL) (HR : SubNatRel RR RL) :
  PropSPropRel (forall j, ArrivalSequence.arrives_in aR j -> job_task j = tsk -> jaR j + RR < t1R + dR ->
                  Schedule.completed cR sR j (jaR j + RR))
    (forall j, I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrives_in Job (ct_decidable_eq Job) aL j ->
       Lean.eq (job_task j) tsk ->
       I.LT_lt_inst1 Lean.Nat I.instLTNat (I.HAdd_hAdd_inst7 Lean.Nat Lean.Nat Lean.Nat (I.instHAdd_inst1 Lean.Nat I.instAddNat) (jaL j) RL)
         (I.HAdd_hAdd_inst7 Lean.Nat Lean.Nat Lean.Nat (I.instHAdd_inst1 Lean.Nat I.instAddNat) t1L dL) ->
       Lean.eq (I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_completed Job (ct_decidable_eq Job) cL nL sL j
          (I.HAdd_hAdd_inst7 Lean.Nat Lean.Nat Lean.Nat (I.instHAdd_inst1 Lean.Nat I.instAddNat) (jaL j) RL)) I.Bool_true).
Proof.
  apply: ct_forall_identity => j.
  apply: ct_imp; first exact (cs_arrives_in Job aR aL Ha j).
  apply: ct_imp; first exact (ct_eq_rel Task (job_task j) tsk).
  have HjR := sub_add_correspondence _ _ _ _ (Hja j) HR.
  apply: ct_imp; first exact (sub_nat_lt_correspondence _ _ _ _ HjR (cwb_t2 _ _ _ _ H1 Hd)).
  exact (ct_bool_truth _ _ (cf_Schedule_completed Job nR nL Hn sR sL Hs cR cL Hc j _ _ HjR)).
Qed.

(* ------------------------------------------------------------------ *)
(** * Definitions *)

Theorem WorkloadBound_max_jobs_correspondence (Task : eqType) cR cL (Hc : CsParRel Task cR cL) pR pL (Hp : CsParRel Task pR pL) tsk
    RR RL (HR : SubNatRel RR RL) dR dL (Hd : SubNatRel dR dL) :
  SubNatRel (WorkloadBound.max_jobs cR pR tsk RR dR) (I.Prosa_Classic_Analysis_Apa_WorkloadBound_WorkloadBound_max_jobs Task (ct_decidable_eq Task) cL pL tsk RL dL).
Proof.
  exact (dm_div_floor_correspondence _ _ _ _ (dm_sub_correspondence _ _ _ _ (dm_add_correspondence _ _ _ _ Hd HR) (Hc tsk)) (Hp tsk)).
Qed.

Theorem WorkloadBound_W_correspondence (Task : eqType) cR cL (Hc : CsParRel Task cR cL) pR pL (Hp : CsParRel Task pR pL) tsk
    RR RL (HR : SubNatRel RR RL) dR dL (Hd : SubNatRel dR dL) :
  SubNatRel (WorkloadBound.W cR pR tsk RR dR) (I.Prosa_Classic_Analysis_Apa_WorkloadBound_WorkloadBound_W Task (ct_decidable_eq Task) cL pL tsk RL dL).
Proof.
  have Hm := WorkloadBound_max_jobs_correspondence Task cR cL Hc pR pL Hp tsk RR RL HR dR dL Hd.
  exact (dm_add_correspondence _ _ _ _
           (ct_min_rel _ _ _ _ (Hc tsk)
              (dm_sub_correspondence _ _ _ _ (dm_sub_correspondence _ _ _ _ (dm_add_correspondence _ _ _ _ Hd HR) (Hc tsk))
                 (dm_mul_correspondence _ _ _ _ Hm (Hp tsk))))
           (dm_mul_correspondence _ _ _ _ Hm (Hc tsk))).
Qed.

(* ------------------------------------------------------------------ *)
(** * Statements *)

Notation sorted := cwb_sorted.
Notation getD := cta_getD.
Notation SD Job nR nL Hn sR sL Hs j t1R t1L dR dL H1 Hd :=
  (cf_Schedule_service_during Job nR nL Hn sR sL Hs j _ _ _ _ H1 (cwb_t2 t1R t1L dR dL H1 Hd)).

Lemma cf_Workload_joblist (Task Job : eqType) nR nL (Hn : SubNatRel nR nL) sR sL (Hs : CsSchedRel Job nR nL sR sL)
    (job_task : Job -> Task) tsk t1R t1L t2R t2L (H1 : SubNatRel t1R t1L) (H2 : SubNatRel t2R t2L) :
  SubNatRel (Workload.workload_joblist job_task sR tsk t1R t2R)
    (I.Prosa_Classic_Model_Schedule_Global_Workload_Workload_workload_joblist Task Job (ct_decidable_eq Task) (ct_decidable_eq Job) job_task nL sL tsk t1L t2L).
Proof.
  have HL := cf_ScheduleOfSporadicTask_jobs_of_task_scheduled_between Task Job nR nL Hn sR sL Hs job_task tsk _ _ _ _ H1 H2.
  exact (cwb_sumSeq_rel Job _ _ (fun j => cf_Schedule_service_during Job nR nL Hn sR sL Hs j _ _ _ _ H1 H2) _ _ HL).
Qed.

Definition src_W_monotonic (Task : eqType) : Prop := ltac:(type_of_term (@WorkloadBound.W_monotonic Task)).
Definition tgt_W_monotonic (Task : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Analysis_Apa_WorkloadBound_WorkloadBound_W_monotonic Task (ct_decidable_eq Task))).
Theorem WorkloadBound_W_monotonic_correspondence (Task : eqType) :
  PropSPropRel (src_W_monotonic Task) (tgt_W_monotonic Task).
Proof.
  unfold src_W_monotonic, tgt_W_monotonic.
  apply: cs_forall_par => task_costR task_costL Htask_cost. apply: cs_forall_par => task_periodR task_periodL Htask_period.
  apply: ct_forall_identity => tsk.
  apply: ct_imp; first exact (sub_nat_lt_correspondence _ _ _ _ (sub_nat_rel_canonical 0) (Htask_period tsk)).
  apply: ct_forall_nat => R1R R1L H1. apply: ct_forall_nat => R2R R2L H2.
  apply: ct_imp; first exact (sub_nat_le_correspondence _ _ _ _ (Htask_cost tsk) H1).
  apply: ct_imp; first exact (sub_nat_le_correspondence _ _ _ _ H1 H2).
  apply: ct_forall_nat => t1R t1L Ht1. apply: ct_forall_nat => t2R t2L Ht2.
  apply: ct_imp; first exact (sub_nat_le_correspondence _ _ _ _ Ht1 Ht2).
  exact (sub_nat_le_correspondence _ _ _ _
           (WorkloadBound_W_correspondence Task task_costR task_costL Htask_cost task_periodR task_periodL Htask_period tsk _ _ H1 _ _ Ht1)
           (WorkloadBound_W_correspondence Task task_costR task_costL Htask_cost task_periodR task_periodL Htask_period tsk _ _ H2 _ _ Ht2)).
Qed.

Definition src_workload_bound_simpl_by_sorting_scheduled_jobs (Task Job : eqType) : Prop :=
  ltac:(type_of_term (@WorkloadBound.workload_bound_simpl_by_sorting_scheduled_jobs Task Job)).
Definition tgt_workload_bound_simpl_by_sorting_scheduled_jobs (Task Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Analysis_Apa_WorkloadBound_WorkloadBound_workload_bound_simpl_by_sorting_scheduled_jobs Task Job (ct_decidable_eq Task) (ct_decidable_eq Job))).
Theorem WorkloadBound_workload_bound_simpl_by_sorting_scheduled_jobs_correspondence (Task Job : eqType) :
  PropSPropRel (src_workload_bound_simpl_by_sorting_scheduled_jobs Task Job) (tgt_workload_bound_simpl_by_sorting_scheduled_jobs Task Job).
Proof.
  unfold src_workload_bound_simpl_by_sorting_scheduled_jobs, tgt_workload_bound_simpl_by_sorting_scheduled_jobs.
  apply: cs_forall_par => jaR jaL Hja.
  apply: ct_forall_identity => job_task.
  apply: cs_forall_ncpus_sched => nR nL Hn sR sL Hs.
  apply: ct_forall_identity => tsk.
  apply: ct_forall_nat => t1R t1L H1. apply: ct_forall_nat => dR dL Hd.
  have Hs' := sorted Task Job nR nL Hn sR sL Hs jaR jaL Hja job_task tsk _ _ _ _ H1 Hd.
  apply: sub_nat_eq_correspondence.
  - exact (cf_Workload_joblist Task Job nR nL Hn sR sL Hs job_task tsk _ _ _ _ H1 (cwb_t2 _ _ _ _ H1 Hd)).
  - exact (cwb_sumSeq_rel Job _ _ (fun i => (SD Job nR nL Hn sR sL Hs i t1R t1L dR dL H1 Hd)) _ _ Hs').
Qed.

Definition src_workload_bound_job_in_same_sequence (Task Job : eqType) : Prop :=
  ltac:(type_of_term (@WorkloadBound.workload_bound_job_in_same_sequence Task Job)).
Definition tgt_workload_bound_job_in_same_sequence (Task Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Analysis_Apa_WorkloadBound_WorkloadBound_workload_bound_job_in_same_sequence Task Job (ct_decidable_eq Task) (ct_decidable_eq Job))).
Theorem WorkloadBound_workload_bound_job_in_same_sequence_correspondence (Task Job : eqType) :
  PropSPropRel (src_workload_bound_job_in_same_sequence Task Job) (tgt_workload_bound_job_in_same_sequence Task Job).
Proof.
  unfold src_workload_bound_job_in_same_sequence, tgt_workload_bound_job_in_same_sequence.
  apply: cs_forall_par => jaR jaL Hja.
  apply: ct_forall_identity => job_task.
  apply: cs_forall_ncpus_sched => nR nL Hn sR sL Hs.
  apply: ct_forall_identity => tsk.
  apply: ct_forall_nat => t1R t1L H1. apply: ct_forall_nat => dR dL Hd.
  apply: ct_forall_identity => j.
  have Hs' := sorted Task Job nR nL Hn sR sL Hs jaR jaL Hja job_task tsk _ _ _ _ H1 Hd.
  apply: ct_bool_eq.
  - exact (ct_decide_bool _ _ _ (cs_mem Job j _ _ (cf_ScheduleOfSporadicTask_jobs_of_task_scheduled_between Task Job nR nL Hn sR sL Hs job_task tsk _ _ _ _ H1 (cwb_t2 _ _ _ _ H1 Hd)))).
  - exact (ct_decide_bool _ _ _ (cs_mem Job j _ _ Hs')).
Qed.

Definition src_workload_bound_all_jobs_from_tsk (Task Job : eqType) : Prop :=
  ltac:(type_of_term (@WorkloadBound.workload_bound_all_jobs_from_tsk Task Job)).
Definition tgt_workload_bound_all_jobs_from_tsk (Task Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Analysis_Apa_WorkloadBound_WorkloadBound_workload_bound_all_jobs_from_tsk Task Job (ct_decidable_eq Task) (ct_decidable_eq Job))).
Theorem WorkloadBound_workload_bound_all_jobs_from_tsk_correspondence (Task Job : eqType) :
  PropSPropRel (src_workload_bound_all_jobs_from_tsk Task Job) (tgt_workload_bound_all_jobs_from_tsk Task Job).
Proof.
  unfold src_workload_bound_all_jobs_from_tsk, tgt_workload_bound_all_jobs_from_tsk.
  apply: cs_forall_par => jaR jaL Hja.
  apply: ct_forall_identity => job_task.
  apply: cwb_forall_arr => aR aL Ha.
  apply: cs_forall_ncpus_sched => nR nL Hn sR sL Hs.
  apply: ct_imp; first exact (cf_Schedule_jobs_come_from_arrival_sequence Job nR nL Hn sR sL Hs aR aL Ha).
  apply: ct_forall_identity => tsk.
  apply: ct_forall_nat => t1R t1L H1. apply: ct_forall_nat => dR dL Hd.
  apply: ct_forall_identity => j_i.
  have Hs' := sorted Task Job nR nL Hn sR sL Hs jaR jaL Hja job_task tsk _ _ _ _ H1 Hd.
  apply: ct_imp; first exact (cs_mem Job j_i _ _ Hs').
  apply: ct_and; first exact (cs_arrives_in Job aR aL Ha j_i).
  apply: ct_and; first exact (ct_eq_rel Task (job_task j_i) tsk).
  apply: ct_and; first exact (ct_bool_truth _ _ (ct_bool_not _ _ (ct_decide_eq_nat _ _ _ _ (SD Job nR nL Hn sR sL Hs (j_i) t1R t1L dR dL H1 Hd) (sub_nat_rel_canonical 0)))).
  exact (cs_mem Job j_i _ _ (cf_Schedule_jobs_scheduled_between Job nR nL Hn sR sL Hs _ _ _ _ H1 (cwb_t2 _ _ _ _ H1 Hd))).
Qed.

Definition src_workload_bound_jobs_ordered_by_arrival (Task Job : eqType) : Prop :=
  ltac:(type_of_term (@WorkloadBound.workload_bound_jobs_ordered_by_arrival Task Job)).
Definition tgt_workload_bound_jobs_ordered_by_arrival (Task Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Analysis_Apa_WorkloadBound_WorkloadBound_workload_bound_jobs_ordered_by_arrival Task Job (ct_decidable_eq Task) (ct_decidable_eq Job))).
Theorem WorkloadBound_workload_bound_jobs_ordered_by_arrival_correspondence (Task Job : eqType) :
  PropSPropRel (src_workload_bound_jobs_ordered_by_arrival Task Job) (tgt_workload_bound_jobs_ordered_by_arrival Task Job).
Proof.
  unfold src_workload_bound_jobs_ordered_by_arrival, tgt_workload_bound_jobs_ordered_by_arrival.
  apply: cs_forall_par => jaR jaL Hja.
  apply: ct_forall_identity => job_task.
  apply: cs_forall_ncpus_sched => nR nL Hn sR sL Hs.
  apply: ct_forall_identity => tsk.
  apply: ct_forall_nat => t1R t1L H1. apply: ct_forall_nat => dR dL Hd.
  apply: ct_forall_nat => iR iL Hi. apply: ct_forall_identity => elem.
  have Hs' := sorted Task Job nR nL Hn sR sL Hs jaR jaL Hja job_task tsk _ _ _ _ H1 Hd.
  apply: ct_imp; first exact (sub_nat_lt_correspondence _ _ _ _ Hi (cta_pred_rel _ _ (cs_list_size Job _ _ Hs'))).
  rewrite (getD Job _ _ Hs' elem _ _ Hi) (getD Job _ _ Hs' elem _ _ (cta_succ_rel _ _ Hi)).
  exact (sub_nat_le_correspondence _ _ _ _ (Hja _) (Hja _)).
Qed.

Definition src_workload_bound_holds_for_at_most_n_k_jobs (Task Job : eqType) : Prop :=
  forall task_cost task_period task_deadline : Task -> Time.time,
    ltac:(type_of_term (@WorkloadBound.workload_bound_holds_for_at_most_n_k_jobs Task task_cost task_period task_deadline Job)).
Definition tgt_workload_bound_holds_for_at_most_n_k_jobs (Task Job : eqType) : SProp :=
  forall task_cost task_period task_deadline : Task -> Lean.Nat,
    ltac:(type_of_term (I.Prosa_Classic_Analysis_Apa_WorkloadBound_WorkloadBound_workload_bound_holds_for_at_most_n_k_jobs Task (ct_decidable_eq Task) task_cost task_period task_deadline Job (ct_decidable_eq Job))).
Theorem WorkloadBound_workload_bound_holds_for_at_most_n_k_jobs_correspondence (Task Job : eqType) :
  PropSPropRel (src_workload_bound_holds_for_at_most_n_k_jobs Task Job) (tgt_workload_bound_holds_for_at_most_n_k_jobs Task Job).
Proof.
  unfold src_workload_bound_holds_for_at_most_n_k_jobs, tgt_workload_bound_holds_for_at_most_n_k_jobs.
  apply: cs_forall_par => task_costR task_costL Htask_cost.
  apply: cs_forall_par => task_periodR task_periodL Htask_period.
  apply: cs_forall_par => task_deadlineR task_deadlineL Htask_deadline.
  apply: cs_forall_par => jaR jaL Hja. apply: cs_forall_par => cR cL Hc.
  apply: ct_forall_identity => job_task.
  apply: cs_forall_par => jdR jdL Hjd.
  apply: cwb_forall_arr => aR aL Ha.
  apply: ct_imp; first exact (cwb_valid_params Task Job task_costR task_costL Htask_cost task_deadlineR task_deadlineL Htask_deadline cR cL Hc jdR jdL Hjd job_task aR aL Ha).
  apply: cs_forall_ncpus_sched => nR nL Hn sR sL Hs.
  apply: ct_imp; first exact (cf_Schedule_jobs_come_from_arrival_sequence Job nR nL Hn sR sL Hs aR aL Ha).
  apply: ct_imp; first exact (cf_Schedule_completed_jobs_dont_execute Job nR nL Hn sR sL Hs cR cL Hc).
  apply: ct_forall_identity => tsk.
  apply: ct_forall_nat => t1R t1L H1. apply: ct_forall_nat => dR dL Hd.
  apply: ct_forall_nat => RR RL HR.
  have Hs' := sorted Task Job nR nL Hn sR sL Hs jaR jaL Hja job_task tsk _ _ _ _ H1 Hd.
  apply: ct_imp; first exact (sub_nat_le_correspondence _ _ _ _ (cs_list_size Job _ _ Hs') (WorkloadBound_max_jobs_correspondence Task task_costR task_costL Htask_cost task_periodR task_periodL Htask_period tsk _ _ HR _ _ Hd)).
  exact (sub_nat_le_correspondence _ _ _ _ (cwb_sumSeq_rel Job _ _ (fun i => (SD Job nR nL Hn sR sL Hs i t1R t1L dR dL H1 Hd)) _ _ Hs') (WorkloadBound_W_correspondence Task task_costR task_costL Htask_cost task_periodR task_periodL Htask_period tsk _ _ HR _ _ Hd)).
Qed.

Definition src_workload_bound_j_fst_is_job_of_tsk (Task Job : eqType) : Prop :=
  ltac:(type_of_term (@WorkloadBound.workload_bound_j_fst_is_job_of_tsk Task Job)).
Definition tgt_workload_bound_j_fst_is_job_of_tsk (Task Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Analysis_Apa_WorkloadBound_WorkloadBound_workload_bound_j_fst_is_job_of_tsk Task Job (ct_decidable_eq Task) (ct_decidable_eq Job))).
Theorem WorkloadBound_workload_bound_j_fst_is_job_of_tsk_correspondence (Task Job : eqType) :
  PropSPropRel (src_workload_bound_j_fst_is_job_of_tsk Task Job) (tgt_workload_bound_j_fst_is_job_of_tsk Task Job).
Proof.
  unfold src_workload_bound_j_fst_is_job_of_tsk, tgt_workload_bound_j_fst_is_job_of_tsk.
  apply: cs_forall_par => jaR jaL Hja.
  apply: ct_forall_identity => job_task.
  apply: cwb_forall_arr => aR aL Ha.
  apply: cs_forall_ncpus_sched => nR nL Hn sR sL Hs.
  apply: ct_imp; first exact (cf_Schedule_jobs_come_from_arrival_sequence Job nR nL Hn sR sL Hs aR aL Ha).
  apply: ct_forall_identity => tsk.
  apply: ct_forall_nat => t1R t1L H1. apply: ct_forall_nat => dR dL Hd.
  have Hs' := sorted Task Job nR nL Hn sR sL Hs jaR jaL Hja job_task tsk _ _ _ _ H1 Hd.
  apply: ct_imp; first exact (sub_nat_lt_correspondence _ _ _ _ (sub_nat_rel_canonical 0) (cs_list_size Job _ _ Hs')).
  apply: ct_forall_identity => elem.
  rewrite (getD Job _ _ Hs' elem _ _ (sub_nat_rel_canonical 0)).
  apply: ct_and; first exact (cs_arrives_in Job aR aL Ha (nth elem (sort (fun x y => jaR x <= jaR y) (ScheduleOfSporadicTask.jobs_of_task_scheduled_between job_task sR tsk t1R (t1R + dR))) 0)).
  apply: ct_and; first exact (ct_eq_rel Task (job_task (nth elem (sort (fun x y => jaR x <= jaR y) (ScheduleOfSporadicTask.jobs_of_task_scheduled_between job_task sR tsk t1R (t1R + dR))) 0)) tsk).
  apply: ct_and; first exact (ct_bool_truth _ _ (ct_bool_not _ _ (ct_decide_eq_nat _ _ _ _ (SD Job nR nL Hn sR sL Hs ((nth elem (sort (fun x y => jaR x <= jaR y) (ScheduleOfSporadicTask.jobs_of_task_scheduled_between job_task sR tsk t1R (t1R + dR))) 0)) t1R t1L dR dL H1 Hd) (sub_nat_rel_canonical 0)))).
  exact (cs_mem Job (nth elem (sort (fun x y => jaR x <= jaR y) (ScheduleOfSporadicTask.jobs_of_task_scheduled_between job_task sR tsk t1R (t1R + dR))) 0) _ _ (cf_Schedule_jobs_scheduled_between Job nR nL Hn sR sL Hs _ _ _ _ H1 (cwb_t2 _ _ _ _ H1 Hd))).
Qed.

Definition src_workload_bound_holds_for_a_single_job (Task Job : eqType) : Prop :=
  forall task_cost task_period task_deadline : Task -> Time.time,
    ltac:(type_of_term (@WorkloadBound.workload_bound_holds_for_a_single_job Task task_cost task_period task_deadline Job)).
Definition tgt_workload_bound_holds_for_a_single_job (Task Job : eqType) : SProp :=
  forall task_cost task_period task_deadline : Task -> Lean.Nat,
    ltac:(type_of_term (I.Prosa_Classic_Analysis_Apa_WorkloadBound_WorkloadBound_workload_bound_holds_for_a_single_job Task (ct_decidable_eq Task) task_cost task_period task_deadline Job (ct_decidable_eq Job))).
Theorem WorkloadBound_workload_bound_holds_for_a_single_job_correspondence (Task Job : eqType) :
  PropSPropRel (src_workload_bound_holds_for_a_single_job Task Job) (tgt_workload_bound_holds_for_a_single_job Task Job).
Proof.
  unfold src_workload_bound_holds_for_a_single_job, tgt_workload_bound_holds_for_a_single_job.
  apply: cs_forall_par => task_costR task_costL Htask_cost.
  apply: cs_forall_par => task_periodR task_periodL Htask_period.
  apply: cs_forall_par => task_deadlineR task_deadlineL Htask_deadline.
  apply: cs_forall_par => jaR jaL Hja. apply: cs_forall_par => cR cL Hc.
  apply: ct_forall_identity => job_task.
  apply: cs_forall_par => jdR jdL Hjd.
  apply: cwb_forall_arr => aR aL Ha.
  apply: ct_imp; first exact (cwb_valid_params Task Job task_costR task_costL Htask_cost task_deadlineR task_deadlineL Htask_deadline cR cL Hc jdR jdL Hjd job_task aR aL Ha).
  apply: cs_forall_ncpus_sched => nR nL Hn sR sL Hs.
  apply: ct_imp; first exact (cf_Schedule_jobs_come_from_arrival_sequence Job nR nL Hn sR sL Hs aR aL Ha).
  apply: ct_imp; first exact (cf_Schedule_completed_jobs_dont_execute Job nR nL Hn sR sL Hs cR cL Hc).
  apply: ct_imp; first exact (cf_Schedule_sequential_jobs Job nR nL Hn sR sL Hs).
  apply: ct_forall_identity => tsk.
  apply: ct_forall_nat => t1R t1L H1. apply: ct_forall_nat => dR dL Hd.
  apply: ct_forall_nat => RR RL HR.
  apply: ct_imp; first exact (sub_nat_le_correspondence _ _ _ _ (Htask_cost tsk) HR).
  have Hs' := sorted Task Job nR nL Hn sR sL Hs jaR jaL Hja job_task tsk _ _ _ _ H1 Hd.
  apply: ct_imp; first exact (sub_nat_lt_correspondence _ _ _ _ (sub_nat_rel_canonical 0) (cs_list_size Job _ _ Hs')).
  apply: ct_forall_identity => elem.
  apply: sub_nat_le_correspondence; last exact (WorkloadBound_W_correspondence Task task_costR task_costL Htask_cost task_periodR task_periodL Htask_period tsk _ _ HR _ _ Hd).
  apply: (cs_ico _ _ _ _ _ _ (sub_nat_rel_canonical 0) (sub_nat_rel_canonical 1)) => iR iL Hi.
  rewrite (getD Job _ _ Hs' elem _ _ Hi). exact (SD Job nR nL Hn sR sL Hs (nth elem _ iR) t1R t1L dR dL H1 Hd).
Qed.

Definition src_workload_bound_j_lst_is_job_of_tsk (Task Job : eqType) : Prop :=
  ltac:(type_of_term (@WorkloadBound.workload_bound_j_lst_is_job_of_tsk Task Job)).
Definition tgt_workload_bound_j_lst_is_job_of_tsk (Task Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Analysis_Apa_WorkloadBound_WorkloadBound_workload_bound_j_lst_is_job_of_tsk Task Job (ct_decidable_eq Task) (ct_decidable_eq Job))).
Theorem WorkloadBound_workload_bound_j_lst_is_job_of_tsk_correspondence (Task Job : eqType) :
  PropSPropRel (src_workload_bound_j_lst_is_job_of_tsk Task Job) (tgt_workload_bound_j_lst_is_job_of_tsk Task Job).
Proof.
  unfold src_workload_bound_j_lst_is_job_of_tsk, tgt_workload_bound_j_lst_is_job_of_tsk.
  apply: cs_forall_par => jaR jaL Hja.
  apply: ct_forall_identity => job_task.
  apply: cwb_forall_arr => aR aL Ha.
  apply: cs_forall_ncpus_sched => nR nL Hn sR sL Hs.
  apply: ct_imp; first exact (cf_Schedule_jobs_come_from_arrival_sequence Job nR nL Hn sR sL Hs aR aL Ha).
  apply: ct_forall_identity => tsk.
  apply: ct_forall_nat => t1R t1L H1. apply: ct_forall_nat => dR dL Hd.
  apply: ct_forall_nat => mR mL Hm.
  have Hs' := sorted Task Job nR nL Hn sR sL Hs jaR jaL Hja job_task tsk _ _ _ _ H1 Hd.
  apply: ct_imp; first exact (sub_nat_eq_correspondence _ _ _ _ (cs_list_size Job _ _ Hs') (cwb_add2 _ _ Hm)).
  apply: ct_forall_identity => elem.
  rewrite (getD Job _ _ Hs' elem _ _ (cta_succ_rel _ _ Hm)).
  apply: ct_and; first exact (cs_arrives_in Job aR aL Ha (nth elem (sort (fun x y => jaR x <= jaR y) (ScheduleOfSporadicTask.jobs_of_task_scheduled_between job_task sR tsk t1R (t1R + dR))) mR.+1)).
  apply: ct_and; first exact (ct_eq_rel Task (job_task (nth elem (sort (fun x y => jaR x <= jaR y) (ScheduleOfSporadicTask.jobs_of_task_scheduled_between job_task sR tsk t1R (t1R + dR))) mR.+1)) tsk).
  apply: ct_and; first exact (ct_bool_truth _ _ (ct_bool_not _ _ (ct_decide_eq_nat _ _ _ _ (SD Job nR nL Hn sR sL Hs ((nth elem (sort (fun x y => jaR x <= jaR y) (ScheduleOfSporadicTask.jobs_of_task_scheduled_between job_task sR tsk t1R (t1R + dR))) mR.+1)) t1R t1L dR dL H1 Hd) (sub_nat_rel_canonical 0)))).
  exact (cs_mem Job (nth elem (sort (fun x y => jaR x <= jaR y) (ScheduleOfSporadicTask.jobs_of_task_scheduled_between job_task sR tsk t1R (t1R + dR))) mR.+1) _ _ (cf_Schedule_jobs_scheduled_between Job nR nL Hn sR sL Hs _ _ _ _ H1 (cwb_t2 _ _ _ _ H1 Hd))).
Qed.

Definition src_workload_bound_response_time_of_first_job_inside_interval (Task Job : eqType) : Prop :=
  ltac:(type_of_term (@WorkloadBound.workload_bound_response_time_of_first_job_inside_interval Task Job)).
Definition tgt_workload_bound_response_time_of_first_job_inside_interval (Task Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Analysis_Apa_WorkloadBound_WorkloadBound_workload_bound_response_time_of_first_job_inside_interval Task Job (ct_decidable_eq Task) (ct_decidable_eq Job))).
Theorem WorkloadBound_workload_bound_response_time_of_first_job_inside_interval_correspondence (Task Job : eqType) :
  PropSPropRel (src_workload_bound_response_time_of_first_job_inside_interval Task Job) (tgt_workload_bound_response_time_of_first_job_inside_interval Task Job).
Proof.
  unfold src_workload_bound_response_time_of_first_job_inside_interval, tgt_workload_bound_response_time_of_first_job_inside_interval.
  apply: cs_forall_par => jaR jaL Hja. apply: cs_forall_par => cR cL Hc.
  apply: ct_forall_identity => job_task.
  apply: cwb_forall_arr => aR aL Ha.
  apply: cs_forall_ncpus_sched => nR nL Hn sR sL Hs.
  apply: ct_imp; first exact (cf_Schedule_jobs_come_from_arrival_sequence Job nR nL Hn sR sL Hs aR aL Ha).
  apply: ct_imp; first exact (cf_Schedule_completed_jobs_dont_execute Job nR nL Hn sR sL Hs cR cL Hc).
  apply: ct_forall_identity => tsk.
  apply: ct_forall_nat => t1R t1L H1. apply: ct_forall_nat => dR dL Hd.
  apply: ct_forall_nat => RR RL HR.
  apply: ct_imp; first exact (cwb_rt_bound Task Job nR nL Hn sR sL Hs jaR jaL Hja cR cL Hc job_task aR aL Ha tsk _ _ _ _ _ _ H1 Hd HR).
  apply: ct_forall_nat => mR mL Hm.
  have Hs' := sorted Task Job nR nL Hn sR sL Hs jaR jaL Hja job_task tsk _ _ _ _ H1 Hd.
  apply: ct_imp; first exact (sub_nat_eq_correspondence _ _ _ _ (cs_list_size Job _ _ Hs') (cwb_add2 _ _ Hm)).
  apply: ct_forall_identity => elem.
  rewrite (getD Job _ _ Hs' elem _ _ (sub_nat_rel_canonical 0)).
  exact (sub_nat_le_correspondence _ _ _ _ H1 (sub_add_correspondence _ _ _ _ (Hja _) HR)).
Qed.

Definition src_workload_bound_last_job_arrives_before_end_of_interval (Task Job : eqType) : Prop :=
  ltac:(type_of_term (@WorkloadBound.workload_bound_last_job_arrives_before_end_of_interval Task Job)).
Definition tgt_workload_bound_last_job_arrives_before_end_of_interval (Task Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Analysis_Apa_WorkloadBound_WorkloadBound_workload_bound_last_job_arrives_before_end_of_interval Task Job (ct_decidable_eq Task) (ct_decidable_eq Job))).
Theorem WorkloadBound_workload_bound_last_job_arrives_before_end_of_interval_correspondence (Task Job : eqType) :
  PropSPropRel (src_workload_bound_last_job_arrives_before_end_of_interval Task Job) (tgt_workload_bound_last_job_arrives_before_end_of_interval Task Job).
Proof.
  unfold src_workload_bound_last_job_arrives_before_end_of_interval, tgt_workload_bound_last_job_arrives_before_end_of_interval.
  apply: cs_forall_par => jaR jaL Hja.
  apply: ct_forall_identity => job_task.
  apply: cwb_forall_arr => aR aL Ha.
  apply: cs_forall_ncpus_sched => nR nL Hn sR sL Hs.
  apply: ct_imp; first exact (cf_Schedule_jobs_come_from_arrival_sequence Job nR nL Hn sR sL Hs aR aL Ha).
  apply: ct_imp; first exact (cf_Schedule_jobs_must_arrive_to_execute Job nR nL Hn sR sL Hs jaR jaL Hja).
  apply: ct_forall_identity => tsk.
  apply: ct_forall_nat => t1R t1L H1. apply: ct_forall_nat => dR dL Hd.
  apply: ct_forall_nat => mR mL Hm.
  have Hs' := sorted Task Job nR nL Hn sR sL Hs jaR jaL Hja job_task tsk _ _ _ _ H1 Hd.
  apply: ct_imp; first exact (sub_nat_eq_correspondence _ _ _ _ (cs_list_size Job _ _ Hs') (cwb_add2 _ _ Hm)).
  apply: ct_forall_identity => elem.
  rewrite (getD Job _ _ Hs' elem _ _ (cta_succ_rel _ _ Hm)).
  exact (sub_nat_lt_correspondence _ _ _ _ (Hja _) (cwb_t2 _ _ _ _ H1 Hd)).
Qed.

Definition src_workload_bound_service_of_first_and_last_jobs (Task Job : eqType) : Prop :=
  ltac:(type_of_term (@WorkloadBound.workload_bound_service_of_first_and_last_jobs Task Job)).
Definition tgt_workload_bound_service_of_first_and_last_jobs (Task Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Analysis_Apa_WorkloadBound_WorkloadBound_workload_bound_service_of_first_and_last_jobs Task Job (ct_decidable_eq Task) (ct_decidable_eq Job))).
Theorem WorkloadBound_workload_bound_service_of_first_and_last_jobs_correspondence (Task Job : eqType) :
  PropSPropRel (src_workload_bound_service_of_first_and_last_jobs Task Job) (tgt_workload_bound_service_of_first_and_last_jobs Task Job).
Proof.
  unfold src_workload_bound_service_of_first_and_last_jobs, tgt_workload_bound_service_of_first_and_last_jobs.
  apply: cs_forall_par => jaR jaL Hja. apply: cs_forall_par => cR cL Hc.
  apply: ct_forall_identity => job_task.
  apply: cwb_forall_arr => aR aL Ha.
  apply: cs_forall_ncpus_sched => nR nL Hn sR sL Hs.
  apply: ct_imp; first exact (cf_Schedule_jobs_come_from_arrival_sequence Job nR nL Hn sR sL Hs aR aL Ha).
  apply: ct_imp; first exact (cf_Schedule_jobs_must_arrive_to_execute Job nR nL Hn sR sL Hs jaR jaL Hja).
  apply: ct_imp; first exact (cf_Schedule_completed_jobs_dont_execute Job nR nL Hn sR sL Hs cR cL Hc).
  apply: ct_imp; first exact (cf_Schedule_sequential_jobs Job nR nL Hn sR sL Hs).
  apply: ct_forall_identity => tsk.
  apply: ct_forall_nat => t1R t1L H1. apply: ct_forall_nat => dR dL Hd.
  apply: ct_forall_nat => RR RL HR.
  apply: ct_imp; first exact (cwb_rt_bound Task Job nR nL Hn sR sL Hs jaR jaL Hja cR cL Hc job_task aR aL Ha tsk _ _ _ _ _ _ H1 Hd HR).
  apply: ct_forall_nat => mR mL Hm.
  have Hs' := sorted Task Job nR nL Hn sR sL Hs jaR jaL Hja job_task tsk _ _ _ _ H1 Hd.
  apply: ct_imp; first exact (sub_nat_eq_correspondence _ _ _ _ (cs_list_size Job _ _ Hs') (cwb_add2 _ _ Hm)).
  apply: ct_forall_identity => elem.
  rewrite (getD Job _ _ Hs' elem _ _ (sub_nat_rel_canonical 0)) (getD Job _ _ Hs' elem _ _ (cta_succ_rel _ _ Hm)).
  exact (sub_nat_le_correspondence _ _ _ _
           (sub_add_correspondence _ _ _ _ (SD Job nR nL Hn sR sL Hs (nth elem _ 0) t1R t1L dR dL H1 Hd) (SD Job nR nL Hn sR sL Hs (nth elem _ mR.+1) t1R t1L dR dL H1 Hd))
           (sub_add_correspondence _ _ _ _ (ct_sub_rel _ _ _ _ (sub_add_correspondence _ _ _ _ (Hja _) HR) H1)
              (ct_sub_rel _ _ _ _ (cwb_t2 _ _ _ _ H1 Hd) (Hja _)))).
Qed.

Definition src_workload_bound_simpl_expression_with_first_and_last (Task Job : eqType) : Prop :=
  ltac:(type_of_term (@WorkloadBound.workload_bound_simpl_expression_with_first_and_last Task Job)).
Definition tgt_workload_bound_simpl_expression_with_first_and_last (Task Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Analysis_Apa_WorkloadBound_WorkloadBound_workload_bound_simpl_expression_with_first_and_last Task Job (ct_decidable_eq Task) (ct_decidable_eq Job))).
Theorem WorkloadBound_workload_bound_simpl_expression_with_first_and_last_correspondence (Task Job : eqType) :
  PropSPropRel (src_workload_bound_simpl_expression_with_first_and_last Task Job) (tgt_workload_bound_simpl_expression_with_first_and_last Task Job).
Proof.
  unfold src_workload_bound_simpl_expression_with_first_and_last, tgt_workload_bound_simpl_expression_with_first_and_last.
  apply: cs_forall_par => jaR jaL Hja. apply: cs_forall_par => cR cL Hc.
  apply: ct_forall_identity => job_task.
  apply: cwb_forall_arr => aR aL Ha.
  apply: cs_forall_ncpus_sched => nR nL Hn sR sL Hs.
  apply: ct_imp; first exact (cf_Schedule_jobs_come_from_arrival_sequence Job nR nL Hn sR sL Hs aR aL Ha).
  apply: ct_imp; first exact (cf_Schedule_jobs_must_arrive_to_execute Job nR nL Hn sR sL Hs jaR jaL Hja).
  apply: ct_imp; first exact (cf_Schedule_completed_jobs_dont_execute Job nR nL Hn sR sL Hs cR cL Hc).
  apply: ct_forall_identity => tsk.
  apply: ct_forall_nat => t1R t1L H1. apply: ct_forall_nat => dR dL Hd.
  apply: ct_forall_nat => RR RL HR.
  apply: ct_imp; first exact (cwb_rt_bound Task Job nR nL Hn sR sL Hs jaR jaL Hja cR cL Hc job_task aR aL Ha tsk _ _ _ _ _ _ H1 Hd HR).
  apply: ct_forall_nat => mR mL Hm.
  have Hs' := sorted Task Job nR nL Hn sR sL Hs jaR jaL Hja job_task tsk _ _ _ _ H1 Hd.
  apply: ct_imp; first exact (sub_nat_eq_correspondence _ _ _ _ (cs_list_size Job _ _ Hs') (cwb_add2 _ _ Hm)).
  apply: ct_forall_identity => elem.
  rewrite (getD Job _ _ Hs' elem _ _ (sub_nat_rel_canonical 0)) (getD Job _ _ Hs' elem _ _ (cta_succ_rel _ _ Hm)).
  exact (sub_nat_eq_correspondence _ _ _ _
           (sub_add_correspondence _ _ _ _ (ct_sub_rel _ _ _ _ (sub_add_correspondence _ _ _ _ (Hja _) HR) H1)
              (ct_sub_rel _ _ _ _ (cwb_t2 _ _ _ _ H1 Hd) (Hja _)))
           (ct_sub_rel _ _ _ _ (sub_add_correspondence _ _ _ _ Hd HR) (ct_sub_rel _ _ _ _ (Hja _) (Hja _)))).
Qed.

Definition src_workload_bound_service_of_middle_jobs (Task Job : eqType) : Prop :=
  forall task_cost task_deadline : Task -> Time.time,
    ltac:(type_of_term (@WorkloadBound.workload_bound_service_of_middle_jobs Task task_cost task_deadline Job)).
Definition tgt_workload_bound_service_of_middle_jobs (Task Job : eqType) : SProp :=
  forall task_cost task_deadline : Task -> Lean.Nat,
    ltac:(type_of_term (I.Prosa_Classic_Analysis_Apa_WorkloadBound_WorkloadBound_workload_bound_service_of_middle_jobs Task (ct_decidable_eq Task) task_cost task_deadline Job (ct_decidable_eq Job))).
Theorem WorkloadBound_workload_bound_service_of_middle_jobs_correspondence (Task Job : eqType) :
  PropSPropRel (src_workload_bound_service_of_middle_jobs Task Job) (tgt_workload_bound_service_of_middle_jobs Task Job).
Proof.
  unfold src_workload_bound_service_of_middle_jobs, tgt_workload_bound_service_of_middle_jobs.
  apply: cs_forall_par => task_costR task_costL Htask_cost.
  apply: cs_forall_par => task_deadlineR task_deadlineL Htask_deadline.
  apply: cs_forall_par => jaR jaL Hja. apply: cs_forall_par => cR cL Hc.
  apply: ct_forall_identity => job_task.
  apply: cs_forall_par => jdR jdL Hjd.
  apply: cwb_forall_arr => aR aL Ha.
  apply: ct_imp; first exact (cwb_valid_params Task Job task_costR task_costL Htask_cost task_deadlineR task_deadlineL Htask_deadline cR cL Hc jdR jdL Hjd job_task aR aL Ha).
  apply: cs_forall_ncpus_sched => nR nL Hn sR sL Hs.
  apply: ct_imp; first exact (cf_Schedule_jobs_come_from_arrival_sequence Job nR nL Hn sR sL Hs aR aL Ha).
  apply: ct_imp; first exact (cf_Schedule_completed_jobs_dont_execute Job nR nL Hn sR sL Hs cR cL Hc).
  apply: ct_forall_identity => tsk.
  apply: ct_forall_nat => t1R t1L H1. apply: ct_forall_nat => dR dL Hd.
  apply: ct_forall_nat => mR mL Hm.
  have Hs' := sorted Task Job nR nL Hn sR sL Hs jaR jaL Hja job_task tsk _ _ _ _ H1 Hd.
  apply: ct_imp; first exact (sub_nat_eq_correspondence _ _ _ _ (cs_list_size Job _ _ Hs') (cwb_add2 _ _ Hm)).
  apply: ct_forall_identity => elem.
  apply: sub_nat_le_correspondence; last exact (sub_mul_correspondence _ _ _ _ Hm (Htask_cost tsk)).
  apply: (cs_ico _ _ _ _ _ _ (sub_nat_rel_canonical 0) Hm) => iR iL Hi.
  rewrite (getD Job _ _ Hs' elem _ _ (cta_succ_rel _ _ Hi)). exact (SD Job nR nL Hn sR sL Hs (nth elem _ iR.+1) t1R t1L dR dL H1 Hd).
Qed.

Definition src_workload_bound_many_periods_in_between (Task Job : eqType) : Prop :=
  forall task_cost task_period task_deadline : Task -> Time.time,
    ltac:(type_of_term (@WorkloadBound.workload_bound_many_periods_in_between Task task_cost task_period task_deadline Job)).
Definition tgt_workload_bound_many_periods_in_between (Task Job : eqType) : SProp :=
  forall task_cost task_period task_deadline : Task -> Lean.Nat,
    ltac:(type_of_term (I.Prosa_Classic_Analysis_Apa_WorkloadBound_WorkloadBound_workload_bound_many_periods_in_between Task (ct_decidable_eq Task) task_cost task_period task_deadline Job (ct_decidable_eq Job))).
Theorem WorkloadBound_workload_bound_many_periods_in_between_correspondence (Task Job : eqType) :
  PropSPropRel (src_workload_bound_many_periods_in_between Task Job) (tgt_workload_bound_many_periods_in_between Task Job).
Proof.
  unfold src_workload_bound_many_periods_in_between, tgt_workload_bound_many_periods_in_between.
  apply: cs_forall_par => task_costR task_costL Htask_cost.
  apply: cs_forall_par => task_periodR task_periodL Htask_period.
  apply: cs_forall_par => task_deadlineR task_deadlineL Htask_deadline.
  apply: cs_forall_par => jaR jaL Hja.
  apply: ct_forall_identity => job_task.
  apply: cwb_forall_arr => aR aL Ha.
  apply: cs_forall_ncpus_sched => nR nL Hn sR sL Hs.
  apply: ct_imp; first exact (cf_Schedule_jobs_come_from_arrival_sequence Job nR nL Hn sR sL Hs aR aL Ha).
  apply: ct_imp; first exact (cwb_sporadic_task_model Task Job task_periodR task_periodL Htask_period jaR jaL Hja job_task aR aL Ha).
  apply: ct_forall_identity => tsk.
  apply: ct_imp; first exact (sub_nat_le_correspondence _ _ _ _ (Htask_deadline tsk) (Htask_period tsk)).
  apply: ct_forall_nat => t1R t1L H1. apply: ct_forall_nat => dR dL Hd. apply: ct_forall_nat => RR RL HR.
  apply: ct_imp; first exact (sub_nat_le_correspondence _ _ _ _ (Htask_cost tsk) HR).
  apply: ct_imp; first exact (sub_nat_le_correspondence _ _ _ _ HR (Htask_deadline tsk)).
  apply: ct_forall_nat => mR mL Hm.
  have Hs' := sorted Task Job nR nL Hn sR sL Hs jaR jaL Hja job_task tsk _ _ _ _ H1 Hd.
  apply: ct_imp; first exact (sub_nat_eq_correspondence _ _ _ _ (cs_list_size Job _ _ Hs') (cwb_add2 _ _ Hm)).
  apply: ct_forall_identity => elem.
  rewrite (getD Job _ _ Hs' elem _ _ (sub_nat_rel_canonical 0)) (getD Job _ _ Hs' elem _ _ (cta_succ_rel _ _ Hm)).
  exact (sub_nat_le_correspondence _ _ _ _ (sub_mul_correspondence _ _ _ _ (cta_succ_rel _ _ Hm) (Htask_period tsk))
           (ct_sub_rel _ _ _ _ (Hja _) (Hja _))).
Qed.

Definition src_workload_bound_n_k_covers_middle_jobs (Task Job : eqType) : Prop :=
  forall task_cost task_period task_deadline : Task -> Time.time,
    ltac:(type_of_term (@WorkloadBound.workload_bound_n_k_covers_middle_jobs Task task_cost task_period task_deadline Job)).
Definition tgt_workload_bound_n_k_covers_middle_jobs (Task Job : eqType) : SProp :=
  forall task_cost task_period task_deadline : Task -> Lean.Nat,
    ltac:(type_of_term (I.Prosa_Classic_Analysis_Apa_WorkloadBound_WorkloadBound_workload_bound_n_k_covers_middle_jobs Task (ct_decidable_eq Task) task_cost task_period task_deadline Job (ct_decidable_eq Job))).
Theorem WorkloadBound_workload_bound_n_k_covers_middle_jobs_correspondence (Task Job : eqType) :
  PropSPropRel (src_workload_bound_n_k_covers_middle_jobs Task Job) (tgt_workload_bound_n_k_covers_middle_jobs Task Job).
Proof.
  unfold src_workload_bound_n_k_covers_middle_jobs, tgt_workload_bound_n_k_covers_middle_jobs.
  apply: cs_forall_par => task_costR task_costL Htask_cost.
  apply: cs_forall_par => task_periodR task_periodL Htask_period.
  apply: cs_forall_par => task_deadlineR task_deadlineL Htask_deadline.
  apply: cs_forall_par => jaR jaL Hja. apply: cs_forall_par => cR cL Hc.
  apply: ct_forall_identity => job_task.
  apply: cwb_forall_arr => aR aL Ha.
  apply: cs_forall_ncpus_sched => nR nL Hn sR sL Hs.
  apply: ct_imp; first exact (cf_Schedule_jobs_come_from_arrival_sequence Job nR nL Hn sR sL Hs aR aL Ha).
  apply: ct_imp; first exact (cf_Schedule_jobs_must_arrive_to_execute Job nR nL Hn sR sL Hs jaR jaL Hja).
  apply: ct_imp; first exact (cf_Schedule_completed_jobs_dont_execute Job nR nL Hn sR sL Hs cR cL Hc).
  apply: ct_imp; first exact (cwb_sporadic_task_model Task Job task_periodR task_periodL Htask_period jaR jaL Hja job_task aR aL Ha).
  apply: ct_forall_identity => tsk.
  apply: ct_imp; first exact (cwb_valid_sporadic_task Task task_costR task_costL Htask_cost task_periodR task_periodL Htask_period task_deadlineR task_deadlineL Htask_deadline tsk).
  apply: ct_imp; first exact (sub_nat_le_correspondence _ _ _ _ (Htask_deadline tsk) (Htask_period tsk)).
  apply: ct_forall_nat => t1R t1L H1. apply: ct_forall_nat => dR dL Hd.
  apply: ct_forall_nat => RR RL HR.
  apply: ct_imp; first exact (cwb_rt_bound Task Job nR nL Hn sR sL Hs jaR jaL Hja cR cL Hc job_task aR aL Ha tsk _ _ _ _ _ _ H1 Hd HR).
  apply: ct_imp; first exact (sub_nat_le_correspondence _ _ _ _ (Htask_cost tsk) HR).
  apply: ct_imp; first exact (sub_nat_le_correspondence _ _ _ _ HR (Htask_deadline tsk)).
  apply: ct_forall_nat => mR mL Hm.
  have Hs' := sorted Task Job nR nL Hn sR sL Hs jaR jaL Hja job_task tsk _ _ _ _ H1 Hd.
  apply: ct_imp; first exact (sub_nat_eq_correspondence _ _ _ _ (cs_list_size Job _ _ Hs') (cwb_add2 _ _ Hm)).
  apply: ct_forall_identity => elem.
  exact (sub_nat_le_correspondence _ _ _ _ Hm (WorkloadBound_max_jobs_correspondence Task task_costR task_costL Htask_cost task_periodR task_periodL Htask_period tsk _ _ HR _ _ Hd)).
Qed.

Definition src_workload_bound_n_k_equals_num_mid_jobs (Task Job : eqType) : Prop :=
  forall task_cost task_period task_deadline : Task -> Time.time,
    ltac:(type_of_term (@WorkloadBound.workload_bound_n_k_equals_num_mid_jobs Task task_cost task_period task_deadline Job)).
Definition tgt_workload_bound_n_k_equals_num_mid_jobs (Task Job : eqType) : SProp :=
  forall task_cost task_period task_deadline : Task -> Lean.Nat,
    ltac:(type_of_term (I.Prosa_Classic_Analysis_Apa_WorkloadBound_WorkloadBound_workload_bound_n_k_equals_num_mid_jobs Task (ct_decidable_eq Task) task_cost task_period task_deadline Job (ct_decidable_eq Job))).
Theorem WorkloadBound_workload_bound_n_k_equals_num_mid_jobs_correspondence (Task Job : eqType) :
  PropSPropRel (src_workload_bound_n_k_equals_num_mid_jobs Task Job) (tgt_workload_bound_n_k_equals_num_mid_jobs Task Job).
Proof.
  unfold src_workload_bound_n_k_equals_num_mid_jobs, tgt_workload_bound_n_k_equals_num_mid_jobs.
  apply: cs_forall_par => task_costR task_costL Htask_cost.
  apply: cs_forall_par => task_periodR task_periodL Htask_period.
  apply: cs_forall_par => task_deadlineR task_deadlineL Htask_deadline.
  apply: cs_forall_par => jaR jaL Hja. apply: cs_forall_par => cR cL Hc.
  apply: ct_forall_identity => job_task.
  apply: cs_forall_par => jdR jdL Hjd.
  apply: cwb_forall_arr => aR aL Ha.
  apply: ct_imp; first exact (cwb_valid_params Task Job task_costR task_costL Htask_cost task_deadlineR task_deadlineL Htask_deadline cR cL Hc jdR jdL Hjd job_task aR aL Ha).
  apply: cs_forall_ncpus_sched => nR nL Hn sR sL Hs.
  apply: ct_imp; first exact (cf_Schedule_jobs_come_from_arrival_sequence Job nR nL Hn sR sL Hs aR aL Ha).
  apply: ct_imp; first exact (cf_Schedule_jobs_must_arrive_to_execute Job nR nL Hn sR sL Hs jaR jaL Hja).
  apply: ct_imp; first exact (cf_Schedule_completed_jobs_dont_execute Job nR nL Hn sR sL Hs cR cL Hc).
  apply: ct_imp; first exact (cf_Schedule_sequential_jobs Job nR nL Hn sR sL Hs).
  apply: ct_imp; first exact (cwb_sporadic_task_model Task Job task_periodR task_periodL Htask_period jaR jaL Hja job_task aR aL Ha).
  apply: ct_forall_identity => tsk.
  apply: ct_imp; first exact (cwb_valid_sporadic_task Task task_costR task_costL Htask_cost task_periodR task_periodL Htask_period task_deadlineR task_deadlineL Htask_deadline tsk).
  apply: ct_imp; first exact (sub_nat_le_correspondence _ _ _ _ (Htask_deadline tsk) (Htask_period tsk)).
  apply: ct_forall_nat => t1R t1L H1. apply: ct_forall_nat => dR dL Hd.
  apply: ct_forall_nat => RR RL HR.
  apply: ct_imp; first exact (cwb_rt_bound Task Job nR nL Hn sR sL Hs jaR jaL Hja cR cL Hc job_task aR aL Ha tsk _ _ _ _ _ _ H1 Hd HR).
  apply: ct_imp; first exact (sub_nat_le_correspondence _ _ _ _ (Htask_cost tsk) HR).
  apply: ct_imp; first exact (sub_nat_le_correspondence _ _ _ _ HR (Htask_deadline tsk)).
  apply: ct_forall_nat => mR mL Hm.
  have Hs' := sorted Task Job nR nL Hn sR sL Hs jaR jaL Hja job_task tsk _ _ _ _ H1 Hd.
  apply: ct_imp; first exact (sub_nat_eq_correspondence _ _ _ _ (cs_list_size Job _ _ Hs') (cwb_add2 _ _ Hm)).
  apply: ct_forall_identity => elem.
  apply: ct_imp; first exact (sub_nat_eq_correspondence _ _ _ _ Hm (WorkloadBound_max_jobs_correspondence Task task_costR task_costL Htask_cost task_periodR task_periodL Htask_period tsk _ _ HR _ _ Hd)).
  rewrite (getD Job _ _ Hs' elem _ _ (sub_nat_rel_canonical 0)) (getD Job _ _ Hs' elem _ _ (cta_succ_rel _ _ Hm)).
  apply: sub_nat_le_correspondence; last exact (WorkloadBound_W_correspondence Task task_costR task_costL Htask_cost task_periodR task_periodL Htask_period tsk _ _ HR _ _ Hd).
  apply: sub_add_correspondence; first exact (sub_add_correspondence _ _ _ _ (SD Job nR nL Hn sR sL Hs (nth elem _ mR.+1) t1R t1L dR dL H1 Hd) (SD Job nR nL Hn sR sL Hs (nth elem _ 0) t1R t1L dR dL H1 Hd)).
  apply: (cs_ico _ _ _ _ _ _ (sub_nat_rel_canonical 0) Hm) => iR iL Hi.
  rewrite (getD Job _ _ Hs' elem _ _ (cta_succ_rel _ _ Hi)). exact (SD Job nR nL Hn sR sL Hs (nth elem _ iR.+1) t1R t1L dR dL H1 Hd).
Qed.

Definition src_workload_bound_n_k_equals_num_mid_jobs_plus_1 (Task Job : eqType) : Prop :=
  forall task_cost task_period task_deadline : Task -> Time.time,
    ltac:(type_of_term (@WorkloadBound.workload_bound_n_k_equals_num_mid_jobs_plus_1 Task task_cost task_period task_deadline Job)).
Definition tgt_workload_bound_n_k_equals_num_mid_jobs_plus_1 (Task Job : eqType) : SProp :=
  forall task_cost task_period task_deadline : Task -> Lean.Nat,
    ltac:(type_of_term (I.Prosa_Classic_Analysis_Apa_WorkloadBound_WorkloadBound_workload_bound_n_k_equals_num_mid_jobs_plus_1 Task (ct_decidable_eq Task) task_cost task_period task_deadline Job (ct_decidable_eq Job))).
Theorem WorkloadBound_workload_bound_n_k_equals_num_mid_jobs_plus_1_correspondence (Task Job : eqType) :
  PropSPropRel (src_workload_bound_n_k_equals_num_mid_jobs_plus_1 Task Job) (tgt_workload_bound_n_k_equals_num_mid_jobs_plus_1 Task Job).
Proof.
  unfold src_workload_bound_n_k_equals_num_mid_jobs_plus_1, tgt_workload_bound_n_k_equals_num_mid_jobs_plus_1.
  apply: cs_forall_par => task_costR task_costL Htask_cost.
  apply: cs_forall_par => task_periodR task_periodL Htask_period.
  apply: cs_forall_par => task_deadlineR task_deadlineL Htask_deadline.
  apply: cs_forall_par => jaR jaL Hja. apply: cs_forall_par => cR cL Hc.
  apply: ct_forall_identity => job_task.
  apply: cs_forall_par => jdR jdL Hjd.
  apply: cwb_forall_arr => aR aL Ha.
  apply: ct_imp; first exact (cwb_valid_params Task Job task_costR task_costL Htask_cost task_deadlineR task_deadlineL Htask_deadline cR cL Hc jdR jdL Hjd job_task aR aL Ha).
  apply: cs_forall_ncpus_sched => nR nL Hn sR sL Hs.
  apply: ct_imp; first exact (cf_Schedule_jobs_come_from_arrival_sequence Job nR nL Hn sR sL Hs aR aL Ha).
  apply: ct_imp; first exact (cf_Schedule_jobs_must_arrive_to_execute Job nR nL Hn sR sL Hs jaR jaL Hja).
  apply: ct_imp; first exact (cf_Schedule_completed_jobs_dont_execute Job nR nL Hn sR sL Hs cR cL Hc).
  apply: ct_imp; first exact (cf_Schedule_sequential_jobs Job nR nL Hn sR sL Hs).
  apply: ct_imp; first exact (cwb_sporadic_task_model Task Job task_periodR task_periodL Htask_period jaR jaL Hja job_task aR aL Ha).
  apply: ct_forall_identity => tsk.
  apply: ct_imp; first exact (sub_nat_le_correspondence _ _ _ _ (Htask_deadline tsk) (Htask_period tsk)).
  apply: ct_forall_nat => t1R t1L H1. apply: ct_forall_nat => dR dL Hd.
  apply: ct_forall_nat => RR RL HR.
  apply: ct_imp; first exact (cwb_rt_bound Task Job nR nL Hn sR sL Hs jaR jaL Hja cR cL Hc job_task aR aL Ha tsk _ _ _ _ _ _ H1 Hd HR).
  apply: ct_imp; first exact (sub_nat_le_correspondence _ _ _ _ (Htask_cost tsk) HR).
  apply: ct_imp; first exact (sub_nat_le_correspondence _ _ _ _ HR (Htask_deadline tsk)).
  apply: ct_forall_nat => mR mL Hm.
  have Hs' := sorted Task Job nR nL Hn sR sL Hs jaR jaL Hja job_task tsk _ _ _ _ H1 Hd.
  apply: ct_imp; first exact (sub_nat_eq_correspondence _ _ _ _ (cs_list_size Job _ _ Hs') (cwb_add2 _ _ Hm)).
  apply: ct_forall_identity => elem.
  apply: ct_imp; first exact (sub_nat_eq_correspondence _ _ _ _ (cta_succ_rel _ _ Hm) (WorkloadBound_max_jobs_correspondence Task task_costR task_costL Htask_cost task_periodR task_periodL Htask_period tsk _ _ HR _ _ Hd)).
  rewrite (getD Job _ _ Hs' elem _ _ (sub_nat_rel_canonical 0)) (getD Job _ _ Hs' elem _ _ (cta_succ_rel _ _ Hm)).
  apply: sub_nat_le_correspondence; last exact (WorkloadBound_W_correspondence Task task_costR task_costL Htask_cost task_periodR task_periodL Htask_period tsk _ _ HR _ _ Hd).
  apply: sub_add_correspondence; first exact (sub_add_correspondence _ _ _ _ (SD Job nR nL Hn sR sL Hs (nth elem _ mR.+1) t1R t1L dR dL H1 Hd) (SD Job nR nL Hn sR sL Hs (nth elem _ 0) t1R t1L dR dL H1 Hd)).
  apply: (cs_ico _ _ _ _ _ _ (sub_nat_rel_canonical 0) Hm) => iR iL Hi.
  rewrite (getD Job _ _ Hs' elem _ _ (cta_succ_rel _ _ Hi)). exact (SD Job nR nL Hn sR sL Hs (nth elem _ iR.+1) t1R t1L dR dL H1 Hd).
Qed.

Definition src_workload_bounded_by_W (Task Job : eqType) : Prop :=
  forall task_cost task_period task_deadline : Task -> Time.time,
    ltac:(type_of_term (@WorkloadBound.workload_bounded_by_W Task task_cost task_period task_deadline Job)).
Definition tgt_workload_bounded_by_W (Task Job : eqType) : SProp :=
  forall task_cost task_period task_deadline : Task -> Lean.Nat,
    ltac:(type_of_term (I.Prosa_Classic_Analysis_Apa_WorkloadBound_WorkloadBound_workload_bounded_by_W Task (ct_decidable_eq Task) task_cost task_period task_deadline Job (ct_decidable_eq Job))).
Theorem WorkloadBound_workload_bounded_by_W_correspondence (Task Job : eqType) :
  PropSPropRel (src_workload_bounded_by_W Task Job) (tgt_workload_bounded_by_W Task Job).
Proof.
  unfold src_workload_bounded_by_W, tgt_workload_bounded_by_W.
  apply: cs_forall_par => task_costR task_costL Htask_cost.
  apply: cs_forall_par => task_periodR task_periodL Htask_period.
  apply: cs_forall_par => task_deadlineR task_deadlineL Htask_deadline.
  apply: cs_forall_par => jaR jaL Hja. apply: cs_forall_par => cR cL Hc.
  apply: ct_forall_identity => job_task.
  apply: cs_forall_par => jdR jdL Hjd.
  apply: cwb_forall_arr => aR aL Ha.
  apply: ct_imp; first exact (cwb_valid_params Task Job task_costR task_costL Htask_cost task_deadlineR task_deadlineL Htask_deadline cR cL Hc jdR jdL Hjd job_task aR aL Ha).
  apply: cs_forall_ncpus_sched => nR nL Hn sR sL Hs.
  apply: ct_imp; first exact (cf_Schedule_jobs_come_from_arrival_sequence Job nR nL Hn sR sL Hs aR aL Ha).
  apply: ct_imp; first exact (cf_Schedule_jobs_must_arrive_to_execute Job nR nL Hn sR sL Hs jaR jaL Hja).
  apply: ct_imp; first exact (cf_Schedule_completed_jobs_dont_execute Job nR nL Hn sR sL Hs cR cL Hc).
  apply: ct_imp; first exact (cf_Schedule_sequential_jobs Job nR nL Hn sR sL Hs).
  apply: ct_imp; first exact (cwb_sporadic_task_model Task Job task_periodR task_periodL Htask_period jaR jaL Hja job_task aR aL Ha).
  apply: ct_forall_identity => tsk.
  apply: ct_imp; first exact (cwb_valid_sporadic_task Task task_costR task_costL Htask_cost task_periodR task_periodL Htask_period task_deadlineR task_deadlineL Htask_deadline tsk).
  apply: ct_imp; first exact (sub_nat_le_correspondence _ _ _ _ (Htask_deadline tsk) (Htask_period tsk)).
  apply: ct_forall_nat => t1R t1L H1. apply: ct_forall_nat => dR dL Hd.
  apply: ct_forall_nat => RR RL HR.
  apply: ct_imp; first exact (cwb_rt_bound Task Job nR nL Hn sR sL Hs jaR jaL Hja cR cL Hc job_task aR aL Ha tsk _ _ _ _ _ _ H1 Hd HR).
  apply: ct_imp; first exact (sub_nat_le_correspondence _ _ _ _ (Htask_cost tsk) HR).
  apply: ct_imp; first exact (sub_nat_le_correspondence _ _ _ _ HR (Htask_deadline tsk)).
  exact (sub_nat_le_correspondence _ _ _ _ (cai_workload Task Job nR nL Hn sR sL Hs job_task tsk _ _ _ _ H1 (cwb_t2 _ _ _ _ H1 Hd))
           (WorkloadBound_W_correspondence Task task_costR task_costL Htask_cost task_periodR task_periodL Htask_period tsk _ _ HR _ _ Hd)).
Qed.
