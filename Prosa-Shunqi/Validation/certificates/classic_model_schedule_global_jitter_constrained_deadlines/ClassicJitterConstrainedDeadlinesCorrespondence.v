From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq fintype bigop.
From prosa Require Import classic.model.time classic.util.notation classic.model.arrival.basic.arrival_sequence classic.model.arrival.basic.task classic.model.arrival.basic.job classic.model.arrival.basic.task_arrival classic.model.schedule.global.basic.schedule util.seqset classic.model.priority classic.model.schedule.global.jitter.job classic.model.schedule.global.jitter.schedule classic.model.schedule.global.jitter.interference classic.model.schedule.global.jitter.platform classic.model.schedule.global.jitter.constrained_deadlines.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedClassicJitterConstrainedDeadlines.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence ClassicJitterConstrainedDeadlinesBase ClassicJitterConstrainedDeadlinesList ClassicJitterConstrainedDeadlinesOrd.



Module I := ImportedClassicJitterConstrainedDeadlines.
Local Open Scope nat_scope.

(** Certificates for [classic/model/schedule/global/jitter/constrained_deadlines.v] (ProsaBuddy classic, commit f692cb7).

    Inputs, relations and computation as in the accepted classic global basic constrained_deadlines certificate (re-stated
    below for this export), with job jitters pointwise through [SubNatRel] and the jitter-aware [pending], [backlogged],
    [task_is_scheduled], [jobs_execute_after_jitter], [work_conserving] and [respects_FP_policy] of the accepted classic
    global jitter schedule/platform certificates: eqTypes identified with their canonical Lean [DecidableEq] instances;
    times and [num_cpus] by [SubNatRel]; processors by their values; schedules pointwise ([CsSchedRel]); job and task
    parameters pointwise; arrival sequences pointwise on related times; FP policies pointwise; task sets through their
    sequences; all with two-way totals.

    Statements: the source side is the exact elaborated type of the pinned lemma (via [type of]; the source proof is not
    used).  For the lemmas whose binder lists put task parameters before the job type, the job type is fixed as an
    [eqType] with its canonical Lean instance and the task parameters stay universally quantified on both sides. *)

Ltac type_of_term t := let T := type of t in exact T.
Notation cid := (fun z => z).

(* ------------------------------------------------------------------ *)
(** * Helpers (re-bound to this export from the accepted classic certificates) *)

(** Base definitions (as in the accepted classic base library), provided here when this export's library lacks them. *)

(* ------------------------------------------------------------------ *)
(** * Generic helpers *)

Lemma ccj_forall_cover (A B : Type) (Rel : A -> B -> SProp) (toB : A -> B) (toA : B -> A)
    (HB : forall a, Rel a (toB a)) (HA : forall b, Rel (toA b) b) (PR : A -> Prop) (PL : B -> SProp) :
  (forall a b, Rel a b -> PropSPropRel (PR a) (PL b)) -> PropSPropRel (forall a, PR a) (forall b, PL b).
Proof.
  intro H. apply prop_sprop_rel_intro.
  - intros HR b. exact (prop_to_sprop _ _ (H _ _ (HA b)) (HR _)).
  - intro HL. apply strictly_inhabits. intro a. exact (sprop_to_prop _ _ (H _ _ (HB a)) (HL _)).
Qed.

Lemma ccj_mem (T : eqType) x s sL : ClListRel cid s sL ->
  PropSPropRel (x \in s) (I.Membership_mem T (I.List T) (I.List_instMembership T) sL x).
Proof. exact (cl_mem_rel_list T T cid cid (fun _ => Logic.eq_refl _) x s sL). Qed.

Lemma ccj_uniq (T : eqType) s sL : ClListRel cid s sL -> PropSPropRel (uniq s) (I.List_Nodup T sL).
Proof. exact (cl_uniq_rel_list T T cid cid (fun _ => Logic.eq_refl _) (fun _ => Logic.eq_refl _) s sL). Qed.

Lemma ccj_list_size (T : Type) s sL : ClListRel (B := T) cid s sL -> SubNatRel (size s) (I.List_length T sL).
Proof. intro H. destruct H. exact (cl_size cid s). Qed.

Lemma ccj_lean_eq_logic (A : Type) (x y : A) : Lean.eq x y -> Logic.eq x y.
Proof. exact (imported_eq_to_coq_eq x y). Qed.

(** Transport along the target equality (definitional UIP), into relevant and SProp-valued families. *)
Definition ccj_tr {A : Type} {x y : A} (E : Lean.eq x y) (P : A -> Type) (h : P x) : P y :=
  match E in Lean.eq _ z return P z with Lean.eq_refl => h end.
Definition ccj_trs {A : Type} {x y : A} (E : Lean.eq x y) (P : A -> SProp) (h : P x) : P y :=
  match E in Lean.eq _ z return P z with Lean.eq_refl => h end.

(** Options: [cl_opt] is injective and [x == Some j] is [cl_opt x = some j]. *)
Lemma ccj_opt_inj (A : Type) (o1 o2 : option A) : Logic.eq (cl_opt o1) (cl_opt o2) -> Logic.eq o1 o2.
Proof. intro E. by rewrite -(cl_unopt_opt o1) -(cl_unopt_opt o2) E. Qed.

Lemma ccj_opt_eq_rel (A : Type) (o1 o2 : option A) :
  PropSPropRel (Logic.eq o1 o2) (Lean.eq (cl_opt o1) (cl_opt o2)).
Proof.
  apply prop_sprop_rel_intro.
  - intro E. rewrite E. exact (@Lean.eq_refl _ _).
  - intro E. apply strictly_inhabits. exact (ccj_opt_inj A o1 o2 (imported_eq_to_coq_eq _ _ E)).
Qed.

Lemma ccj_opt_eqb_rel (A : eqType) (o1 o2 : option A) :
  PropSPropRel (is_true (o1 == o2)) (Lean.eq (cl_opt o1) (cl_opt o2)).
Proof.
  apply prop_sprop_rel_intro.
  - move=> /eqP E. rewrite E. exact (@Lean.eq_refl _ _).
  - intro E. apply strictly_inhabits. apply/eqP. exact (ccj_opt_inj A o1 o2 (imported_eq_to_coq_eq _ _ E)).
Qed.

(* ------------------------------------------------------------------ *)
(** * Half-open sums and concatenations over [nat] (as in the accepted sum / arrival_sequence certificates) *)

Fixpoint ccj_natl (s : seq nat) : I.List_inst1 Lean.Nat :=
  match s with [::] => I.List_nil_inst1 _ | x :: s' => I.List_cons_inst1 _ (sub_nat_to_imported x) (ccj_natl s') end.

Lemma ccj_iota_range : forall n s,
  Logic.eq (I.List_range' (sub_nat_to_imported s) (sub_nat_to_imported n) (Lean.Nat_succ Lean.Nat_zero)) (ccj_natl (iota s n)).
Proof.
  elim => [|n IH] s; first reflexivity.
  change (Logic.eq (I.List_cons_inst1 _ (sub_nat_to_imported s)
      (I.List_range' (sub_nat_to_imported (S s)) (sub_nat_to_imported n) (Lean.Nat_succ Lean.Nat_zero)))
    (I.List_cons_inst1 _ (sub_nat_to_imported s) (ccj_natl (iota (S s) n)))).
  by rewrite IH.
Qed.

Lemma ccj_foldr_add (f : Lean.Nat -> Lean.Nat) (g : nat -> nat) (Hf : forall k, Logic.eq (f (sub_nat_to_imported k)) (sub_nat_to_imported (g k))) :
  forall s, Logic.eq (I.List_foldr_inst3 Lean.Nat Lean.Nat Lean.Nat_add Lean.Nat_zero (I.List_map_inst3 Lean.Nat Lean.Nat f (ccj_natl s)))
                     (sub_nat_to_imported (foldr addn 0 (map g s))).
Proof.
  elim => [|k s IH] //=.
  change (Logic.eq (Lean.Nat_add (f (sub_nat_to_imported k))
            (I.List_foldr_inst3 Lean.Nat Lean.Nat Lean.Nat_add Lean.Nat_zero (I.List_map_inst3 Lean.Nat Lean.Nat f (ccj_natl s))))
         (sub_nat_to_imported (g k + foldr addn 0 (map g s)))).
  rewrite IH Hf. exact (imported_eq_to_coq_eq _ _ (sub_add_canonical _ _)).
Qed.

Lemma ccj_big_fold (xs : seq nat) (F : nat -> nat) : Logic.eq (\sum_(i <- xs) F i) (foldr addn 0 (map F xs)).
Proof. elim: xs => [|x xs IH]; first by rewrite big_nil. by rewrite big_cons IH. Qed.

Definition CcjFunRel (FR : nat -> nat) (FL : Lean.Nat -> Lean.Nat) : SProp :=
  forall kR kL, SubNatRel kR kL -> SubNatRel (FR kR) (FL kL).

Lemma ccj_fun_canonical FR FL (HF : CcjFunRel FR FL) k : Logic.eq (FL (sub_nat_to_imported k)) (sub_nat_to_imported (FR k)).
Proof. exact (co_nat_logic _ _ (HF _ _ (sub_nat_rel_canonical k))). Qed.

Lemma ccj_ico mR mL nR nL FR FL (Hm : SubNatRel mR mL) (Hn : SubNatRel nR nL) (HF : CcjFunRel FR FL) :
  SubNatRel (\sum_(mR <= i < nR) FR i)
    (I.List_foldr_inst3 Lean.Nat Lean.Nat Lean.Nat_add Lean.Nat_zero
       (I.List_map_inst3 Lean.Nat Lean.Nat FL (I.List_range' mL (I.Nat_sub nL mL) (Lean.Nat_succ Lean.Nat_zero)))).
Proof.
  rewrite (co_nat_logic _ _ Hm) (co_nat_logic _ _ Hn).
  have -> : Logic.eq (I.Nat_sub (sub_nat_to_imported nR) (sub_nat_to_imported mR)) (sub_nat_to_imported (nR - mR))
    := ct_sub_canonical nR mR.
  rewrite ccj_iota_range.
  apply: coq_eq_to_imported_eq. apply: Logic.eq_sym. rewrite (ccj_foldr_add FL FR (ccj_fun_canonical FR FL HF)).
  by rewrite ccj_big_fold.
Qed.

Lemma ccj_map_natl {B : Type} (f : Lean.Nat -> B) : forall s,
  Logic.eq (I.List_map_inst1 Lean.Nat B f (ccj_natl s)) (cl_map (fun k => f (sub_nat_to_imported k)) s).
Proof.
  elim => [|k s IH] //=.
  change (Logic.eq (I.List_cons B (f (sub_nat_to_imported k)) (I.List_map_inst1 Lean.Nat B f (ccj_natl s)))
                   (I.List_cons B (f (sub_nat_to_imported k)) (cl_map (fun k => f (sub_nat_to_imported k)) s))).
  by rewrite IH.
Qed.

Lemma ccj_big_seq {A : Type} (F : nat -> seq A) : forall s : seq nat,
  Logic.eq (\big[cat/[::]]_(i <- s) F i) (flatten (map F s)).
Proof. elim => [|x s IH]; first by rewrite big_nil. by rewrite big_cons IH. Qed.

Definition CcjNatFamRel (A : Type) (fR : nat -> seq A) (fL : Lean.Nat -> I.List A) : SProp :=
  forall nR nL, SubNatRel nR nL -> ClListRel cid (fR nR) (fL nL).

Lemma ccj_bigcat_nat_rel (A : Type) fR fL (Hf : CcjNatFamRel A fR fL) mR mL nR nL :
  SubNatRel mR mL -> SubNatRel nR nL ->
  ClListRel cid (\big[cat/[::]]_(mR <= t < nR) fR t) (I.Prosa_Util_Notation_bigCat A mL nL fL).
Proof.
  intros Hm Hn. have E1 := co_nat_logic _ _ Hm. have E2 := co_nat_logic _ _ Hn. subst mL nL.
  apply: coq_eq_to_imported_eq. apply: Logic.eq_sym.
  rewrite (imported_eq_to_coq_eq _ _ (I.Prosa_Validation_ClassicJitterConstrainedDeadlinesInterface_bigCat_range'
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
  rewrite ccj_big_seq /index_iota Hi -map_comp.
  reflexivity.
Qed.

Lemma ccj_notin_target (T : eqType) x s : Logic.eq (x \in s) false ->
  I.Not (I.Membership_mem T (I.List T) (I.List_instMembership T) (cl_map cid s) x).
Proof.
  intros Hx H. apply: ct_coq_false_to_target.
  have Hm := sprop_to_prop _ _ (ccj_mem T x s _ (cl_lean_eq _ _ _ (Logic.eq_refl _))) H.
  rewrite Hx in Hm. discriminate.
Qed.

(** [undup] against Mathlib's [List.dedup] (step equations exported with their proofs). *)
Lemma ccj_undup_rel (T : eqType) : forall s sL, ClListRel cid s sL ->
  ClListRel cid (undup s) (I.List_dedup T (ct_decidable_eq T) sL).
Proof.
  intros s sL Hs. have E := cl_list_logic _ _ _ Hs. subst sL. apply: coq_eq_to_imported_eq. clear Hs.
  elim: s => [|x s IH].
  - exact (Logic.eq_sym (imported_eq_to_coq_eq _ _ (I.Prosa_Validation_ClassicJitterConstrainedDeadlinesInterface_dedup_nil T (ct_decidable_eq T)))).
  - change (Logic.eq (cl_map cid (if x \in s then undup s else x :: undup s))
      (I.List_dedup T (ct_decidable_eq T) (I.List_cons T x (cl_map cid s)))).
    case Hx: (x \in s).
    + rewrite (imported_eq_to_coq_eq _ _ (I.Prosa_Validation_ClassicJitterConstrainedDeadlinesInterface_dedup_cons_mem
                 T (ct_decidable_eq T) x (cl_map cid s)
                 (prop_to_sprop _ _ (ccj_mem T x s _ (cl_lean_eq _ _ _ (Logic.eq_refl _))) Hx))).
      exact IH.
    + rewrite (imported_eq_to_coq_eq _ _ (I.Prosa_Validation_ClassicJitterConstrainedDeadlinesInterface_dedup_cons_not_mem
                 T (ct_decidable_eq T) x (cl_map cid s) (ccj_notin_target T x s Hx))).
      change (Logic.eq (I.List_cons T x (cl_map cid (undup s))) (I.List_cons T x (I.List_dedup T (ct_decidable_eq T) (cl_map cid s)))).
      by rewrite IH.
Qed.

(* ------------------------------------------------------------------ *)
(** * Schedules, arrival sequences, parameters *)

Definition CcjParRel (T : Type) (pR : T -> nat) (pL : T -> Lean.Nat) : SProp := forall x, SubNatRel (pR x) (pL x).

Lemma ccj_forall_par (T : Type) (PR : (T -> nat) -> Prop) (PL : (T -> Lean.Nat) -> SProp) :
  (forall pR pL, CcjParRel T pR pL -> PropSPropRel (PR pR) (PL pL)) -> PropSPropRel (forall p, PR p) (forall p, PL p).
Proof.
  exact (ccj_forall_cover _ _ (CcjParRel T) (fun pR j => sub_nat_to_imported (pR j)) (fun pL j => sub_nat_to_rocq (pL j))
           (fun pR j => sub_nat_rel_canonical (pR j)) (fun pL j => sub_nat_rel_surjective (pL j)) PR PL).
Qed.

Section Sched.
Variables (Job : eqType) (nR : nat) (nL : Lean.Nat).
Hypothesis Hn : SubNatRel nR nL.
Notation dJ := (ct_decidable_eq Job).
Notation LSched := (I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_schedule Job dJ nL).

Definition CcjSchedRel (sR : Schedule.schedule Job nR) (sL : LSched) : SProp :=
  forall oR oL, CoOrdRel nR nL oR oL -> forall tR tL, SubNatRel tR tL -> Lean.eq (cl_opt (sR oR tR)) (sL oL tL).

Definition ccj_sched_to_target (sR : Schedule.schedule Job nR) : LSched :=
  fun oL tL => cl_opt (sR (co_fin_to_ord nR nL Hn oL) (sub_nat_to_rocq tL)).

Definition ccj_sched_to_source (sL : LSched) : Schedule.schedule Job nR :=
  fun oR tR => cl_unopt (sL (co_ord_to_fin nR nL Hn oR) (sub_nat_to_imported tR)).

Lemma ccj_sched_canonical sR : CcjSchedRel sR (ccj_sched_to_target sR).
Proof.
  intros oR oL Ho tR tL Ht. apply: coq_eq_to_imported_eq. rewrite /ccj_sched_to_target (co_nat_input _ _ Ht).
  by rewrite (co_ord_eq _ _ _ _ _ Ho (co_ord_surjective nR nL Hn oL)).
Qed.

Lemma ccj_sched_surjective sL : CcjSchedRel (ccj_sched_to_source sL) sL.
Proof.
  intros oR oL Ho tR tL Ht. apply: coq_eq_to_imported_eq. rewrite /ccj_sched_to_source cl_opt_unopt.
  rewrite (co_nat_logic _ _ Ht). by rewrite (co_fin_rel_eq _ _ _ _ _ (co_ord_canonical nR nL Hn oR) Ho).
Qed.

Lemma ccj_forall_sched (PR : Schedule.schedule Job nR -> Prop) (PL : LSched -> SProp) :
  (forall sR sL, CcjSchedRel sR sL -> PropSPropRel (PR sR) (PL sL)) -> PropSPropRel (forall s, PR s) (forall s, PL s).
Proof. exact (ccj_forall_cover _ _ CcjSchedRel ccj_sched_to_target ccj_sched_to_source ccj_sched_canonical ccj_sched_surjective PR PL). Qed.

End Sched.

Section Arr.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).
Notation LArr := (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrival_sequence Job dJ).

Definition CcjArrRel (aR : ArrivalSequence.arrival_sequence Job) (aL : LArr) : SProp :=
  forall tR tL, SubNatRel tR tL -> ClListRel cid (aR tR) (aL tL).

Definition ccj_arr_to_target (aR : ArrivalSequence.arrival_sequence Job) : LArr :=
  fun tL => cl_map cid (aR (sub_nat_to_rocq tL)).

Definition ccj_arr_to_source (aL : LArr) : ArrivalSequence.arrival_sequence Job :=
  fun tR => cl_unmap cid (aL (sub_nat_to_imported tR)).

Lemma ccj_arr_canonical aR : CcjArrRel aR (ccj_arr_to_target aR).
Proof.
  intros tR tL Ht. have E := co_nat_logic _ _ Ht. subst tL.
  apply: coq_eq_to_imported_eq. rewrite /ccj_arr_to_target sub_nat_rocq_roundtrip. reflexivity.
Qed.

Lemma ccj_arr_surjective aL : CcjArrRel (ccj_arr_to_source aL) aL.
Proof.
  intros tR tL Ht. have E := co_nat_logic _ _ Ht. subst tL.
  apply: coq_eq_to_imported_eq. exact (cl_map_unmap cid cid (fun _ => Logic.eq_refl _) _).
Qed.

Lemma ccj_arrives_in aR aL (Ha : CcjArrRel aR aL) j :
  PropSPropRel (ArrivalSequence.arrives_in aR j)
    (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrives_in Job dJ aL j).
Proof. apply: ct_exists_nat => tR tL Ht. exact (ccj_mem Job j _ _ (Ha tR tL Ht)). Qed.

End Arr.

(* ------------------------------------------------------------------ *)
(** * Definitions *)

Section Defs.
Variables (Job : eqType) (nR : nat) (nL : Lean.Nat).
Hypothesis Hn : SubNatRel nR nL.
Notation dJ := (ct_decidable_eq Job).
Variables (sR : Schedule.schedule Job nR)
  (sL : I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_schedule Job dJ nL).
Hypothesis Hs : CcjSchedRel Job nR nL sR sL.

Lemma ccj_GS_scheduled_on j oR oL (Ho : CoOrdRel nR nL oR oL) tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (Schedule.scheduled_on sR j oR tR)
    (I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_scheduled_on Job dJ nL sL j oL tL).
Proof.
  apply: ct_decide_bool.
  exact (ccj_tr (Hs oR oL Ho tR tL Ht) (fun z => PropSPropRel (sR oR tR == Some j) (Lean.eq z (cl_opt (Some j))))
           (ccj_opt_eqb_rel Job (sR oR tR) (Some j))).
Qed.

Lemma ccj_GS_scheduled j tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (Schedule.scheduled sR j tR)
    (I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_scheduled Job dJ nL sL j tL).
Proof.
  apply: (co_exists_rel nR nL Hn). intros oR oL Ho. exact (ccj_GS_scheduled_on j oR oL Ho tR tL Ht).
Qed.

Lemma ccj_GS_service_at j tR tL (Ht : SubNatRel tR tL) :
  SubNatRel (Schedule.service_at sR j tR)
    (I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_service_at Job dJ nL sL j tL).
Proof.
  apply: coq_eq_to_imported_eq.
  rewrite (imported_eq_to_coq_eq _ _ (I.Prosa_Validation_ClassicJitterConstrainedDeadlinesInterface_service_at_sum Job dJ nL sL j tL)).
  apply: imported_eq_to_coq_eq.
  rewrite /Schedule.service_at big_mkcond /=.
  apply: (co_sum_rel nR nL Hn). intros oR oL Ho.
  have H := ccj_GS_scheduled_on j oR oL Ho tR tL Ht.
  rewrite (ct_bool_rel_logic _ _ H). destruct (Schedule.scheduled_on sR j oR tR).
  - exact (sub_nat_rel_canonical 1).
  - exact (sub_nat_rel_canonical 0).
Qed.

Lemma ccj_service_at_fun j : CcjFunRel (fun t => Schedule.service_at sR j t)
    (fun t => I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_service_at Job dJ nL sL j t).
Proof. intros kR kL Hk. exact (ccj_GS_service_at j kR kL Hk). Qed.

Lemma ccj_GS_service j tR tL (Ht : SubNatRel tR tL) :
  SubNatRel (Schedule.service sR j tR)
    (I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_service Job dJ nL sL j tL).
Proof. exact (ccj_ico 0 _ tR tL _ _ (sub_nat_rel_canonical 0) Ht (ccj_service_at_fun j)). Qed.

Lemma ccj_GS_completed cR cL (Hc : CcjParRel Job cR cL) j tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (Schedule.completed cR sR j tR)
    (I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_completed Job dJ cL nL sL j tL).
Proof. exact (ct_decide_le _ _ _ _ (Hc j) (ccj_GS_service j tR tL Ht)). Qed.

Lemma ccj_GS_sequential_jobs :
  PropSPropRel (Schedule.sequential_jobs sR)
    (I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_sequential_jobs Job dJ nL sL).
Proof.
  apply: ct_forall_identity => j. apply: ct_forall_nat => tR tL Ht.
  apply: (co_forall_ord nR nL Hn) => o1R o1L H1. apply: (co_forall_ord nR nL Hn) => o2R o2L H2.
  apply: ct_imp.
  { exact (ccj_tr (Hs o1R o1L H1 tR tL Ht) (fun z => PropSPropRel (sR o1R tR = Some j) (Lean.eq z (cl_opt (Some j))))
             (ccj_opt_eq_rel Job (sR o1R tR) (Some j))). }
  apply: ct_imp.
  { exact (ccj_tr (Hs o2R o2L H2 tR tL Ht) (fun z => PropSPropRel (sR o2R tR = Some j) (Lean.eq z (cl_opt (Some j))))
             (ccj_opt_eq_rel Job (sR o2R tR) (Some j))). }
  exact (co_ord_eq_rel _ _ _ _ _ _ H1 H2).
Qed.

Lemma ccj_GS_completed_jobs_dont_execute cR cL (Hc : CcjParRel Job cR cL) :
  PropSPropRel (Schedule.completed_jobs_dont_execute cR sR)
    (I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_completed_jobs_dont_execute Job dJ cL nL sL).
Proof.
  apply: ct_forall_identity => j. apply: ct_forall_nat => tR tL Ht.
  exact (sub_nat_le_correspondence _ _ _ _ (ccj_GS_service j tR tL Ht) (Hc j)).
Qed.

Lemma ccj_GS_jobs_come_from_arrival_sequence arrR arrL (Harr : CcjArrRel Job arrR arrL) :
  PropSPropRel (Schedule.jobs_come_from_arrival_sequence sR arrR)
    (I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_jobs_come_from_arrival_sequence Job dJ nL sL arrL).
Proof.
  apply: ct_forall_identity => j. apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (ct_bool_truth _ _ (ccj_GS_scheduled j tR tL Ht)).
  exact (ccj_arrives_in Job arrR arrL Harr j).
Qed.

End Defs.

Section TaskDefs.
Variables (Task Job : eqType) (nR : nat) (nL : Lean.Nat).
Hypothesis Hn : SubNatRel nR nL.
Notation dT := (ct_decidable_eq Task).
Notation dJ := (ct_decidable_eq Job).
Variables (sR : Schedule.schedule Job nR)
  (sL : I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_schedule Job dJ nL).
Hypothesis Hs : CcjSchedRel Job nR nL sR sL.
Variable job_task : Job -> Task.

End TaskDefs.

Lemma ccj_GS_processor nR nL (Hn : SubNatRel nR nL) :
  And (forall o : Schedule.processor nR, CoOrdRel nR nL o (co_ord_to_fin nR nL Hn o))
      (forall o : I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_processor nL,
         CoOrdRel nR nL (co_fin_to_ord nR nL Hn o) o).
Proof. exact (And_intro _ _ (co_ord_canonical nR nL Hn) (co_ord_surjective nR nL Hn)). Qed.

Lemma ccj_GS_schedule (Job : eqType) nR nL (Hn : SubNatRel nR nL) :
  And (forall s : Schedule.schedule Job nR, CcjSchedRel Job nR nL s (ccj_sched_to_target Job nR nL Hn s))
      (forall s : I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_schedule Job (ct_decidable_eq Job) nL,
         CcjSchedRel Job nR nL (ccj_sched_to_source Job nR nL Hn s) s).
Proof. exact (And_intro _ _ (ccj_sched_canonical Job nR nL Hn) (ccj_sched_surjective Job nR nL Hn)). Qed.

(* ------------------------------------------------------------------ *)
(** * Statements *)

(** The common prefix [forall num_cpus (sched : schedule Job num_cpus)]. *)
Lemma ccj_forall_ncpus_sched (Job : eqType)
    (PR : forall n : nat, Schedule.schedule Job n -> Prop)
    (PL : forall n : Lean.Nat, I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_schedule Job (ct_decidable_eq Job) n -> SProp) :
  (forall nR nL (Hn : SubNatRel nR nL) sR sL, CcjSchedRel Job nR nL sR sL -> PropSPropRel (PR nR sR) (PL nL sL)) ->
  PropSPropRel (forall n s, PR n s) (forall n s, PL n s).
Proof.
  intro H. apply: ct_forall_nat => nR nL Hn. exact (ccj_forall_sched Job nR nL Hn _ _ (H nR nL Hn)).
Qed.

Section GjschedDefs.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).

Lemma ccj_GJ_actual_arrival aR aL (Ha : CcjParRel Job aR aL) jjR jjL (Hjj : CcjParRel Job jjR jjL) j :
  SubNatRel (ScheduleWithJitter.actual_arrival aR jjR j) (I.Prosa_Classic_Model_Schedule_Global_Jitter_Schedule_ScheduleWithJitter_actual_arrival Job dJ aL jjL j).
Proof. exact (sub_add_correspondence _ _ _ _ (Ha j) (Hjj j)). Qed.

Lemma ccj_GJ_jitter_has_passed aR aL (Ha : CcjParRel Job aR aL) jjR jjL (Hjj : CcjParRel Job jjR jjL) j
    tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (ScheduleWithJitter.jitter_has_passed aR jjR j tR) (I.Prosa_Classic_Model_Schedule_Global_Jitter_Schedule_ScheduleWithJitter_jitter_has_passed Job dJ aL jjL j tL).
Proof. exact (ct_decide_le _ _ _ _ (ccj_GJ_actual_arrival aR aL Ha jjR jjL Hjj j) Ht). Qed.

Section GjschedSched.
Variables (nR : nat) (nL : Lean.Nat).
Hypothesis Hn : SubNatRel nR nL.
Variables (sR : Schedule.schedule Job nR)
  (sL : I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_schedule Job dJ nL).
Hypothesis Hs : CcjSchedRel Job nR nL sR sL.

Lemma ccj_GJ_pending aR aL (Ha : CcjParRel Job aR aL) cR cL (Hc : CcjParRel Job cR cL)
    jjR jjL (Hjj : CcjParRel Job jjR jjL) j tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (ScheduleWithJitter.pending aR cR jjR sR j tR) (I.Prosa_Classic_Model_Schedule_Global_Jitter_Schedule_ScheduleWithJitter_pending Job dJ aL cL jjL nL sL j tL).
Proof.
  exact (ct_bool_and _ _ _ _ (ccj_GJ_jitter_has_passed aR aL Ha jjR jjL Hjj j tR tL Ht)
           (ct_bool_not _ _ (ccj_GS_completed Job nR nL Hn sR sL Hs cR cL Hc j tR tL Ht))).
Qed.

Lemma ccj_GJ_backlogged aR aL (Ha : CcjParRel Job aR aL) cR cL (Hc : CcjParRel Job cR cL)
    jjR jjL (Hjj : CcjParRel Job jjR jjL) j tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (ScheduleWithJitter.backlogged aR cR jjR sR j tR) (I.Prosa_Classic_Model_Schedule_Global_Jitter_Schedule_ScheduleWithJitter_backlogged Job dJ aL cL jjL nL sL j tL).
Proof.
  exact (ct_bool_and _ _ _ _ (ccj_GJ_pending aR aL Ha cR cL Hc jjR jjL Hjj j tR tL Ht)
           (ct_bool_not _ _ (ccj_GS_scheduled Job nR nL Hn sR sL Hs j tR tL Ht))).
Qed.

Lemma ccj_GJ_jobs_execute_after_jitter aR aL (Ha : CcjParRel Job aR aL) jjR jjL (Hjj : CcjParRel Job jjR jjL) :
  PropSPropRel (ScheduleWithJitter.jobs_execute_after_jitter aR jjR sR) (I.Prosa_Classic_Model_Schedule_Global_Jitter_Schedule_ScheduleWithJitter_jobs_execute_after_jitter Job dJ aL jjL nL sL).
Proof.
  apply: ct_forall_identity => j. apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (ct_bool_truth _ _ (ccj_GS_scheduled Job nR nL Hn sR sL Hs j tR tL Ht)).
  exact (ct_bool_truth _ _ (ccj_GJ_jitter_has_passed aR aL Ha jjR jjL Hjj j tR tL Ht)).
Qed.

End GjschedSched.

End GjschedDefs.

Section GjschedTaskDefs.
Variables (Task Job : eqType) (nR : nat) (nL : Lean.Nat).
Hypothesis Hn : SubNatRel nR nL.
Notation dT := (ct_decidable_eq Task).
Notation dJ := (ct_decidable_eq Job).
Variables (sR : Schedule.schedule Job nR)
  (sL : I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_schedule Job dJ nL).
Hypothesis Hs : CcjSchedRel Job nR nL sR sL.
Variable job_task : Job -> Task.

Lemma ccj_GJT_task_scheduled_on tsk oR oL (Ho : CoOrdRel nR nL oR oL) tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (ScheduleOfSporadicTaskWithJitter.task_scheduled_on job_task sR tsk oR tR) (I.Prosa_Classic_Model_Schedule_Global_Jitter_Schedule_ScheduleOfSporadicTaskWithJitter_task_scheduled_on Task Job dT dJ job_task nL sL tsk oL tL).
Proof.
  refine (ccj_trs (Hs oR oL Ho tR tL Ht)
            (fun z => CtBoolRel (ScheduleOfSporadicTaskWithJitter.task_scheduled_on job_task sR tsk oR tR)
                        (match z with
                         | I.Option_some j => I.Decidable_decide (Lean.eq (job_task j) tsk) (dT (job_task j) tsk)
                         | I.Option_none => I.Bool_false end)) _).
  rewrite /ScheduleOfSporadicTaskWithJitter.task_scheduled_on. destruct (sR oR tR) as [x|].
  - exact (ct_decide_eq Task (job_task x) tsk).
  - exact (ct_bool_canonical false).
Qed.

Lemma ccj_GJT_task_is_scheduled tsk tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (ScheduleOfSporadicTaskWithJitter.task_is_scheduled job_task sR tsk tR) (I.Prosa_Classic_Model_Schedule_Global_Jitter_Schedule_ScheduleOfSporadicTaskWithJitter_task_is_scheduled Task Job dT dJ job_task nL sL tsk tL).
Proof.
  apply: (co_exists_rel nR nL Hn). intros oR oL Ho.
  exact (ccj_GJT_task_scheduled_on tsk oR oL Ho tR tL Ht).
Qed.

End GjschedTaskDefs.

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
  rewrite (imported_eq_to_coq_eq _ _ (I.Prosa_Validation_ClassicJitterConstrainedDeadlinesInterface_service_at_sum Job dJ nL sL j tL)).
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
(** * Policies (as in the accepted classic priority certificate) *)

Definition CpRelRel (T : Type) (rR : T -> T -> bool) (rL : T -> T -> I.Bool) : SProp :=
  forall a b, CtBoolRel (rR a b) (rL a b).

Lemma cp_forall_rel (T : Type) (PR : (T -> T -> bool) -> Prop) (PL : (T -> T -> I.Bool) -> SProp) :
  (forall rR rL, CpRelRel T rR rL -> PropSPropRel (PR rR) (PL rL)) -> PropSPropRel (forall r, PR r) (forall r, PL r).
Proof.
  exact (cs_forall_cover _ _ (CpRelRel T) (fun rR a b => ct_b2l (rR a b)) (fun rL a b => ct_l2b (rL a b))
           (fun rR a b => ct_bool_canonical _) (fun rL a b => ct_bool_surjective _) PR PL).
Qed.

(* ------------------------------------------------------------------ *)
(** * Task model (as in the accepted classic task_arrival and workload_bound certificates) *)

Lemma cta_false_rel : PropSPropRel Logic.False I.False.
Proof.
  apply prop_sprop_rel_intro.
  - exact ct_coq_false_to_target.
  - exact ct_target_false_to_strict.
Qed.

Lemma cta_ne (T : Type) (x y : T) : PropSPropRel (x <> y) (I.Ne T x y).
Proof. exact (ct_imp _ _ _ _ (ct_eq_rel T x y) cta_false_rel). Qed.

Lemma cwb_forall_arr (Job : eqType) PR PL :
  (forall aR aL, CsArrRel Job aR aL -> PropSPropRel (PR aR) (PL aL)) -> PropSPropRel (forall a, PR a) (forall a, PL a).
Proof. exact (cs_forall_cover _ _ (CsArrRel Job) (cs_arr_to_target Job) (cs_arr_to_source Job) (cs_arr_canonical Job) (cs_arr_surjective Job) PR PL). Qed.

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

(* ------------------------------------------------------------------ *)
(** * Platform (as in the accepted classic global platform certificate) *)

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
Variables (jjR : Job -> nat) (jjL : Job -> Lean.Nat).
Hypothesis Hjj : CsParRel Job jjR jjL.
Notation bl := (ccj_GJ_backlogged Job nR nL Hn sR sL Hs jaR jaL Hja cR cL Hc jjR jjL Hjj).
Notation son := (cf_Schedule_scheduled_on Job nR nL sR sL Hs).
Notation sch := (cf_Schedule_scheduled Job nR nL Hn sR sL Hs).

Lemma ccd_work_conserving :
  PropSPropRel (Platform.work_conserving jaR cR jjR aR sR) (I.Prosa_Classic_Model_Schedule_Global_Jitter_Platform_Platform_work_conserving Job dJ jaL cL jjL aL nL sL).
Proof.
  apply: ct_forall_identity => j. apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (cs_arrives_in Job aR aL Ha j).
  apply: ct_imp; first exact (ct_bool_truth _ _ (bl j tR tL Ht)).
  apply: (co_forall_ord nR nL Hn) => oR oL Ho.
  apply: ct_exists_identity => j_other.
  exact (ct_bool_truth _ _ (son j_other oR oL Ho tR tL Ht)).
Qed.

Lemma ccd_respects_FP_policy hpR hpL (Hhp : CpRelRel Task hpR hpL) :
  PropSPropRel (Platform.respects_FP_policy jaR cR job_task jjR aR sR hpR)
    (I.Prosa_Classic_Model_Schedule_Global_Jitter_Platform_Platform_respects_FP_policy Task Job dT dJ jaL cL job_task jjL aL nL sL hpL).
Proof.
  apply: ct_forall_identity => j. apply: ct_forall_identity => j_hp. apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (cs_arrives_in Job aR aL Ha j).
  apply: ct_imp; first exact (ct_bool_truth _ _ (bl j tR tL Ht)).
  apply: ct_imp; first exact (ct_bool_truth _ _ (sch j_hp tR tL Ht)).
  exact (ct_bool_truth _ _ (Hhp (job_task j_hp) (job_task j))).
Qed.

End PlatDefs.

(* ------------------------------------------------------------------ *)
(** * Task sets and counting *)

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
  PropSPropRel (x \in tsR) (I.Membership_mem Task LTs (I.Prosa_Util_Seqset_instMembershipSet Task dT) tsL x).
Proof. exact (cl_mem_rel_list _ _ cid cid cts_id x _ _ Hts). Qed.

(** [count P s] against [List.countP P l] by structural induction through [countP.go] and its
    accumulator (as in the accepted classic counting certificate). *)
Lemma cts_countP_go (pR : Task -> bool) (pL : Task -> I.Bool) (Hp : forall x, CtBoolRel (pR x) (pL x)) :
  forall (s : seq Task) n,
  Logic.eq (I.List_countP_go Task pL (cl_map cid s) (sub_nat_to_imported n)) (sub_nat_to_imported (n + count pR s)).
Proof.
  elim => [|x s IH] n.
  - by rewrite addn0.
  - have -> : Logic.eq (I.List_countP_go Task pL (cl_map cid (x :: s)) (sub_nat_to_imported n))
        (match pL x with
         | I.Bool_true => I.List_countP_go Task pL (cl_map cid s) (sub_nat_to_imported n.+1)
         | I.Bool_false => I.List_countP_go Task pL (cl_map cid s) (sub_nat_to_imported n) end).
    { cbn. destruct (pL x); reflexivity. }
    rewrite (ct_bool_rel_logic _ _ (Hp x)) (IH n.+1) (IH n).
    change (count pR (x :: s)) with (pR x + count pR s).
    case: (pR x).
    + by rewrite addSnnS add1n.
    + by rewrite add0n.
Qed.

Lemma cts_count pR pL (Hp : forall x, CtBoolRel (pR x) (pL x)) tsR tsL (Hts : CtsRel tsR tsL) :
  SubNatRel (count pR tsR) (I.List_countP Task pL (LVal tsL)).
Proof.
  refine (cs_trs Hts (fun z => SubNatRel (count pR tsR) (I.List_countP Task pL z)) _).
  apply: coq_eq_to_imported_eq. apply: Logic.eq_sym.
  exact (cts_countP_go pR pL Hp _ 0).
Qed.

End Ts.

(** [higher_priority_task] (as in the accepted classic priority certificate). *)
Lemma ccd_higher_priority_task (Task : eqType) hpR hpL (Hhp : CpRelRel Task hpR hpL) tsk tsk_other :
  CtBoolRel (Priority.higher_priority_task hpR tsk tsk_other)
    (I.Prosa_Classic_Model_Priority_Priority_higher_priority_task Task (ct_decidable_eq Task) hpL tsk tsk_other).
Proof. exact (ct_bool_and _ _ _ _ (Hhp tsk_other tsk) (ct_bool_not _ _ (ct_decide_eq Task tsk_other tsk))). Qed.

(* ------------------------------------------------------------------ *)
(** * Definitions *)

Theorem ConstrainedDeadlines_scheduled_task_with_higher_eq_priority_correspondence (Task Job : eqType) nR nL (Hn : SubNatRel nR nL)
    sR sL (Hs : CsSchedRel Job nR nL sR sL) (job_task : Job -> Task)
    hpR hpL (Hhp : CpRelRel Task hpR hpL) tsk tR tL (Ht : SubNatRel tR tL) tsk_other :
  CtBoolRel (ConstrainedDeadlines.scheduled_task_with_higher_eq_priority job_task sR hpR tsk tR tsk_other)
    (I.Prosa_Classic_Model_Schedule_Global_Jitter_ConstrainedDeadlines_ConstrainedDeadlines_scheduled_task_with_higher_eq_priority Task Job (ct_decidable_eq Task) (ct_decidable_eq Job) job_task nL sL hpL tsk tL tsk_other).
Proof.
  exact (ct_bool_and _ _ _ _ (ccj_GJT_task_is_scheduled Task Job nR nL Hn sR sL Hs job_task tsk_other tR tL Ht)
           (ccd_higher_priority_task Task hpR hpL Hhp tsk tsk_other)).
Qed.

(* ------------------------------------------------------------------ *)
(** * Statements *)

Definition src_platform_at_most_one_pending_job_of_each_task (Task Job : eqType) : Prop :=
  forall task_cost task_period task_deadline : Task -> Time.time,
    ltac:(type_of_term (@ConstrainedDeadlines.platform_at_most_one_pending_job_of_each_task Task task_cost task_period task_deadline Job)).
Definition tgt_platform_at_most_one_pending_job_of_each_task (Task Job : eqType) : SProp :=
  forall task_cost task_period task_deadline : Task -> Lean.Nat,
    ltac:(type_of_term (I.Prosa_Classic_Model_Schedule_Global_Jitter_ConstrainedDeadlines_ConstrainedDeadlines_platform_at_most_one_pending_job_of_each_task Task (ct_decidable_eq Task) task_cost task_period task_deadline Job (ct_decidable_eq Job))).
Theorem ConstrainedDeadlines_platform_at_most_one_pending_job_of_each_task_correspondence (Task Job : eqType) :
  PropSPropRel (src_platform_at_most_one_pending_job_of_each_task Task Job) (tgt_platform_at_most_one_pending_job_of_each_task Task Job).
Proof.
  unfold src_platform_at_most_one_pending_job_of_each_task, tgt_platform_at_most_one_pending_job_of_each_task.
  apply: cs_forall_par => tcR tcL Htc. apply: cs_forall_par => tpR tpL Htp. apply: cs_forall_par => tdR tdL Htd.
  apply: cs_forall_par => jaR jaL Hja. apply: cs_forall_par => cR cL Hc.
  apply: ct_forall_identity => job_task.
  apply: cs_forall_par => jjR jjL Hjj.
  apply: cwb_forall_arr => aR aL Ha.
  apply: cs_forall_ncpus_sched => nR nL Hn sR sL Hs.
  apply: ct_imp; first exact (cwb_sporadic_task_model Task Job tpR tpL Htp jaR jaL Hja job_task aR aL Ha).
  apply: ct_forall_identity => tsk.
  apply: ct_imp; first exact (cwb_valid_sporadic_task Task tcR tcL Htc tpR tpL Htp tdR tdL Htd tsk).
  apply: ct_forall_identity => j.
  apply: ct_imp; first exact (ct_eq_rel Task (job_task j) tsk).
  apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp.
  { apply: ct_forall_identity => j_other. apply: ct_forall_identity => tsk_other.
    apply: ct_imp; first exact (cs_arrives_in Job aR aL Ha j_other).
    apply: ct_imp; first exact (ct_eq_rel Task (job_task j_other) tsk_other).
    apply: ct_imp; first exact (sub_nat_le_correspondence _ _ _ _ (sub_add_correspondence _ _ _ _ (Hja j_other) (Htp tsk_other)) Ht).
    exact (ct_bool_truth _ _ (cf_Schedule_completed Job nR nL Hn sR sL Hs cR cL Hc j_other _ _
                                (sub_add_correspondence _ _ _ _ (Hja j_other) (Htp (job_task j_other))))). }
  apply: ct_forall_identity => j1. apply: ct_forall_identity => j2.
  apply: ct_imp; first exact (cs_arrives_in Job aR aL Ha j1).
  apply: ct_imp; first exact (cs_arrives_in Job aR aL Ha j2).
  apply: ct_imp; first exact (ct_bool_truth _ _ (ccj_GJ_pending Job nR nL Hn sR sL Hs jaR jaL Hja cR cL Hc jjR jjL Hjj j1 tR tL Ht)).
  apply: ct_imp; first exact (ct_bool_truth _ _ (ccj_GJ_pending Job nR nL Hn sR sL Hs jaR jaL Hja cR cL Hc jjR jjL Hjj j2 tR tL Ht)).
  apply: ct_imp; first exact (ct_eq_rel Task (job_task j1) (job_task j2)).
  exact (ct_eq_rel Job j1 j2).
Qed.

Definition src_platform_cpus_busy_with_interfering_tasks (Task Job : eqType) : Prop :=
  forall task_cost task_period task_deadline : Task -> Time.time,
    ltac:(type_of_term (@ConstrainedDeadlines.platform_cpus_busy_with_interfering_tasks Task task_cost task_period task_deadline Job)).
Definition tgt_platform_cpus_busy_with_interfering_tasks (Task Job : eqType) : SProp :=
  forall task_cost task_period task_deadline : Task -> Lean.Nat,
    ltac:(type_of_term (I.Prosa_Classic_Model_Schedule_Global_Jitter_ConstrainedDeadlines_ConstrainedDeadlines_platform_cpus_busy_with_interfering_tasks Task (ct_decidable_eq Task) task_cost task_period task_deadline Job (ct_decidable_eq Job))).
Theorem ConstrainedDeadlines_platform_cpus_busy_with_interfering_tasks_correspondence (Task Job : eqType) :
  PropSPropRel (src_platform_cpus_busy_with_interfering_tasks Task Job) (tgt_platform_cpus_busy_with_interfering_tasks Task Job).
Proof.
  unfold src_platform_cpus_busy_with_interfering_tasks, tgt_platform_cpus_busy_with_interfering_tasks.
  apply: cs_forall_par => tcR tcL Htc. apply: cs_forall_par => tpR tpL Htp. apply: cs_forall_par => tdR tdL Htd.
  apply: cs_forall_par => jaR jaL Hja. apply: cs_forall_par => cR cL Hc.
  apply: ct_forall_identity => job_task.
  apply: cs_forall_par => jjR jjL Hjj.
  apply: cwb_forall_arr => aR aL Ha.
  apply: cs_forall_ncpus_sched => nR nL Hn sR sL Hs.
  apply: ct_imp; first exact (cf_Schedule_jobs_come_from_arrival_sequence Job nR nL Hn sR sL Hs aR aL Ha).
  apply: ct_imp; first exact (ccd_work_conserving Job nR nL Hn sR sL Hs jaR jaL cR cL Hja Hc aR aL Ha jjR jjL Hjj).
  apply: (cts_forall Task) => tsR tsL Hts.
  apply: ct_imp.
  { apply: ct_forall_identity => j.
    exact (ct_imp _ _ _ _ (cs_arrives_in Job aR aL Ha j) (cts_mem Task tsR tsL Hts (job_task j))). }
  apply: ct_imp; first exact (cf_Schedule_sequential_jobs Job nR nL Hn sR sL Hs).
  apply: ct_imp; first exact (ccj_GJ_jobs_execute_after_jitter Job nR nL Hn sR sL Hs jaR jaL Hja jjR jjL Hjj).
  apply: ct_imp; first exact (cf_Schedule_completed_jobs_dont_execute Job nR nL Hn sR sL Hs cR cL Hc).
  apply: ct_imp; first exact (cwb_sporadic_task_model Task Job tpR tpL Htp jaR jaL Hja job_task aR aL Ha).
  apply: ct_forall_identity => tsk.
  apply: ct_imp; first exact (cwb_valid_sporadic_task Task tcR tcL Htc tpR tpL Htp tdR tdL Htd tsk).
  apply: ct_forall_identity => j.
  apply: ct_imp; first exact (cs_arrives_in Job aR aL Ha j).
  apply: ct_imp; first exact (ct_eq_rel Task (job_task j) tsk).
  apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (ct_bool_truth _ _ (ccj_GJ_backlogged Job nR nL Hn sR sL Hs jaR jaL Hja cR cL Hc jjR jjL Hjj j tR tL Ht)).
  apply: ct_imp.
  { apply: ct_forall_identity => j_other. apply: ct_forall_identity => tsk_other.
    apply: ct_imp; first exact (cs_arrives_in Job aR aL Ha j_other).
    apply: ct_imp; first exact (ct_eq_rel Task (job_task j_other) tsk_other).
    apply: ct_imp; first exact (sub_nat_le_correspondence _ _ _ _ (sub_add_correspondence _ _ _ _ (Hja j_other) (Htp tsk_other)) Ht).
    exact (ct_bool_truth _ _ (cf_Schedule_completed Job nR nL Hn sR sL Hs cR cL Hc j_other _ _
                                (sub_add_correspondence _ _ _ _ (Hja j_other) (Htp (job_task j_other))))). }
  exact (sub_nat_eq_correspondence _ _ _ _
           (cts_count Task _ _ (fun tsk_other => ct_bool_and _ _ _ _
                                   (ccj_GJT_task_is_scheduled Task Job nR nL Hn sR sL Hs job_task tsk_other tR tL Ht)
                                   (ct_bool_not _ _ (ct_decide_eq Task tsk_other tsk))) tsR tsL Hts) Hn).
Qed.

Definition src_platform_fp_no_multiple_jobs_of_interfering_tasks (Task Job : eqType) : Prop :=
  forall task_period : Task -> Time.time,
    ltac:(type_of_term (@ConstrainedDeadlines.platform_fp_no_multiple_jobs_of_interfering_tasks Task task_period Job)).
Definition tgt_platform_fp_no_multiple_jobs_of_interfering_tasks (Task Job : eqType) : SProp :=
  forall task_period : Task -> Lean.Nat,
    ltac:(type_of_term (I.Prosa_Classic_Model_Schedule_Global_Jitter_ConstrainedDeadlines_ConstrainedDeadlines_platform_fp_no_multiple_jobs_of_interfering_tasks Task (ct_decidable_eq Task) task_period Job (ct_decidable_eq Job))).
Theorem ConstrainedDeadlines_platform_fp_no_multiple_jobs_of_interfering_tasks_correspondence (Task Job : eqType) :
  PropSPropRel (src_platform_fp_no_multiple_jobs_of_interfering_tasks Task Job)
    (tgt_platform_fp_no_multiple_jobs_of_interfering_tasks Task Job).
Proof.
  unfold src_platform_fp_no_multiple_jobs_of_interfering_tasks, tgt_platform_fp_no_multiple_jobs_of_interfering_tasks.
  apply: cs_forall_par => tpR tpL Htp.
  apply: cs_forall_par => jaR jaL Hja. apply: cs_forall_par => cR cL Hc.
  apply: ct_forall_identity => job_task.
  apply: cs_forall_par => jjR jjL Hjj.
  apply: cwb_forall_arr => aR aL Ha.
  apply: cs_forall_ncpus_sched => nR nL Hn sR sL Hs.
  apply: cp_forall_rel => hpR hpL Hhp.
  apply: ct_imp; first exact (cwb_sporadic_task_model Task Job tpR tpL Htp jaR jaL Hja job_task aR aL Ha).
  apply: ct_forall_identity => tsk.
  apply: ct_forall_nat => tR tL Ht.
  have Hhpt := ccd_higher_priority_task Task hpR hpL Hhp tsk.
  apply: ct_imp.
  { apply: ct_forall_identity => j_other. apply: ct_forall_identity => tsk_other.
    apply: ct_imp; first exact (cs_arrives_in Job aR aL Ha j_other).
    apply: ct_imp; first exact (ct_eq_rel Task (job_task j_other) tsk_other).
    apply: ct_imp; first exact (ct_bool_truth _ _ (Hhpt tsk_other)).
    exact (ct_bool_truth _ _ (cf_Schedule_completed Job nR nL Hn sR sL Hs cR cL Hc j_other _ _
                                (sub_add_correspondence _ _ _ _ (Hja j_other) (Htp tsk_other)))). }
  apply: ct_forall_identity => j1. apply: ct_forall_identity => j2.
  apply: ct_imp; first exact (cs_arrives_in Job aR aL Ha j1).
  apply: ct_imp; first exact (cs_arrives_in Job aR aL Ha j2).
  apply: ct_imp; first exact (ct_bool_truth _ _ (ccj_GJ_pending Job nR nL Hn sR sL Hs jaR jaL Hja cR cL Hc jjR jjL Hjj j1 tR tL Ht)).
  apply: ct_imp; first exact (ct_bool_truth _ _ (ccj_GJ_pending Job nR nL Hn sR sL Hs jaR jaL Hja cR cL Hc jjR jjL Hjj j2 tR tL Ht)).
  apply: ct_imp; first exact (ct_eq_rel Task (job_task j1) (job_task j2)).
  apply: ct_imp; first exact (ct_bool_truth _ _ (Hhpt (job_task j1))).
  exact (ct_eq_rel Job j1 j2).
Qed.

Definition src_platform_fp_no_multiple_jobs_of_tsk (Task Job : eqType) : Prop :=
  forall task_cost task_period task_deadline : Task -> Time.time,
    ltac:(type_of_term (@ConstrainedDeadlines.platform_fp_no_multiple_jobs_of_tsk Task task_cost task_period task_deadline Job)).
Definition tgt_platform_fp_no_multiple_jobs_of_tsk (Task Job : eqType) : SProp :=
  forall task_cost task_period task_deadline : Task -> Lean.Nat,
    ltac:(type_of_term (I.Prosa_Classic_Model_Schedule_Global_Jitter_ConstrainedDeadlines_ConstrainedDeadlines_platform_fp_no_multiple_jobs_of_tsk Task (ct_decidable_eq Task) task_cost task_period task_deadline Job (ct_decidable_eq Job))).
Theorem ConstrainedDeadlines_platform_fp_no_multiple_jobs_of_tsk_correspondence (Task Job : eqType) :
  PropSPropRel (src_platform_fp_no_multiple_jobs_of_tsk Task Job) (tgt_platform_fp_no_multiple_jobs_of_tsk Task Job).
Proof.
  unfold src_platform_fp_no_multiple_jobs_of_tsk, tgt_platform_fp_no_multiple_jobs_of_tsk.
  apply: cs_forall_par => tcR tcL Htc. apply: cs_forall_par => tpR tpL Htp. apply: cs_forall_par => tdR tdL Htd.
  apply: cs_forall_par => jaR jaL Hja. apply: cs_forall_par => cR cL Hc.
  apply: ct_forall_identity => job_task.
  apply: cs_forall_par => jjR jjL Hjj.
  apply: cwb_forall_arr => aR aL Ha.
  apply: cs_forall_ncpus_sched => nR nL Hn sR sL Hs.
  apply: ct_imp; first exact (cwb_sporadic_task_model Task Job tpR tpL Htp jaR jaL Hja job_task aR aL Ha).
  apply: ct_forall_identity => tsk.
  apply: ct_imp; first exact (cwb_valid_sporadic_task Task tcR tcL Htc tpR tpL Htp tdR tdL Htd tsk).
  apply: ct_forall_identity => j.
  apply: ct_imp; first exact (cs_arrives_in Job aR aL Ha j).
  apply: ct_imp; first exact (ct_eq_rel Task (job_task j) tsk).
  apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (ct_bool_truth _ _ (ccj_GJ_backlogged Job nR nL Hn sR sL Hs jaR jaL Hja cR cL Hc jjR jjL Hjj j tR tL Ht)).
  apply: ct_imp; first exact (sub_nat_lt_correspondence _ _ _ _ Ht (sub_add_correspondence _ _ _ _ (Hja j) (Htp tsk))).
  apply: ct_imp.
  { apply: ct_forall_identity => j0.
    apply: ct_imp; first exact (cs_arrives_in Job aR aL Ha j0).
    apply: ct_imp; first exact (ct_eq_rel Task (job_task j0) tsk).
    apply: ct_imp; first exact (sub_nat_lt_correspondence _ _ _ _ (Hja j0) (Hja j)).
    exact (ct_bool_truth _ _ (cf_Schedule_completed Job nR nL Hn sR sL Hs cR cL Hc j0 _ _
                                (sub_add_correspondence _ _ _ _ (Hja j0) (Htp tsk)))). }
  apply: ct_forall_identity => j'.
  apply: ct_imp; first exact (cs_arrives_in Job aR aL Ha j').
  apply: ct_imp; first exact (ct_bool_truth _ _ (ccj_GJ_pending Job nR nL Hn sR sL Hs jaR jaL Hja cR cL Hc jjR jjL Hjj j' tR tL Ht)).
  apply: ct_imp; first exact (ct_eq_rel Task (job_task j') tsk).
  exact (ct_eq_rel Job j' j).
Qed.

Definition src_platform_fp_cpus_busy_with_interfering_tasks (Task Job : eqType) : Prop :=
  forall task_cost task_period task_deadline : Task -> Time.time,
    ltac:(type_of_term (@ConstrainedDeadlines.platform_fp_cpus_busy_with_interfering_tasks Task task_cost task_period task_deadline Job)).
Definition tgt_platform_fp_cpus_busy_with_interfering_tasks (Task Job : eqType) : SProp :=
  forall task_cost task_period task_deadline : Task -> Lean.Nat,
    ltac:(type_of_term (I.Prosa_Classic_Model_Schedule_Global_Jitter_ConstrainedDeadlines_ConstrainedDeadlines_platform_fp_cpus_busy_with_interfering_tasks Task (ct_decidable_eq Task) task_cost task_period task_deadline Job (ct_decidable_eq Job))).
Theorem ConstrainedDeadlines_platform_fp_cpus_busy_with_interfering_tasks_correspondence (Task Job : eqType) :
  PropSPropRel (src_platform_fp_cpus_busy_with_interfering_tasks Task Job) (tgt_platform_fp_cpus_busy_with_interfering_tasks Task Job).
Proof.
  unfold src_platform_fp_cpus_busy_with_interfering_tasks, tgt_platform_fp_cpus_busy_with_interfering_tasks.
  apply: cs_forall_par => tcR tcL Htc. apply: cs_forall_par => tpR tpL Htp. apply: cs_forall_par => tdR tdL Htd.
  apply: cs_forall_par => jaR jaL Hja. apply: cs_forall_par => cR cL Hc.
  apply: ct_forall_identity => job_task.
  apply: cs_forall_par => jjR jjL Hjj.
  apply: cwb_forall_arr => aR aL Ha.
  apply: cs_forall_ncpus_sched => nR nL Hn sR sL Hs.
  apply: ct_imp; first exact (cf_Schedule_jobs_come_from_arrival_sequence Job nR nL Hn sR sL Hs aR aL Ha).
  apply: cp_forall_rel => hpR hpL Hhp.
  apply: ct_imp; first exact (ccd_work_conserving Job nR nL Hn sR sL Hs jaR jaL cR cL Hja Hc aR aL Ha jjR jjL Hjj).
  apply: ct_imp; first exact (ccd_respects_FP_policy Task Job nR nL Hn sR sL Hs jaR jaL cR cL Hja Hc job_task aR aL Ha jjR jjL Hjj hpR hpL Hhp).
  apply: (cts_forall Task) => tsR tsL Hts.
  apply: ct_imp.
  { apply: ct_forall_identity => j.
    exact (ct_imp _ _ _ _ (cs_arrives_in Job aR aL Ha j) (cts_mem Task tsR tsL Hts (job_task j))). }
  apply: ct_imp; first exact (cf_Schedule_sequential_jobs Job nR nL Hn sR sL Hs).
  apply: ct_imp; first exact (ccj_GJ_jobs_execute_after_jitter Job nR nL Hn sR sL Hs jaR jaL Hja jjR jjL Hjj).
  apply: ct_imp; first exact (cf_Schedule_completed_jobs_dont_execute Job nR nL Hn sR sL Hs cR cL Hc).
  apply: ct_imp; first exact (cwb_sporadic_task_model Task Job tpR tpL Htp jaR jaL Hja job_task aR aL Ha).
  apply: ct_forall_identity => tsk.
  apply: ct_imp; first exact (cwb_valid_sporadic_task Task tcR tcL Htc tpR tpL Htp tdR tdL Htd tsk).
  apply: ct_forall_identity => j.
  apply: ct_imp; first exact (cs_arrives_in Job aR aL Ha j).
  apply: ct_imp; first exact (ct_eq_rel Task (job_task j) tsk).
  apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (ct_bool_truth _ _ (ccj_GJ_backlogged Job nR nL Hn sR sL Hs jaR jaL Hja cR cL Hc jjR jjL Hjj j tR tL Ht)).
  apply: ct_imp; first exact (sub_nat_lt_correspondence _ _ _ _ Ht (sub_add_correspondence _ _ _ _ (Hja j) (Htp tsk))).
  have Hhpt := ccd_higher_priority_task Task hpR hpL Hhp tsk.
  apply: ct_imp.
  { apply: ct_forall_identity => j_other. apply: ct_forall_identity => tsk_other.
    apply: ct_imp; first exact (cs_arrives_in Job aR aL Ha j_other).
    apply: ct_imp; first exact (ct_eq_rel Task (job_task j_other) tsk_other).
    apply: ct_imp; first exact (ct_bool_truth _ _ (Hhpt tsk_other)).
    exact (ct_bool_truth _ _ (cf_Schedule_completed Job nR nL Hn sR sL Hs cR cL Hc j_other _ _
                                (sub_add_correspondence _ _ _ _ (Hja j_other) (Htp tsk_other)))). }
  apply: ct_imp.
  { apply: ct_forall_identity => j0.
    apply: ct_imp; first exact (cs_arrives_in Job aR aL Ha j0).
    apply: ct_imp; first exact (ct_eq_rel Task (job_task j0) tsk).
    apply: ct_imp; first exact (sub_nat_lt_correspondence _ _ _ _ (Hja j0) (Hja j)).
    exact (ct_bool_truth _ _ (cf_Schedule_completed Job nR nL Hn sR sL Hs cR cL Hc j0 _ _
                                (sub_add_correspondence _ _ _ _ (Hja j0) (Htp tsk)))). }
  exact (sub_nat_eq_correspondence _ _ _ _
           (cts_count Task _ _ (ConstrainedDeadlines_scheduled_task_with_higher_eq_priority_correspondence Task Job nR nL Hn sR sL Hs
                                  job_task hpR hpL Hhp tsk tR tL Ht) tsR tsL Hts) Hn).
Qed.
