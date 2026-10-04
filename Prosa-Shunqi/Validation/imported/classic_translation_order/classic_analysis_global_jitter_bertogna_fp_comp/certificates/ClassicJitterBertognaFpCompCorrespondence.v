From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq path fintype bigop div.
From prosa Require Import classic.util.div_mod classic.model.time classic.util.notation classic.model.arrival.basic.arrival_sequence classic.model.arrival.basic.task classic.model.arrival.basic.job classic.model.arrival.basic.task_arrival classic.model.schedule.global.basic.schedule classic.model.schedule.global.workload classic.model.schedule.global.response_time classic.model.schedule.global.jitter.job classic.model.schedule.global.jitter.schedule classic.analysis.global.jitter.workload_bound util.seqset classic.model.priority classic.model.schedule.global.jitter.platform classic.model.schedule.global.jitter.interference classic.model.schedule.global.jitter.constrained_deadlines classic.analysis.global.jitter.interference_bound classic.analysis.global.jitter.interference_bound_fp classic.analysis.global.jitter.bertogna_fp_theory classic.model.schedule.global.schedulability classic.analysis.global.jitter.bertogna_fp_comp.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedClassicJitterBertognaFpComp.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence ClassicJitterBertognaFpCompBase ClassicJitterBertognaFpCompList ClassicJitterBertognaFpCompOrd.



Module I := ImportedClassicJitterBertognaFpComp.
Local Open Scope nat_scope.

(** Certificates for [classic/analysis/global/jitter/bertogna_fp_comp.v] (ProsaBuddy classic, commit f692cb7).

    Inputs, relations and computation as in the accepted classic global workload_bound certificate (re-stated below for
    this export): eqTypes identified with their canonical Lean [DecidableEq] instances; times and [num_cpus] by
    [SubNatRel]; processors by their values; schedules pointwise; job and task parameters pointwise; sequences
    elementwise; arrival sequences pointwise on related times; all with two-way totals.  The sorted jobs against the
    core [List.mergeSort] through the exported stable-sort facts ([cjg_sort_rel]); [nth] against [getD];
    [workload]/[service]/[service_during] through kernel-guarded [rfl] body projections and the four half-open sums of
    the statements through kernel-guarded type normalization, related by [cjw_ico]; [\sum_(i <- s) F i] against the
    v0.6 [sumSeq]; [div_floor], [minn] and the Nat operations through the accepted operation-level bridge [DivModCorrespondence].

    Statements: the source side is the exact elaborated type of the pinned lemma (via [type of]; the source proof is
    not used).  For the lemmas whose binder lists put task parameters before the job type, the job type is fixed as an
    [eqType] with its canonical Lean instance and the task parameters stay universally quantified on both sides. *)

Ltac type_of_term t := let T := type of t in exact T.
Notation cid := (fun z => z).

(* ------------------------------------------------------------------ *)
(** * Helpers (re-bound to this export from the accepted classic certificates) *)

(** Base definitions (as in the accepted classic base library), provided here when this export's library lacks them. *)

(* ------------------------------------------------------------------ *)
(** * Generic helpers *)

Lemma cbt_forall_cover (A B : Type) (Rel : A -> B -> SProp) (toB : A -> B) (toA : B -> A)
    (HB : forall a, Rel a (toB a)) (HA : forall b, Rel (toA b) b) (PR : A -> Prop) (PL : B -> SProp) :
  (forall a b, Rel a b -> PropSPropRel (PR a) (PL b)) -> PropSPropRel (forall a, PR a) (forall b, PL b).
Proof.
  intro H. apply prop_sprop_rel_intro.
  - intros HR b. exact (prop_to_sprop _ _ (H _ _ (HA b)) (HR _)).
  - intro HL. apply strictly_inhabits. intro a. exact (sprop_to_prop _ _ (H _ _ (HB a)) (HL _)).
Qed.

Lemma cbt_mem (T : eqType) x s sL : ClListRel cid s sL ->
  PropSPropRel (x \in s) (I.Membership_mem T (I.List T) (I.List_instMembership T) sL x).
Proof. exact (cl_mem_rel_list T T cid cid (fun _ => Logic.eq_refl _) x s sL). Qed.

Lemma cbt_uniq (T : eqType) s sL : ClListRel cid s sL -> PropSPropRel (uniq s) (I.List_Nodup T sL).
Proof. exact (cl_uniq_rel_list T T cid cid (fun _ => Logic.eq_refl _) (fun _ => Logic.eq_refl _) s sL). Qed.

Lemma cbt_list_size (T : Type) s sL : ClListRel (B := T) cid s sL -> SubNatRel (size s) (I.List_length T sL).
Proof. intro H. destruct H. exact (cl_size cid s). Qed.

Lemma cbt_lean_eq_logic (A : Type) (x y : A) : Lean.eq x y -> Logic.eq x y.
Proof. exact (imported_eq_to_coq_eq x y). Qed.

(** Transport along the target equality (definitional UIP), into relevant and SProp-valued families. *)
Definition cbt_tr {A : Type} {x y : A} (E : Lean.eq x y) (P : A -> Type) (h : P x) : P y :=
  match E in Lean.eq _ z return P z with Lean.eq_refl => h end.
Definition cbt_trs {A : Type} {x y : A} (E : Lean.eq x y) (P : A -> SProp) (h : P x) : P y :=
  match E in Lean.eq _ z return P z with Lean.eq_refl => h end.

(** Options: [cl_opt] is injective and [x == Some j] is [cl_opt x = some j]. *)
Lemma cbt_opt_inj (A : Type) (o1 o2 : option A) : Logic.eq (cl_opt o1) (cl_opt o2) -> Logic.eq o1 o2.
Proof. intro E. by rewrite -(cl_unopt_opt o1) -(cl_unopt_opt o2) E. Qed.

Lemma cbt_opt_eq_rel (A : Type) (o1 o2 : option A) :
  PropSPropRel (Logic.eq o1 o2) (Lean.eq (cl_opt o1) (cl_opt o2)).
Proof.
  apply prop_sprop_rel_intro.
  - intro E. rewrite E. exact (@Lean.eq_refl _ _).
  - intro E. apply strictly_inhabits. exact (cbt_opt_inj A o1 o2 (imported_eq_to_coq_eq _ _ E)).
Qed.

Lemma cbt_opt_eqb_rel (A : eqType) (o1 o2 : option A) :
  PropSPropRel (is_true (o1 == o2)) (Lean.eq (cl_opt o1) (cl_opt o2)).
Proof.
  apply prop_sprop_rel_intro.
  - move=> /eqP E. rewrite E. exact (@Lean.eq_refl _ _).
  - intro E. apply strictly_inhabits. apply/eqP. exact (cbt_opt_inj A o1 o2 (imported_eq_to_coq_eq _ _ E)).
Qed.

(* ------------------------------------------------------------------ *)
(** * Half-open sums and concatenations over [nat] (as in the accepted sum / arrival_sequence certificates) *)

Fixpoint cbt_natl (s : seq nat) : I.List_inst1 Lean.Nat :=
  match s with [::] => I.List_nil_inst1 _ | x :: s' => I.List_cons_inst1 _ (sub_nat_to_imported x) (cbt_natl s') end.

Lemma cbt_iota_range : forall n s,
  Logic.eq (I.List_range' (sub_nat_to_imported s) (sub_nat_to_imported n) (Lean.Nat_succ Lean.Nat_zero)) (cbt_natl (iota s n)).
Proof.
  elim => [|n IH] s; first reflexivity.
  change (Logic.eq (I.List_cons_inst1 _ (sub_nat_to_imported s)
      (I.List_range' (sub_nat_to_imported (S s)) (sub_nat_to_imported n) (Lean.Nat_succ Lean.Nat_zero)))
    (I.List_cons_inst1 _ (sub_nat_to_imported s) (cbt_natl (iota (S s) n)))).
  by rewrite IH.
Qed.

Lemma cbt_foldr_add (f : Lean.Nat -> Lean.Nat) (g : nat -> nat) (Hf : forall k, Logic.eq (f (sub_nat_to_imported k)) (sub_nat_to_imported (g k))) :
  forall s, Logic.eq (I.List_foldr_inst3 Lean.Nat Lean.Nat Lean.Nat_add Lean.Nat_zero (I.List_map_inst3 Lean.Nat Lean.Nat f (cbt_natl s)))
                     (sub_nat_to_imported (foldr addn 0 (map g s))).
Proof.
  elim => [|k s IH] //=.
  change (Logic.eq (Lean.Nat_add (f (sub_nat_to_imported k))
            (I.List_foldr_inst3 Lean.Nat Lean.Nat Lean.Nat_add Lean.Nat_zero (I.List_map_inst3 Lean.Nat Lean.Nat f (cbt_natl s))))
         (sub_nat_to_imported (g k + foldr addn 0 (map g s)))).
  rewrite IH Hf. exact (imported_eq_to_coq_eq _ _ (sub_add_canonical _ _)).
Qed.

Lemma cbt_big_fold (xs : seq nat) (F : nat -> nat) : Logic.eq (\sum_(i <- xs) F i) (foldr addn 0 (map F xs)).
Proof. elim: xs => [|x xs IH]; first by rewrite big_nil. by rewrite big_cons IH. Qed.

Definition CbtFunRel (FR : nat -> nat) (FL : Lean.Nat -> Lean.Nat) : SProp :=
  forall kR kL, SubNatRel kR kL -> SubNatRel (FR kR) (FL kL).

Lemma cbt_fun_canonical FR FL (HF : CbtFunRel FR FL) k : Logic.eq (FL (sub_nat_to_imported k)) (sub_nat_to_imported (FR k)).
Proof. exact (co_nat_logic _ _ (HF _ _ (sub_nat_rel_canonical k))). Qed.

Lemma cbt_ico mR mL nR nL FR FL (Hm : SubNatRel mR mL) (Hn : SubNatRel nR nL) (HF : CbtFunRel FR FL) :
  SubNatRel (\sum_(mR <= i < nR) FR i)
    (I.List_foldr_inst3 Lean.Nat Lean.Nat Lean.Nat_add Lean.Nat_zero
       (I.List_map_inst3 Lean.Nat Lean.Nat FL (I.List_range' mL (I.Nat_sub nL mL) (Lean.Nat_succ Lean.Nat_zero)))).
Proof.
  rewrite (co_nat_logic _ _ Hm) (co_nat_logic _ _ Hn).
  have -> : Logic.eq (I.Nat_sub (sub_nat_to_imported nR) (sub_nat_to_imported mR)) (sub_nat_to_imported (nR - mR))
    := ct_sub_canonical nR mR.
  rewrite cbt_iota_range.
  apply: coq_eq_to_imported_eq. apply: Logic.eq_sym. rewrite (cbt_foldr_add FL FR (cbt_fun_canonical FR FL HF)).
  by rewrite cbt_big_fold.
Qed.

Lemma cbt_map_natl {B : Type} (f : Lean.Nat -> B) : forall s,
  Logic.eq (I.List_map_inst1 Lean.Nat B f (cbt_natl s)) (cl_map (fun k => f (sub_nat_to_imported k)) s).
Proof.
  elim => [|k s IH] //=.
  change (Logic.eq (I.List_cons B (f (sub_nat_to_imported k)) (I.List_map_inst1 Lean.Nat B f (cbt_natl s)))
                   (I.List_cons B (f (sub_nat_to_imported k)) (cl_map (fun k => f (sub_nat_to_imported k)) s))).
  by rewrite IH.
Qed.

Lemma cbt_big_seq {A : Type} (F : nat -> seq A) : forall s : seq nat,
  Logic.eq (\big[cat/[::]]_(i <- s) F i) (flatten (map F s)).
Proof. elim => [|x s IH]; first by rewrite big_nil. by rewrite big_cons IH. Qed.

Definition CbtNatFamRel (A : Type) (fR : nat -> seq A) (fL : Lean.Nat -> I.List A) : SProp :=
  forall nR nL, SubNatRel nR nL -> ClListRel cid (fR nR) (fL nL).

Lemma cbt_bigcat_nat_rel (A : Type) fR fL (Hf : CbtNatFamRel A fR fL) mR mL nR nL :
  SubNatRel mR mL -> SubNatRel nR nL ->
  ClListRel cid (\big[cat/[::]]_(mR <= t < nR) fR t) (I.Prosa_Util_Notation_bigCat A mL nL fL).
Proof.
  intros Hm Hn. have E1 := co_nat_logic _ _ Hm. have E2 := co_nat_logic _ _ Hn. subst mL nL.
  apply: coq_eq_to_imported_eq. apply: Logic.eq_sym.
  rewrite (imported_eq_to_coq_eq _ _ (I.Prosa_Validation_ClassicJitterBertognaFpCompInterface_bigCat_range'
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
  rewrite cbt_big_seq /index_iota Hi -map_comp.
  reflexivity.
Qed.

Lemma cbt_notin_target (T : eqType) x s : Logic.eq (x \in s) false ->
  I.Not (I.Membership_mem T (I.List T) (I.List_instMembership T) (cl_map cid s) x).
Proof.
  intros Hx H. apply: ct_coq_false_to_target.
  have Hm := sprop_to_prop _ _ (cbt_mem T x s _ (cl_lean_eq _ _ _ (Logic.eq_refl _))) H.
  rewrite Hx in Hm. discriminate.
Qed.

(** [undup] against Mathlib's [List.dedup] (step equations exported with their proofs). *)
Lemma cbt_undup_rel (T : eqType) : forall s sL, ClListRel cid s sL ->
  ClListRel cid (undup s) (I.List_dedup T (ct_decidable_eq T) sL).
Proof.
  intros s sL Hs. have E := cl_list_logic _ _ _ Hs. subst sL. apply: coq_eq_to_imported_eq. clear Hs.
  elim: s => [|x s IH].
  - exact (Logic.eq_sym (imported_eq_to_coq_eq _ _ (I.Prosa_Validation_ClassicJitterBertognaFpCompInterface_dedup_nil T (ct_decidable_eq T)))).
  - change (Logic.eq (cl_map cid (if x \in s then undup s else x :: undup s))
      (I.List_dedup T (ct_decidable_eq T) (I.List_cons T x (cl_map cid s)))).
    case Hx: (x \in s).
    + rewrite (imported_eq_to_coq_eq _ _ (I.Prosa_Validation_ClassicJitterBertognaFpCompInterface_dedup_cons_mem
                 T (ct_decidable_eq T) x (cl_map cid s)
                 (prop_to_sprop _ _ (cbt_mem T x s _ (cl_lean_eq _ _ _ (Logic.eq_refl _))) Hx))).
      exact IH.
    + rewrite (imported_eq_to_coq_eq _ _ (I.Prosa_Validation_ClassicJitterBertognaFpCompInterface_dedup_cons_not_mem
                 T (ct_decidable_eq T) x (cl_map cid s) (cbt_notin_target T x s Hx))).
      change (Logic.eq (I.List_cons T x (cl_map cid (undup s))) (I.List_cons T x (I.List_dedup T (ct_decidable_eq T) (cl_map cid s)))).
      by rewrite IH.
Qed.

(* ------------------------------------------------------------------ *)
(** * Schedules, arrival sequences, parameters *)

Definition CbtParRel (T : Type) (pR : T -> nat) (pL : T -> Lean.Nat) : SProp := forall x, SubNatRel (pR x) (pL x).

Lemma cbt_forall_par (T : Type) (PR : (T -> nat) -> Prop) (PL : (T -> Lean.Nat) -> SProp) :
  (forall pR pL, CbtParRel T pR pL -> PropSPropRel (PR pR) (PL pL)) -> PropSPropRel (forall p, PR p) (forall p, PL p).
Proof.
  exact (cbt_forall_cover _ _ (CbtParRel T) (fun pR j => sub_nat_to_imported (pR j)) (fun pL j => sub_nat_to_rocq (pL j))
           (fun pR j => sub_nat_rel_canonical (pR j)) (fun pL j => sub_nat_rel_surjective (pL j)) PR PL).
Qed.

Section Sched.
Variables (Job : eqType) (nR : nat) (nL : Lean.Nat).
Hypothesis Hn : SubNatRel nR nL.
Notation dJ := (ct_decidable_eq Job).
Notation LSched := (I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_schedule Job dJ nL).

Definition CbtSchedRel (sR : Schedule.schedule Job nR) (sL : LSched) : SProp :=
  forall oR oL, CoOrdRel nR nL oR oL -> forall tR tL, SubNatRel tR tL -> Lean.eq (cl_opt (sR oR tR)) (sL oL tL).

Definition cbt_sched_to_target (sR : Schedule.schedule Job nR) : LSched :=
  fun oL tL => cl_opt (sR (co_fin_to_ord nR nL Hn oL) (sub_nat_to_rocq tL)).

Definition cbt_sched_to_source (sL : LSched) : Schedule.schedule Job nR :=
  fun oR tR => cl_unopt (sL (co_ord_to_fin nR nL Hn oR) (sub_nat_to_imported tR)).

Lemma cbt_sched_canonical sR : CbtSchedRel sR (cbt_sched_to_target sR).
Proof.
  intros oR oL Ho tR tL Ht. apply: coq_eq_to_imported_eq. rewrite /cbt_sched_to_target (co_nat_input _ _ Ht).
  by rewrite (co_ord_eq _ _ _ _ _ Ho (co_ord_surjective nR nL Hn oL)).
Qed.

Lemma cbt_sched_surjective sL : CbtSchedRel (cbt_sched_to_source sL) sL.
Proof.
  intros oR oL Ho tR tL Ht. apply: coq_eq_to_imported_eq. rewrite /cbt_sched_to_source cl_opt_unopt.
  rewrite (co_nat_logic _ _ Ht). by rewrite (co_fin_rel_eq _ _ _ _ _ (co_ord_canonical nR nL Hn oR) Ho).
Qed.

Lemma cbt_forall_sched (PR : Schedule.schedule Job nR -> Prop) (PL : LSched -> SProp) :
  (forall sR sL, CbtSchedRel sR sL -> PropSPropRel (PR sR) (PL sL)) -> PropSPropRel (forall s, PR s) (forall s, PL s).
Proof. exact (cbt_forall_cover _ _ CbtSchedRel cbt_sched_to_target cbt_sched_to_source cbt_sched_canonical cbt_sched_surjective PR PL). Qed.

End Sched.

Section Arr.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).
Notation LArr := (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrival_sequence Job dJ).

Definition CbtArrRel (aR : ArrivalSequence.arrival_sequence Job) (aL : LArr) : SProp :=
  forall tR tL, SubNatRel tR tL -> ClListRel cid (aR tR) (aL tL).

Definition cbt_arr_to_target (aR : ArrivalSequence.arrival_sequence Job) : LArr :=
  fun tL => cl_map cid (aR (sub_nat_to_rocq tL)).

Definition cbt_arr_to_source (aL : LArr) : ArrivalSequence.arrival_sequence Job :=
  fun tR => cl_unmap cid (aL (sub_nat_to_imported tR)).

Lemma cbt_arr_canonical aR : CbtArrRel aR (cbt_arr_to_target aR).
Proof.
  intros tR tL Ht. have E := co_nat_logic _ _ Ht. subst tL.
  apply: coq_eq_to_imported_eq. rewrite /cbt_arr_to_target sub_nat_rocq_roundtrip. reflexivity.
Qed.

Lemma cbt_arr_surjective aL : CbtArrRel (cbt_arr_to_source aL) aL.
Proof.
  intros tR tL Ht. have E := co_nat_logic _ _ Ht. subst tL.
  apply: coq_eq_to_imported_eq. exact (cl_map_unmap cid cid (fun _ => Logic.eq_refl _) _).
Qed.

Lemma cbt_arrives_in aR aL (Ha : CbtArrRel aR aL) j :
  PropSPropRel (ArrivalSequence.arrives_in aR j)
    (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrives_in Job dJ aL j).
Proof. apply: ct_exists_nat => tR tL Ht. exact (cbt_mem Job j _ _ (Ha tR tL Ht)). Qed.

End Arr.

(* ------------------------------------------------------------------ *)
(** * Definitions *)

Section Defs.
Variables (Job : eqType) (nR : nat) (nL : Lean.Nat).
Hypothesis Hn : SubNatRel nR nL.
Notation dJ := (ct_decidable_eq Job).
Variables (sR : Schedule.schedule Job nR)
  (sL : I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_schedule Job dJ nL).
Hypothesis Hs : CbtSchedRel Job nR nL sR sL.

Lemma cbt_GS_scheduled_on j oR oL (Ho : CoOrdRel nR nL oR oL) tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (Schedule.scheduled_on sR j oR tR)
    (I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_scheduled_on Job dJ nL sL j oL tL).
Proof.
  apply: ct_decide_bool.
  exact (cbt_tr (Hs oR oL Ho tR tL Ht) (fun z => PropSPropRel (sR oR tR == Some j) (Lean.eq z (cl_opt (Some j))))
           (cbt_opt_eqb_rel Job (sR oR tR) (Some j))).
Qed.

Lemma cbt_GS_scheduled j tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (Schedule.scheduled sR j tR)
    (I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_scheduled Job dJ nL sL j tL).
Proof.
  apply: (co_exists_rel nR nL Hn). intros oR oL Ho. exact (cbt_GS_scheduled_on j oR oL Ho tR tL Ht).
Qed.

Lemma cbt_GS_service_at j tR tL (Ht : SubNatRel tR tL) :
  SubNatRel (Schedule.service_at sR j tR)
    (I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_service_at Job dJ nL sL j tL).
Proof.
  apply: coq_eq_to_imported_eq.
  rewrite (imported_eq_to_coq_eq _ _ (I.Prosa_Validation_ClassicJitterBertognaFpCompInterface_service_at_sum Job dJ nL sL j tL)).
  apply: imported_eq_to_coq_eq.
  rewrite /Schedule.service_at big_mkcond /=.
  apply: (co_sum_rel nR nL Hn). intros oR oL Ho.
  have H := cbt_GS_scheduled_on j oR oL Ho tR tL Ht.
  rewrite (ct_bool_rel_logic _ _ H). destruct (Schedule.scheduled_on sR j oR tR).
  - exact (sub_nat_rel_canonical 1).
  - exact (sub_nat_rel_canonical 0).
Qed.

Lemma cbt_service_at_fun j : CbtFunRel (fun t => Schedule.service_at sR j t)
    (fun t => I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_service_at Job dJ nL sL j t).
Proof. intros kR kL Hk. exact (cbt_GS_service_at j kR kL Hk). Qed.

Lemma cbt_GS_service j tR tL (Ht : SubNatRel tR tL) :
  SubNatRel (Schedule.service sR j tR)
    (I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_service Job dJ nL sL j tL).
Proof. exact (cbt_ico 0 _ tR tL _ _ (sub_nat_rel_canonical 0) Ht (cbt_service_at_fun j)). Qed.

Lemma cbt_GS_completed cR cL (Hc : CbtParRel Job cR cL) j tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (Schedule.completed cR sR j tR)
    (I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_completed Job dJ cL nL sL j tL).
Proof. exact (ct_decide_le _ _ _ _ (Hc j) (cbt_GS_service j tR tL Ht)). Qed.

Lemma cbt_GS_sequential_jobs :
  PropSPropRel (Schedule.sequential_jobs sR)
    (I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_sequential_jobs Job dJ nL sL).
Proof.
  apply: ct_forall_identity => j. apply: ct_forall_nat => tR tL Ht.
  apply: (co_forall_ord nR nL Hn) => o1R o1L H1. apply: (co_forall_ord nR nL Hn) => o2R o2L H2.
  apply: ct_imp.
  { exact (cbt_tr (Hs o1R o1L H1 tR tL Ht) (fun z => PropSPropRel (sR o1R tR = Some j) (Lean.eq z (cl_opt (Some j))))
             (cbt_opt_eq_rel Job (sR o1R tR) (Some j))). }
  apply: ct_imp.
  { exact (cbt_tr (Hs o2R o2L H2 tR tL Ht) (fun z => PropSPropRel (sR o2R tR = Some j) (Lean.eq z (cl_opt (Some j))))
             (cbt_opt_eq_rel Job (sR o2R tR) (Some j))). }
  exact (co_ord_eq_rel _ _ _ _ _ _ H1 H2).
Qed.

Lemma cbt_GS_completed_jobs_dont_execute cR cL (Hc : CbtParRel Job cR cL) :
  PropSPropRel (Schedule.completed_jobs_dont_execute cR sR)
    (I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_completed_jobs_dont_execute Job dJ cL nL sL).
Proof.
  apply: ct_forall_identity => j. apply: ct_forall_nat => tR tL Ht.
  exact (sub_nat_le_correspondence _ _ _ _ (cbt_GS_service j tR tL Ht) (Hc j)).
Qed.

Lemma cbt_GS_jobs_come_from_arrival_sequence arrR arrL (Harr : CbtArrRel Job arrR arrL) :
  PropSPropRel (Schedule.jobs_come_from_arrival_sequence sR arrR)
    (I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_jobs_come_from_arrival_sequence Job dJ nL sL arrL).
Proof.
  apply: ct_forall_identity => j. apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (ct_bool_truth _ _ (cbt_GS_scheduled j tR tL Ht)).
  exact (cbt_arrives_in Job arrR arrL Harr j).
Qed.

End Defs.

Section TaskDefs.
Variables (Task Job : eqType) (nR : nat) (nL : Lean.Nat).
Hypothesis Hn : SubNatRel nR nL.
Notation dT := (ct_decidable_eq Task).
Notation dJ := (ct_decidable_eq Job).
Variables (sR : Schedule.schedule Job nR)
  (sL : I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_schedule Job dJ nL).
Hypothesis Hs : CbtSchedRel Job nR nL sR sL.
Variable job_task : Job -> Task.

End TaskDefs.

Lemma cbt_GS_processor nR nL (Hn : SubNatRel nR nL) :
  And (forall o : Schedule.processor nR, CoOrdRel nR nL o (co_ord_to_fin nR nL Hn o))
      (forall o : I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_processor nL,
         CoOrdRel nR nL (co_fin_to_ord nR nL Hn o) o).
Proof. exact (And_intro _ _ (co_ord_canonical nR nL Hn) (co_ord_surjective nR nL Hn)). Qed.

Lemma cbt_GS_schedule (Job : eqType) nR nL (Hn : SubNatRel nR nL) :
  And (forall s : Schedule.schedule Job nR, CbtSchedRel Job nR nL s (cbt_sched_to_target Job nR nL Hn s))
      (forall s : I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_schedule Job (ct_decidable_eq Job) nL,
         CbtSchedRel Job nR nL (cbt_sched_to_source Job nR nL Hn s) s).
Proof. exact (And_intro _ _ (cbt_sched_canonical Job nR nL Hn) (cbt_sched_surjective Job nR nL Hn)). Qed.

(* ------------------------------------------------------------------ *)
(** * Statements *)

(** The common prefix [forall num_cpus (sched : schedule Job num_cpus)]. *)
Lemma cbt_forall_ncpus_sched (Job : eqType)
    (PR : forall n : nat, Schedule.schedule Job n -> Prop)
    (PL : forall n : Lean.Nat, I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_schedule Job (ct_decidable_eq Job) n -> SProp) :
  (forall nR nL (Hn : SubNatRel nR nL) sR sL, CbtSchedRel Job nR nL sR sL -> PropSPropRel (PR nR sR) (PL nL sL)) ->
  PropSPropRel (forall n s, PR n s) (forall n s, PL n s).
Proof.
  intro H. apply: ct_forall_nat => nR nL Hn. exact (cbt_forall_sched Job nR nL Hn _ _ (H nR nL Hn)).
Qed.

Section GjschedDefs.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).

Lemma cbt_GJ_actual_arrival aR aL (Ha : CbtParRel Job aR aL) jjR jjL (Hjj : CbtParRel Job jjR jjL) j :
  SubNatRel (ScheduleWithJitter.actual_arrival aR jjR j) (I.Prosa_Classic_Model_Schedule_Global_Jitter_Schedule_ScheduleWithJitter_actual_arrival Job dJ aL jjL j).
Proof. exact (sub_add_correspondence _ _ _ _ (Ha j) (Hjj j)). Qed.

Lemma cbt_GJ_jitter_has_passed aR aL (Ha : CbtParRel Job aR aL) jjR jjL (Hjj : CbtParRel Job jjR jjL) j
    tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (ScheduleWithJitter.jitter_has_passed aR jjR j tR) (I.Prosa_Classic_Model_Schedule_Global_Jitter_Schedule_ScheduleWithJitter_jitter_has_passed Job dJ aL jjL j tL).
Proof. exact (ct_decide_le _ _ _ _ (cbt_GJ_actual_arrival aR aL Ha jjR jjL Hjj j) Ht). Qed.

Section GjschedSched.
Variables (nR : nat) (nL : Lean.Nat).
Hypothesis Hn : SubNatRel nR nL.
Variables (sR : Schedule.schedule Job nR)
  (sL : I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_schedule Job dJ nL).
Hypothesis Hs : CbtSchedRel Job nR nL sR sL.

Lemma cbt_GJ_pending aR aL (Ha : CbtParRel Job aR aL) cR cL (Hc : CbtParRel Job cR cL)
    jjR jjL (Hjj : CbtParRel Job jjR jjL) j tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (ScheduleWithJitter.pending aR cR jjR sR j tR) (I.Prosa_Classic_Model_Schedule_Global_Jitter_Schedule_ScheduleWithJitter_pending Job dJ aL cL jjL nL sL j tL).
Proof.
  exact (ct_bool_and _ _ _ _ (cbt_GJ_jitter_has_passed aR aL Ha jjR jjL Hjj j tR tL Ht)
           (ct_bool_not _ _ (cbt_GS_completed Job nR nL Hn sR sL Hs cR cL Hc j tR tL Ht))).
Qed.

Lemma cbt_GJ_backlogged aR aL (Ha : CbtParRel Job aR aL) cR cL (Hc : CbtParRel Job cR cL)
    jjR jjL (Hjj : CbtParRel Job jjR jjL) j tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (ScheduleWithJitter.backlogged aR cR jjR sR j tR) (I.Prosa_Classic_Model_Schedule_Global_Jitter_Schedule_ScheduleWithJitter_backlogged Job dJ aL cL jjL nL sL j tL).
Proof.
  exact (ct_bool_and _ _ _ _ (cbt_GJ_pending aR aL Ha cR cL Hc jjR jjL Hjj j tR tL Ht)
           (ct_bool_not _ _ (cbt_GS_scheduled Job nR nL Hn sR sL Hs j tR tL Ht))).
Qed.

Lemma cbt_GJ_jobs_execute_after_jitter aR aL (Ha : CbtParRel Job aR aL) jjR jjL (Hjj : CbtParRel Job jjR jjL) :
  PropSPropRel (ScheduleWithJitter.jobs_execute_after_jitter aR jjR sR) (I.Prosa_Classic_Model_Schedule_Global_Jitter_Schedule_ScheduleWithJitter_jobs_execute_after_jitter Job dJ aL jjL nL sL).
Proof.
  apply: ct_forall_identity => j. apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (ct_bool_truth _ _ (cbt_GS_scheduled Job nR nL Hn sR sL Hs j tR tL Ht)).
  exact (ct_bool_truth _ _ (cbt_GJ_jitter_has_passed aR aL Ha jjR jjL Hjj j tR tL Ht)).
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
Hypothesis Hs : CbtSchedRel Job nR nL sR sL.
Variable job_task : Job -> Task.

End GjschedTaskDefs.

(* ------------------------------------------------------------------ *)
(** * Generic covers and helpers *)

Lemma cjg_forall_cover (A B : Type) (Rel : A -> B -> SProp) (toB : A -> B) (toA : B -> A)
    (HB : forall a, Rel a (toB a)) (HA : forall b, Rel (toA b) b) (PR : A -> Prop) (PL : B -> SProp) :
  (forall a b, Rel a b -> PropSPropRel (PR a) (PL b)) -> PropSPropRel (forall a, PR a) (forall b, PL b).
Proof.
  intro H. apply prop_sprop_rel_intro.
  - intros HR b. exact (prop_to_sprop _ _ (H _ _ (HA b)) (HR _)).
  - intro HL. apply strictly_inhabits. intro a. exact (sprop_to_prop _ _ (H _ _ (HB a)) (HL _)).
Qed.

Lemma cjg_false_rel : PropSPropRel Logic.False I.False.
Proof.
  apply prop_sprop_rel_intro.
  - exact ct_coq_false_to_target.
  - exact ct_target_false_to_strict.
Qed.

Lemma cjg_ne (T : Type) (x y : T) : PropSPropRel (x <> y) (I.Ne T x y).
Proof. exact (ct_imp _ _ _ _ (ct_eq_rel T x y) cjg_false_rel). Qed.

Lemma cjg_mem (T : eqType) x s sL : ClListRel cid s sL ->
  PropSPropRel (x \in s) (I.Membership_mem T (I.List T) (I.List_instMembership T) sL x).
Proof. exact (cl_mem_rel_list T T cid cid (fun _ => Logic.eq_refl _) x s sL). Qed.

Lemma cjg_uniq (T : eqType) s sL : ClListRel cid s sL -> PropSPropRel (uniq s) (I.List_Nodup T sL).
Proof. exact (cl_uniq_rel_list T T cid cid (fun _ => Logic.eq_refl _) (fun _ => Logic.eq_refl _) s sL). Qed.

Lemma cjg_unmap_rel (T : Type) (l : I.List T) : ClListRel cid (cl_unmap cid l) l.
Proof. apply: coq_eq_to_imported_eq. exact (cl_map_unmap cid cid (fun _ => Logic.eq_refl _) l). Qed.

Lemma cjg_cl_map_inj (T : Type) (s1 s2 : seq T) : Logic.eq (cl_map cid s1) (cl_map cid s2) -> Logic.eq s1 s2.
Proof.
  intro E. rewrite -(cl_unmap_map cid cid (fun _ => Logic.eq_refl _) s1) -(cl_unmap_map cid cid (fun _ => Logic.eq_refl _) s2).
  by rewrite E.
Qed.

Lemma cjg_succ_rel nR nL : SubNatRel nR nL ->
  SubNatRel nR.+1 (I.HAdd_hAdd_inst7 Lean.Nat Lean.Nat Lean.Nat (I.instHAdd_inst1 Lean.Nat I.instAddNat) nL
                     (I.OfNat_ofNat_inst1 Lean.Nat 1 (I.instOfNatNat 1))).
Proof. intro Hn. exact (sub_imported_eq_congr Lean.Nat_succ _ _ Hn). Qed.

(* ------------------------------------------------------------------ *)
(** * Big concatenation over a half-open interval (as in the accepted arrival_sequence certificate) *)

Lemma cjg_forall_list (T : Type) (PR : seq T -> Prop) (PL : I.List T -> SProp) :
  (forall sR sL, ClListRel (B := T) cid sR sL -> PropSPropRel (PR sR) (PL sL)) -> PropSPropRel (forall s, PR s) (forall s, PL s).
Proof.
  exact (cjg_forall_cover _ _ (fun sR sL => ClListRel (B := T) cid sR sL) (cl_map cid) (cl_unmap cid)
           (fun s => @Lean.eq_refl _ _) (fun l => cjg_unmap_rel T l) PR PL).
Qed.

(* ------------------------------------------------------------------ *)
(** * Stable sorting: MathComp [sort] against the core [List.mergeSort] *)

Section SortUniq.
Variables (T : eqType) (f : T -> nat).
Notation leT := (fun a b : T => f a <= f b).
Notation cls x := (fun y : T => f y == f x).

Lemma cjg_leT_trans : transitive leT.
Proof. move=> y x z. exact: leq_trans. Qed.

Lemma cjg_leT_total : total leT.
Proof. move=> a b. exact: leq_total. Qed.

Lemma cjg_class_sorted x : forall l : seq T, all (cls x) l -> sorted leT l.
Proof.
  case => [|a l] //= /andP [Ha Hl]. elim: l a Ha Hl => [|b l IH] a Ha //= /andP [Hb Hl].
  rewrite (eqP Ha) (eqP Hb) leqnn /=. exact: IH.
Qed.

Lemma cjg_sort_filter_class s x : filter (cls x) (sort leT s) = filter (cls x) s.
Proof.
  rewrite (filter_sort cjg_leT_total cjg_leT_trans).
  apply: (sorted_sort cjg_leT_trans). apply: cjg_class_sorted. exact: filter_all.
Qed.

Lemma cjg_sorted_class_uniq : forall u t : seq T, sorted leT u -> sorted leT t ->
  (forall x, filter (cls x) u = filter (cls x) t) -> u = t.
Proof.
  elim => [|a u IH] t Su St H.
  { case: t St H => [//|b t] St H. by have := H b; rewrite /= eqxx. }
  case: t St H => [|b t] St H; first by have := H a; rewrite /= eqxx.
  have Ma : all (leT a) u := order_path_min cjg_leT_trans Su.
  have Mb : all (leT b) t := order_path_min cjg_leT_trans St.
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

Lemma cjg_sort_unique (u s : seq T) : sorted leT u -> (forall x, filter (cls x) u = filter (cls x) s) -> u = sort leT s.
Proof.
  move=> Su H. apply: cjg_sorted_class_uniq => //.
  - exact: (sort_sorted cjg_leT_total).
  - move=> x. by rewrite cjg_sort_filter_class H.
Qed.

End SortUniq.

Section Chain.
Variables (T : Type) (leR : T -> T -> bool) (leL : T -> T -> I.Bool).
Hypothesis HR : forall a b, CtBoolRel (leR a b) (leL a b).
Notation RL := (fun a b : T => Lean.eq (leL a b) I.Bool_true).

Inductive CjgTrue : SProp := cjg_true_intro.

Definition cjg_chain_head (x y : T) (l : I.List T) (H : I.List_IsChain T RL (I.List_cons T x (I.List_cons T y l))) : RL x y :=
  match H in I.List_IsChain _ _ L
    return (match L with I.List_cons a (I.List_cons b _) => RL a b | _ => CjgTrue end) with
  | I.List_IsChain_nil => cjg_true_intro
  | I.List_IsChain_singleton _ => cjg_true_intro
  | I.List_IsChain_cons_cons a b l h _ => h
  end.

Definition cjg_chain_tail (x y : T) (l : I.List T) (H : I.List_IsChain T RL (I.List_cons T x (I.List_cons T y l))) :
    I.List_IsChain T RL (I.List_cons T y l) :=
  match H in I.List_IsChain _ _ L
    return (match L with I.List_cons _ (I.List_cons b l') => I.List_IsChain T RL (I.List_cons T b l') | _ => CjgTrue end) with
  | I.List_IsChain_nil => cjg_true_intro
  | I.List_IsChain_singleton _ => cjg_true_intro
  | I.List_IsChain_cons_cons a b l _ t => t
  end.

Fixpoint cjg_path_backward (x : T) (s : seq T) : I.List_IsChain T RL (I.List_cons T x (cl_map cid s)) -> StrictlyInhabited (path leR x s) :=
  match s as s0 return I.List_IsChain T RL (I.List_cons T x (cl_map cid s0)) -> StrictlyInhabited (path leR x s0) with
  | [::] => fun _ => strictly_inhabits (Logic.eq_refl true)
  | y :: s' => fun H =>
      match cjg_path_backward y s' (cjg_chain_tail x y _ H) with
      | strictly_inhabits Hp =>
          strictly_inhabits (introT andP (conj (sprop_to_prop _ _ (ct_bool_truth _ _ (HR x y)) (cjg_chain_head x y _ H)) Hp))
      end
  end.

Lemma cjg_sorted_backward s : I.List_IsChain T RL (cl_map cid s) -> StrictlyInhabited (sorted leR s).
Proof.
  destruct s as [|x s].
  - intros _. exact (strictly_inhabits (Logic.eq_refl true)).
  - exact (cjg_path_backward x s).
Qed.

End Chain.

Section Sort.
Variables (T : eqType) (f : T -> nat) (fL : T -> Lean.Nat).
Hypothesis Hf : forall x, SubNatRel (f x) (fL x).
Notation leL := (fun j j' : T => I.Decidable_decide (I.LE_le_inst1 Lean.Nat I.instLENat (fL j) (fL j')) (I.Nat_decLe (fL j) (fL j'))).
Notation clsL x := (fun y : T => I.Decidable_decide (Lean.eq (fL y) (fL x)) (I.instDecidableEqNat (fL y) (fL x))).

Lemma cjg_sort_rel s sL : ClListRel cid s sL ->
  ClListRel cid (sort (fun j j' => f j <= f j') s) (I.List_mergeSort T sL leL).
Proof.
  intro Hs.
  pose m := I.List_mergeSort T sL leL. pose u := cl_unmap cid m.
  have Hu : ClListRel cid u m := cjg_unmap_rel T m.
  have Su : sorted (fun a b => f a <= f b) u :=
    interpret_strict _
      (cjg_sorted_backward T (fun a b => f a <= f b) leL (fun a b => ct_decide_le _ _ _ _ (Hf a) (Hf b)) u
         (match Hu in Lean.eq _ z
                return I.List_IsChain T (fun a b => Lean.eq (leL a b) I.Bool_true) z ->
                       I.List_IsChain T (fun a b => Lean.eq (leL a b) I.Bool_true) (cl_map cid u) with
          | Lean.eq_refl => fun h => h
          end (I.Prosa_Validation_ClassicJitterBertognaFpCompInterface_mergeSort_isChain T fL sL))).
  have Fu : forall x, filter (fun y => f y == f x) u = filter (fun y => f y == f x) s.
  { intro x. apply: cjg_cl_map_inj.
    have Hp : forall y, CtBoolRel (f y == f x) (clsL x y) := fun y => ct_decide_eq_nat _ _ _ _ (Hf y) (Hf x).
    refine (Logic.eq_trans (cl_filter cid (fun y => f y == f x) (clsL x) Hp u)
              (Logic.eq_trans _ (Logic.eq_sym (cl_filter cid (fun y => f y == f x) (clsL x) Hp s)))).
    refine (Logic.eq_trans (f_equal (I.List_filter T (clsL x)) (Logic.eq_sym (cl_list_logic _ _ _ Hu)))
              (Logic.eq_trans _ (f_equal (I.List_filter T (clsL x)) (cl_list_logic _ _ _ Hs)))).
    exact (imported_eq_to_coq_eq _ _ (I.Prosa_Validation_ClassicJitterBertognaFpCompInterface_mergeSort_filter_class T fL x sL)). }
  have E := cjg_sort_unique T f u s Su Fu.
  apply: coq_eq_to_imported_eq. rewrite -E. exact (Logic.eq_sym (cl_list_logic _ _ _ Hu)).
Qed.

End Sort.

Lemma cjg_getD (T : Type) (s : seq T) sL (Hs : ClListRel cid s sL) (x0 : T) nR nL (Hn : SubNatRel nR nL) :
  Logic.eq (I.List_getD T sL nL x0) (nth x0 s nR).
Proof.
  rewrite (cl_list_logic _ _ _ Hs) (cl_nat_logic _ _ Hn). exact (Logic.eq_sym (cl_nth cid x0 s nR)).
Qed.

Lemma cjg_pred_rel nR nL : SubNatRel nR nL ->
  SubNatRel nR.-1 (ct_sub nL (I.OfNat_ofNat_inst1 Lean.Nat 1 (I.instOfNatNat 1))).
Proof.
  intro Hn. apply: coq_eq_to_imported_eq. rewrite -subn1.
  exact (imported_eq_to_coq_eq _ _ (ct_sub_rel _ _ _ _ Hn (sub_nat_rel_canonical 1))).
Qed.

(* ------------------------------------------------------------------ *)
(** * Sequence sums against [sumSeq] / [sumFiltered] (as in the accepted v0.6 request-bound-function certificates) *)

Section SeqSums.
Variable X : Type.
Variable FR : X -> nat.
Variable FL : X -> Lean.Nat.
Hypothesis HF : forall x, SubNatRel (FR x) (FL x).

Lemma cbt_sum_canonical (xs : seq X) :
  SubNatRel (\sum_(x <- xs) FR x) (I.Prosa_Util_Sum_sumSeq X (cl_map cid xs) FL).
Proof.
  induction xs as [|x xs IH].
  - rewrite big_nil.
    exact (sub_imported_eq_sym _ _ (I.Prosa_Validation_ClassicJitterBertognaFpCompInterface_production_sumSeq_nil X FL)).
  - rewrite big_cons. cbn [cl_map].
    refine (sub_imported_eq_trans _ _ _ _ (sub_imported_eq_sym _ _
      (I.Prosa_Validation_ClassicJitterBertognaFpCompInterface_production_sumSeq_cons X FL x (cl_map cid xs)))).
    exact (sub_add_correspondence _ _ _ _ (HF x) IH).
Qed.

Lemma cbt_sum_rel xsR xsL : ClListRel cid xsR xsL ->
  SubNatRel (\sum_(x <- xsR) FR x) (I.Prosa_Util_Sum_sumSeq X xsL FL).
Proof.
  intro Hxs.
  exact (sub_imported_eq_trans _ _ _ (cbt_sum_canonical xsR)
    (sub_imported_eq_congr (fun l => I.Prosa_Util_Sum_sumSeq X l FL) _ _ Hxs)).
Qed.

Variable PR : X -> bool.
Variable PL : X -> I.Bool.
Hypothesis HP : forall x, CtBoolRel (PR x) (PL x).

Lemma cbt_sum_filtered_canonical (xs : seq X) :
  SubNatRel (\sum_(x <- xs | PR x) FR x) (I.Prosa_Util_Sum_sumFiltered X (cl_map cid xs) PL FL).
Proof.
  induction xs as [|x xs IH].
  - rewrite big_nil.
    exact (sub_imported_eq_sym _ _ (I.Prosa_Validation_ClassicJitterBertognaFpCompInterface_production_sumFiltered_nil X PL FL)).
  - rewrite big_cons. cbn [cl_map].
    have Hx := HP x. unfold CtBoolRel in Hx.
    destruct (PR x).
    + refine (sub_imported_eq_trans _ _ _ _ (sub_imported_eq_sym _ _
        (I.Prosa_Validation_ClassicJitterBertognaFpCompInterface_production_sumFiltered_cons_true
          X PL FL x (cl_map cid xs) (sub_imported_eq_sym _ _ Hx)))).
      exact (sub_add_correspondence _ _ _ _ (HF x) IH).
    + exact (sub_imported_eq_trans _ _ _ IH (sub_imported_eq_sym _ _
        (I.Prosa_Validation_ClassicJitterBertognaFpCompInterface_production_sumFiltered_cons_false
          X PL FL x (cl_map cid xs) (sub_imported_eq_sym _ _ Hx)))).
Qed.

Lemma cbt_sum_filtered_rel xsR xsL : ClListRel cid xsR xsL ->
  SubNatRel (\sum_(x <- xsR | PR x) FR x) (I.Prosa_Util_Sum_sumFiltered X xsL PL FL).
Proof.
  intro Hxs.
  exact (sub_imported_eq_trans _ _ _ (cbt_sum_filtered_canonical xsR)
    (sub_imported_eq_congr (fun l => I.Prosa_Util_Sum_sumFiltered X l PL FL) _ _ Hxs)).
Qed.

End SeqSums.

Definition CbtPredRel (T : Type) (pR : T -> bool) (pL : T -> I.Bool) : SProp := forall x, CtBoolRel (pR x) (pL x).

Lemma cbt_forall_pred (T : Type) (PR : (T -> bool) -> Prop) (PL : (T -> I.Bool) -> SProp) :
  (forall pR pL, CbtPredRel T pR pL -> PropSPropRel (PR pR) (PL pL)) -> PropSPropRel (forall p, PR p) (forall p, PL p).
Proof.
  exact (cbt_forall_cover _ _ (CbtPredRel T) (fun pR x => ct_b2l (pR x)) (fun pL x => ct_l2b (pL x))
           (fun pR x => ct_bool_canonical _) (fun pL x => ct_bool_surjective _) PR PL).
Qed.

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

(** The imported [Job] definitions (as in the accepted classic job certificate). *)
Section JobDefs.
Notation c0 := (sub_nat_rel_canonical 0).
Variables (Task Job : eqType).
Notation dT := (ct_decidable_eq Task).
Notation dJ := (ct_decidable_eq Job).

Lemma cbt_J_job_cost_positive cR cL (Hc : CbtParRel Job cR cL) j :
  CtBoolRel (Job.job_cost_positive cR j) (I.Prosa_Classic_Model_Arrival_Basic_Job_Job_job_cost_positive Job dJ cL j).
Proof. exact (ct_decide_lt _ _ _ _ c0 (Hc j)). Qed.

Lemma cbt_J_job_deadline_positive dR dL (Hd : CbtParRel Job dR dL) j :
  CtBoolRel (Job.job_deadline_positive dR j) (I.Prosa_Classic_Model_Arrival_Basic_Job_Job_job_deadline_positive Job dJ dL j).
Proof. exact (ct_decide_lt _ _ _ _ c0 (Hd j)). Qed.

Lemma cbt_J_job_cost_le_deadline cR cL dR dL (Hc : CbtParRel Job cR cL) (Hd : CbtParRel Job dR dL) j :
  CtBoolRel (Job.job_cost_le_deadline cR dR j) (I.Prosa_Classic_Model_Arrival_Basic_Job_Job_job_cost_le_deadline Job dJ cL dL j).
Proof. exact (ct_decide_le _ _ _ _ (Hc j) (Hd j)). Qed.

Lemma cbt_J_valid_realtime_job cR cL dR dL (Hc : CbtParRel Job cR cL) (Hd : CbtParRel Job dR dL) j :
  PropSPropRel (Job.valid_realtime_job cR dR j) (I.Prosa_Classic_Model_Arrival_Basic_Job_Job_valid_realtime_job Job dJ cL dL j).
Proof.
  apply: ct_and; first exact (ct_bool_truth _ _ (cbt_J_job_cost_positive cR cL Hc j)).
  apply: ct_and; first exact (ct_bool_truth _ _ (cbt_J_job_cost_le_deadline cR cL dR dL Hc Hd j)).
  exact (ct_bool_truth _ _ (cbt_J_job_deadline_positive dR dL Hd j)).
Qed.

Lemma cbt_J_job_cost_le_task_cost tcR tcL (Htc : CbtParRel Task tcR tcL) cR cL (Hc : CbtParRel Job cR cL)
    (job_task : Job -> Task) j :
  CtBoolRel (Job.job_cost_le_task_cost tcR cR job_task j)
    (I.Prosa_Classic_Model_Arrival_Basic_Job_Job_job_cost_le_task_cost Task dT tcL Job dJ cL job_task j).
Proof. exact (ct_decide_le _ _ _ _ (Hc j) (Htc (job_task j))). Qed.

Lemma cbt_J_job_deadline_eq_task_deadline tdR tdL (Htd : CbtParRel Task tdR tdL) dR dL (Hd : CbtParRel Job dR dL)
    (job_task : Job -> Task) j :
  PropSPropRel (Job.job_deadline_eq_task_deadline tdR dR job_task j)
    (I.Prosa_Classic_Model_Arrival_Basic_Job_Job_job_deadline_eq_task_deadline Task dT tdL Job dJ dL job_task j).
Proof. exact (sub_nat_eq_correspondence _ _ _ _ (Hd j) (Htd (job_task j))). Qed.

Lemma cbt_J_valid_sporadic_job tcR tcL tdR tdL (Htc : CbtParRel Task tcR tcL) (Htd : CbtParRel Task tdR tdL)
    cR cL dR dL (Hc : CbtParRel Job cR cL) (Hd : CbtParRel Job dR dL) (job_task : Job -> Task) j :
  PropSPropRel (Job.valid_sporadic_job tcR tdR cR dR job_task j)
    (I.Prosa_Classic_Model_Arrival_Basic_Job_Job_valid_sporadic_job Task dT tcL tdL Job dJ cL dL job_task j).
Proof.
  apply: ct_and; first exact (cbt_J_valid_realtime_job cR cL dR dL Hc Hd j).
  apply: ct_and; first exact (ct_bool_truth _ _ (cbt_J_job_cost_le_task_cost tcR tcL Htc cR cL Hc job_task j)).
  exact (cbt_J_job_deadline_eq_task_deadline tdR tdL Htd dR dL Hd job_task j).
Qed.

End JobDefs.

(* ------------------------------------------------------------------ *)
(** * Workload (as in the accepted classic workload certificate) *)

Section WBWl.
Variables (Task Job : eqType) (nR : nat) (nL : Lean.Nat).
Hypothesis Hn : SubNatRel nR nL.
Notation dT := (ct_decidable_eq Task).
Notation dJ := (ct_decidable_eq Job).
Variables (sR : Schedule.schedule Job nR)
  (sL : I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_schedule Job dJ nL).
Hypothesis Hs : CbtSchedRel Job nR nL sR sL.
Variable job_task : Job -> Task.

End WBWl.

Lemma cbt_t2 t1R t1L dR dL (H1 : SubNatRel t1R t1L) (Hd : SubNatRel dR dL) :
  SubNatRel (t1R + dR) (I.HAdd_hAdd_inst7 Lean.Nat Lean.Nat Lean.Nat (I.instHAdd_inst1 Lean.Nat I.instAddNat) t1L dL).
Proof. exact (sub_add_correspondence _ _ _ _ H1 Hd). Qed.

Lemma cbt_add2 nR nL : SubNatRel nR nL ->
  SubNatRel nR.+2 (I.HAdd_hAdd_inst7 Lean.Nat Lean.Nat Lean.Nat (I.instHAdd_inst1 Lean.Nat I.instAddNat) nL
                     (I.OfNat_ofNat_inst1 Lean.Nat 2 (I.instOfNatNat 2))).
Proof.
  intro H. apply: coq_eq_to_imported_eq. rewrite -addn2.
  exact (imported_eq_to_coq_eq _ _ (sub_add_correspondence _ _ 2 _ H (sub_nat_rel_canonical 2))).
Qed.

(* ------------------------------------------------------------------ *)
(** * Task, job and arrival-model relations (as in the accepted classic task, job and task_arrival certificates) *)

Lemma cbt_forall_arr (Job : eqType) PR PL :
  (forall aR aL, CbtArrRel Job aR aL -> PropSPropRel (PR aR) (PL aL)) -> PropSPropRel (forall a, PR a) (forall a, PL a).
Proof. exact (cbt_forall_cover _ _ (CbtArrRel Job) (cbt_arr_to_target Job) (cbt_arr_to_source Job) (cbt_arr_canonical Job) (cbt_arr_surjective Job) PR PL). Qed.

Lemma cbt_valid_sporadic_job (Task Job : eqType) tcR tcL (Htc : CbtParRel Task tcR tcL) tdR tdL (Htd : CbtParRel Task tdR tdL)
    cR cL (Hc : CbtParRel Job cR cL) dR dL (Hd : CbtParRel Job dR dL) (job_task : Job -> Task) j :
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

Lemma cbt_valid_sporadic_job_with_jitter (Task Job : eqType) tcR tcL (Htc : CbtParRel Task tcR tcL) tdR tdL (Htd : CbtParRel Task tdR tdL)
    tjR tjL (Htj : CbtParRel Task tjR tjL) cR cL (Hc : CbtParRel Job cR cL) dR dL (Hd : CbtParRel Job dR dL) (job_task : Job -> Task)
    jjR jjL (Hjj : CbtParRel Job jjR jjL) j :
  PropSPropRel (JobWithJitter.valid_sporadic_job_with_jitter tcR tdR tjR cR dR job_task jjR j)
    (I.Prosa_Classic_Model_Schedule_Global_Jitter_Job_JobWithJitter_valid_sporadic_job_with_jitter Task (ct_decidable_eq Task) tcL tdL tjL Job (ct_decidable_eq Job) cL dL job_task jjL j).
Proof.
  apply: ct_and; first exact (cbt_valid_sporadic_job Task Job tcR tcL Htc tdR tdL Htd cR cL Hc dR dL Hd job_task j).
  exact (ct_bool_truth _ _ (ct_decide_le _ _ _ _ (Hjj j) (Htj (job_task j)))).
Qed.

Lemma cbt_valid_params (Task Job : eqType) tcR tcL (Htc : CbtParRel Task tcR tcL) tdR tdL (Htd : CbtParRel Task tdR tdL)
    tjR tjL (Htj : CbtParRel Task tjR tjL) cR cL (Hc : CbtParRel Job cR cL) dR dL (Hd : CbtParRel Job dR dL) (job_task : Job -> Task)
    jjR jjL (Hjj : CbtParRel Job jjR jjL) aR aL (Ha : CbtArrRel Job aR aL) :
  PropSPropRel (forall j, ArrivalSequence.arrives_in aR j -> JobWithJitter.valid_sporadic_job_with_jitter tcR tdR tjR cR dR job_task jjR j)
    (forall j, I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrives_in Job (ct_decidable_eq Job) aL j ->
       I.Prosa_Classic_Model_Schedule_Global_Jitter_Job_JobWithJitter_valid_sporadic_job_with_jitter Task (ct_decidable_eq Task) tcL tdL tjL Job (ct_decidable_eq Job) cL dL job_task jjL j).
Proof.
  apply: ct_forall_identity => j.
  exact (ct_imp _ _ _ _ (cbt_arrives_in Job aR aL Ha j)
           (cbt_valid_sporadic_job_with_jitter Task Job tcR tcL Htc tdR tdL Htd tjR tjL Htj cR cL Hc dR dL Hd job_task jjR jjL Hjj j)).
Qed.

Lemma cbt_sporadic_task_model (Task Job : eqType) tpR tpL (Htp : CbtParRel Task tpR tpL) jaR jaL (Hja : CbtParRel Job jaR jaL)
    (job_task : Job -> Task) aR aL (Ha : CbtArrRel Job aR aL) :
  PropSPropRel (TaskArrival.sporadic_task_model tpR jaR job_task aR)
    (I.Prosa_Classic_Model_Arrival_Basic_TaskArrival_TaskArrival_sporadic_task_model Task (ct_decidable_eq Task) tpL Job (ct_decidable_eq Job) jaL job_task aL).
Proof.
  apply: ct_forall_identity => j. apply: ct_forall_identity => j'.
  apply: ct_imp; first exact (cjg_ne Job j j').
  apply: ct_imp; first exact (cbt_arrives_in Job aR aL Ha j).
  apply: ct_imp; first exact (cbt_arrives_in Job aR aL Ha j').
  apply: ct_imp; first exact (ct_eq_rel Task (job_task j) (job_task j')).
  apply: ct_imp; first exact (sub_nat_le_correspondence _ _ _ _ (Hja j) (Hja j')).
  exact (sub_nat_le_correspondence _ _ _ _ (sub_add_correspondence _ _ _ _ (Hja j) (Htp (job_task j))) (Hja j')).
Qed.

Lemma cbt_valid_sporadic_task (Task : eqType) cR cL (Hc : CbtParRel Task cR cL) pR pL (Hp : CbtParRel Task pR pL)
    dR dL (Hd : CbtParRel Task dR dL) tsk :
  PropSPropRel (SporadicTask.is_valid_sporadic_task cR pR dR tsk)
    (I.Prosa_Classic_Model_Arrival_Basic_Task_SporadicTask_is_valid_sporadic_task Task (ct_decidable_eq Task) cL pL dL tsk).
Proof.
  apply: ct_and; first exact (ct_bool_truth _ _ (ct_decide_lt _ _ _ _ (sub_nat_rel_canonical 0) (Hc tsk))).
  apply: ct_and; first exact (ct_bool_truth _ _ (ct_decide_lt _ _ _ _ (sub_nat_rel_canonical 0) (Hp tsk))).
  apply: ct_and; first exact (ct_bool_truth _ _ (ct_decide_lt _ _ _ _ (sub_nat_rel_canonical 0) (Hd tsk))).
  apply: ct_and; first exact (ct_bool_truth _ _ (ct_decide_le _ _ _ _ (Hc tsk) (Hd tsk))).
  exact (ct_bool_truth _ _ (ct_decide_le _ _ _ _ (Hc tsk) (Hp tsk))).
Qed.

Lemma cbt_rt_bound (Task Job : eqType) nR nL (Hn : SubNatRel nR nL) sR sL (Hs : CbtSchedRel Job nR nL sR sL)
    jaR jaL (Hja : CbtParRel Job jaR jaL) cR cL (Hc : CbtParRel Job cR cL) (job_task : Job -> Task) aR aL (Ha : CbtArrRel Job aR aL)
    tjR tjL (Htj : CbtParRel Task tjR tjL) tsk t1R t1L dR dL RR RL (H1 : SubNatRel t1R t1L) (Hd : SubNatRel dR dL) (HR : SubNatRel RR RL) :
  PropSPropRel (forall j, ArrivalSequence.arrives_in aR j -> job_task j = tsk -> jaR j + tjR tsk + RR < t1R + dR ->
                  Schedule.completed cR sR j (jaR j + tjR tsk + RR))
    (forall j, I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrives_in Job (ct_decidable_eq Job) aL j ->
       Lean.eq (job_task j) tsk ->
       I.LT_lt_inst1 Lean.Nat I.instLTNat (I.HAdd_hAdd_inst7 Lean.Nat Lean.Nat Lean.Nat (I.instHAdd_inst1 Lean.Nat I.instAddNat)
           (I.HAdd_hAdd_inst7 Lean.Nat Lean.Nat Lean.Nat (I.instHAdd_inst1 Lean.Nat I.instAddNat) (jaL j) (tjL tsk)) RL)
         (I.HAdd_hAdd_inst7 Lean.Nat Lean.Nat Lean.Nat (I.instHAdd_inst1 Lean.Nat I.instAddNat) t1L dL) ->
       Lean.eq (I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_completed Job (ct_decidable_eq Job) cL nL sL j
          (I.HAdd_hAdd_inst7 Lean.Nat Lean.Nat Lean.Nat (I.instHAdd_inst1 Lean.Nat I.instAddNat)
             (I.HAdd_hAdd_inst7 Lean.Nat Lean.Nat Lean.Nat (I.instHAdd_inst1 Lean.Nat I.instAddNat) (jaL j) (tjL tsk)) RL)) I.Bool_true).
Proof.
  apply: ct_forall_identity => j.
  apply: ct_imp; first exact (cbt_arrives_in Job aR aL Ha j).
  apply: ct_imp; first exact (ct_eq_rel Task (job_task j) tsk).
  have HjR := sub_add_correspondence _ _ _ _ (sub_add_correspondence _ _ _ _ (Hja j) (Htj tsk)) HR.
  apply: ct_imp; first exact (sub_nat_lt_correspondence _ _ _ _ HjR (cbt_t2 _ _ _ _ H1 Hd)).
  exact (ct_bool_truth _ _ (cbt_GS_completed Job nR nL Hn sR sL Hs cR cL Hc j _ _ HjR)).
Qed.

(* ------------------------------------------------------------------ *)
(** * Definitions *)

(** [minn] against the core [Min.min] on [Nat] (as in the accepted classic global workload_bound certificate). *)
Lemma cbt_min_canonical (a b : nat) :
  Logic.eq ((I.Min_min_inst1 Lean.Nat I.instMinNat) (sub_nat_to_imported a) (sub_nat_to_imported b)) (sub_nat_to_imported (minn a b)).
Proof.
  have Hle := sub_nat_le_correspondence _ _ _ _ (sub_nat_rel_canonical a) (sub_nat_rel_canonical b).
  have -> : Logic.eq ((I.Min_min_inst1 Lean.Nat I.instMinNat) (sub_nat_to_imported a) (sub_nat_to_imported b))
      (I.ite Lean.Nat (I.LE_le_inst1 Lean.Nat I.instLENat (sub_nat_to_imported a) (sub_nat_to_imported b))
         (I.Nat_decLe (sub_nat_to_imported a) (sub_nat_to_imported b)) (sub_nat_to_imported a) (sub_nat_to_imported b))
    by reflexivity.
  destruct (I.Nat_decLe (sub_nat_to_imported a) (sub_nat_to_imported b)) as [h|h].
  - have Hab : ~~ (a <= b)%nat.
    { apply/negP => Hs. exact (interpret_strict _ (ct_target_false_to_strict (h (prop_to_sprop _ _ Hle Hs)))). }
    rewrite -ltnNge in Hab. rewrite (minn_idPr (ltnW Hab)). reflexivity.
  - have Hab : (a <= b)%nat := sprop_to_prop _ _ Hle h. rewrite (minn_idPl Hab). reflexivity.
Qed.

Lemma cbt_min_rel aR aL bR bL : SubNatRel aR aL -> SubNatRel bR bL -> SubNatRel (minn aR bR) ((I.Min_min_inst1 Lean.Nat I.instMinNat) aL bL).
Proof.
  intros Ha Hb. rewrite -(imported_eq_to_coq_eq _ _ Ha) -(imported_eq_to_coq_eq _ _ Hb).
  apply: coq_eq_to_imported_eq. exact (Logic.eq_sym (cbt_min_canonical aR bR)).
Qed.

Lemma cbt_WB_WorkloadBoundJitter_max_jobs_jitter (Task : eqType) cR cL (Hc : CbtParRel Task cR cL) pR pL (Hp : CbtParRel Task pR pL)
    jR jL (Hj : CbtParRel Task jR jL) tsk RR RL (HR : SubNatRel RR RL) dR dL (Hd : SubNatRel dR dL) :
  SubNatRel (WorkloadBoundJitter.max_jobs_jitter cR pR jR tsk RR dR) (I.Prosa_Classic_Analysis_Global_Jitter_WorkloadBound_WorkloadBoundJitter_max_jobs_jitter Task (ct_decidable_eq Task) cL pL jL tsk RL dL).
Proof.
  exact (dm_div_floor_correspondence _ _ _ _
           (dm_sub_correspondence _ _ _ _ (dm_add_correspondence _ _ _ _ (dm_add_correspondence _ _ _ _ Hd (Hj tsk)) HR) (Hc tsk)) (Hp tsk)).
Qed.

Lemma cbt_WB_WorkloadBoundJitter_W_jitter (Task : eqType) cR cL (Hc : CbtParRel Task cR cL) pR pL (Hp : CbtParRel Task pR pL)
    jR jL (Hj : CbtParRel Task jR jL) tsk RR RL (HR : SubNatRel RR RL) dR dL (Hd : SubNatRel dR dL) :
  SubNatRel (WorkloadBoundJitter.W_jitter cR pR jR tsk RR dR) (I.Prosa_Classic_Analysis_Global_Jitter_WorkloadBound_WorkloadBoundJitter_W_jitter Task (ct_decidable_eq Task) cL pL jL tsk RL dL).
Proof.
  have Hm := cbt_WB_WorkloadBoundJitter_max_jobs_jitter Task cR cL Hc pR pL Hp jR jL Hj tsk RR RL HR dR dL Hd.
  exact (dm_add_correspondence _ _ _ _
           (cbt_min_rel _ _ _ _ (Hc tsk)
              (dm_sub_correspondence _ _ _ _
                 (dm_sub_correspondence _ _ _ _ (dm_add_correspondence _ _ _ _ (dm_add_correspondence _ _ _ _ Hd (Hj tsk)) HR) (Hc tsk))
                 (dm_mul_correspondence _ _ _ _ Hm (Hp tsk))))
           (dm_mul_correspondence _ _ _ _ Hm (Hc tsk))).
Qed.

Module GJP := prosa.classic.model.schedule.global.jitter.platform.Platform.

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

Section PLSched.
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

End PLSched.

Section PLArr.
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

End PLArr.

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

Section PLDefs.
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
  rewrite (imported_eq_to_coq_eq _ _ (I.Prosa_Validation_ClassicJitterBertognaFpCompInterface_service_at_sum Job dJ nL sL j tL)).
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

End PLDefs.

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

Definition CpJldpRel (T : Type) (rR : nat -> T -> T -> bool) (rL : Lean.Nat -> T -> T -> I.Bool) : SProp :=
  forall tR tL, SubNatRel tR tL -> CpRelRel T (rR tR) (rL tL).

Section PLDefs.
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
Notation bl := (cbt_GJ_backlogged Job nR nL Hn sR sL Hs jaR jaL Hja cR cL Hc jjR jjL Hjj).
Notation son := (cf_Schedule_scheduled_on Job nR nL sR sL Hs).
Notation sch := (cf_Schedule_scheduled Job nR nL Hn sR sL Hs).

Lemma cbt_PL_Platform_work_conserving :
  PropSPropRel (GJP.work_conserving jaR cR jjR aR sR) (I.Prosa_Classic_Model_Schedule_Global_Jitter_Platform_Platform_work_conserving Job dJ jaL cL jjL aL nL sL).
Proof.
  apply: ct_forall_identity => j. apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (cs_arrives_in Job aR aL Ha j).
  apply: ct_imp; first exact (ct_bool_truth _ _ (bl j tR tL Ht)).
  apply: (co_forall_ord nR nL Hn) => oR oL Ho.
  apply: ct_exists_identity => j_other.
  exact (ct_bool_truth _ _ (son j_other oR oL Ho tR tL Ht)).
Qed.

Lemma cbt_PL_Platform_respects_FP_policy hpR hpL (Hhp : CpRelRel Task hpR hpL) :
  PropSPropRel (GJP.respects_FP_policy jaR cR job_task jjR aR sR hpR)
    (I.Prosa_Classic_Model_Schedule_Global_Jitter_Platform_Platform_respects_FP_policy Task Job dT dJ jaL cL job_task jjL aL nL sL hpL).
Proof.
  apply: ct_forall_identity => j. apply: ct_forall_identity => j_hp. apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (cs_arrives_in Job aR aL Ha j).
  apply: ct_imp; first exact (ct_bool_truth _ _ (bl j tR tL Ht)).
  apply: ct_imp; first exact (ct_bool_truth _ _ (sch j_hp tR tL Ht)).
  exact (ct_bool_truth _ _ (Hhp (job_task j_hp) (job_task j))).
Qed.

End PLDefs.

Module GJI := prosa.classic.model.schedule.global.jitter.interference.Interference.

Section INTSched.
Variables (Job : eqType) (nR : nat) (nL : Lean.Nat).
Hypothesis Hn : SubNatRel nR nL.
Notation dJ := (ct_decidable_eq Job).
Notation LSched := (I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_schedule Job dJ nL).

End INTSched.

Definition CsNatFamRel (A : Type) (fR : nat -> seq A) (fL : Lean.Nat -> I.List A) : SProp :=
  forall nR nL, SubNatRel nR nL -> ClListRel cid (fR nR) (fL nL).

Lemma cs_bigcat_nat_rel (A : Type) fR fL (Hf : CsNatFamRel A fR fL) mR mL nR nL :
  SubNatRel mR mL -> SubNatRel nR nL ->
  ClListRel cid (\big[cat/[::]]_(mR <= t < nR) fR t) (I.Prosa_Util_Notation_bigCat A mL nL fL).
Proof.
  intros Hm Hn. have E1 := co_nat_logic _ _ Hm. have E2 := co_nat_logic _ _ Hn. subst mL nL.
  apply: coq_eq_to_imported_eq. apply: Logic.eq_sym.
  rewrite (imported_eq_to_coq_eq _ _ (I.Prosa_Validation_ClassicJitterBertognaFpCompInterface_bigCat_range'
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
  - exact (Logic.eq_sym (imported_eq_to_coq_eq _ _ (I.Prosa_Validation_ClassicJitterBertognaFpCompInterface_dedup_nil T (ct_decidable_eq T)))).
  - change (Logic.eq (cl_map cid (if x \in s then undup s else x :: undup s))
      (I.List_dedup T (ct_decidable_eq T) (I.List_cons T x (cl_map cid s)))).
    case Hx: (x \in s).
    + rewrite (imported_eq_to_coq_eq _ _ (I.Prosa_Validation_ClassicJitterBertognaFpCompInterface_dedup_cons_mem
                 T (ct_decidable_eq T) x (cl_map cid s)
                 (prop_to_sprop _ _ (cs_mem T x s _ (cl_lean_eq _ _ _ (Logic.eq_refl _))) Hx))).
      exact IH.
    + rewrite (imported_eq_to_coq_eq _ _ (I.Prosa_Validation_ClassicJitterBertognaFpCompInterface_dedup_cons_not_mem
                 T (ct_decidable_eq T) x (cl_map cid s) (cs_notin_target T x s Hx))).
      change (Logic.eq (I.List_cons T x (cl_map cid (undup s))) (I.List_cons T x (I.List_dedup T (ct_decidable_eq T) (cl_map cid s)))).
      by rewrite IH.
Qed.

Section INTDefs.
Variables (Job : eqType) (nR : nat) (nL : Lean.Nat).
Hypothesis Hn : SubNatRel nR nL.
Notation dJ := (ct_decidable_eq Job).
Variables (sR : Schedule.schedule Job nR)
  (sL : I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_schedule Job dJ nL).
Hypothesis Hs : CsSchedRel Job nR nL sR sL.

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

End INTDefs.

Section INTTaskDefs.
Variables (Task Job : eqType) (nR : nat) (nL : Lean.Nat).
Hypothesis Hn : SubNatRel nR nL.
Notation dT := (ct_decidable_eq Task).
Notation dJ := (ct_decidable_eq Job).
Variables (sR : Schedule.schedule Job nR)
  (sL : I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_schedule Job dJ nL).
Hypothesis Hs : CsSchedRel Job nR nL sR sL.
Variable job_task : Job -> Task.

End INTTaskDefs.

(* ------------------------------------------------------------------ *)
(** * Workload (as in the accepted classic workload certificate) *)

Section INTWl.
Variables (Task Job : eqType) (nR : nat) (nL : Lean.Nat).
Hypothesis Hn : SubNatRel nR nL.
Notation dT := (ct_decidable_eq Task).
Notation dJ := (ct_decidable_eq Job).
Variables (sR : Schedule.schedule Job nR)
  (sL : I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_schedule Job dJ nL).
Hypothesis Hs : CsSchedRel Job nR nL sR sL.
Variable job_task : Job -> Task.

End INTWl.

(** [\sum_(i <- l | P i) F i] against the accepted v0.6 [sumFiltered] ([((l.filter P).map F).sum]), by induction. *)
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

(* ------------------------------------------------------------------ *)
(** * Definitions *)

Section INTIntDefs.
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
Variables (jjR : Job -> nat) (jjL : Job -> Lean.Nat).
Hypothesis Hjj : CsParRel Job jjR jjL.

Notation bl := (cbt_GJ_backlogged Job nR nL Hn sR sL Hs jaR jaL Hja cR cL Hc jjR jjL Hjj).

End INTIntDefs.

Definition cbt_pair (T : Type) (p : T * nat) : I.Prod_inst2 T Lean.Nat := I.Prod_mk_inst2 T Lean.Nat p.1 (sub_nat_to_imported p.2).

(** A (task, response time) pair by its components (two-way totals: every Lean pair is the image of its components). *)
Definition CbtPairRel (T : Type) (pR : T * nat) (pL : I.Prod_inst2 T Lean.Nat) : SProp := Lean.eq (cbt_pair T pR) pL.

(** [minn] against the core [Min.min] on [Nat] (as in the accepted classic global workload_bound certificate). *)

Lemma cbt_max_jobs (Task : eqType) cR cL (Hc : CbtParRel Task cR cL) pR pL (Hp : CbtParRel Task pR pL)
    jR jL (Hj : CbtParRel Task jR jL) tsk RR RL (HR : SubNatRel RR RL) dR dL (Hd : SubNatRel dR dL) :
  SubNatRel (WorkloadBoundJitter.max_jobs_jitter cR pR jR tsk RR dR) (I.Prosa_Classic_Analysis_Global_Jitter_WorkloadBound_WorkloadBoundJitter_max_jobs_jitter Task (ct_decidable_eq Task) cL pL jL tsk RL dL).
Proof.
  exact (dm_div_floor_correspondence _ _ _ _
           (dm_sub_correspondence _ _ _ _ (dm_add_correspondence _ _ _ _ (dm_add_correspondence _ _ _ _ Hd (Hj tsk)) HR) (Hc tsk)) (Hp tsk)).
Qed.

Lemma cbt_W (Task : eqType) cR cL (Hc : CbtParRel Task cR cL) pR pL (Hp : CbtParRel Task pR pL)
    jR jL (Hj : CbtParRel Task jR jL) tsk RR RL (HR : SubNatRel RR RL) dR dL (Hd : SubNatRel dR dL) :
  SubNatRel (WorkloadBoundJitter.W_jitter cR pR jR tsk RR dR) (I.Prosa_Classic_Analysis_Global_Jitter_WorkloadBound_WorkloadBoundJitter_W_jitter Task (ct_decidable_eq Task) cL pL jL tsk RL dL).
Proof.
  have Hm := cbt_max_jobs Task cR cL Hc pR pL Hp jR jL Hj tsk RR RL HR dR dL Hd.
  exact (dm_add_correspondence _ _ _ _
           (cbt_min_rel _ _ _ _ (Hc tsk)
              (dm_sub_correspondence _ _ _ _
                 (dm_sub_correspondence _ _ _ _ (dm_add_correspondence _ _ _ _ (dm_add_correspondence _ _ _ _ Hd (Hj tsk)) HR) (Hc tsk))
                 (dm_mul_correspondence _ _ _ _ Hm (Hp tsk))))
           (dm_mul_correspondence _ _ _ _ Hm (Hc tsk))).
Qed.

Lemma cbt_generic (Task : eqType) cR cL (Hc : CbtParRel Task cR cL) pR pL (Hp : CbtParRel Task pR pL)
    jR jL (Hj : CbtParRel Task jR jL) tsk dR dL (Hd : SubNatRel dR dL) (p : Task * nat) :
  SubNatRel (InterferenceBoundJitter.interference_bound_generic cR pR jR tsk dR p)
    (I.Prosa_Classic_Analysis_Global_Jitter_InterferenceBound_InterferenceBoundJitter_interference_bound_generic Task (ct_decidable_eq Task) cL pL jL tsk dL (cbt_pair Task p)).
Proof.
  exact (cbt_min_rel _ _ _ _ (cbt_W Task cR cL Hc pR pL Hp jR jL Hj p.1 _ _ (sub_nat_rel_canonical p.2) _ _ Hd)
           (dm_add_correspondence _ _ _ _ (dm_sub_correspondence _ _ _ _ Hd (Hc tsk)) (sub_nat_rel_canonical 1))).
Qed.

Lemma cbt_IB_InterferenceBoundJitter_interference_bound_generic (Task : eqType)
    cR cL (Hc : CbtParRel Task cR cL) pR pL (Hp : CbtParRel Task pR pL) jR jL (Hj : CbtParRel Task jR jL) tsk
    dR dL (Hd : SubNatRel dR dL) prR prL (Hpr : CbtPairRel Task prR prL) :
  SubNatRel (InterferenceBoundJitter.interference_bound_generic cR pR jR tsk dR prR)
    (I.Prosa_Classic_Analysis_Global_Jitter_InterferenceBound_InterferenceBoundJitter_interference_bound_generic Task (ct_decidable_eq Task) cL pL jL tsk dL prL).
Proof.
  exact (cbt_trs Hpr (fun z => SubNatRel (InterferenceBoundJitter.interference_bound_generic cR pR jR tsk dR prR)
            (I.Prosa_Classic_Analysis_Global_Jitter_InterferenceBound_InterferenceBoundJitter_interference_bound_generic Task (ct_decidable_eq Task) cL pL jL tsk dL z))
           (cbt_generic Task cR cL Hc pR pL Hp jR jL Hj tsk dR dL Hd prR)).
Qed.

(** A (task, response time) pair by its components (two-way totals: every Lean pair is the image of its components). *)

(** [minn] against the core [Min.min] on [Nat] (as in the accepted classic global workload_bound certificate). *)

(** [\sum_(i <- l) F i] against the v0.6 [sumSeq] along an element map, by induction (constructor equations restated in
    the interface and exported with their proofs). *)
Lemma cbt_sum_map (A B : Type) (c : A -> B) FR FL (HF : forall x, SubNatRel (FR x) (FL (c x))) : forall l,
  SubNatRel (\sum_(i <- l) FR i) (I.Prosa_Util_Sum_sumSeq B (cl_map c l) FL).
Proof.
  intro l. induction l as [|x l IH].
  - rewrite big_nil. exact (sub_imported_eq_sym _ _ (I.Prosa_Validation_ClassicJitterBertognaFpCompInterface_production_sumSeq_nil B FL)).
  - rewrite big_cons. cbn [cl_map].
    refine (sub_imported_eq_trans _ _ _ _ (sub_imported_eq_sym _ _
      (I.Prosa_Validation_ClassicJitterBertognaFpCompInterface_production_sumSeq_cons B FL (c x) (cl_map c l)))).
    exact (sub_add_correspondence _ _ _ _ (HF x) IH).
Qed.

Lemma cbt_IBFP_InterferenceBoundFP_total_interference_bound_fp (Task : eqType)
    cR cL (Hc : CbtParRel Task cR cL) pR pL (Hp : CbtParRel Task pR pL) jR jL (Hj : CbtParRel Task jR jL) tsk
    (Rp : seq (Task * nat)) RpL (HRp : ClListRel (cbt_pair Task) Rp RpL) dR dL (Hd : SubNatRel dR dL) :
  SubNatRel (InterferenceBoundFP.total_interference_bound_fp cR pR jR tsk Rp dR)
    (I.Prosa_Classic_Analysis_Global_Jitter_InterferenceBoundFp_InterferenceBoundFP_total_interference_bound_fp Task (ct_decidable_eq Task) cL pL jL tsk RpL dL).
Proof.
  rewrite /InterferenceBoundFP.total_interference_bound_fp.
  unfold I.Prosa_Classic_Analysis_Global_Jitter_InterferenceBoundFp_InterferenceBoundFP_total_interference_bound_fp.
  refine (cbt_trs HRp (fun z => SubNatRel _ (I.Prosa_Util_Sum_sumSeq _ z _)) _).
  apply: cbt_sum_map. intros [a b]. exact (cbt_generic Task cR cL Hc pR pL Hp jR jL Hj tsk dR dL Hd (a, b)).
Qed.

(* ------------------------------------------------------------------ *)
(** * Definitions *)

Section SCHDefs.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).

Lemma cbt_SCH_actual_arrival aR aL (Ha : CbtParRel Job aR aL) jjR jjL (Hjj : CbtParRel Job jjR jjL) j :
  SubNatRel (ScheduleWithJitter.actual_arrival aR jjR j) (I.Prosa_Classic_Model_Schedule_Global_Jitter_Schedule_ScheduleWithJitter_actual_arrival Job dJ aL jjL j).
Proof. exact (sub_add_correspondence _ _ _ _ (Ha j) (Hjj j)). Qed.

Lemma cbt_SCH_jitter_has_passed aR aL (Ha : CbtParRel Job aR aL) jjR jjL (Hjj : CbtParRel Job jjR jjL) j
    tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (ScheduleWithJitter.jitter_has_passed aR jjR j tR) (I.Prosa_Classic_Model_Schedule_Global_Jitter_Schedule_ScheduleWithJitter_jitter_has_passed Job dJ aL jjL j tL).
Proof. exact (ct_decide_le _ _ _ _ (cbt_SCH_actual_arrival aR aL Ha jjR jjL Hjj j) Ht). Qed.

Section SCHSched.
Variables (nR : nat) (nL : Lean.Nat).
Hypothesis Hn : SubNatRel nR nL.
Variables (sR : Schedule.schedule Job nR)
  (sL : I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_schedule Job dJ nL).
Hypothesis Hs : CbtSchedRel Job nR nL sR sL.

Lemma cbt_SCH_pending aR aL (Ha : CbtParRel Job aR aL) cR cL (Hc : CbtParRel Job cR cL)
    jjR jjL (Hjj : CbtParRel Job jjR jjL) j tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (ScheduleWithJitter.pending aR cR jjR sR j tR) (I.Prosa_Classic_Model_Schedule_Global_Jitter_Schedule_ScheduleWithJitter_pending Job dJ aL cL jjL nL sL j tL).
Proof.
  exact (ct_bool_and _ _ _ _ (cbt_SCH_jitter_has_passed aR aL Ha jjR jjL Hjj j tR tL Ht)
           (ct_bool_not _ _ (cbt_GS_completed Job nR nL Hn sR sL Hs cR cL Hc j tR tL Ht))).
Qed.

Lemma cbt_SCH_backlogged aR aL (Ha : CbtParRel Job aR aL) cR cL (Hc : CbtParRel Job cR cL)
    jjR jjL (Hjj : CbtParRel Job jjR jjL) j tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (ScheduleWithJitter.backlogged aR cR jjR sR j tR) (I.Prosa_Classic_Model_Schedule_Global_Jitter_Schedule_ScheduleWithJitter_backlogged Job dJ aL cL jjL nL sL j tL).
Proof.
  exact (ct_bool_and _ _ _ _ (cbt_SCH_pending aR aL Ha cR cL Hc jjR jjL Hjj j tR tL Ht)
           (ct_bool_not _ _ (cbt_GS_scheduled Job nR nL Hn sR sL Hs j tR tL Ht))).
Qed.

Lemma cbt_SCH_jobs_execute_after_jitter aR aL (Ha : CbtParRel Job aR aL) jjR jjL (Hjj : CbtParRel Job jjR jjL) :
  PropSPropRel (ScheduleWithJitter.jobs_execute_after_jitter aR jjR sR) (I.Prosa_Classic_Model_Schedule_Global_Jitter_Schedule_ScheduleWithJitter_jobs_execute_after_jitter Job dJ aL jjL nL sL).
Proof.
  apply: ct_forall_identity => j. apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (ct_bool_truth _ _ (cbt_GS_scheduled Job nR nL Hn sR sL Hs j tR tL Ht)).
  exact (ct_bool_truth _ _ (cbt_SCH_jitter_has_passed aR aL Ha jjR jjL Hjj j tR tL Ht)).
Qed.

End SCHSched.

End SCHDefs.

Section SCHTaskDefs.
Variables (Task Job : eqType) (nR : nat) (nL : Lean.Nat).
Hypothesis Hn : SubNatRel nR nL.
Notation dT := (ct_decidable_eq Task).
Notation dJ := (ct_decidable_eq Job).
Variables (sR : Schedule.schedule Job nR)
  (sL : I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_schedule Job dJ nL).
Hypothesis Hs : CbtSchedRel Job nR nL sR sL.
Variable job_task : Job -> Task.

End SCHTaskDefs.

(* ------------------------------------------------------------------ *)
(** * Definitions *)

Section JOBDefs.
Variables (Task Job : eqType).
Notation dT := (ct_decidable_eq Task).
Notation dJ := (ct_decidable_eq Job).

Lemma cbt_JOB_job_jitter_leq_task_jitter tjR tjL (Htj : CbtParRel Task tjR tjL)
    jjR jjL (Hjj : CbtParRel Job jjR jjL) (job_task : Job -> Task) j :
  CtBoolRel (JobWithJitter.job_jitter_leq_task_jitter tjR job_task jjR j)
    (I.Prosa_Classic_Model_Schedule_Global_Jitter_Job_JobWithJitter_job_jitter_leq_task_jitter Task dT tjL Job dJ job_task jjL j).
Proof. exact (ct_decide_le _ _ _ _ (Hjj j) (Htj (job_task j))). Qed.

Lemma cbt_JOB_valid_sporadic_job_with_jitter tcR tcL tdR tdL tjR tjL
    (Htc : CbtParRel Task tcR tcL) (Htd : CbtParRel Task tdR tdL) (Htj : CbtParRel Task tjR tjL)
    cR cL dR dL jjR jjL (Hc : CbtParRel Job cR cL) (Hd : CbtParRel Job dR dL) (Hjj : CbtParRel Job jjR jjL)
    (job_task : Job -> Task) j :
  PropSPropRel (JobWithJitter.valid_sporadic_job_with_jitter tcR tdR tjR cR dR job_task jjR j)
    (I.Prosa_Classic_Model_Schedule_Global_Jitter_Job_JobWithJitter_valid_sporadic_job_with_jitter Task dT tcL tdL tjL Job dJ cL dL job_task jjL j).
Proof.
  apply: ct_and; first exact (cbt_J_valid_sporadic_job Task Job tcR tcL tdR tdL Htc Htd cR cL dR dL Hc Hd job_task j).
  exact (ct_bool_truth _ _ (cbt_JOB_job_jitter_leq_task_jitter tjR tjL Htj jjR jjL Hjj job_task j)).
Qed.

End JOBDefs.

Lemma cbt_succ_rel nR nL : SubNatRel nR nL ->
  SubNatRel nR.+1 (I.HAdd_hAdd_inst7 Lean.Nat Lean.Nat Lean.Nat (I.instHAdd_inst1 Lean.Nat I.instAddNat) nL
                     (I.OfNat_ofNat_inst1 Lean.Nat 1 (I.instOfNatNat 1))).
Proof. intro Hn. exact (sub_imported_eq_congr Lean.Nat_succ _ _ Hn). Qed.
Lemma cbt_succ_nat nR nL : SubNatRel nR nL -> SubNatRel nR.+1 (Lean.Nat_succ nL).
Proof. intro Hn. exact (sub_imported_eq_congr Lean.Nat_succ _ _ Hn). Qed.

(** Nat literals at the alias type [time] (the Lean [OfNat] instance of [Nat] at [time]). *)
Lemma cbt_lit0_time : SubNatRel 0 (I.OfNat_ofNat_inst1 I.Prosa_Classic_Model_Time_Time_time 0 (I.instOfNatNat 0)).
Proof. exact (sub_nat_rel_canonical 0). Qed.
Lemma cbt_lit1_time : SubNatRel 1 (I.OfNat_ofNat_inst1 I.Prosa_Classic_Model_Time_Time_time 1 (I.instOfNatNat 1)).
Proof. exact (sub_nat_rel_canonical 1). Qed.
Definition cibfp_pair (T : Type) (p : T * nat) : I.Prod_inst2 T Lean.Nat := I.Prod_mk_inst2 T Lean.Nat p.1 (sub_nat_to_imported p.2).

Definition cibfp_trs {A : Type} {x y : A} (E : Lean.eq x y) (P : A -> SProp) (h : P x) : P y :=
  match E in Lean.eq _ z return P z with Lean.eq_refl => h end.

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

Lemma cwb_forall_arr (Job : eqType) PR PL :
  (forall aR aL, CsArrRel Job aR aL -> PropSPropRel (PR aR) (PL aL)) -> PropSPropRel (forall a, PR a) (forall a, PL a).
Proof. exact (cs_forall_cover _ _ (CsArrRel Job) (cs_arr_to_target Job) (cs_arr_to_source Job) (cs_arr_canonical Job) (cs_arr_surjective Job) PR PL). Qed.

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
    (interpret_strict _ (cl_uniq_backward _ _ cid cid cts_id _ (@I.nodup Task dT tsL))).

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

Lemma cbt_RT_is_response_time_bound_of_task (Task Job : eqType) nR nL (Hn : SubNatRel nR nL)
    sR sL (Hs : CsSchedRel Job nR nL sR sL) jaR jaL (Hja : CsParRel Job jaR jaL) cR cL (Hc : CsParRel Job cR cL)
    (job_task : Job -> Task) aR aL (Ha : CsArrRel Job aR aL) tsk RR RL (HR : SubNatRel RR RL) :
  PropSPropRel (ResponseTime.is_response_time_bound_of_task jaR cR job_task aR sR tsk RR)
    (I.Prosa_Classic_Model_Schedule_Global_ResponseTime_ResponseTime_is_response_time_bound_of_task
       Task Job (ct_decidable_eq Task) (ct_decidable_eq Job) jaL cL job_task aL nL sL tsk RL).
Proof.
  apply: ct_forall_identity => j.
  apply: ct_imp; first exact (cs_arrives_in Job aR aL Ha j).
  apply: ct_imp; first exact (ct_eq_rel Task (job_task j) tsk).
  exact (ct_bool_truth _ _ (cf_Schedule_completed Job nR nL Hn sR sL Hs cR cL Hc j _ _ (sub_add_correspondence _ _ _ _ (Hja j) HR))).
Qed.

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

(* ------------------------------------------------------------------ *)
(** * The fixed-point iteration: lists, options, [iter] and the left fold *)

Definition cs_succ_rel := cbt_succ_rel.
Definition cs_ne := cta_ne.
Definition cs_false_rel := cta_false_rel.

Notation cfc_EQ H := (imported_eq_to_coq_eq _ _ H).

Lemma cfc_forall_list (T : Type) (PR : seq T -> Prop) (PL : I.List T -> SProp) :
  (forall sR sL, ClListRel (B := T) cid sR sL -> PropSPropRel (PR sR) (PL sL)) -> PropSPropRel (forall s, PR s) (forall s, PL s).
Proof. exact (cl_forall_list (B := T) cid cid (fun _ => Logic.eq_refl _) PR PL). Qed.

(** Sequences by identity: equality, [rcons], [take]. *)
Lemma cfc_list_eq (T : Type) aR aL (Ha : ClListRel (B := T) cid aR aL) bR bL (Hb : ClListRel (B := T) cid bR bL) :
  PropSPropRel (Logic.eq aR bR) (Lean.eq aL bL).
Proof.
  rewrite -(cfc_EQ Ha) -(cfc_EQ Hb). apply prop_sprop_rel_intro.
  - move=> ->. exact (@Lean.eq_refl _ _).
  - move=> E. apply strictly_inhabits. have E' := f_equal (cl_unmap (fun z : T => z)) (cfc_EQ E).
    by rewrite !(cl_unmap_map (fun z : T => z) (fun z : T => z) (fun _ => Logic.eq_refl _)) in E'.
Qed.

Lemma cfc_map_rcons (A B : Type) (c : A -> B) (l : seq A) (x : A) :
  Logic.eq (cl_map c (rcons l x))
    (I.HAppend_hAppend (I.List B) (I.List B) (I.List B) (I.instHAppendOfAppend (I.List B) (I.List_instAppend B))
       (cl_map c l) (I.List_cons B (c x) (I.List_nil B))).
Proof.
  elim: l => [|y l IH]; first reflexivity.
  change (Logic.eq (I.List_cons B (c y) (cl_map c (rcons l x)))
    (I.HAppend_hAppend (I.List B) (I.List B) (I.List B) (I.instHAppendOfAppend (I.List B) (I.List_instAppend B))
       (I.List_cons B (c y) (cl_map c l)) (I.List_cons B (c x) (I.List_nil B)))).
  rewrite IH. reflexivity.
Qed.

Lemma cfc_map_take (A B : Type) (c : A -> B) : forall (l : seq A) i,
  Logic.eq (cl_map c (take i l)) (I.List_take B (sub_nat_to_imported i) (cl_map c l)).
Proof.
  elim => [|x l IH] [|i]; try reflexivity.
  change (Logic.eq (I.List_cons B (c x) (cl_map c (take i l)))
                   (I.List_cons B (c x) (I.List_take B (sub_nat_to_imported i) (cl_map c l)))).
  by rewrite IH.
Qed.

Lemma cfc_rcons_id (T : Type) lR lL (Hl : ClListRel (B := T) cid lR lL) x :
  ClListRel (B := T) cid (rcons lR x)
    (I.HAppend_hAppend (I.List T) (I.List T) (I.List T) (I.instHAppendOfAppend (I.List T) (I.List_instAppend T))
       lL (I.List_cons T x (I.List_nil T))).
Proof. rewrite /ClListRel -(cfc_EQ Hl). apply: coq_eq_to_imported_eq. exact (cfc_map_rcons _ _ (fun z : T => z) lR x). Qed.

Lemma cfc_take_id (T : Type) lR lL (Hl : ClListRel (B := T) cid lR lL) iR iL (Hi : SubNatRel iR iL) :
  ClListRel (B := T) cid (take iR lR) (I.List_take T iL lL).
Proof.
  rewrite /ClListRel -(cfc_EQ Hl) (cl_nat_logic _ _ Hi). apply: coq_eq_to_imported_eq.
  exact (cfc_map_take _ _ (fun z : T => z) lR iR).
Qed.

(** Sequences of (task, time) pairs ([cibfp_pair]). *)
Lemma cfc_rcons_pair (T : Type) lR lL (Hl : ClListRel (cibfp_pair T) lR lL) a RR RL (HR : SubNatRel RR RL) :
  ClListRel (cibfp_pair T) (rcons lR (a, RR))
    (I.HAppend_hAppend (I.List (I.Prod_inst2 T Lean.Nat)) (I.List (I.Prod_inst2 T Lean.Nat)) (I.List (I.Prod_inst2 T Lean.Nat))
       (I.instHAppendOfAppend (I.List (I.Prod_inst2 T Lean.Nat)) (I.List_instAppend (I.Prod_inst2 T Lean.Nat)))
       lL (I.List_cons (I.Prod_inst2 T Lean.Nat) (I.Prod_mk_inst2 T Lean.Nat a RL) (I.List_nil (I.Prod_inst2 T Lean.Nat)))).
Proof.
  rewrite /ClListRel -(cfc_EQ Hl) (cl_nat_logic _ _ HR). apply: coq_eq_to_imported_eq.
  exact (cfc_map_rcons _ _ (cibfp_pair T) lR (a, RR)).
Qed.

Lemma cfc_take_pair (T : Type) lR lL (Hl : ClListRel (cibfp_pair T) lR lL) iR iL (Hi : SubNatRel iR iL) :
  ClListRel (cibfp_pair T) (take iR lR) (I.List_take (I.Prod_inst2 T Lean.Nat) iL lL).
Proof.
  rewrite /ClListRel -(cfc_EQ Hl) (cl_nat_logic _ _ Hi). apply: coq_eq_to_imported_eq.
  exact (cfc_map_take _ _ (cibfp_pair T) lR iR).
Qed.

Lemma cfc_size_pair (T : Type) lR lL (Hl : ClListRel (cibfp_pair T) lR lL) :
  SubNatRel (size lR) (I.List_length (I.Prod_inst2 T Lean.Nat) lL).
Proof.
  rewrite -(cfc_EQ Hl). clear Hl. apply: coq_eq_to_imported_eq.
  elim: lR => [|x l IH]; first reflexivity.
  exact (f_equal Lean.Nat_succ IH).
Qed.

Lemma cfc_unzip1 (T : Type) lR lL (Hl : ClListRel (cibfp_pair T) lR lL) :
  ClListRel (B := T) cid (unzip1 lR) (I.List_map (I.Prod_inst2 T Lean.Nat) T (I.Prod_fst_inst2 T Lean.Nat) lL).
Proof.
  rewrite /ClListRel -(cfc_EQ Hl). clear Hl. apply: coq_eq_to_imported_eq.
  elim: lR => [|[a b] l IH]; first reflexivity.
  change (Logic.eq (I.List_cons T a (cl_map (fun z : T => z) (unzip1 l)))
                   (I.List_cons T a (I.List_map (I.Prod_inst2 T Lean.Nat) T (I.Prod_fst_inst2 T Lean.Nat) (cl_map (cibfp_pair T) l)))).
  by rewrite IH.
Qed.

(** Indexing a task sequence ([nth] against [List.getD]). *)
Lemma cfc_getD (T : Type) : forall (s : seq T) i e,
  Logic.eq (I.List_getD T (cl_map (fun z : T => z) s) (sub_nat_to_imported i) e) (nth e s i).
Proof. elim => [|x s IH] [|i] e; try reflexivity. exact (IH i e). Qed.

Lemma cfc_hp_nth (T : eqType) hR hL (Hh : CpRelRel T hR hL) sR sL (Hs : ClListRel (B := T) cid sR sL) e
    iR iL (Hi : SubNatRel iR iL) jR jL (Hj : SubNatRel jR jL) :
  CtBoolRel (hR (nth e sR iR) (nth e sR jR)) (hL (I.List_getD T sL iL e) (I.List_getD T sL jL e)).
Proof. rewrite -(cfc_EQ Hs) (cl_nat_logic _ _ Hi) (cl_nat_logic _ _ Hj) !cfc_getD. exact (Hh _ _). Qed.

(** [sorted] against [List.IsChain] (as in the accepted classic sorting certificate). *)
Inductive CfcTrue : SProp := cfc_true_intro.

Section Chain.
Variables (T : Type) (leR : T -> T -> bool) (leL : T -> T -> I.Bool).
Hypothesis HR : forall a b, CtBoolRel (leR a b) (leL a b).
Notation RL := (fun a b : T => Lean.eq (leL a b) I.Bool_true).

Definition cfc_chain_head (x y : T) (l : I.List T) (H : I.List_IsChain T RL (I.List_cons T x (I.List_cons T y l))) : RL x y :=
  match H in I.List_IsChain _ _ L
    return (match L with I.List_cons a (I.List_cons b _) => RL a b | _ => CfcTrue end) with
  | I.List_IsChain_nil => cfc_true_intro
  | I.List_IsChain_singleton _ => cfc_true_intro
  | I.List_IsChain_cons_cons a b l h _ => h
  end.

Definition cfc_chain_tail (x y : T) (l : I.List T) (H : I.List_IsChain T RL (I.List_cons T x (I.List_cons T y l))) :
    I.List_IsChain T RL (I.List_cons T y l) :=
  match H in I.List_IsChain _ _ L
    return (match L with I.List_cons _ (I.List_cons b l') => I.List_IsChain T RL (I.List_cons T b l') | _ => CfcTrue end) with
  | I.List_IsChain_nil => cfc_true_intro
  | I.List_IsChain_singleton _ => cfc_true_intro
  | I.List_IsChain_cons_cons a b l _ t => t
  end.

Fixpoint cfc_path_forward (x : T) (s : seq T) : path leR x s -> I.List_IsChain T RL (I.List_cons T x (cl_map (fun z : T => z) s)) :=
  match s as s0 return path leR x s0 -> I.List_IsChain T RL (I.List_cons T x (cl_map (fun z : T => z) s0)) with
  | [::] => fun _ => I.List_IsChain_singleton T RL x
  | y :: s' => fun H =>
      I.List_IsChain_cons_cons T RL x y (cl_map (fun z : T => z) s')
        (prop_to_sprop _ _ (ct_bool_truth _ _ (HR x y)) (elimTF andP H).1)
        (cfc_path_forward y s' (elimTF andP H).2)
  end.

Fixpoint cfc_path_backward (x : T) (s : seq T) :
    I.List_IsChain T RL (I.List_cons T x (cl_map (fun z : T => z) s)) -> StrictlyInhabited (path leR x s) :=
  match s as s0 return I.List_IsChain T RL (I.List_cons T x (cl_map (fun z : T => z) s0)) -> StrictlyInhabited (path leR x s0) with
  | [::] => fun _ => strictly_inhabits (Logic.eq_refl true)
  | y :: s' => fun H =>
      match cfc_path_backward y s' (cfc_chain_tail x y _ H) with
      | strictly_inhabits Hp =>
          strictly_inhabits (introT andP (conj (sprop_to_prop _ _ (ct_bool_truth _ _ (HR x y)) (cfc_chain_head x y _ H)) Hp))
      end
  end.

Lemma cfc_sorted_canonical s : PropSPropRel (sorted leR s) (I.List_IsChain T RL (cl_map (fun z : T => z) s)).
Proof.
  apply prop_sprop_rel_intro; destruct s as [|x s].
  - intros _. exact (I.List_IsChain_nil T RL).
  - exact (cfc_path_forward x s).
  - intros _. exact (strictly_inhabits (Logic.eq_refl true)).
  - exact (cfc_path_backward x s).
Qed.

End Chain.

Lemma cfc_sorted (T : eqType) hR hL (Hh : CpRelRel T hR hL) s sL (Hs : ClListRel (B := T) cid s sL) :
  PropSPropRel (sorted hR s) (I.List_IsChain T (fun a b => Lean.eq (hL a b) I.Bool_true) sL).
Proof. rewrite -(cfc_EQ Hs). exact (cfc_sorted_canonical T hR hL Hh s). Qed.

(** FP policies (as in the accepted classic priority certificate). *)
Section Prio.
Variable Task : eqType.
Notation dT := (ct_decidable_eq Task).

Lemma cfc_FP_is_transitive rR rL (Hr : CpRelRel Task rR rL) :
  PropSPropRel (Priority.FP_is_transitive rR) (I.Prosa_Classic_Model_Priority_Priority_FP_is_transitive Task dT rL).
Proof.
  apply: ct_forall_identity => y. apply: ct_forall_identity => x. apply: ct_forall_identity => z.
  apply: ct_imp; first exact (ct_bool_truth _ _ (Hr x y)).
  apply: ct_imp; first exact (ct_bool_truth _ _ (Hr y z)).
  exact (ct_bool_truth _ _ (Hr x z)).
Qed.

Lemma cfc_FP_is_total_over_task_set rR rL (Hr : CpRelRel Task rR rL) ts tsL (Hts : ClListRel (B := Task) cid ts tsL) :
  PropSPropRel (Priority.FP_is_total_over_task_set rR ts)
    (I.Prosa_Classic_Model_Priority_Priority_FP_is_total_over_task_set Task dT rL tsL).
Proof.
  apply: ct_forall_identity => x1. apply: ct_forall_identity => x2.
  apply: ct_imp; first exact (cs_mem Task x1 ts tsL Hts).
  apply: ct_imp; first exact (cs_mem Task x2 ts tsL Hts).
  exact (ct_or _ _ _ _ (ct_bool_truth _ _ (Hr x1 x2)) (ct_bool_truth _ _ (Hr x2 x1))).
Qed.

Lemma cfc_FP_is_antisymmetric_over_task_set rR rL (Hr : CpRelRel Task rR rL) ts tsL (Hts : ClListRel (B := Task) cid ts tsL) :
  PropSPropRel (Priority.FP_is_antisymmetric_over_task_set rR ts)
    (I.Prosa_Classic_Model_Priority_Priority_FP_is_antisymmetric_over_task_set Task dT rL tsL).
Proof.
  apply: ct_forall_identity => x1. apply: ct_forall_identity => x2.
  apply: ct_imp; first exact (cs_mem Task x1 ts tsL Hts).
  apply: ct_imp; first exact (cs_mem Task x2 ts tsL Hts).
  apply: ct_imp; first exact (ct_bool_truth _ _ (Hr x1 x2)).
  apply: ct_imp; first exact (ct_bool_truth _ _ (Hr x2 x1)).
  exact (ct_eq_rel Task x1 x2).
Qed.

End Prio.

(** Global schedulability (as in the accepted classic global schedulability definitions). *)
Lemma cfc_job_misses_no_deadline (Job : eqType) nR nL (Hn : SubNatRel nR nL) sR sL (Hs : CsSchedRel Job nR nL sR sL)
    aR aL (Ha : CsParRel Job aR aL) cR cL (Hc : CsParRel Job cR cL) dR dL (Hd : CsParRel Job dR dL) j :
  CtBoolRel (Schedulability.job_misses_no_deadline aR cR dR sR j)
    (I.Prosa_Classic_Model_Schedule_Global_Schedulability_Schedulability_job_misses_no_deadline Job (ct_decidable_eq Job) aL cL dL nL sL j).
Proof. exact (cf_Schedule_completed Job nR nL Hn sR sL Hs cR cL Hc j _ _ (sub_add_correspondence _ _ _ _ (Ha j) (Hd j))). Qed.

Lemma cfc_task_misses_no_deadline (Task Job : eqType) nR nL (Hn : SubNatRel nR nL) sR sL (Hs : CsSchedRel Job nR nL sR sL)
    aR aL (Ha : CsParRel Job aR aL) cR cL (Hc : CsParRel Job cR cL) dR dL (Hd : CsParRel Job dR dL)
    (job_task : Job -> Task) arrR arrL (Harr : CsArrRel Job arrR arrL) tsk :
  PropSPropRel (Schedulability.task_misses_no_deadline aR cR dR job_task arrR sR tsk)
    (I.Prosa_Classic_Model_Schedule_Global_Schedulability_Schedulability_task_misses_no_deadline Task Job
       (ct_decidable_eq Task) (ct_decidable_eq Job) aL cL dL job_task arrL nL sL tsk).
Proof.
  apply: ct_forall_identity => j.
  apply: ct_imp; first exact (cs_arrives_in Job arrR arrL Harr j).
  apply: ct_imp; first exact (ct_eq_rel Task (job_task j) tsk).
  exact (ct_bool_truth _ _ (cfc_job_misses_no_deadline Job nR nL Hn sR sL Hs aR aL Ha cR cL Hc dR dL Hd j)).
Qed.

Lemma cfc_ite_dec (A : Type) (P : SProp) (dec : I.Decidable P) bR (Hb : CtBoolRel bR (I.Decidable_decide P dec)) (a b : A) :
  Logic.eq (I.ite A P dec a b) (if bR then a else b).
Proof.
  have E := ct_bool_rel_logic _ _ Hb. clear Hb. move: E.
  case: dec => [h|h] E; destruct bR; try reflexivity; discriminate E.
Qed.

Section CfcOpt.
Variable Task : eqType.
Notation dT := (ct_decidable_eq Task).
Notation PT := (I.Prod_inst2 Task Lean.Nat).

Definition cfc_olist (o : option (seq (Task * nat))) : I.Option (I.List PT) :=
  match o with Some l => I.Option_some (I.List PT) (cl_map (cibfp_pair Task) l) | None => I.Option_none (I.List PT) end.
Definition CfcORel (oR : option (seq (Task * nat))) (oL : I.Option (I.List PT)) : SProp := Lean.eq (cfc_olist oR) oL.

Lemma cfc_olist_inj o1 o2 : Logic.eq (cfc_olist o1) (cfc_olist o2) -> Logic.eq o1 o2.
Proof.
  case: o1 => [l1|]; case: o2 => [l2|] //= E; try discriminate E.
  injection E => E'. have E'' := f_equal (cl_unmap (cpair_unpair Task)) E'.
  by rewrite !(cl_unmap_map (cibfp_pair Task) (cpair_unpair Task) (cpair_dc Task)) in E''; rewrite E''.
Qed.

Lemma cfc_oeq oR1 oL1 (H1 : CfcORel oR1 oL1) oR2 oL2 (H2 : CfcORel oR2 oL2) :
  PropSPropRel (Logic.eq oR1 oR2) (Lean.eq oL1 oL2).
Proof.
  rewrite -(cfc_EQ H1) -(cfc_EQ H2). apply prop_sprop_rel_intro.
  - move=> ->. exact (@Lean.eq_refl _ _).
  - move=> E. apply strictly_inhabits. exact (cfc_olist_inj _ _ (cfc_EQ E)).
Qed.

Lemma cfc_osome lR lL (Hl : ClListRel (cibfp_pair Task) lR lL) : CfcORel (Some lR) (I.Option_some (I.List PT) lL).
Proof. rewrite /CfcORel -(cfc_EQ Hl). exact (@Lean.eq_refl _ _). Qed.

Lemma cfc_none_rel oR oL (Ho : CfcORel oR oL) :
  PropSPropRel (is_true (oR == None)) (Lean.eq oL (I.Option_none (I.List PT))).
Proof.
  rewrite -(cfc_EQ Ho). clear Ho. case: oR => [l|]; apply prop_sprop_rel_intro.
  - move=> H. exact (cl_false_elim_s _ H).
  - move=> E. have := cfc_EQ E. discriminate.
  - move=> _. exact (@Lean.eq_refl _ _).
  - move=> _. exact (strictly_inhabits (Logic.eq_refl true)).
Qed.

End CfcOpt.

(** [x \In o] against [optIn x o]. *)
Lemma cfc_optIn (Task : eqType) tsk RR RL (HR : SubNatRel RR RL) oR oL (Ho : CfcORel Task oR oL) dP :
  CtBoolRel ((tsk, RR) \In oR)
    (I.Prosa_Classic_Util_Notation_optIn (I.Prod_inst2 Task Lean.Nat) dP (I.Prod_mk_inst2 Task Lean.Nat tsk RL) oL).
Proof.
  rewrite -(cfc_EQ Ho). clear Ho. destruct oR as [l|].
  - exact (ct_decide_bool _ _ _ (cpair_mem Task tsk RR RL HR l _ (@Lean.eq_refl _ _))).
  - exact (ct_bool_canonical false).
Qed.

(** MathComp's [iter] against the accepted Lean [Fixedpoint.iter], by induction on the step count (fixture
    equations [xfc_iter_zero], [xfc_iter_succ]). *)
Lemma cfc_iter_canonical (fR : nat -> nat) (fL : Lean.Nat -> Lean.Nat)
    (Hf : forall a, Logic.eq (fL (sub_nat_to_imported a)) (sub_nat_to_imported (fR a))) :
  forall k x, Logic.eq (I.Prosa_Classic_Util_Fixedpoint_iter_inst1 Lean.Nat (sub_nat_to_imported k) fL (sub_nat_to_imported x))
                       (sub_nat_to_imported (iter k fR x)).
Proof.
  elim => [|k IH] x.
  - exact (cfc_EQ (I.Prosa_Validation_ClassicJitterBertognaFpCompInterface_xfc_iter_zero fL (sub_nat_to_imported x))).
  - refine (Logic.eq_trans (cfc_EQ (I.Prosa_Validation_ClassicJitterBertognaFpCompInterface_xfc_iter_succ fL (sub_nat_to_imported k) (sub_nat_to_imported x))) _).
    rewrite IH. exact (Hf (iter k fR x)).
Qed.

Lemma cfc_iter (fR : nat -> nat) (fL : Lean.Nat -> Lean.Nat) (Hf : forall a aL, SubNatRel a aL -> SubNatRel (fR a) (fL aL))
    k xR xL (Hx : SubNatRel xR xL) :
  SubNatRel (iter k fR xR) (I.Prosa_Classic_Util_Fixedpoint_iter_inst1 Lean.Nat (sub_nat_to_imported k) fL xL).
Proof.
  have Hf' : forall a, Logic.eq (fL (sub_nat_to_imported a)) (sub_nat_to_imported (fR a)) :=
    fun a => cl_nat_logic _ _ (Hf a _ (sub_nat_rel_canonical a)).
  have E := cl_nat_logic _ _ Hx. subst xL. apply: coq_eq_to_imported_eq.
  exact (Logic.eq_sym (cfc_iter_canonical fR fL Hf' k xR)).
Qed.

Section CfcDefs.
Variable Task : eqType.
Notation dT := (ct_decidable_eq Task).
Notation PT := (I.Prod_inst2 Task Lean.Nat).

Variables (tcR tpR tdR tjR : Task -> nat) (tcL tpL tdL tjL : Task -> Lean.Nat).
Hypotheses (Htc : CsParRel Task tcR tcL) (Htp : CsParRel Task tpR tpL) (Htd : CsParRel Task tdR tdL) (Htj : CsParRel Task tjR tjL).
Variables (nR : nat) (nL : Lean.Nat).
Hypothesis Hn : SubNatRel nR nL.

Lemma cfc_max_steps' tsk : SubNatRel (@ResponseTimeIterationFP.max_steps Task tcR tdR tsk) (I.Prosa_Classic_Analysis_Global_Jitter_BertognaFpComp_ResponseTimeIterationFP_max_steps Task dT tcL tdL tsk).
Proof. exact (sub_add_correspondence _ _ _ _ (ct_sub_rel _ _ _ _ (Htd tsk) (Htc tsk)) (sub_nat_rel_canonical 1)). Qed.

Lemma cfc_per_task_rta' tsk rR rL (Hr : ClListRel (cibfp_pair Task) rR rL) kR kL (Hk : SubNatRel kR kL) :
  SubNatRel (@ResponseTimeIterationFP.per_task_rta Task tcR tpR tjR nR tsk rR kR) (I.Prosa_Classic_Analysis_Global_Jitter_BertognaFpComp_ResponseTimeIterationFP_per_task_rta Task dT tcL tpL tjL nL tsk rL kL).
Proof.
  have E := cl_nat_logic _ _ Hk. subst kL.
  exact (cfc_iter _ _ (fun a aL Ha => sub_add_correspondence _ _ _ _ (Htc tsk)
           (dm_div_floor_correspondence _ _ _ _ (cbt_IBFP_InterferenceBoundFP_total_interference_bound_fp Task tcR tcL Htc tpR tpL Htp tjR tjL Htj tsk rR rL Hr a aL Ha) Hn))
           kR _ _ (Htc tsk)).
Qed.

Lemma cfc_bound_of_task oR tsk :
  Logic.eq (cfc_olist Task (@ResponseTimeIterationFP.fp_bound_of_task Task tcR tpR tdR tjR nR oR tsk))
           (I.Prosa_Classic_Analysis_Global_Jitter_BertognaFpComp_ResponseTimeIterationFP_fp_bound_of_task Task dT tcL tpL tdL tjL nL (cfc_olist Task oR) tsk).
Proof.
  case: oR => [l|]; last first.
  - exact (Logic.eq_sym (cfc_EQ (I.Prosa_Validation_ClassicJitterBertognaFpCompInterface_xfc_bound_none Task dT tcL tpL tdL tjL nL tsk))).
  - refine (Logic.eq_trans _ (Logic.eq_sym (cfc_EQ (I.Prosa_Validation_ClassicJitterBertognaFpCompInterface_xfc_bound_some Task dT tcL tpL tdL tjL nL
                                                     (cl_map (cibfp_pair Task) l) tsk)))).
    have HR := cfc_per_task_rta' tsk l _ (@Lean.eq_refl _ _) _ _ (cfc_max_steps' tsk).
    rewrite (cfc_ite_dec _ _ _ _ (ct_decide_le _ _ _ _ (sub_add_correspondence _ _ _ _ (Htj tsk) HR) (Htd tsk))).
    rewrite /ResponseTimeIterationFP.fp_bound_of_task.
    case: (_ <= _); last reflexivity.
    rewrite (cl_nat_logic _ _ HR) /cfc_olist cfc_map_rcons. reflexivity.
Qed.

Lemma cfc_foldl : forall (ts : seq Task) oR,
  Logic.eq (cfc_olist Task (foldl (@ResponseTimeIterationFP.fp_bound_of_task Task tcR tpR tdR tjR nR) oR ts))
           (I.List_foldl (I.Option (I.List PT)) Task (I.Prosa_Classic_Analysis_Global_Jitter_BertognaFpComp_ResponseTimeIterationFP_fp_bound_of_task Task dT tcL tpL tdL tjL nL) (cfc_olist Task oR)
              (cl_map (fun z : Task => z) ts)).
Proof.
  elim => [|x s IH] oR; first reflexivity.
  change (Logic.eq (cfc_olist Task (foldl (@ResponseTimeIterationFP.fp_bound_of_task Task tcR tpR tdR tjR nR) (@ResponseTimeIterationFP.fp_bound_of_task Task tcR tpR tdR tjR nR oR x) s))
           (I.List_foldl (I.Option (I.List PT)) Task (I.Prosa_Classic_Analysis_Global_Jitter_BertognaFpComp_ResponseTimeIterationFP_fp_bound_of_task Task dT tcL tpL tdL tjL nL)
              (I.Prosa_Classic_Analysis_Global_Jitter_BertognaFpComp_ResponseTimeIterationFP_fp_bound_of_task Task dT tcL tpL tdL tjL nL (cfc_olist Task oR) x) (cl_map (fun z : Task => z) s))).
  by rewrite IH cfc_bound_of_task.
Qed.

Lemma cfc_fcb' tsR tsL (Hts : ClListRel (B := Task) cid tsR tsL) :
  CfcORel Task (@ResponseTimeIterationFP.fp_claimed_bounds Task tcR tpR tdR tjR nR tsR) (I.Prosa_Classic_Analysis_Global_Jitter_BertognaFpComp_ResponseTimeIterationFP_fp_claimed_bounds Task dT tcL tpL tdL tjL nL tsL).
Proof. rewrite -(cfc_EQ Hts). apply: coq_eq_to_imported_eq. exact (cfc_foldl tsR (Some [::])). Qed.

Lemma cfc_fp_schedulable' tsR tsL (Hts : ClListRel (B := Task) cid tsR tsL) :
  CtBoolRel (@ResponseTimeIterationFP.fp_schedulable Task tcR tpR tdR tjR nR tsR) (I.Prosa_Classic_Analysis_Global_Jitter_BertognaFpComp_ResponseTimeIterationFP_fp_schedulable Task dT tcL tpL tdL tjL nL tsL).
Proof. exact (ct_bool_not _ _ (ct_decide_bool _ _ _ (cfc_none_rel Task _ _ (cfc_fcb' tsR tsL Hts)))). Qed.

End CfcDefs.

(** The definitions of [bertogna_fp_comp], with all inputs as hypotheses (for the relation search). *)
Theorem ResponseTimeIterationFP_max_steps_correspondence (Task : eqType) tcR tcL (Htc : CsParRel Task tcR tcL) tdR tdL (Htd : CsParRel Task tdR tdL) tsk :
  SubNatRel (@ResponseTimeIterationFP.max_steps Task tcR tdR tsk) (I.Prosa_Classic_Analysis_Global_Jitter_BertognaFpComp_ResponseTimeIterationFP_max_steps Task (ct_decidable_eq Task) tcL tdL tsk).
Proof. exact (cfc_max_steps' Task tcR tdR tcL tdL Htc Htd tsk). Qed.

Theorem ResponseTimeIterationFP_per_task_rta_correspondence (Task : eqType) tcR tcL (Htc : CsParRel Task tcR tcL) tpR tpL (Htp : CsParRel Task tpR tpL)
    tjR tjL (Htj : CsParRel Task tjR tjL) nR nL (Hn : SubNatRel nR nL) tsk rR rL (Hr : ClListRel (cibfp_pair Task) rR rL) kR kL (Hk : SubNatRel kR kL) :
  SubNatRel (@ResponseTimeIterationFP.per_task_rta Task tcR tpR tjR nR tsk rR kR) (I.Prosa_Classic_Analysis_Global_Jitter_BertognaFpComp_ResponseTimeIterationFP_per_task_rta Task (ct_decidable_eq Task) tcL tpL tjL nL tsk rL kL).
Proof. exact (cfc_per_task_rta' Task tcR tpR tjR tcL tpL tjL Htc Htp Htj nR nL Hn tsk rR rL Hr kR kL Hk). Qed.

Theorem ResponseTimeIterationFP_fp_bound_of_task_correspondence (Task : eqType) tcR tcL (Htc : CsParRel Task tcR tcL) tpR tpL (Htp : CsParRel Task tpR tpL)
    tdR tdL (Htd : CsParRel Task tdR tdL) tjR tjL (Htj : CsParRel Task tjR tjL) nR nL (Hn : SubNatRel nR nL) oR oL (Ho : CfcORel Task oR oL) tsk :
  CfcORel Task (@ResponseTimeIterationFP.fp_bound_of_task Task tcR tpR tdR tjR nR oR tsk) (I.Prosa_Classic_Analysis_Global_Jitter_BertognaFpComp_ResponseTimeIterationFP_fp_bound_of_task Task (ct_decidable_eq Task) tcL tpL tdL tjL nL oL tsk).
Proof.
  rewrite -(cfc_EQ Ho). apply: coq_eq_to_imported_eq.
  exact (cfc_bound_of_task Task tcR tpR tdR tjR tcL tpL tdL tjL Htc Htp Htd Htj nR nL Hn oR tsk).
Qed.

Theorem ResponseTimeIterationFP_fp_claimed_bounds_correspondence (Task : eqType) tcR tcL (Htc : CsParRel Task tcR tcL) tpR tpL (Htp : CsParRel Task tpR tpL)
    tdR tdL (Htd : CsParRel Task tdR tdL) tjR tjL (Htj : CsParRel Task tjR tjL) nR nL (Hn : SubNatRel nR nL) tsR tsL (Hts : ClListRel (B := Task) cid tsR tsL) :
  CfcORel Task (@ResponseTimeIterationFP.fp_claimed_bounds Task tcR tpR tdR tjR nR tsR) (I.Prosa_Classic_Analysis_Global_Jitter_BertognaFpComp_ResponseTimeIterationFP_fp_claimed_bounds Task (ct_decidable_eq Task) tcL tpL tdL tjL nL tsL).
Proof. exact (cfc_fcb' Task tcR tpR tdR tjR tcL tpL tdL tjL Htc Htp Htd Htj nR nL Hn tsR tsL Hts). Qed.

Theorem ResponseTimeIterationFP_fp_schedulable_correspondence (Task : eqType) tcR tcL (Htc : CsParRel Task tcR tcL) tpR tpL (Htp : CsParRel Task tpR tpL)
    tdR tdL (Htd : CsParRel Task tdR tdL) tjR tjL (Htj : CsParRel Task tjR tjL) nR nL (Hn : SubNatRel nR nL) tsR tsL (Hts : ClListRel (B := Task) cid tsR tsL) :
  CtBoolRel (@ResponseTimeIterationFP.fp_schedulable Task tcR tpR tdR tjR nR tsR) (I.Prosa_Classic_Analysis_Global_Jitter_BertognaFpComp_ResponseTimeIterationFP_fp_schedulable Task (ct_decidable_eq Task) tcL tpL tdL tjL nL tsL).
Proof. exact (cfc_fp_schedulable' Task tcR tpR tdR tjR tcL tpL tdL tjL Htc Htp Htd Htj nR nL Hn tsR tsL Hts). Qed.

(* ------------------------------------------------------------------ *)
(** * Statement relation search

    [crel] proves a [PropSPropRel P PL] (and the [SubNatRel], [CtBoolRel], [ClListRel] and relation goals it
    generates) by the structure of the source side [P], as in the accepted classic case-study certificates: each
    binder by the cover lemma of its type's relation, each connective by its [LogicalRelation]/base lemma, and
    each atom by the correspondence lemma of its head (above), whose remaining relation premises are hypotheses
    introduced by the binders.  It only chains lemmas proved in this file or its imports; a goal it cannot close
    makes the proof fail. *)

Ltac crel_hyp :=
  match goal with
  | |- SubNatRel (?f ?x) (?g ?x) => match goal with H : CbtParRel _ f g |- _ => exact (H x) end
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
  | seq _ => apply: cfc_forall_list; intros ? ? ?
  | _ => apply: ct_forall_identity; intro
  end.

Ltac crel_intro T :=
  tryif crel_isnat T then (apply: ct_forall_nat; intros ? ? ?) else
  lazymatch T with
  | ?A -> ?B => tryif crel_isnat B then (apply: cbt_forall_par; intros ? ? ?) else crel_intro_defs T
  | _ => crel_intro_defs T
  end.

Ltac crel :=
  first
  [ assumption
  | crel_hyp; crel
  | lazymatch goal with
    | |- forall x : prod _ _, _ => intros [? ?]; cbv beta iota zeta; try unfold I.Prosa_Classic_Analysis_Global_Jitter_BertognaFpComp_ResponseTimeIterationFP_fp_bound_of_task_match_1; try unfold I.Prosa_Classic_Analysis_Global_Jitter_InterferenceBoundFp_InterferenceBoundFP_total_interference_bound_fp_match_1; cbn [cibfp_pair fst snd]; crel
    | |- forall _, _ => intro; crel
    | |- CpRelRel _ _ _ => assumption
    | |- ClListRel _ (prosa.util.seqset._set_seq ?t) _ => match goal with H : CtsRel _ t _ |- _ => exact H end
    | |- CfcORel _ (@ResponseTimeIterationFP.fp_claimed_bounds _ _ _ _ _ _ _) _ => eapply ResponseTimeIterationFP_fp_claimed_bounds_correspondence; crel
    | |- CfcORel _ (Some _) _ => eapply cfc_osome; crel
    | |- CsParRel _ (fun _ => _) (fun _ => _) => intro; cbv beta; crel
    | |- SubNatRel 1 _ => first [ exact (sub_nat_rel_canonical 1) | exact cbt_lit1_time | eapply cbt_succ_rel; crel | eapply cbt_succ_nat; crel ]
    | |- SubNatRel (S _) _ => first [ eapply cbt_succ_rel; crel | eapply cbt_succ_nat; crel ]
    | |- SubNatRel 0 (I.OfNat_ofNat_inst1 I.Prosa_Classic_Model_Time_Time_time _ _) => exact cbt_lit0_time
    | |- SubNatRel ?a _ => crel_n a
    | |- CtBoolRel ?b _ => crel_b b
    | |- ClListRel _ ?l _ => crel_l l
    | |- PropSPropRel ?P _ => crel_p P
    end ]
with crel_n a :=
  lazymatch a with
  | addn _ _ => eapply sub_add_correspondence; crel
  | subn _ _ => first [ eapply ct_sub_rel; crel | eapply dm_sub_correspondence; crel ]
  | muln _ _ => first [ eapply dm_mul_correspondence; crel | eapply sub_mul_correspondence; crel ]
  | modn _ _ => eapply dm_mod_correspondence; crel
  | S _ => eapply cbt_succ_rel; crel
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
  | _ <-> _ => fail; crel
  | _ <> _ => fail| ~ _ => eapply ct_imp; [crel | fail]
  | @Logic.eq bool _ _ => eapply ct_bool_eq; crel
  | @Logic.eq ?T _ _ => tryif crel_isnat T then (eapply sub_nat_eq_correspondence; crel) else crel_eq_defs
  | is_true (leq _ _) => first [ eapply sub_nat_lt_correspondence; crel | eapply sub_nat_le_correspondence; crel
                              | eapply ct_bool_truth; crel ]
  | is_true _ => first [ crel_p_defs | eapply ct_bool_truth; crel ]
  | _ => crel_p_defs
  end
with crel_eq_defs := first [ eapply ct_eq_rel | eapply cfc_oeq; crel | eapply cfc_list_eq; crel ]
with crel_n_defs := first [ eapply ResponseTimeIterationFP_per_task_rta_correspondence; crel
    | eapply ResponseTimeIterationFP_max_steps_correspondence; crel
    | eapply cfc_size_pair; crel
    | eapply cbt_lit0_time; crel
    | eapply cbt_lit1_time; crel
    | eapply cbt_GJ_actual_arrival; crel
    | eapply dm_div_floor_correspondence; crel
    | eapply cbt_IBFP_InterferenceBoundFP_total_interference_bound_fp; crel
    | eapply cbt_WB_WorkloadBoundJitter_W_jitter; crel
    | eapply cbt_WB_WorkloadBoundJitter_max_jobs_jitter; crel
    | eapply cs_list_size; crel
    | eapply ccount_rel; crel
    | eapply cwb_sumSeq_rel; crel
    | eapply (cibfp_sumSeq_rel _ _ _ (cibfp_pair _)); crel
    | eapply cbt_min_rel; crel
    | eapply cai_sumFiltered_rel; crel
    | eapply cbt_list_size; crel ]
with crel_b_defs := first [ eapply cbt_GJ_pending; crel
    | eapply cbt_GJ_backlogged; crel
    | eapply cbt_GJ_jitter_has_passed; crel
    | eapply cbt_GS_completed; crel
    | eapply cbt_GS_scheduled; crel
    | eapply ResponseTimeIterationFP_fp_schedulable_correspondence; crel
    | eapply cfc_optIn; crel
    | eapply cfc_hp_nth; crel
    | eapply cfc_job_misses_no_deadline; crel
    | eapply cbt_J_job_cost_positive; crel
    | eapply cbt_J_job_deadline_positive; crel
    | eapply cbt_J_job_cost_le_deadline; crel
    | eapply cbt_J_job_cost_le_task_cost; crel ]
with crel_l_defs := first [ eapply cts_filter; crel
    | eapply cfc_rcons_id; crel
    | eapply cfc_rcons_pair; crel
    | eapply cfc_take_id; crel
    | eapply cfc_take_pair; crel
    | eapply cfc_unzip1; crel ]
with crel_p_defs := first [ eapply cfc_sorted; crel
    | eapply cfc_FP_is_transitive; crel
    | eapply cfc_FP_is_total_over_task_set; crel
    | eapply cfc_FP_is_antisymmetric_over_task_set; crel
    | eapply cfc_task_misses_no_deadline; crel
    | eapply cbt_GJ_jobs_execute_after_jitter; crel
    | eapply cs_arrives_in; crel
    | eapply cbt_sporadic_task_model; crel
    | eapply cbt_valid_sporadic_job_with_jitter; crel
    | eapply cts_valid_taskset; crel
    | eapply cts_mem; crel
    | eapply cpair_mem; crel
    | eapply cbt_RT_is_response_time_bound_of_task; crel
    | eapply cbt_PL_Platform_work_conserving; crel
    | eapply cbt_PL_Platform_respects_FP_policy; crel
    | eapply cbt_GS_jobs_come_from_arrival_sequence; crel
    | eapply cbt_GS_sequential_jobs; crel
    | eapply cbt_GS_completed_jobs_dont_execute; crel
    | eapply cbt_arrives_in; crel
    | eapply cbt_mem; crel
    | eapply cbt_uniq; crel
    | eapply cbt_J_valid_realtime_job; crel
    | eapply cbt_J_valid_sporadic_job; crel
    | eapply cbt_J_job_deadline_eq_task_deadline; crel ].

Ltac crel_spine :=
  repeat lazymatch goal with
  | |- PropSPropRel (forall x : ?T, _) _ =>
      lazymatch type of T with Prop => eapply ct_imp; [ crel | idtac ] | _ => crel_intro T end
  end.

(* ------------------------------------------------------------------ *)
(** * Statements *)

Definition src_fp_claimed_bounds_unzip (Task : eqType) : Prop :=
  ltac:(type_of_term (@ResponseTimeIterationFP.fp_claimed_bounds_unzip Task)).
Definition tgt_fp_claimed_bounds_unzip (Task : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Analysis_Global_Jitter_BertognaFpComp_ResponseTimeIterationFP_fp_claimed_bounds_unzip Task (ct_decidable_eq Task))).
Theorem ResponseTimeIterationFP_fp_claimed_bounds_unzip_correspondence (Task : eqType) :
  PropSPropRel (src_fp_claimed_bounds_unzip Task) (tgt_fp_claimed_bounds_unzip Task).
Proof. unfold src_fp_claimed_bounds_unzip, tgt_fp_claimed_bounds_unzip. crel_spine. crel. Unshelve. all: crel. Qed.

Definition src_fp_claimed_bounds_rcons (Task : eqType) : Prop :=
  ltac:(type_of_term (@ResponseTimeIterationFP.fp_claimed_bounds_rcons Task)).
Definition tgt_fp_claimed_bounds_rcons (Task : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Analysis_Global_Jitter_BertognaFpComp_ResponseTimeIterationFP_fp_claimed_bounds_rcons Task (ct_decidable_eq Task))).
Theorem ResponseTimeIterationFP_fp_claimed_bounds_rcons_correspondence (Task : eqType) :
  PropSPropRel (src_fp_claimed_bounds_rcons Task) (tgt_fp_claimed_bounds_rcons Task).
Proof. unfold src_fp_claimed_bounds_rcons, tgt_fp_claimed_bounds_rcons. crel_spine. crel. Unshelve. all: crel. Qed.

Definition src_fp_claimed_bounds_take (Task : eqType) : Prop :=
  ltac:(type_of_term (@ResponseTimeIterationFP.fp_claimed_bounds_take Task)).
Definition tgt_fp_claimed_bounds_take (Task : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Analysis_Global_Jitter_BertognaFpComp_ResponseTimeIterationFP_fp_claimed_bounds_take Task (ct_decidable_eq Task))).
Theorem ResponseTimeIterationFP_fp_claimed_bounds_take_correspondence (Task : eqType) :
  PropSPropRel (src_fp_claimed_bounds_take Task) (tgt_fp_claimed_bounds_take Task).
Proof. unfold src_fp_claimed_bounds_take, tgt_fp_claimed_bounds_take. crel_spine. crel. Unshelve. all: crel. Qed.

Definition src_fp_claimed_bounds_le_deadline (Task : eqType) : Prop :=
  ltac:(type_of_term (@ResponseTimeIterationFP.fp_claimed_bounds_le_deadline Task)).
Definition tgt_fp_claimed_bounds_le_deadline (Task : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Analysis_Global_Jitter_BertognaFpComp_ResponseTimeIterationFP_fp_claimed_bounds_le_deadline Task (ct_decidable_eq Task))).
Theorem ResponseTimeIterationFP_fp_claimed_bounds_le_deadline_correspondence (Task : eqType) :
  PropSPropRel (src_fp_claimed_bounds_le_deadline Task) (tgt_fp_claimed_bounds_le_deadline Task).
Proof. unfold src_fp_claimed_bounds_le_deadline, tgt_fp_claimed_bounds_le_deadline. crel_spine. crel. Unshelve. all: crel. Qed.

Definition src_fp_claimed_bounds_ge_cost (Task : eqType) : Prop :=
  ltac:(type_of_term (@ResponseTimeIterationFP.fp_claimed_bounds_ge_cost Task)).
Definition tgt_fp_claimed_bounds_ge_cost (Task : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Analysis_Global_Jitter_BertognaFpComp_ResponseTimeIterationFP_fp_claimed_bounds_ge_cost Task (ct_decidable_eq Task))).
Theorem ResponseTimeIterationFP_fp_claimed_bounds_ge_cost_correspondence (Task : eqType) :
  PropSPropRel (src_fp_claimed_bounds_ge_cost Task) (tgt_fp_claimed_bounds_ge_cost Task).
Proof. unfold src_fp_claimed_bounds_ge_cost, tgt_fp_claimed_bounds_ge_cost. crel_spine. crel. Unshelve. all: crel. Qed.

Definition src_per_task_rta_fold (Task : eqType) : Prop :=
  ltac:(type_of_term (@ResponseTimeIterationFP.per_task_rta_fold Task)).
Definition tgt_per_task_rta_fold (Task : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Analysis_Global_Jitter_BertognaFpComp_ResponseTimeIterationFP_per_task_rta_fold Task (ct_decidable_eq Task))).
Theorem ResponseTimeIterationFP_per_task_rta_fold_correspondence (Task : eqType) :
  PropSPropRel (src_per_task_rta_fold Task) (tgt_per_task_rta_fold Task).
Proof. unfold src_per_task_rta_fold, tgt_per_task_rta_fold. crel_spine. crel. Unshelve. all: crel. Qed.

Definition src_fp_claimed_bounds_hp_tasks_have_smaller_index (Task : eqType) : Prop :=
  ltac:(type_of_term (@ResponseTimeIterationFP.fp_claimed_bounds_hp_tasks_have_smaller_index Task)).
Definition tgt_fp_claimed_bounds_hp_tasks_have_smaller_index (Task : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Analysis_Global_Jitter_BertognaFpComp_ResponseTimeIterationFP_fp_claimed_bounds_hp_tasks_have_smaller_index Task (ct_decidable_eq Task))).
Theorem ResponseTimeIterationFP_fp_claimed_bounds_hp_tasks_have_smaller_index_correspondence (Task : eqType) :
  PropSPropRel (src_fp_claimed_bounds_hp_tasks_have_smaller_index Task) (tgt_fp_claimed_bounds_hp_tasks_have_smaller_index Task).
Proof. unfold src_fp_claimed_bounds_hp_tasks_have_smaller_index, tgt_fp_claimed_bounds_hp_tasks_have_smaller_index. crel_spine. crel. Unshelve. all: crel. Qed.

Definition src_bertogna_fp_comp_f_monotonic (Task : eqType) : Prop :=
  ltac:(type_of_term (@ResponseTimeIterationFP.bertogna_fp_comp_f_monotonic Task)).
Definition tgt_bertogna_fp_comp_f_monotonic (Task : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Analysis_Global_Jitter_BertognaFpComp_ResponseTimeIterationFP_bertogna_fp_comp_f_monotonic Task (ct_decidable_eq Task))).
Theorem ResponseTimeIterationFP_bertogna_fp_comp_f_monotonic_correspondence (Task : eqType) :
  PropSPropRel (src_bertogna_fp_comp_f_monotonic Task) (tgt_bertogna_fp_comp_f_monotonic Task).
Proof. unfold src_bertogna_fp_comp_f_monotonic, tgt_bertogna_fp_comp_f_monotonic. crel_spine. crel. Unshelve. all: crel. Qed.

Definition src_bertogna_fp_comp_f_converges_early (Task : eqType) : Prop :=
  ltac:(type_of_term (@ResponseTimeIterationFP.bertogna_fp_comp_f_converges_early Task)).
Definition tgt_bertogna_fp_comp_f_converges_early (Task : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Analysis_Global_Jitter_BertognaFpComp_ResponseTimeIterationFP_bertogna_fp_comp_f_converges_early Task (ct_decidable_eq Task))).
Theorem ResponseTimeIterationFP_bertogna_fp_comp_f_converges_early_correspondence (Task : eqType) :
  PropSPropRel (src_bertogna_fp_comp_f_converges_early Task) (tgt_bertogna_fp_comp_f_converges_early Task).
Proof. unfold src_bertogna_fp_comp_f_converges_early, tgt_bertogna_fp_comp_f_converges_early. crel_spine. crel. Unshelve. all: crel. Qed.

Definition src_bertogna_fp_comp_f_increases (Task : eqType) : Prop :=
  ltac:(type_of_term (@ResponseTimeIterationFP.bertogna_fp_comp_f_increases Task)).
Definition tgt_bertogna_fp_comp_f_increases (Task : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Analysis_Global_Jitter_BertognaFpComp_ResponseTimeIterationFP_bertogna_fp_comp_f_increases Task (ct_decidable_eq Task))).
Theorem ResponseTimeIterationFP_bertogna_fp_comp_f_increases_correspondence (Task : eqType) :
  PropSPropRel (src_bertogna_fp_comp_f_increases Task) (tgt_bertogna_fp_comp_f_increases Task).
Proof. unfold src_bertogna_fp_comp_f_increases, tgt_bertogna_fp_comp_f_increases. crel_spine. crel. Unshelve. all: crel. Qed.

Definition src_bertogna_fp_comp_rt_grows_too_much (Task : eqType) : Prop :=
  ltac:(type_of_term (@ResponseTimeIterationFP.bertogna_fp_comp_rt_grows_too_much Task)).
Definition tgt_bertogna_fp_comp_rt_grows_too_much (Task : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Analysis_Global_Jitter_BertognaFpComp_ResponseTimeIterationFP_bertogna_fp_comp_rt_grows_too_much Task (ct_decidable_eq Task))).
Theorem ResponseTimeIterationFP_bertogna_fp_comp_rt_grows_too_much_correspondence (Task : eqType) :
  PropSPropRel (src_bertogna_fp_comp_rt_grows_too_much Task) (tgt_bertogna_fp_comp_rt_grows_too_much Task).
Proof. unfold src_bertogna_fp_comp_rt_grows_too_much, tgt_bertogna_fp_comp_rt_grows_too_much. crel_spine. crel. Unshelve. all: crel. Qed.

Definition src_per_task_rta_converges (Task : eqType) : Prop :=
  ltac:(type_of_term (@ResponseTimeIterationFP.per_task_rta_converges Task)).
Definition tgt_per_task_rta_converges (Task : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Analysis_Global_Jitter_BertognaFpComp_ResponseTimeIterationFP_per_task_rta_converges Task (ct_decidable_eq Task))).
Theorem ResponseTimeIterationFP_per_task_rta_converges_correspondence (Task : eqType) :
  PropSPropRel (src_per_task_rta_converges Task) (tgt_per_task_rta_converges Task).
Proof. unfold src_per_task_rta_converges, tgt_per_task_rta_converges. crel_spine. crel. Unshelve. all: crel. Qed.

Definition src_fp_analysis_yields_response_time_bounds (Task Job : eqType) : Prop :=
  forall p0 p1 p2 p3 : Task -> nat,
    ltac:(type_of_term (@ResponseTimeIterationFP.fp_analysis_yields_response_time_bounds Task p0 p1 p2 p3 Job)).
Definition tgt_fp_analysis_yields_response_time_bounds (Task Job : eqType) : SProp :=
  forall p0 p1 p2 p3 : Task -> Lean.Nat,
    ltac:(type_of_term (I.Prosa_Classic_Analysis_Global_Jitter_BertognaFpComp_ResponseTimeIterationFP_fp_analysis_yields_response_time_bounds Task (ct_decidable_eq Task) p0 p1 p2 p3 Job (ct_decidable_eq Job))).
Theorem ResponseTimeIterationFP_fp_analysis_yields_response_time_bounds_correspondence (Task Job : eqType) :
  PropSPropRel (src_fp_analysis_yields_response_time_bounds Task Job) (tgt_fp_analysis_yields_response_time_bounds Task Job).
Proof. unfold src_fp_analysis_yields_response_time_bounds, tgt_fp_analysis_yields_response_time_bounds. crel_spine. crel. Unshelve. all: crel. Qed.

Definition src_taskset_schedulable_by_fp_rta (Task Job : eqType) : Prop :=
  forall p0 p1 p2 p3 : Task -> nat,
    ltac:(type_of_term (@ResponseTimeIterationFP.taskset_schedulable_by_fp_rta Task p0 p1 p2 p3 Job)).
Definition tgt_taskset_schedulable_by_fp_rta (Task Job : eqType) : SProp :=
  forall p0 p1 p2 p3 : Task -> Lean.Nat,
    ltac:(type_of_term (I.Prosa_Classic_Analysis_Global_Jitter_BertognaFpComp_ResponseTimeIterationFP_taskset_schedulable_by_fp_rta Task (ct_decidable_eq Task) p0 p1 p2 p3 Job (ct_decidable_eq Job))).
Theorem ResponseTimeIterationFP_taskset_schedulable_by_fp_rta_correspondence (Task Job : eqType) :
  PropSPropRel (src_taskset_schedulable_by_fp_rta Task Job) (tgt_taskset_schedulable_by_fp_rta Task Job).
Proof. unfold src_taskset_schedulable_by_fp_rta, tgt_taskset_schedulable_by_fp_rta. crel_spine. crel. Unshelve. all: crel. Qed.

Definition src_jobs_schedulable_by_fp_rta (Task Job : eqType) : Prop :=
  forall p0 p1 p2 p3 : Task -> nat,
    ltac:(type_of_term (@ResponseTimeIterationFP.jobs_schedulable_by_fp_rta Task p0 p1 p2 p3 Job)).
Definition tgt_jobs_schedulable_by_fp_rta (Task Job : eqType) : SProp :=
  forall p0 p1 p2 p3 : Task -> Lean.Nat,
    ltac:(type_of_term (I.Prosa_Classic_Analysis_Global_Jitter_BertognaFpComp_ResponseTimeIterationFP_jobs_schedulable_by_fp_rta Task (ct_decidable_eq Task) p0 p1 p2 p3 Job (ct_decidable_eq Job))).
Theorem ResponseTimeIterationFP_jobs_schedulable_by_fp_rta_correspondence (Task Job : eqType) :
  PropSPropRel (src_jobs_schedulable_by_fp_rta Task Job) (tgt_jobs_schedulable_by_fp_rta Task Job).
Proof. unfold src_jobs_schedulable_by_fp_rta, tgt_jobs_schedulable_by_fp_rta. crel_spine. crel. Unshelve. all: crel. Qed.
