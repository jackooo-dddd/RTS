From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq path fintype bigop div.
From prosa Require Import classic.util.div_mod classic.model.time classic.util.notation classic.model.arrival.basic.arrival_sequence classic.model.arrival.basic.task classic.model.arrival.basic.job classic.model.arrival.basic.task_arrival classic.model.schedule.global.basic.schedule classic.model.schedule.global.workload classic.model.schedule.global.response_time classic.analysis.global.parallel.workload_bound.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedClassicParallelWorkloadBound.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence ClassicParallelWorkloadBoundBase ClassicParallelWorkloadBoundList ClassicParallelWorkloadBoundOrd.

Module I := ImportedClassicParallelWorkloadBound.
Local Open Scope nat_scope.

(** Certificates for [classic/analysis/global/parallel/workload_bound.v] (ProsaBuddy classic, commit f692cb7).

    Inputs, relations and computation as in the accepted classic global workload_bound certificate (re-stated below for
    this export): eqTypes identified with their canonical Lean [DecidableEq] instances; times and [num_cpus] by
    [SubNatRel]; processors by their values; schedules pointwise; job and task parameters pointwise; sequences
    elementwise; arrival sequences pointwise on related times; all with two-way totals.  The sorted jobs against the
    core [List.mergeSort] through the exported stable-sort facts ([cpg_sort_rel]); [nth] against [getD];
    [workload]/[service]/[service_during] through kernel-guarded [rfl] body projections and the three half-open sums of
    the statements through kernel-guarded type normalization, related by [cpw_ico]; [\sum_(i <- s) F i] against the
    v0.6 [sumSeq]; [div_ceil] and the Nat operations through the accepted operation-level bridge [DivModCorrespondence].

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

Lemma cpw_forall_cover (A B : Type) (Rel : A -> B -> SProp) (toB : A -> B) (toA : B -> A)
    (HB : forall a, Rel a (toB a)) (HA : forall b, Rel (toA b) b) (PR : A -> Prop) (PL : B -> SProp) :
  (forall a b, Rel a b -> PropSPropRel (PR a) (PL b)) -> PropSPropRel (forall a, PR a) (forall b, PL b).
Proof.
  intro H. apply prop_sprop_rel_intro.
  - intros HR b. exact (prop_to_sprop _ _ (H _ _ (HA b)) (HR _)).
  - intro HL. apply strictly_inhabits. intro a. exact (sprop_to_prop _ _ (H _ _ (HB a)) (HL _)).
Qed.

Lemma cpw_mem (T : eqType) x s sL : ClListRel cid s sL ->
  PropSPropRel (x \in s) (I.Membership_mem T (I.List T) (I.List_instMembership T) sL x).
Proof. exact (cl_mem_rel_list T T cid cid (fun _ => Logic.eq_refl _) x s sL). Qed.

Lemma cpw_uniq (T : eqType) s sL : ClListRel cid s sL -> PropSPropRel (uniq s) (I.List_Nodup T sL).
Proof. exact (cl_uniq_rel_list T T cid cid (fun _ => Logic.eq_refl _) (fun _ => Logic.eq_refl _) s sL). Qed.

Lemma cpw_list_size (T : Type) s sL : ClListRel (B := T) cid s sL -> SubNatRel (size s) (I.List_length T sL).
Proof. intro H. destruct H. exact (cl_size cid s). Qed.

Lemma cpw_lean_eq_logic (A : Type) (x y : A) : Lean.eq x y -> Logic.eq x y.
Proof. exact (imported_eq_to_coq_eq x y). Qed.

(** Transport along the target equality (definitional UIP), into relevant and SProp-valued families. *)
Definition cpw_tr {A : Type} {x y : A} (E : Lean.eq x y) (P : A -> Type) (h : P x) : P y :=
  match E in Lean.eq _ z return P z with Lean.eq_refl => h end.
Definition cpw_trs {A : Type} {x y : A} (E : Lean.eq x y) (P : A -> SProp) (h : P x) : P y :=
  match E in Lean.eq _ z return P z with Lean.eq_refl => h end.

(** Options: [cl_opt] is injective and [x == Some j] is [cl_opt x = some j]. *)
Lemma cpw_opt_inj (A : Type) (o1 o2 : option A) : Logic.eq (cl_opt o1) (cl_opt o2) -> Logic.eq o1 o2.
Proof. intro E. by rewrite -(cl_unopt_opt o1) -(cl_unopt_opt o2) E. Qed.

Lemma cpw_opt_eq_rel (A : Type) (o1 o2 : option A) :
  PropSPropRel (Logic.eq o1 o2) (Lean.eq (cl_opt o1) (cl_opt o2)).
Proof.
  apply prop_sprop_rel_intro.
  - intro E. rewrite E. exact (@Lean.eq_refl _ _).
  - intro E. apply strictly_inhabits. exact (cpw_opt_inj A o1 o2 (imported_eq_to_coq_eq _ _ E)).
Qed.

Lemma cpw_opt_eqb_rel (A : eqType) (o1 o2 : option A) :
  PropSPropRel (is_true (o1 == o2)) (Lean.eq (cl_opt o1) (cl_opt o2)).
Proof.
  apply prop_sprop_rel_intro.
  - move=> /eqP E. rewrite E. exact (@Lean.eq_refl _ _).
  - intro E. apply strictly_inhabits. apply/eqP. exact (cpw_opt_inj A o1 o2 (imported_eq_to_coq_eq _ _ E)).
Qed.

(* ------------------------------------------------------------------ *)
(** * Half-open sums and concatenations over [nat] (as in the accepted sum / arrival_sequence certificates) *)

Fixpoint cpw_natl (s : seq nat) : I.List_inst1 Lean.Nat :=
  match s with [::] => I.List_nil_inst1 _ | x :: s' => I.List_cons_inst1 _ (sub_nat_to_imported x) (cpw_natl s') end.

Lemma cpw_iota_range : forall n s,
  Logic.eq (I.List_range' (sub_nat_to_imported s) (sub_nat_to_imported n) (Lean.Nat_succ Lean.Nat_zero)) (cpw_natl (iota s n)).
Proof.
  elim => [|n IH] s; first reflexivity.
  change (Logic.eq (I.List_cons_inst1 _ (sub_nat_to_imported s)
      (I.List_range' (sub_nat_to_imported (S s)) (sub_nat_to_imported n) (Lean.Nat_succ Lean.Nat_zero)))
    (I.List_cons_inst1 _ (sub_nat_to_imported s) (cpw_natl (iota (S s) n)))).
  by rewrite IH.
Qed.

Lemma cpw_foldr_add (f : Lean.Nat -> Lean.Nat) (g : nat -> nat) (Hf : forall k, Logic.eq (f (sub_nat_to_imported k)) (sub_nat_to_imported (g k))) :
  forall s, Logic.eq (I.List_foldr_inst3 Lean.Nat Lean.Nat Lean.Nat_add Lean.Nat_zero (I.List_map_inst3 Lean.Nat Lean.Nat f (cpw_natl s)))
                     (sub_nat_to_imported (foldr addn 0 (map g s))).
Proof.
  elim => [|k s IH] //=.
  change (Logic.eq (Lean.Nat_add (f (sub_nat_to_imported k))
            (I.List_foldr_inst3 Lean.Nat Lean.Nat Lean.Nat_add Lean.Nat_zero (I.List_map_inst3 Lean.Nat Lean.Nat f (cpw_natl s))))
         (sub_nat_to_imported (g k + foldr addn 0 (map g s)))).
  rewrite IH Hf. exact (imported_eq_to_coq_eq _ _ (sub_add_canonical _ _)).
Qed.

Lemma cpw_big_fold (xs : seq nat) (F : nat -> nat) : Logic.eq (\sum_(i <- xs) F i) (foldr addn 0 (map F xs)).
Proof. elim: xs => [|x xs IH]; first by rewrite big_nil. by rewrite big_cons IH. Qed.

Definition CpwFunRel (FR : nat -> nat) (FL : Lean.Nat -> Lean.Nat) : SProp :=
  forall kR kL, SubNatRel kR kL -> SubNatRel (FR kR) (FL kL).

Lemma cpw_fun_canonical FR FL (HF : CpwFunRel FR FL) k : Logic.eq (FL (sub_nat_to_imported k)) (sub_nat_to_imported (FR k)).
Proof. exact (co_nat_logic _ _ (HF _ _ (sub_nat_rel_canonical k))). Qed.

Lemma cpw_ico mR mL nR nL FR FL (Hm : SubNatRel mR mL) (Hn : SubNatRel nR nL) (HF : CpwFunRel FR FL) :
  SubNatRel (\sum_(mR <= i < nR) FR i)
    (I.List_foldr_inst3 Lean.Nat Lean.Nat Lean.Nat_add Lean.Nat_zero
       (I.List_map_inst3 Lean.Nat Lean.Nat FL (I.List_range' mL (I.Nat_sub nL mL) (Lean.Nat_succ Lean.Nat_zero)))).
Proof.
  rewrite (co_nat_logic _ _ Hm) (co_nat_logic _ _ Hn).
  have -> : Logic.eq (I.Nat_sub (sub_nat_to_imported nR) (sub_nat_to_imported mR)) (sub_nat_to_imported (nR - mR))
    := ct_sub_canonical nR mR.
  rewrite cpw_iota_range.
  apply: coq_eq_to_imported_eq. apply: Logic.eq_sym. rewrite (cpw_foldr_add FL FR (cpw_fun_canonical FR FL HF)).
  by rewrite cpw_big_fold.
Qed.

Lemma cpw_map_natl {B : Type} (f : Lean.Nat -> B) : forall s,
  Logic.eq (I.List_map_inst1 Lean.Nat B f (cpw_natl s)) (cl_map (fun k => f (sub_nat_to_imported k)) s).
Proof.
  elim => [|k s IH] //=.
  change (Logic.eq (I.List_cons B (f (sub_nat_to_imported k)) (I.List_map_inst1 Lean.Nat B f (cpw_natl s)))
                   (I.List_cons B (f (sub_nat_to_imported k)) (cl_map (fun k => f (sub_nat_to_imported k)) s))).
  by rewrite IH.
Qed.

Lemma cpw_big_seq {A : Type} (F : nat -> seq A) : forall s : seq nat,
  Logic.eq (\big[cat/[::]]_(i <- s) F i) (flatten (map F s)).
Proof. elim => [|x s IH]; first by rewrite big_nil. by rewrite big_cons IH. Qed.

Definition CpwNatFamRel (A : Type) (fR : nat -> seq A) (fL : Lean.Nat -> I.List A) : SProp :=
  forall nR nL, SubNatRel nR nL -> ClListRel cid (fR nR) (fL nL).

Lemma cpw_bigcat_nat_rel (A : Type) fR fL (Hf : CpwNatFamRel A fR fL) mR mL nR nL :
  SubNatRel mR mL -> SubNatRel nR nL ->
  ClListRel cid (\big[cat/[::]]_(mR <= t < nR) fR t) (I.Prosa_Util_Notation_bigCat A mL nL fL).
Proof.
  intros Hm Hn. have E1 := co_nat_logic _ _ Hm. have E2 := co_nat_logic _ _ Hn. subst mL nL.
  apply: coq_eq_to_imported_eq. apply: Logic.eq_sym.
  rewrite (imported_eq_to_coq_eq _ _ (I.Prosa_Validation_ClassicParallelWorkloadBoundInterface_bigCat_range'
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
  rewrite cpw_big_seq /index_iota Hi -map_comp.
  reflexivity.
Qed.

Lemma cpw_notin_target (T : eqType) x s : Logic.eq (x \in s) false ->
  I.Not (I.Membership_mem T (I.List T) (I.List_instMembership T) (cl_map cid s) x).
Proof.
  intros Hx H. apply: ct_coq_false_to_target.
  have Hm := sprop_to_prop _ _ (cpw_mem T x s _ (cl_lean_eq _ _ _ (Logic.eq_refl _))) H.
  rewrite Hx in Hm. discriminate.
Qed.

(** [undup] against Mathlib's [List.dedup] (step equations exported with their proofs). *)
Lemma cpw_undup_rel (T : eqType) : forall s sL, ClListRel cid s sL ->
  ClListRel cid (undup s) (I.List_dedup T (ct_decidable_eq T) sL).
Proof.
  intros s sL Hs. have E := cl_list_logic _ _ _ Hs. subst sL. apply: coq_eq_to_imported_eq. clear Hs.
  elim: s => [|x s IH].
  - exact (Logic.eq_sym (imported_eq_to_coq_eq _ _ (I.Prosa_Validation_ClassicParallelWorkloadBoundInterface_dedup_nil T (ct_decidable_eq T)))).
  - change (Logic.eq (cl_map cid (if x \in s then undup s else x :: undup s))
      (I.List_dedup T (ct_decidable_eq T) (I.List_cons T x (cl_map cid s)))).
    case Hx: (x \in s).
    + rewrite (imported_eq_to_coq_eq _ _ (I.Prosa_Validation_ClassicParallelWorkloadBoundInterface_dedup_cons_mem
                 T (ct_decidable_eq T) x (cl_map cid s)
                 (prop_to_sprop _ _ (cpw_mem T x s _ (cl_lean_eq _ _ _ (Logic.eq_refl _))) Hx))).
      exact IH.
    + rewrite (imported_eq_to_coq_eq _ _ (I.Prosa_Validation_ClassicParallelWorkloadBoundInterface_dedup_cons_not_mem
                 T (ct_decidable_eq T) x (cl_map cid s) (cpw_notin_target T x s Hx))).
      change (Logic.eq (I.List_cons T x (cl_map cid (undup s))) (I.List_cons T x (I.List_dedup T (ct_decidable_eq T) (cl_map cid s)))).
      by rewrite IH.
Qed.

(* ------------------------------------------------------------------ *)
(** * Schedules, arrival sequences, parameters *)

Definition CpwParRel (T : Type) (pR : T -> nat) (pL : T -> Lean.Nat) : SProp := forall x, SubNatRel (pR x) (pL x).

Lemma cpw_forall_par (T : Type) (PR : (T -> nat) -> Prop) (PL : (T -> Lean.Nat) -> SProp) :
  (forall pR pL, CpwParRel T pR pL -> PropSPropRel (PR pR) (PL pL)) -> PropSPropRel (forall p, PR p) (forall p, PL p).
Proof.
  exact (cpw_forall_cover _ _ (CpwParRel T) (fun pR j => sub_nat_to_imported (pR j)) (fun pL j => sub_nat_to_rocq (pL j))
           (fun pR j => sub_nat_rel_canonical (pR j)) (fun pL j => sub_nat_rel_surjective (pL j)) PR PL).
Qed.

Section Sched.
Variables (Job : eqType) (nR : nat) (nL : Lean.Nat).
Hypothesis Hn : SubNatRel nR nL.
Notation dJ := (ct_decidable_eq Job).
Notation LSched := (I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_schedule Job dJ nL).

Definition CpwSchedRel (sR : Schedule.schedule Job nR) (sL : LSched) : SProp :=
  forall oR oL, CoOrdRel nR nL oR oL -> forall tR tL, SubNatRel tR tL -> Lean.eq (cl_opt (sR oR tR)) (sL oL tL).

Definition cpw_sched_to_target (sR : Schedule.schedule Job nR) : LSched :=
  fun oL tL => cl_opt (sR (co_fin_to_ord nR nL Hn oL) (sub_nat_to_rocq tL)).

Definition cpw_sched_to_source (sL : LSched) : Schedule.schedule Job nR :=
  fun oR tR => cl_unopt (sL (co_ord_to_fin nR nL Hn oR) (sub_nat_to_imported tR)).

Lemma cpw_sched_canonical sR : CpwSchedRel sR (cpw_sched_to_target sR).
Proof.
  intros oR oL Ho tR tL Ht. apply: coq_eq_to_imported_eq. rewrite /cpw_sched_to_target (co_nat_input _ _ Ht).
  by rewrite (co_ord_eq _ _ _ _ _ Ho (co_ord_surjective nR nL Hn oL)).
Qed.

Lemma cpw_sched_surjective sL : CpwSchedRel (cpw_sched_to_source sL) sL.
Proof.
  intros oR oL Ho tR tL Ht. apply: coq_eq_to_imported_eq. rewrite /cpw_sched_to_source cl_opt_unopt.
  rewrite (co_nat_logic _ _ Ht). by rewrite (co_fin_rel_eq _ _ _ _ _ (co_ord_canonical nR nL Hn oR) Ho).
Qed.

Lemma cpw_forall_sched (PR : Schedule.schedule Job nR -> Prop) (PL : LSched -> SProp) :
  (forall sR sL, CpwSchedRel sR sL -> PropSPropRel (PR sR) (PL sL)) -> PropSPropRel (forall s, PR s) (forall s, PL s).
Proof. exact (cpw_forall_cover _ _ CpwSchedRel cpw_sched_to_target cpw_sched_to_source cpw_sched_canonical cpw_sched_surjective PR PL). Qed.

End Sched.

Section Arr.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).
Notation LArr := (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrival_sequence Job dJ).

Definition CpwArrRel (aR : ArrivalSequence.arrival_sequence Job) (aL : LArr) : SProp :=
  forall tR tL, SubNatRel tR tL -> ClListRel cid (aR tR) (aL tL).

Definition cpw_arr_to_target (aR : ArrivalSequence.arrival_sequence Job) : LArr :=
  fun tL => cl_map cid (aR (sub_nat_to_rocq tL)).

Definition cpw_arr_to_source (aL : LArr) : ArrivalSequence.arrival_sequence Job :=
  fun tR => cl_unmap cid (aL (sub_nat_to_imported tR)).

Lemma cpw_arr_canonical aR : CpwArrRel aR (cpw_arr_to_target aR).
Proof.
  intros tR tL Ht. have E := co_nat_logic _ _ Ht. subst tL.
  apply: coq_eq_to_imported_eq. rewrite /cpw_arr_to_target sub_nat_rocq_roundtrip. reflexivity.
Qed.

Lemma cpw_arr_surjective aL : CpwArrRel (cpw_arr_to_source aL) aL.
Proof.
  intros tR tL Ht. have E := co_nat_logic _ _ Ht. subst tL.
  apply: coq_eq_to_imported_eq. exact (cl_map_unmap cid cid (fun _ => Logic.eq_refl _) _).
Qed.

Lemma cpw_arrives_in aR aL (Ha : CpwArrRel aR aL) j :
  PropSPropRel (ArrivalSequence.arrives_in aR j)
    (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrives_in Job dJ aL j).
Proof. apply: ct_exists_nat => tR tL Ht. exact (cpw_mem Job j _ _ (Ha tR tL Ht)). Qed.

End Arr.

(* ------------------------------------------------------------------ *)
(** * Definitions *)

Section Defs.
Variables (Job : eqType) (nR : nat) (nL : Lean.Nat).
Hypothesis Hn : SubNatRel nR nL.
Notation dJ := (ct_decidable_eq Job).
Variables (sR : Schedule.schedule Job nR)
  (sL : I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_schedule Job dJ nL).
Hypothesis Hs : CpwSchedRel Job nR nL sR sL.

Lemma cpw_GS_scheduled_on j oR oL (Ho : CoOrdRel nR nL oR oL) tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (Schedule.scheduled_on sR j oR tR)
    (I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_scheduled_on Job dJ nL sL j oL tL).
Proof.
  apply: ct_decide_bool.
  exact (cpw_tr (Hs oR oL Ho tR tL Ht) (fun z => PropSPropRel (sR oR tR == Some j) (Lean.eq z (cl_opt (Some j))))
           (cpw_opt_eqb_rel Job (sR oR tR) (Some j))).
Qed.

Lemma cpw_GS_scheduled j tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (Schedule.scheduled sR j tR)
    (I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_scheduled Job dJ nL sL j tL).
Proof.
  apply: (co_exists_rel nR nL Hn). intros oR oL Ho. exact (cpw_GS_scheduled_on j oR oL Ho tR tL Ht).
Qed.

Lemma cpw_GS_service_at j tR tL (Ht : SubNatRel tR tL) :
  SubNatRel (Schedule.service_at sR j tR)
    (I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_service_at Job dJ nL sL j tL).
Proof.
  apply: coq_eq_to_imported_eq.
  rewrite (imported_eq_to_coq_eq _ _ (I.Prosa_Validation_ClassicParallelWorkloadBoundInterface_service_at_sum Job dJ nL sL j tL)).
  apply: imported_eq_to_coq_eq.
  rewrite /Schedule.service_at big_mkcond /=.
  apply: (co_sum_rel nR nL Hn). intros oR oL Ho.
  have H := cpw_GS_scheduled_on j oR oL Ho tR tL Ht.
  rewrite (ct_bool_rel_logic _ _ H). destruct (Schedule.scheduled_on sR j oR tR).
  - exact (sub_nat_rel_canonical 1).
  - exact (sub_nat_rel_canonical 0).
Qed.

Lemma cpw_service_at_fun j : CpwFunRel (fun t => Schedule.service_at sR j t)
    (fun t => I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_service_at Job dJ nL sL j t).
Proof. intros kR kL Hk. exact (cpw_GS_service_at j kR kL Hk). Qed.

Lemma cpw_GS_service j tR tL (Ht : SubNatRel tR tL) :
  SubNatRel (Schedule.service sR j tR)
    (I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_service Job dJ nL sL j tL).
Proof. exact (cpw_ico 0 _ tR tL _ _ (sub_nat_rel_canonical 0) Ht (cpw_service_at_fun j)). Qed.

Lemma cpw_GS_service_during j t1R t1L t2R t2L (H1 : SubNatRel t1R t1L) (H2 : SubNatRel t2R t2L) :
  SubNatRel (Schedule.service_during sR j t1R t2R)
    (I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_service_during Job dJ nL sL j t1L t2L).
Proof. exact (cpw_ico _ _ _ _ _ _ H1 H2 (cpw_service_at_fun j)). Qed.

Lemma cpw_GS_completed cR cL (Hc : CpwParRel Job cR cL) j tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (Schedule.completed cR sR j tR)
    (I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_completed Job dJ cL nL sL j tL).
Proof. exact (ct_decide_le _ _ _ _ (Hc j) (cpw_GS_service j tR tL Ht)). Qed.

Lemma cpw_make_sequence (o : option Job) :
  ClListRel cid (make_sequence o) (I.Prosa_Classic_Util_Notation_make_sequence Job (cl_opt o)).
Proof. destruct o as [x|]; exact (@Lean.eq_refl _ _). Qed.

Lemma cpw_GS_jobs_scheduled_at tR tL (Ht : SubNatRel tR tL) :
  ClListRel cid (Schedule.jobs_scheduled_at sR tR)
    (I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_jobs_scheduled_at Job dJ nL sL tL).
Proof.
  apply: (co_bigcat_rel Job nR nL Hn). intros oR oL Ho.
  exact (cpw_trs (Hs oR oL Ho tR tL Ht)
           (fun z => ClListRel cid (make_sequence (sR oR tR)) (I.Prosa_Classic_Util_Notation_make_sequence Job z))
           (cpw_make_sequence (sR oR tR))).
Qed.

Lemma cpw_GS_jobs_scheduled_between t1R t1L t2R t2L (H1 : SubNatRel t1R t1L) (H2 : SubNatRel t2R t2L) :
  ClListRel cid (Schedule.jobs_scheduled_between sR t1R t2R)
    (I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_jobs_scheduled_between Job dJ nL sL t1L t2L).
Proof.
  apply: cpw_undup_rel. apply: (cpw_bigcat_nat_rel Job (fun t => Schedule.jobs_scheduled_at sR t) _ _ _ _ _ _ H1 H2).
  intros kR kL Hk. exact (cpw_GS_jobs_scheduled_at kR kL Hk).
Qed.

Lemma cpw_GS_jobs_must_arrive_to_execute aR aL (Ha : CpwParRel Job aR aL) :
  PropSPropRel (Schedule.jobs_must_arrive_to_execute aR sR)
    (I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_jobs_must_arrive_to_execute Job dJ aL nL sL).
Proof.
  apply: ct_forall_identity => j. apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (ct_bool_truth _ _ (cpw_GS_scheduled j tR tL Ht)).
  exact (ct_bool_truth _ _ (ct_decide_le _ _ _ _ (Ha j) Ht)).
Qed.

Lemma cpw_GS_completed_jobs_dont_execute cR cL (Hc : CpwParRel Job cR cL) :
  PropSPropRel (Schedule.completed_jobs_dont_execute cR sR)
    (I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_completed_jobs_dont_execute Job dJ cL nL sL).
Proof.
  apply: ct_forall_identity => j. apply: ct_forall_nat => tR tL Ht.
  exact (sub_nat_le_correspondence _ _ _ _ (cpw_GS_service j tR tL Ht) (Hc j)).
Qed.

Lemma cpw_GS_jobs_come_from_arrival_sequence arrR arrL (Harr : CpwArrRel Job arrR arrL) :
  PropSPropRel (Schedule.jobs_come_from_arrival_sequence sR arrR)
    (I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_jobs_come_from_arrival_sequence Job dJ nL sL arrL).
Proof.
  apply: ct_forall_identity => j. apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (ct_bool_truth _ _ (cpw_GS_scheduled j tR tL Ht)).
  exact (cpw_arrives_in Job arrR arrL Harr j).
Qed.

End Defs.

Section TaskDefs.
Variables (Task Job : eqType) (nR : nat) (nL : Lean.Nat).
Hypothesis Hn : SubNatRel nR nL.
Notation dT := (ct_decidable_eq Task).
Notation dJ := (ct_decidable_eq Job).
Variables (sR : Schedule.schedule Job nR)
  (sL : I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_schedule Job dJ nL).
Hypothesis Hs : CpwSchedRel Job nR nL sR sL.
Variable job_task : Job -> Task.

Lemma cpw_GT_jobs_of_task_scheduled_between tsk t1R t1L t2R t2L
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
           (Logic.eq_sym (cl_list_logic _ _ _ (cpw_GS_jobs_scheduled_between Job nR nL Hn sR sL Hs _ _ _ _ H1 H2)))).
Qed.

End TaskDefs.

Lemma cpw_GS_processor nR nL (Hn : SubNatRel nR nL) :
  And (forall o : Schedule.processor nR, CoOrdRel nR nL o (co_ord_to_fin nR nL Hn o))
      (forall o : I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_processor nL,
         CoOrdRel nR nL (co_fin_to_ord nR nL Hn o) o).
Proof. exact (And_intro _ _ (co_ord_canonical nR nL Hn) (co_ord_surjective nR nL Hn)). Qed.

Lemma cpw_GS_schedule (Job : eqType) nR nL (Hn : SubNatRel nR nL) :
  And (forall s : Schedule.schedule Job nR, CpwSchedRel Job nR nL s (cpw_sched_to_target Job nR nL Hn s))
      (forall s : I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_schedule Job (ct_decidable_eq Job) nL,
         CpwSchedRel Job nR nL (cpw_sched_to_source Job nR nL Hn s) s).
Proof. exact (And_intro _ _ (cpw_sched_canonical Job nR nL Hn) (cpw_sched_surjective Job nR nL Hn)). Qed.

(* ------------------------------------------------------------------ *)
(** * Statements *)

(** The common prefix [forall num_cpus (sched : schedule Job num_cpus)]. *)
Lemma cpw_forall_ncpus_sched (Job : eqType)
    (PR : forall n : nat, Schedule.schedule Job n -> Prop)
    (PL : forall n : Lean.Nat, I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_schedule Job (ct_decidable_eq Job) n -> SProp) :
  (forall nR nL (Hn : SubNatRel nR nL) sR sL, CpwSchedRel Job nR nL sR sL -> PropSPropRel (PR nR sR) (PL nL sL)) ->
  PropSPropRel (forall n s, PR n s) (forall n s, PL n s).
Proof.
  intro H. apply: ct_forall_nat => nR nL Hn. exact (cpw_forall_sched Job nR nL Hn _ _ (H nR nL Hn)).
Qed.

Notation sa := cpw_GS_service_at.
Notation sd := cpw_GS_service_during.
Notation sc := cpw_GS_scheduled.

(* ------------------------------------------------------------------ *)
(** * Generic covers and helpers *)

Lemma cpg_forall_cover (A B : Type) (Rel : A -> B -> SProp) (toB : A -> B) (toA : B -> A)
    (HB : forall a, Rel a (toB a)) (HA : forall b, Rel (toA b) b) (PR : A -> Prop) (PL : B -> SProp) :
  (forall a b, Rel a b -> PropSPropRel (PR a) (PL b)) -> PropSPropRel (forall a, PR a) (forall b, PL b).
Proof.
  intro H. apply prop_sprop_rel_intro.
  - intros HR b. exact (prop_to_sprop _ _ (H _ _ (HA b)) (HR _)).
  - intro HL. apply strictly_inhabits. intro a. exact (sprop_to_prop _ _ (H _ _ (HB a)) (HL _)).
Qed.

Lemma cpg_false_rel : PropSPropRel Logic.False I.False.
Proof.
  apply prop_sprop_rel_intro.
  - exact ct_coq_false_to_target.
  - exact ct_target_false_to_strict.
Qed.

Lemma cpg_ne (T : Type) (x y : T) : PropSPropRel (x <> y) (I.Ne T x y).
Proof. exact (ct_imp _ _ _ _ (ct_eq_rel T x y) cpg_false_rel). Qed.

Lemma cpg_mem (T : eqType) x s sL : ClListRel cid s sL ->
  PropSPropRel (x \in s) (I.Membership_mem T (I.List T) (I.List_instMembership T) sL x).
Proof. exact (cl_mem_rel_list T T cid cid (fun _ => Logic.eq_refl _) x s sL). Qed.

Lemma cpg_uniq (T : eqType) s sL : ClListRel cid s sL -> PropSPropRel (uniq s) (I.List_Nodup T sL).
Proof. exact (cl_uniq_rel_list T T cid cid (fun _ => Logic.eq_refl _) (fun _ => Logic.eq_refl _) s sL). Qed.

Lemma cpg_unmap_rel (T : Type) (l : I.List T) : ClListRel cid (cl_unmap cid l) l.
Proof. apply: coq_eq_to_imported_eq. exact (cl_map_unmap cid cid (fun _ => Logic.eq_refl _) l). Qed.

Lemma cpg_cl_map_inj (T : Type) (s1 s2 : seq T) : Logic.eq (cl_map cid s1) (cl_map cid s2) -> Logic.eq s1 s2.
Proof.
  intro E. rewrite -(cl_unmap_map cid cid (fun _ => Logic.eq_refl _) s1) -(cl_unmap_map cid cid (fun _ => Logic.eq_refl _) s2).
  by rewrite E.
Qed.

Lemma cpg_succ_rel nR nL : SubNatRel nR nL ->
  SubNatRel nR.+1 (I.HAdd_hAdd_inst7 Lean.Nat Lean.Nat Lean.Nat (I.instHAdd_inst1 Lean.Nat I.instAddNat) nL
                     (I.OfNat_ofNat_inst1 Lean.Nat 1 (I.instOfNatNat 1))).
Proof. intro Hn. exact (sub_imported_eq_congr Lean.Nat_succ _ _ Hn). Qed.

(* ------------------------------------------------------------------ *)
(** * Big concatenation over a half-open interval (as in the accepted arrival_sequence certificate) *)

Lemma cpg_forall_list (T : Type) (PR : seq T -> Prop) (PL : I.List T -> SProp) :
  (forall sR sL, ClListRel (B := T) cid sR sL -> PropSPropRel (PR sR) (PL sL)) -> PropSPropRel (forall s, PR s) (forall s, PL s).
Proof.
  exact (cpg_forall_cover _ _ (fun sR sL => ClListRel (B := T) cid sR sL) (cl_map cid) (cl_unmap cid)
           (fun s => @Lean.eq_refl _ _) (fun l => cpg_unmap_rel T l) PR PL).
Qed.

(* ------------------------------------------------------------------ *)
(** * Stable sorting: MathComp [sort] against the core [List.mergeSort] *)

Section SortUniq.
Variables (T : eqType) (f : T -> nat).
Notation leT := (fun a b : T => f a <= f b).
Notation cls x := (fun y : T => f y == f x).

Lemma cpg_leT_trans : transitive leT.
Proof. move=> y x z. exact: leq_trans. Qed.

Lemma cpg_leT_total : total leT.
Proof. move=> a b. exact: leq_total. Qed.

Lemma cpg_class_sorted x : forall l : seq T, all (cls x) l -> sorted leT l.
Proof.
  case => [|a l] //= /andP [Ha Hl]. elim: l a Ha Hl => [|b l IH] a Ha //= /andP [Hb Hl].
  rewrite (eqP Ha) (eqP Hb) leqnn /=. exact: IH.
Qed.

Lemma cpg_sort_filter_class s x : filter (cls x) (sort leT s) = filter (cls x) s.
Proof.
  rewrite (filter_sort cpg_leT_total cpg_leT_trans).
  apply: (sorted_sort cpg_leT_trans). apply: cpg_class_sorted. exact: filter_all.
Qed.

Lemma cpg_sorted_class_uniq : forall u t : seq T, sorted leT u -> sorted leT t ->
  (forall x, filter (cls x) u = filter (cls x) t) -> u = t.
Proof.
  elim => [|a u IH] t Su St H.
  { case: t St H => [//|b t] St H. by have := H b; rewrite /= eqxx. }
  case: t St H => [|b t] St H; first by have := H a; rewrite /= eqxx.
  have Ma : all (leT a) u := order_path_min cpg_leT_trans Su.
  have Mb : all (leT b) t := order_path_min cpg_leT_trans St.
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

Lemma cpg_sort_unique (u s : seq T) : sorted leT u -> (forall x, filter (cls x) u = filter (cls x) s) -> u = sort leT s.
Proof.
  move=> Su H. apply: cpg_sorted_class_uniq => //.
  - exact: (sort_sorted cpg_leT_total).
  - move=> x. by rewrite cpg_sort_filter_class H.
Qed.

End SortUniq.

Section Chain.
Variables (T : Type) (leR : T -> T -> bool) (leL : T -> T -> I.Bool).
Hypothesis HR : forall a b, CtBoolRel (leR a b) (leL a b).
Notation RL := (fun a b : T => Lean.eq (leL a b) I.Bool_true).

Inductive CpgTrue : SProp := cpg_true_intro.

Definition cpg_chain_head (x y : T) (l : I.List T) (H : I.List_IsChain T RL (I.List_cons T x (I.List_cons T y l))) : RL x y :=
  match H in I.List_IsChain _ _ L
    return (match L with I.List_cons a (I.List_cons b _) => RL a b | _ => CpgTrue end) with
  | I.List_IsChain_nil => cpg_true_intro
  | I.List_IsChain_singleton _ => cpg_true_intro
  | I.List_IsChain_cons_cons a b l h _ => h
  end.

Definition cpg_chain_tail (x y : T) (l : I.List T) (H : I.List_IsChain T RL (I.List_cons T x (I.List_cons T y l))) :
    I.List_IsChain T RL (I.List_cons T y l) :=
  match H in I.List_IsChain _ _ L
    return (match L with I.List_cons _ (I.List_cons b l') => I.List_IsChain T RL (I.List_cons T b l') | _ => CpgTrue end) with
  | I.List_IsChain_nil => cpg_true_intro
  | I.List_IsChain_singleton _ => cpg_true_intro
  | I.List_IsChain_cons_cons a b l _ t => t
  end.

Fixpoint cpg_path_backward (x : T) (s : seq T) : I.List_IsChain T RL (I.List_cons T x (cl_map cid s)) -> StrictlyInhabited (path leR x s) :=
  match s as s0 return I.List_IsChain T RL (I.List_cons T x (cl_map cid s0)) -> StrictlyInhabited (path leR x s0) with
  | [::] => fun _ => strictly_inhabits (Logic.eq_refl true)
  | y :: s' => fun H =>
      match cpg_path_backward y s' (cpg_chain_tail x y _ H) with
      | strictly_inhabits Hp =>
          strictly_inhabits (introT andP (conj (sprop_to_prop _ _ (ct_bool_truth _ _ (HR x y)) (cpg_chain_head x y _ H)) Hp))
      end
  end.

Lemma cpg_sorted_backward s : I.List_IsChain T RL (cl_map cid s) -> StrictlyInhabited (sorted leR s).
Proof.
  destruct s as [|x s].
  - intros _. exact (strictly_inhabits (Logic.eq_refl true)).
  - exact (cpg_path_backward x s).
Qed.

End Chain.

Section Sort.
Variables (T : eqType) (f : T -> nat) (fL : T -> Lean.Nat).
Hypothesis Hf : forall x, SubNatRel (f x) (fL x).
Notation leL := (fun j j' : T => I.Decidable_decide (I.LE_le_inst1 Lean.Nat I.instLENat (fL j) (fL j')) (I.Nat_decLe (fL j) (fL j'))).
Notation clsL x := (fun y : T => I.Decidable_decide (Lean.eq (fL y) (fL x)) (I.instDecidableEqNat (fL y) (fL x))).

Lemma cpg_sort_rel s sL : ClListRel cid s sL ->
  ClListRel cid (sort (fun j j' => f j <= f j') s) (I.List_mergeSort T sL leL).
Proof.
  intro Hs.
  pose m := I.List_mergeSort T sL leL. pose u := cl_unmap cid m.
  have Hu : ClListRel cid u m := cpg_unmap_rel T m.
  have Su : sorted (fun a b => f a <= f b) u :=
    interpret_strict _
      (cpg_sorted_backward T (fun a b => f a <= f b) leL (fun a b => ct_decide_le _ _ _ _ (Hf a) (Hf b)) u
         (match Hu in Lean.eq _ z
                return I.List_IsChain T (fun a b => Lean.eq (leL a b) I.Bool_true) z ->
                       I.List_IsChain T (fun a b => Lean.eq (leL a b) I.Bool_true) (cl_map cid u) with
          | Lean.eq_refl => fun h => h
          end (I.Prosa_Validation_ClassicParallelWorkloadBoundInterface_mergeSort_isChain T fL sL))).
  have Fu : forall x, filter (fun y => f y == f x) u = filter (fun y => f y == f x) s.
  { intro x. apply: cpg_cl_map_inj.
    have Hp : forall y, CtBoolRel (f y == f x) (clsL x y) := fun y => ct_decide_eq_nat _ _ _ _ (Hf y) (Hf x).
    refine (Logic.eq_trans (cl_filter cid (fun y => f y == f x) (clsL x) Hp u)
              (Logic.eq_trans _ (Logic.eq_sym (cl_filter cid (fun y => f y == f x) (clsL x) Hp s)))).
    refine (Logic.eq_trans (f_equal (I.List_filter T (clsL x)) (Logic.eq_sym (cl_list_logic _ _ _ Hu)))
              (Logic.eq_trans _ (f_equal (I.List_filter T (clsL x)) (cl_list_logic _ _ _ Hs)))).
    exact (imported_eq_to_coq_eq _ _ (I.Prosa_Validation_ClassicParallelWorkloadBoundInterface_mergeSort_filter_class T fL x sL)). }
  have E := cpg_sort_unique T f u s Su Fu.
  apply: coq_eq_to_imported_eq. rewrite -E. exact (Logic.eq_sym (cl_list_logic _ _ _ Hu)).
Qed.

End Sort.

Lemma cpg_getD (T : Type) (s : seq T) sL (Hs : ClListRel cid s sL) (x0 : T) nR nL (Hn : SubNatRel nR nL) :
  Logic.eq (I.List_getD T sL nL x0) (nth x0 s nR).
Proof.
  rewrite (cl_list_logic _ _ _ Hs) (cl_nat_logic _ _ Hn). exact (Logic.eq_sym (cl_nth cid x0 s nR)).
Qed.

Lemma cpg_pred_rel nR nL : SubNatRel nR nL ->
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

Lemma cpw_sum_canonical (xs : seq X) :
  SubNatRel (\sum_(x <- xs) FR x) (I.Prosa_Util_Sum_sumSeq X (cl_map cid xs) FL).
Proof.
  induction xs as [|x xs IH].
  - rewrite big_nil.
    exact (sub_imported_eq_sym _ _ (I.Prosa_Validation_ClassicParallelWorkloadBoundInterface_production_sumSeq_nil X FL)).
  - rewrite big_cons. cbn [cl_map].
    refine (sub_imported_eq_trans _ _ _ _ (sub_imported_eq_sym _ _
      (I.Prosa_Validation_ClassicParallelWorkloadBoundInterface_production_sumSeq_cons X FL x (cl_map cid xs)))).
    exact (sub_add_correspondence _ _ _ _ (HF x) IH).
Qed.

Lemma cpw_sum_rel xsR xsL : ClListRel cid xsR xsL ->
  SubNatRel (\sum_(x <- xsR) FR x) (I.Prosa_Util_Sum_sumSeq X xsL FL).
Proof.
  intro Hxs.
  exact (sub_imported_eq_trans _ _ _ (cpw_sum_canonical xsR)
    (sub_imported_eq_congr (fun l => I.Prosa_Util_Sum_sumSeq X l FL) _ _ Hxs)).
Qed.

Variable PR : X -> bool.
Variable PL : X -> I.Bool.
Hypothesis HP : forall x, CtBoolRel (PR x) (PL x).

Lemma cpw_sum_filtered_canonical (xs : seq X) :
  SubNatRel (\sum_(x <- xs | PR x) FR x) (I.Prosa_Util_Sum_sumFiltered X (cl_map cid xs) PL FL).
Proof.
  induction xs as [|x xs IH].
  - rewrite big_nil.
    exact (sub_imported_eq_sym _ _ (I.Prosa_Validation_ClassicParallelWorkloadBoundInterface_production_sumFiltered_nil X PL FL)).
  - rewrite big_cons. cbn [cl_map].
    have Hx := HP x. unfold CtBoolRel in Hx.
    destruct (PR x).
    + refine (sub_imported_eq_trans _ _ _ _ (sub_imported_eq_sym _ _
        (I.Prosa_Validation_ClassicParallelWorkloadBoundInterface_production_sumFiltered_cons_true
          X PL FL x (cl_map cid xs) (sub_imported_eq_sym _ _ Hx)))).
      exact (sub_add_correspondence _ _ _ _ (HF x) IH).
    + exact (sub_imported_eq_trans _ _ _ IH (sub_imported_eq_sym _ _
        (I.Prosa_Validation_ClassicParallelWorkloadBoundInterface_production_sumFiltered_cons_false
          X PL FL x (cl_map cid xs) (sub_imported_eq_sym _ _ Hx)))).
Qed.

Lemma cpw_sum_filtered_rel xsR xsL : ClListRel cid xsR xsL ->
  SubNatRel (\sum_(x <- xsR | PR x) FR x) (I.Prosa_Util_Sum_sumFiltered X xsL PL FL).
Proof.
  intro Hxs.
  exact (sub_imported_eq_trans _ _ _ (cpw_sum_filtered_canonical xsR)
    (sub_imported_eq_congr (fun l => I.Prosa_Util_Sum_sumFiltered X l PL FL) _ _ Hxs)).
Qed.

End SeqSums.

Definition CpwPredRel (T : Type) (pR : T -> bool) (pL : T -> I.Bool) : SProp := forall x, CtBoolRel (pR x) (pL x).

Lemma cpw_forall_pred (T : Type) (PR : (T -> bool) -> Prop) (PL : (T -> I.Bool) -> SProp) :
  (forall pR pL, CpwPredRel T pR pL -> PropSPropRel (PR pR) (PL pL)) -> PropSPropRel (forall p, PR p) (forall p, PL p).
Proof.
  exact (cpw_forall_cover _ _ (CpwPredRel T) (fun pR x => ct_b2l (pR x)) (fun pL x => ct_l2b (pL x))
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




(* ------------------------------------------------------------------ *)
(** * Workload (as in the accepted classic workload certificate) *)

Section Wl.
Variables (Task Job : eqType) (nR : nat) (nL : Lean.Nat).
Hypothesis Hn : SubNatRel nR nL.
Notation dT := (ct_decidable_eq Task).
Notation dJ := (ct_decidable_eq Job).
Variables (sR : Schedule.schedule Job nR)
  (sL : I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_schedule Job dJ nL).
Hypothesis Hs : CpwSchedRel Job nR nL sR sL.
Variable job_task : Job -> Task.

Lemma cpw_service_of_task tsk (oR : 'I_nR) (oL : Fin nL) (o : option Job) :
  SubNatRel (Workload.service_of_task job_task tsk oR o)
    (I.Prosa_Classic_Model_Schedule_Global_Workload_Workload_service_of_task Task Job dT dJ job_task nL tsk oL (cl_opt o)).
Proof.
  destruct o as [x|].
  - exact (ct_bool_to_nat _ _ (ct_decide_eq Task (job_task x) tsk)).
  - exact (sub_nat_rel_canonical 0).
Qed.

Lemma cpw_workload tsk t1R t1L t2R t2L (H1 : SubNatRel t1R t1L) (H2 : SubNatRel t2R t2L) :
  SubNatRel (Workload.workload job_task sR tsk t1R t2R)
    (I.Prosa_Classic_Model_Schedule_Global_Workload_Workload_workload Task Job dT dJ job_task nL sL tsk t1L t2L).
Proof.
  apply: (cpw_ico _ _ _ _ _ _ H1 H2) => tR tL Ht.
  apply: (co_sum_rel nR nL Hn) => oR oL Ho.
  exact (cpw_trs (Hs oR oL Ho tR tL Ht)
           (fun z => SubNatRel (Workload.service_of_task job_task tsk oR (sR oR tR))
                       (I.Prosa_Classic_Model_Schedule_Global_Workload_Workload_service_of_task Task Job dT dJ job_task nL tsk oL z))
           (cpw_service_of_task tsk oR oL (sR oR tR))).
Qed.

Lemma cpw_workload_joblist tsk t1R t1L t2R t2L (H1 : SubNatRel t1R t1L) (H2 : SubNatRel t2R t2L) :
  SubNatRel (Workload.workload_joblist job_task sR tsk t1R t2R)
    (I.Prosa_Classic_Model_Schedule_Global_Workload_Workload_workload_joblist Task Job dT dJ job_task nL sL tsk t1L t2L).
Proof.
  exact (cpw_sum_rel Job _ _ (fun j => cpw_GS_service_during Job nR nL Hn sR sL Hs j _ _ _ _ H1 H2) _ _ (cpw_GT_jobs_of_task_scheduled_between Task Job nR nL Hn sR sL Hs job_task tsk _ _ _ _ H1 H2)).
Qed.
End Wl.

(* ------------------------------------------------------------------ *)
(** * The sorted scheduled jobs of the analysed task *)

Notation LSJ Task Job job_task nL sL tsk t1L dL :=
  (I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_ScheduleOfSporadicTask_jobs_of_task_scheduled_between Task Job (ct_decidable_eq Task) (ct_decidable_eq Job) job_task nL sL tsk t1L
     (I.HAdd_hAdd_inst7 Lean.Nat Lean.Nat Lean.Nat (I.instHAdd_inst1 Lean.Nat I.instAddNat) t1L dL)).
Notation LSORT Job jaL l :=
  (I.List_mergeSort Job l (fun x y => I.Decidable_decide (I.LE_le_inst1 Lean.Nat I.instLENat (jaL x) (jaL y)) (I.Nat_decLe (jaL x) (jaL y)))).

Lemma cpw_t2 t1R t1L dR dL (H1 : SubNatRel t1R t1L) (Hd : SubNatRel dR dL) :
  SubNatRel (t1R + dR) (I.HAdd_hAdd_inst7 Lean.Nat Lean.Nat Lean.Nat (I.instHAdd_inst1 Lean.Nat I.instAddNat) t1L dL).
Proof. exact (sub_add_correspondence _ _ _ _ H1 Hd). Qed.

Lemma cpw_sorted (Task Job : eqType) nR nL (Hn : SubNatRel nR nL) sR sL (Hs : CpwSchedRel Job nR nL sR sL)
    jaR jaL (Hja : CpwParRel Job jaR jaL) (job_task : Job -> Task) tsk t1R t1L dR dL (H1 : SubNatRel t1R t1L) (Hd : SubNatRel dR dL) :
  ClListRel cid (sort (fun x y => jaR x <= jaR y) (ScheduleOfSporadicTask.jobs_of_task_scheduled_between job_task sR tsk t1R (t1R + dR)))
    (LSORT Job jaL (LSJ Task Job job_task nL sL tsk t1L dL)).
Proof.
  exact (cpg_sort_rel Job jaR jaL Hja _ _ (cpw_GT_jobs_of_task_scheduled_between Task Job nR nL Hn sR sL Hs job_task tsk _ _ _ _ H1 (cpw_t2 _ _ _ _ H1 Hd))).
Qed.

Lemma cpw_add2 nR nL : SubNatRel nR nL ->
  SubNatRel nR.+2 (I.HAdd_hAdd_inst7 Lean.Nat Lean.Nat Lean.Nat (I.instHAdd_inst1 Lean.Nat I.instAddNat) nL
                     (I.OfNat_ofNat_inst1 Lean.Nat 2 (I.instOfNatNat 2))).
Proof.
  intro H. apply: coq_eq_to_imported_eq. rewrite -addn2.
  exact (imported_eq_to_coq_eq _ _ (sub_add_correspondence _ _ 2 _ H (sub_nat_rel_canonical 2))).
Qed.

(* ------------------------------------------------------------------ *)
(** * Task, job and arrival-model relations (as in the accepted classic task, job and task_arrival certificates) *)

Lemma cpw_forall_arr (Job : eqType) PR PL :
  (forall aR aL, CpwArrRel Job aR aL -> PropSPropRel (PR aR) (PL aL)) -> PropSPropRel (forall a, PR a) (forall a, PL a).
Proof. exact (cpw_forall_cover _ _ (CpwArrRel Job) (cpw_arr_to_target Job) (cpw_arr_to_source Job) (cpw_arr_canonical Job) (cpw_arr_surjective Job) PR PL). Qed.

Lemma cpw_valid_sporadic_job (Task Job : eqType) tcR tcL (Htc : CpwParRel Task tcR tcL) tdR tdL (Htd : CpwParRel Task tdR tdL)
    cR cL (Hc : CpwParRel Job cR cL) dR dL (Hd : CpwParRel Job dR dL) (job_task : Job -> Task) j :
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

Lemma cpw_valid_params (Task Job : eqType) tcR tcL (Htc : CpwParRel Task tcR tcL) tdR tdL (Htd : CpwParRel Task tdR tdL)
    cR cL (Hc : CpwParRel Job cR cL) dR dL (Hd : CpwParRel Job dR dL) (job_task : Job -> Task) aR aL (Ha : CpwArrRel Job aR aL) :
  PropSPropRel (forall j, ArrivalSequence.arrives_in aR j -> Job.valid_sporadic_job tcR tdR cR dR job_task j)
    (forall j, I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrives_in Job (ct_decidable_eq Job) aL j ->
       I.Prosa_Classic_Model_Arrival_Basic_Job_Job_valid_sporadic_job Task (ct_decidable_eq Task) tcL tdL Job (ct_decidable_eq Job) cL dL job_task j).
Proof.
  apply: ct_forall_identity => j.
  exact (ct_imp _ _ _ _ (cpw_arrives_in Job aR aL Ha j) (cpw_valid_sporadic_job Task Job tcR tcL Htc tdR tdL Htd cR cL Hc dR dL Hd job_task j)).
Qed.

Lemma cpw_sporadic_task_model (Task Job : eqType) tpR tpL (Htp : CpwParRel Task tpR tpL) jaR jaL (Hja : CpwParRel Job jaR jaL)
    (job_task : Job -> Task) aR aL (Ha : CpwArrRel Job aR aL) :
  PropSPropRel (TaskArrival.sporadic_task_model tpR jaR job_task aR)
    (I.Prosa_Classic_Model_Arrival_Basic_TaskArrival_TaskArrival_sporadic_task_model Task (ct_decidable_eq Task) tpL Job (ct_decidable_eq Job) jaL job_task aL).
Proof.
  apply: ct_forall_identity => j. apply: ct_forall_identity => j'.
  apply: ct_imp; first exact (cpg_ne Job j j').
  apply: ct_imp; first exact (cpw_arrives_in Job aR aL Ha j).
  apply: ct_imp; first exact (cpw_arrives_in Job aR aL Ha j').
  apply: ct_imp; first exact (ct_eq_rel Task (job_task j) (job_task j')).
  apply: ct_imp; first exact (sub_nat_le_correspondence _ _ _ _ (Hja j) (Hja j')).
  exact (sub_nat_le_correspondence _ _ _ _ (sub_add_correspondence _ _ _ _ (Hja j) (Htp (job_task j))) (Hja j')).
Qed.

Lemma cpw_valid_sporadic_task (Task : eqType) cR cL (Hc : CpwParRel Task cR cL) pR pL (Hp : CpwParRel Task pR pL)
    dR dL (Hd : CpwParRel Task dR dL) tsk :
  PropSPropRel (SporadicTask.is_valid_sporadic_task cR pR dR tsk)
    (I.Prosa_Classic_Model_Arrival_Basic_Task_SporadicTask_is_valid_sporadic_task Task (ct_decidable_eq Task) cL pL dL tsk).
Proof.
  apply: ct_and; first exact (ct_bool_truth _ _ (ct_decide_lt _ _ _ _ (sub_nat_rel_canonical 0) (Hc tsk))).
  apply: ct_and; first exact (ct_bool_truth _ _ (ct_decide_lt _ _ _ _ (sub_nat_rel_canonical 0) (Hp tsk))).
  apply: ct_and; first exact (ct_bool_truth _ _ (ct_decide_lt _ _ _ _ (sub_nat_rel_canonical 0) (Hd tsk))).
  apply: ct_and; first exact (ct_bool_truth _ _ (ct_decide_le _ _ _ _ (Hc tsk) (Hd tsk))).
  exact (ct_bool_truth _ _ (ct_decide_le _ _ _ _ (Hc tsk) (Hp tsk))).
Qed.

Lemma cpw_rt_bound (Task Job : eqType) nR nL (Hn : SubNatRel nR nL) sR sL (Hs : CpwSchedRel Job nR nL sR sL)
    jaR jaL (Hja : CpwParRel Job jaR jaL) cR cL (Hc : CpwParRel Job cR cL) (job_task : Job -> Task) aR aL (Ha : CpwArrRel Job aR aL)
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
  apply: ct_imp; first exact (cpw_arrives_in Job aR aL Ha j).
  apply: ct_imp; first exact (ct_eq_rel Task (job_task j) tsk).
  have HjR := sub_add_correspondence _ _ _ _ (Hja j) HR.
  apply: ct_imp; first exact (sub_nat_lt_correspondence _ _ _ _ HjR (cpw_t2 _ _ _ _ H1 Hd)).
  exact (ct_bool_truth _ _ (cpw_GS_completed Job nR nL Hn sR sL Hs cR cL Hc j _ _ HjR)).
Qed.

(* ------------------------------------------------------------------ *)
(** * Definitions *)

Theorem WorkloadBound_max_jobs_correspondence (Task : eqType) pR pL (Hp : CpwParRel Task pR pL) tsk
    RR RL (HR : SubNatRel RR RL) dR dL (Hd : SubNatRel dR dL) :
  SubNatRel (WorkloadBound.max_jobs pR tsk RR dR) (I.Prosa_Classic_Analysis_Global_Parallel_WorkloadBound_WorkloadBound_max_jobs Task (ct_decidable_eq Task) pL tsk RL dL).
Proof. exact (dm_div_ceil_correspondence _ _ _ _ (dm_add_correspondence _ _ _ _ Hd HR) (Hp tsk)). Qed.

Theorem WorkloadBound_W_correspondence (Task : eqType) cR cL (Hc : CpwParRel Task cR cL) pR pL (Hp : CpwParRel Task pR pL) tsk
    RR RL (HR : SubNatRel RR RL) dR dL (Hd : SubNatRel dR dL) :
  SubNatRel (WorkloadBound.W cR pR tsk RR dR) (I.Prosa_Classic_Analysis_Global_Parallel_WorkloadBound_WorkloadBound_W Task (ct_decidable_eq Task) cL pL tsk RL dL).
Proof.
  exact (dm_mul_correspondence _ _ _ _ (WorkloadBound_max_jobs_correspondence Task pR pL Hp tsk RR RL HR dR dL Hd) (Hc tsk)).
Qed.

(* ------------------------------------------------------------------ *)
(** * Statements *)

Notation sorted := cpw_sorted.
Notation getD := cpg_getD.

Definition src_W_monotonic (Task : eqType) : Prop := ltac:(type_of_term (@WorkloadBound.W_monotonic Task)).
Definition tgt_W_monotonic (Task : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Analysis_Global_Parallel_WorkloadBound_WorkloadBound_W_monotonic Task (ct_decidable_eq Task))).
Theorem WorkloadBound_W_monotonic_correspondence (Task : eqType) :
  PropSPropRel (src_W_monotonic Task) (tgt_W_monotonic Task).
Proof.
  unfold src_W_monotonic, tgt_W_monotonic.
  apply: cpw_forall_par => task_costR task_costL Htask_cost. apply: cpw_forall_par => task_periodR task_periodL Htask_period.
  apply: ct_forall_identity => tsk.
  apply: ct_imp; first exact (sub_nat_lt_correspondence _ _ _ _ (sub_nat_rel_canonical 0) (Htask_period tsk)).
  apply: ct_forall_nat => R1R R1L H1. apply: ct_forall_nat => R2R R2L H2.
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
  ltac:(type_of_term (I.Prosa_Classic_Analysis_Global_Parallel_WorkloadBound_WorkloadBound_workload_bound_simpl_by_sorting_scheduled_jobs Task (ct_decidable_eq Task) Job (ct_decidable_eq Job))).
Theorem WorkloadBound_workload_bound_simpl_by_sorting_scheduled_jobs_correspondence (Task Job : eqType) :
  PropSPropRel (src_workload_bound_simpl_by_sorting_scheduled_jobs Task Job) (tgt_workload_bound_simpl_by_sorting_scheduled_jobs Task Job).
Proof.
  unfold src_workload_bound_simpl_by_sorting_scheduled_jobs, tgt_workload_bound_simpl_by_sorting_scheduled_jobs.
  apply: cpw_forall_par => jaR jaL Hja.
  apply: ct_forall_identity => job_task.
  apply: cpw_forall_ncpus_sched => nR nL Hn sR sL Hs.
  apply: ct_forall_identity => tsk.
  apply: ct_forall_nat => t1R t1L H1. apply: ct_forall_nat => dR dL Hd.
  have Hs' := sorted Task Job nR nL Hn sR sL Hs jaR jaL Hja job_task tsk _ _ _ _ H1 Hd.
  apply: sub_nat_eq_correspondence.
  - exact (cpw_workload_joblist Task Job nR nL Hn sR sL Hs job_task tsk _ _ _ _ H1 (cpw_t2 _ _ _ _ H1 Hd)).
  - exact (cpw_sum_rel Job _ _ (fun i => (cpw_GS_service_during Job nR nL Hn sR sL Hs (i) _ _ _ _ H1 (cpw_t2 _ _ _ _ H1 Hd))) _ _ Hs').
Qed.

Definition src_workload_bound_job_in_same_sequence (Task Job : eqType) : Prop :=
  ltac:(type_of_term (@WorkloadBound.workload_bound_job_in_same_sequence Task Job)).
Definition tgt_workload_bound_job_in_same_sequence (Task Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Analysis_Global_Parallel_WorkloadBound_WorkloadBound_workload_bound_job_in_same_sequence Task (ct_decidable_eq Task) Job (ct_decidable_eq Job))).
Theorem WorkloadBound_workload_bound_job_in_same_sequence_correspondence (Task Job : eqType) :
  PropSPropRel (src_workload_bound_job_in_same_sequence Task Job) (tgt_workload_bound_job_in_same_sequence Task Job).
Proof.
  unfold src_workload_bound_job_in_same_sequence, tgt_workload_bound_job_in_same_sequence.
  apply: cpw_forall_par => jaR jaL Hja.
  apply: ct_forall_identity => job_task.
  apply: cpw_forall_ncpus_sched => nR nL Hn sR sL Hs.
  apply: ct_forall_identity => tsk.
  apply: ct_forall_nat => t1R t1L H1. apply: ct_forall_nat => dR dL Hd.
  apply: ct_forall_identity => j.
  have Hs' := sorted Task Job nR nL Hn sR sL Hs jaR jaL Hja job_task tsk _ _ _ _ H1 Hd.
  apply: ct_bool_eq.
  - exact (ct_decide_bool _ _ _ (cpw_mem Job j _ _ (cpw_GT_jobs_of_task_scheduled_between Task Job nR nL Hn sR sL Hs job_task tsk _ _ _ _ H1 (cpw_t2 _ _ _ _ H1 Hd)))).
  - exact (ct_decide_bool _ _ _ (cpw_mem Job j _ _ Hs')).
Qed.

Definition src_workload_bound_all_jobs_from_tsk (Task Job : eqType) : Prop :=
  ltac:(type_of_term (@WorkloadBound.workload_bound_all_jobs_from_tsk Task Job)).
Definition tgt_workload_bound_all_jobs_from_tsk (Task Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Analysis_Global_Parallel_WorkloadBound_WorkloadBound_workload_bound_all_jobs_from_tsk Task (ct_decidable_eq Task) Job (ct_decidable_eq Job))).
Theorem WorkloadBound_workload_bound_all_jobs_from_tsk_correspondence (Task Job : eqType) :
  PropSPropRel (src_workload_bound_all_jobs_from_tsk Task Job) (tgt_workload_bound_all_jobs_from_tsk Task Job).
Proof.
  unfold src_workload_bound_all_jobs_from_tsk, tgt_workload_bound_all_jobs_from_tsk.
  apply: cpw_forall_par => jaR jaL Hja.
  apply: ct_forall_identity => job_task.
  apply: cpw_forall_arr => aR aL Ha.
  apply: cpw_forall_ncpus_sched => nR nL Hn sR sL Hs.
  apply: ct_imp; first exact (cpw_GS_jobs_come_from_arrival_sequence Job nR nL Hn sR sL Hs aR aL Ha).
  apply: ct_forall_identity => tsk.
  apply: ct_forall_nat => t1R t1L H1. apply: ct_forall_nat => dR dL Hd.
  apply: ct_forall_identity => j_i.
  have Hs' := sorted Task Job nR nL Hn sR sL Hs jaR jaL Hja job_task tsk _ _ _ _ H1 Hd.
  apply: ct_imp; first exact (cpw_mem Job j_i _ _ Hs').
  apply: ct_and; first exact (cpw_arrives_in Job aR aL Ha j_i).
  apply: ct_and; first exact (ct_eq_rel Task (job_task j_i) tsk).
  apply: ct_and; first exact (ct_bool_truth _ _ (ct_bool_not _ _ (ct_decide_eq_nat _ _ _ _ (cpw_GS_service_during Job nR nL Hn sR sL Hs (j_i) _ _ _ _ H1 (cpw_t2 _ _ _ _ H1 Hd)) (sub_nat_rel_canonical 0)))).
  exact (cpw_mem Job j_i _ _ (cpw_GS_jobs_scheduled_between Job nR nL Hn sR sL Hs _ _ _ _ H1 (cpw_t2 _ _ _ _ H1 Hd))).
Qed.

Definition src_workload_bound_jobs_ordered_by_arrival (Task Job : eqType) : Prop :=
  ltac:(type_of_term (@WorkloadBound.workload_bound_jobs_ordered_by_arrival Task Job)).
Definition tgt_workload_bound_jobs_ordered_by_arrival (Task Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Analysis_Global_Parallel_WorkloadBound_WorkloadBound_workload_bound_jobs_ordered_by_arrival Task (ct_decidable_eq Task) Job (ct_decidable_eq Job))).
Theorem WorkloadBound_workload_bound_jobs_ordered_by_arrival_correspondence (Task Job : eqType) :
  PropSPropRel (src_workload_bound_jobs_ordered_by_arrival Task Job) (tgt_workload_bound_jobs_ordered_by_arrival Task Job).
Proof.
  unfold src_workload_bound_jobs_ordered_by_arrival, tgt_workload_bound_jobs_ordered_by_arrival.
  apply: cpw_forall_par => jaR jaL Hja.
  apply: ct_forall_identity => job_task.
  apply: cpw_forall_ncpus_sched => nR nL Hn sR sL Hs.
  apply: ct_forall_identity => tsk.
  apply: ct_forall_nat => t1R t1L H1. apply: ct_forall_nat => dR dL Hd.
  apply: ct_forall_nat => iR iL Hi. apply: ct_forall_identity => elem.
  have Hs' := sorted Task Job nR nL Hn sR sL Hs jaR jaL Hja job_task tsk _ _ _ _ H1 Hd.
  apply: ct_imp; first exact (sub_nat_lt_correspondence _ _ _ _ Hi (cpg_pred_rel _ _ (cpw_list_size Job _ _ Hs'))).
  rewrite (getD Job _ _ Hs' elem _ _ Hi) (getD Job _ _ Hs' elem _ _ (cpg_succ_rel _ _ Hi)).
  exact (sub_nat_le_correspondence _ _ _ _ (Hja _) (Hja _)).
Qed.

Definition src_workload_bound_holds_for_at_most_n_k_jobs (Task Job : eqType) : Prop :=
  forall task_cost task_period task_deadline : Task -> Time.time,
    ltac:(type_of_term (@WorkloadBound.workload_bound_holds_for_at_most_n_k_jobs Task task_cost task_period task_deadline Job)).
Definition tgt_workload_bound_holds_for_at_most_n_k_jobs (Task Job : eqType) : SProp :=
  forall task_cost task_period task_deadline : Task -> Lean.Nat,
    ltac:(type_of_term (I.Prosa_Classic_Analysis_Global_Parallel_WorkloadBound_WorkloadBound_workload_bound_holds_for_at_most_n_k_jobs Task (ct_decidable_eq Task) task_cost task_period task_deadline Job (ct_decidable_eq Job))).
Theorem WorkloadBound_workload_bound_holds_for_at_most_n_k_jobs_correspondence (Task Job : eqType) :
  PropSPropRel (src_workload_bound_holds_for_at_most_n_k_jobs Task Job) (tgt_workload_bound_holds_for_at_most_n_k_jobs Task Job).
Proof.
  unfold src_workload_bound_holds_for_at_most_n_k_jobs, tgt_workload_bound_holds_for_at_most_n_k_jobs.
  apply: cpw_forall_par => task_costR task_costL Htask_cost.
  apply: cpw_forall_par => task_periodR task_periodL Htask_period.
  apply: cpw_forall_par => task_deadlineR task_deadlineL Htask_deadline.
  apply: cpw_forall_par => jaR jaL Hja. apply: cpw_forall_par => cR cL Hc.
  apply: ct_forall_identity => job_task.
  apply: cpw_forall_par => jdR jdL Hjd.
  apply: cpw_forall_arr => aR aL Ha.
  apply: ct_imp; first exact (cpw_valid_params Task Job task_costR task_costL Htask_cost task_deadlineR task_deadlineL Htask_deadline cR cL Hc jdR jdL Hjd job_task aR aL Ha).
  apply: cpw_forall_ncpus_sched => nR nL Hn sR sL Hs.
  apply: ct_imp; first exact (cpw_GS_jobs_come_from_arrival_sequence Job nR nL Hn sR sL Hs aR aL Ha).
  apply: ct_imp; first exact (cpw_GS_completed_jobs_dont_execute Job nR nL Hn sR sL Hs cR cL Hc).
  apply: ct_forall_identity => tsk.
  apply: ct_forall_nat => t1R t1L H1. apply: ct_forall_nat => dR dL Hd.
  apply: ct_forall_nat => RR RL HR.
  have Hs' := sorted Task Job nR nL Hn sR sL Hs jaR jaL Hja job_task tsk _ _ _ _ H1 Hd.
  apply: ct_imp; first exact (sub_nat_le_correspondence _ _ _ _ (cpw_list_size Job _ _ Hs') (WorkloadBound_max_jobs_correspondence Task task_periodR task_periodL Htask_period tsk _ _ HR _ _ Hd)).
  exact (sub_nat_le_correspondence _ _ _ _ (cpw_sum_rel Job _ _ (fun i => (cpw_GS_service_during Job nR nL Hn sR sL Hs (i) _ _ _ _ H1 (cpw_t2 _ _ _ _ H1 Hd))) _ _ Hs') (WorkloadBound_W_correspondence Task task_costR task_costL Htask_cost task_periodR task_periodL Htask_period tsk _ _ HR _ _ Hd)).
Qed.

Definition src_workload_bound_j_fst_is_job_of_tsk (Task Job : eqType) : Prop :=
  ltac:(type_of_term (@WorkloadBound.workload_bound_j_fst_is_job_of_tsk Task Job)).
Definition tgt_workload_bound_j_fst_is_job_of_tsk (Task Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Analysis_Global_Parallel_WorkloadBound_WorkloadBound_workload_bound_j_fst_is_job_of_tsk Task (ct_decidable_eq Task) Job (ct_decidable_eq Job))).
Theorem WorkloadBound_workload_bound_j_fst_is_job_of_tsk_correspondence (Task Job : eqType) :
  PropSPropRel (src_workload_bound_j_fst_is_job_of_tsk Task Job) (tgt_workload_bound_j_fst_is_job_of_tsk Task Job).
Proof.
  unfold src_workload_bound_j_fst_is_job_of_tsk, tgt_workload_bound_j_fst_is_job_of_tsk.
  apply: cpw_forall_par => jaR jaL Hja.
  apply: ct_forall_identity => job_task.
  apply: cpw_forall_arr => aR aL Ha.
  apply: cpw_forall_ncpus_sched => nR nL Hn sR sL Hs.
  apply: ct_imp; first exact (cpw_GS_jobs_come_from_arrival_sequence Job nR nL Hn sR sL Hs aR aL Ha).
  apply: ct_forall_identity => tsk.
  apply: ct_forall_nat => t1R t1L H1. apply: ct_forall_nat => dR dL Hd.
  have Hs' := sorted Task Job nR nL Hn sR sL Hs jaR jaL Hja job_task tsk _ _ _ _ H1 Hd.
  apply: ct_imp; first exact (sub_nat_lt_correspondence _ _ _ _ (sub_nat_rel_canonical 0) (cpw_list_size Job _ _ Hs')).
  apply: ct_forall_identity => elem.
  rewrite (getD Job _ _ Hs' elem _ _ (sub_nat_rel_canonical 0)).
  apply: ct_and; first exact (cpw_arrives_in Job aR aL Ha (nth elem (sort (fun x y => jaR x <= jaR y) (ScheduleOfSporadicTask.jobs_of_task_scheduled_between job_task sR tsk t1R (t1R + dR))) 0)).
  apply: ct_and; first exact (ct_eq_rel Task (job_task (nth elem (sort (fun x y => jaR x <= jaR y) (ScheduleOfSporadicTask.jobs_of_task_scheduled_between job_task sR tsk t1R (t1R + dR))) 0)) tsk).
  apply: ct_and; first exact (ct_bool_truth _ _ (ct_bool_not _ _ (ct_decide_eq_nat _ _ _ _ (cpw_GS_service_during Job nR nL Hn sR sL Hs ((nth elem (sort (fun x y => jaR x <= jaR y) (ScheduleOfSporadicTask.jobs_of_task_scheduled_between job_task sR tsk t1R (t1R + dR))) 0)) _ _ _ _ H1 (cpw_t2 _ _ _ _ H1 Hd)) (sub_nat_rel_canonical 0)))).
  exact (cpw_mem Job (nth elem (sort (fun x y => jaR x <= jaR y) (ScheduleOfSporadicTask.jobs_of_task_scheduled_between job_task sR tsk t1R (t1R + dR))) 0) _ _ (cpw_GS_jobs_scheduled_between Job nR nL Hn sR sL Hs _ _ _ _ H1 (cpw_t2 _ _ _ _ H1 Hd))).
Qed.

Definition src_workload_bound_holds_for_a_single_job (Task Job : eqType) : Prop :=
  forall task_cost task_period task_deadline : Task -> Time.time,
    ltac:(type_of_term (@WorkloadBound.workload_bound_holds_for_a_single_job Task task_cost task_period task_deadline Job)).
Definition tgt_workload_bound_holds_for_a_single_job (Task Job : eqType) : SProp :=
  forall task_cost task_period task_deadline : Task -> Lean.Nat,
    ltac:(type_of_term (I.Prosa_Classic_Analysis_Global_Parallel_WorkloadBound_WorkloadBound_workload_bound_holds_for_a_single_job Task (ct_decidable_eq Task) task_cost task_period task_deadline Job (ct_decidable_eq Job))).
Theorem WorkloadBound_workload_bound_holds_for_a_single_job_correspondence (Task Job : eqType) :
  PropSPropRel (src_workload_bound_holds_for_a_single_job Task Job) (tgt_workload_bound_holds_for_a_single_job Task Job).
Proof.
  unfold src_workload_bound_holds_for_a_single_job, tgt_workload_bound_holds_for_a_single_job.
  apply: cpw_forall_par => task_costR task_costL Htask_cost.
  apply: cpw_forall_par => task_periodR task_periodL Htask_period.
  apply: cpw_forall_par => task_deadlineR task_deadlineL Htask_deadline.
  apply: cpw_forall_par => jaR jaL Hja. apply: cpw_forall_par => cR cL Hc.
  apply: ct_forall_identity => job_task.
  apply: cpw_forall_par => jdR jdL Hjd.
  apply: cpw_forall_arr => aR aL Ha.
  apply: ct_imp; first exact (cpw_valid_params Task Job task_costR task_costL Htask_cost task_deadlineR task_deadlineL Htask_deadline cR cL Hc jdR jdL Hjd job_task aR aL Ha).
  apply: cpw_forall_ncpus_sched => nR nL Hn sR sL Hs.
  apply: ct_imp; first exact (cpw_GS_jobs_come_from_arrival_sequence Job nR nL Hn sR sL Hs aR aL Ha).
  apply: ct_imp; first exact (cpw_GS_completed_jobs_dont_execute Job nR nL Hn sR sL Hs cR cL Hc).
  apply: ct_forall_identity => tsk.
  apply: ct_imp; first exact (cpw_valid_sporadic_task Task task_costR task_costL Htask_cost task_periodR task_periodL Htask_period task_deadlineR task_deadlineL Htask_deadline tsk).
  apply: ct_forall_nat => t1R t1L H1. apply: ct_forall_nat => dR dL Hd.
  apply: ct_forall_nat => RR RL HR.
  have Hs' := sorted Task Job nR nL Hn sR sL Hs jaR jaL Hja job_task tsk _ _ _ _ H1 Hd.
  apply: ct_imp; first exact (sub_nat_lt_correspondence _ _ _ _ (sub_nat_rel_canonical 0) (cpw_list_size Job _ _ Hs')).
  apply: ct_forall_identity => elem.
  apply: sub_nat_le_correspondence; last exact (WorkloadBound_W_correspondence Task task_costR task_costL Htask_cost task_periodR task_periodL Htask_period tsk _ _ HR _ _ Hd).
  apply: (cpw_ico _ _ _ _ _ _ (sub_nat_rel_canonical 0) (sub_nat_rel_canonical 1)) => iR iL Hi.
  rewrite (getD Job _ _ Hs' elem _ _ Hi). exact (cpw_GS_service_during Job nR nL Hn sR sL Hs (nth elem _ iR) _ _ _ _ H1 (cpw_t2 _ _ _ _ H1 Hd)).
Qed.

Definition src_workload_bound_j_lst_is_job_of_tsk (Task Job : eqType) : Prop :=
  ltac:(type_of_term (@WorkloadBound.workload_bound_j_lst_is_job_of_tsk Task Job)).
Definition tgt_workload_bound_j_lst_is_job_of_tsk (Task Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Analysis_Global_Parallel_WorkloadBound_WorkloadBound_workload_bound_j_lst_is_job_of_tsk Task (ct_decidable_eq Task) Job (ct_decidable_eq Job))).
Theorem WorkloadBound_workload_bound_j_lst_is_job_of_tsk_correspondence (Task Job : eqType) :
  PropSPropRel (src_workload_bound_j_lst_is_job_of_tsk Task Job) (tgt_workload_bound_j_lst_is_job_of_tsk Task Job).
Proof.
  unfold src_workload_bound_j_lst_is_job_of_tsk, tgt_workload_bound_j_lst_is_job_of_tsk.
  apply: cpw_forall_par => jaR jaL Hja.
  apply: ct_forall_identity => job_task.
  apply: cpw_forall_arr => aR aL Ha.
  apply: cpw_forall_ncpus_sched => nR nL Hn sR sL Hs.
  apply: ct_imp; first exact (cpw_GS_jobs_come_from_arrival_sequence Job nR nL Hn sR sL Hs aR aL Ha).
  apply: ct_forall_identity => tsk.
  apply: ct_forall_nat => t1R t1L H1. apply: ct_forall_nat => dR dL Hd.
  apply: ct_forall_nat => mR mL Hm.
  have Hs' := sorted Task Job nR nL Hn sR sL Hs jaR jaL Hja job_task tsk _ _ _ _ H1 Hd.
  apply: ct_imp; first exact (sub_nat_eq_correspondence _ _ _ _ (cpw_list_size Job _ _ Hs') (cpw_add2 _ _ Hm)).
  apply: ct_forall_identity => elem.
  rewrite (getD Job _ _ Hs' elem _ _ (cpg_succ_rel _ _ Hm)).
  apply: ct_and; first exact (cpw_arrives_in Job aR aL Ha (nth elem (sort (fun x y => jaR x <= jaR y) (ScheduleOfSporadicTask.jobs_of_task_scheduled_between job_task sR tsk t1R (t1R + dR))) mR.+1)).
  apply: ct_and; first exact (ct_eq_rel Task (job_task (nth elem (sort (fun x y => jaR x <= jaR y) (ScheduleOfSporadicTask.jobs_of_task_scheduled_between job_task sR tsk t1R (t1R + dR))) mR.+1)) tsk).
  apply: ct_and; first exact (ct_bool_truth _ _ (ct_bool_not _ _ (ct_decide_eq_nat _ _ _ _ (cpw_GS_service_during Job nR nL Hn sR sL Hs ((nth elem (sort (fun x y => jaR x <= jaR y) (ScheduleOfSporadicTask.jobs_of_task_scheduled_between job_task sR tsk t1R (t1R + dR))) mR.+1)) _ _ _ _ H1 (cpw_t2 _ _ _ _ H1 Hd)) (sub_nat_rel_canonical 0)))).
  exact (cpw_mem Job (nth elem (sort (fun x y => jaR x <= jaR y) (ScheduleOfSporadicTask.jobs_of_task_scheduled_between job_task sR tsk t1R (t1R + dR))) mR.+1) _ _ (cpw_GS_jobs_scheduled_between Job nR nL Hn sR sL Hs _ _ _ _ H1 (cpw_t2 _ _ _ _ H1 Hd))).
Qed.

Definition src_workload_bound_response_time_of_first_job_inside_interval (Task Job : eqType) : Prop :=
  ltac:(type_of_term (@WorkloadBound.workload_bound_response_time_of_first_job_inside_interval Task Job)).
Definition tgt_workload_bound_response_time_of_first_job_inside_interval (Task Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Analysis_Global_Parallel_WorkloadBound_WorkloadBound_workload_bound_response_time_of_first_job_inside_interval Task (ct_decidable_eq Task) Job (ct_decidable_eq Job))).
Theorem WorkloadBound_workload_bound_response_time_of_first_job_inside_interval_correspondence (Task Job : eqType) :
  PropSPropRel (src_workload_bound_response_time_of_first_job_inside_interval Task Job) (tgt_workload_bound_response_time_of_first_job_inside_interval Task Job).
Proof.
  unfold src_workload_bound_response_time_of_first_job_inside_interval, tgt_workload_bound_response_time_of_first_job_inside_interval.
  apply: cpw_forall_par => jaR jaL Hja. apply: cpw_forall_par => cR cL Hc.
  apply: ct_forall_identity => job_task.
  apply: cpw_forall_arr => aR aL Ha.
  apply: cpw_forall_ncpus_sched => nR nL Hn sR sL Hs.
  apply: ct_imp; first exact (cpw_GS_jobs_come_from_arrival_sequence Job nR nL Hn sR sL Hs aR aL Ha).
  apply: ct_imp; first exact (cpw_GS_completed_jobs_dont_execute Job nR nL Hn sR sL Hs cR cL Hc).
  apply: ct_forall_identity => tsk.
  apply: ct_forall_nat => t1R t1L H1. apply: ct_forall_nat => dR dL Hd.
  apply: ct_forall_nat => RR RL HR.
  apply: ct_imp; first exact (cpw_rt_bound Task Job nR nL Hn sR sL Hs jaR jaL Hja cR cL Hc job_task aR aL Ha tsk _ _ _ _ _ _ H1 Hd HR).
  apply: ct_forall_nat => mR mL Hm.
  have Hs' := sorted Task Job nR nL Hn sR sL Hs jaR jaL Hja job_task tsk _ _ _ _ H1 Hd.
  apply: ct_imp; first exact (sub_nat_eq_correspondence _ _ _ _ (cpw_list_size Job _ _ Hs') (cpw_add2 _ _ Hm)).
  apply: ct_forall_identity => elem.
  rewrite (getD Job _ _ Hs' elem _ _ (sub_nat_rel_canonical 0)).
  exact (sub_nat_le_correspondence _ _ _ _ H1 (sub_add_correspondence _ _ _ _ (Hja _) HR)).
Qed.

Definition src_workload_bound_last_job_arrives_before_end_of_interval (Task Job : eqType) : Prop :=
  ltac:(type_of_term (@WorkloadBound.workload_bound_last_job_arrives_before_end_of_interval Task Job)).
Definition tgt_workload_bound_last_job_arrives_before_end_of_interval (Task Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Analysis_Global_Parallel_WorkloadBound_WorkloadBound_workload_bound_last_job_arrives_before_end_of_interval Task (ct_decidable_eq Task) Job (ct_decidable_eq Job))).
Theorem WorkloadBound_workload_bound_last_job_arrives_before_end_of_interval_correspondence (Task Job : eqType) :
  PropSPropRel (src_workload_bound_last_job_arrives_before_end_of_interval Task Job) (tgt_workload_bound_last_job_arrives_before_end_of_interval Task Job).
Proof.
  unfold src_workload_bound_last_job_arrives_before_end_of_interval, tgt_workload_bound_last_job_arrives_before_end_of_interval.
  apply: cpw_forall_par => jaR jaL Hja.
  apply: ct_forall_identity => job_task.
  apply: cpw_forall_arr => aR aL Ha.
  apply: cpw_forall_ncpus_sched => nR nL Hn sR sL Hs.
  apply: ct_imp; first exact (cpw_GS_jobs_come_from_arrival_sequence Job nR nL Hn sR sL Hs aR aL Ha).
  apply: ct_imp; first exact (cpw_GS_jobs_must_arrive_to_execute Job nR nL Hn sR sL Hs jaR jaL Hja).
  apply: ct_forall_identity => tsk.
  apply: ct_forall_nat => t1R t1L H1. apply: ct_forall_nat => dR dL Hd.
  apply: ct_forall_nat => mR mL Hm.
  have Hs' := sorted Task Job nR nL Hn sR sL Hs jaR jaL Hja job_task tsk _ _ _ _ H1 Hd.
  apply: ct_imp; first exact (sub_nat_eq_correspondence _ _ _ _ (cpw_list_size Job _ _ Hs') (cpw_add2 _ _ Hm)).
  apply: ct_forall_identity => elem.
  rewrite (getD Job _ _ Hs' elem _ _ (cpg_succ_rel _ _ Hm)).
  exact (sub_nat_lt_correspondence _ _ _ _ (Hja _) (cpw_t2 _ _ _ _ H1 Hd)).
Qed.

Definition src_workload_bound_service_of_middle_jobs (Task Job : eqType) : Prop :=
  forall task_cost task_deadline : Task -> Time.time,
    ltac:(type_of_term (@WorkloadBound.workload_bound_service_of_middle_jobs Task task_cost task_deadline Job)).
Definition tgt_workload_bound_service_of_middle_jobs (Task Job : eqType) : SProp :=
  forall task_cost task_deadline : Task -> Lean.Nat,
    ltac:(type_of_term (I.Prosa_Classic_Analysis_Global_Parallel_WorkloadBound_WorkloadBound_workload_bound_service_of_middle_jobs Task (ct_decidable_eq Task) task_cost task_deadline Job (ct_decidable_eq Job))).
Theorem WorkloadBound_workload_bound_service_of_middle_jobs_correspondence (Task Job : eqType) :
  PropSPropRel (src_workload_bound_service_of_middle_jobs Task Job) (tgt_workload_bound_service_of_middle_jobs Task Job).
Proof.
  unfold src_workload_bound_service_of_middle_jobs, tgt_workload_bound_service_of_middle_jobs.
  apply: cpw_forall_par => task_costR task_costL Htask_cost.
  apply: cpw_forall_par => task_deadlineR task_deadlineL Htask_deadline.
  apply: cpw_forall_par => jaR jaL Hja. apply: cpw_forall_par => cR cL Hc.
  apply: ct_forall_identity => job_task.
  apply: cpw_forall_par => jdR jdL Hjd.
  apply: cpw_forall_arr => aR aL Ha.
  apply: ct_imp; first exact (cpw_valid_params Task Job task_costR task_costL Htask_cost task_deadlineR task_deadlineL Htask_deadline cR cL Hc jdR jdL Hjd job_task aR aL Ha).
  apply: cpw_forall_ncpus_sched => nR nL Hn sR sL Hs.
  apply: ct_imp; first exact (cpw_GS_jobs_come_from_arrival_sequence Job nR nL Hn sR sL Hs aR aL Ha).
  apply: ct_imp; first exact (cpw_GS_completed_jobs_dont_execute Job nR nL Hn sR sL Hs cR cL Hc).
  apply: ct_forall_identity => tsk.
  apply: ct_forall_nat => t1R t1L H1. apply: ct_forall_nat => dR dL Hd.
  apply: ct_forall_nat => mR mL Hm.
  have Hs' := sorted Task Job nR nL Hn sR sL Hs jaR jaL Hja job_task tsk _ _ _ _ H1 Hd.
  apply: ct_imp; first exact (sub_nat_eq_correspondence _ _ _ _ (cpw_list_size Job _ _ Hs') (cpw_add2 _ _ Hm)).
  apply: ct_forall_identity => elem.
  apply: sub_nat_le_correspondence; last exact (sub_mul_correspondence _ _ _ _ Hm (Htask_cost tsk)).
  apply: (cpw_ico _ _ _ _ _ _ (sub_nat_rel_canonical 0) Hm) => iR iL Hi.
  rewrite (getD Job _ _ Hs' elem _ _ (cpg_succ_rel _ _ Hi)). exact (cpw_GS_service_during Job nR nL Hn sR sL Hs (nth elem _ iR.+1) _ _ _ _ H1 (cpw_t2 _ _ _ _ H1 Hd)).
Qed.

Definition src_workload_bound_many_periods_in_between (Task Job : eqType) : Prop :=
  forall task_cost task_period : Task -> Time.time,
    ltac:(type_of_term (@WorkloadBound.workload_bound_many_periods_in_between Task task_cost task_period Job)).
Definition tgt_workload_bound_many_periods_in_between (Task Job : eqType) : SProp :=
  forall task_cost task_period : Task -> Lean.Nat,
    ltac:(type_of_term (I.Prosa_Classic_Analysis_Global_Parallel_WorkloadBound_WorkloadBound_workload_bound_many_periods_in_between Task (ct_decidable_eq Task) task_cost task_period Job (ct_decidable_eq Job))).
Theorem WorkloadBound_workload_bound_many_periods_in_between_correspondence (Task Job : eqType) :
  PropSPropRel (src_workload_bound_many_periods_in_between Task Job) (tgt_workload_bound_many_periods_in_between Task Job).
Proof.
  unfold src_workload_bound_many_periods_in_between, tgt_workload_bound_many_periods_in_between.
  apply: cpw_forall_par => task_costR task_costL Htask_cost.
  apply: cpw_forall_par => task_periodR task_periodL Htask_period.
  apply: cpw_forall_par => jaR jaL Hja.
  apply: ct_forall_identity => job_task.
  apply: cpw_forall_arr => aR aL Ha.
  apply: cpw_forall_ncpus_sched => nR nL Hn sR sL Hs.
  apply: ct_imp; first exact (cpw_GS_jobs_come_from_arrival_sequence Job nR nL Hn sR sL Hs aR aL Ha).
  apply: ct_imp; first exact (cpw_sporadic_task_model Task Job task_periodR task_periodL Htask_period jaR jaL Hja job_task aR aL Ha).
  apply: ct_forall_identity => tsk.
  apply: ct_forall_nat => t1R t1L H1. apply: ct_forall_nat => dR dL Hd.
  apply: ct_forall_nat => RR RL HR.
  apply: ct_forall_nat => mR mL Hm.
  have Hs' := sorted Task Job nR nL Hn sR sL Hs jaR jaL Hja job_task tsk _ _ _ _ H1 Hd.
  apply: ct_imp; first exact (sub_nat_eq_correspondence _ _ _ _ (cpw_list_size Job _ _ Hs') (cpw_add2 _ _ Hm)).
  apply: ct_forall_identity => elem.
  rewrite (getD Job _ _ Hs' elem _ _ (sub_nat_rel_canonical 0)) (getD Job _ _ Hs' elem _ _ (cpg_succ_rel _ _ Hm)).
  exact (sub_nat_le_correspondence _ _ _ _ (sub_mul_correspondence _ _ _ _ (cpg_succ_rel _ _ Hm) (Htask_period tsk))
           (ct_sub_rel _ _ _ _ (Hja _) (Hja _))).
Qed.

Definition src_workload_bound_n_k_covers_all_jobs (Task Job : eqType) : Prop :=
  forall task_cost task_period task_deadline : Task -> Time.time,
    ltac:(type_of_term (@WorkloadBound.workload_bound_n_k_covers_all_jobs Task task_cost task_period task_deadline Job)).
Definition tgt_workload_bound_n_k_covers_all_jobs (Task Job : eqType) : SProp :=
  forall task_cost task_period task_deadline : Task -> Lean.Nat,
    ltac:(type_of_term (I.Prosa_Classic_Analysis_Global_Parallel_WorkloadBound_WorkloadBound_workload_bound_n_k_covers_all_jobs Task (ct_decidable_eq Task) task_cost task_period task_deadline Job (ct_decidable_eq Job))).
Theorem WorkloadBound_workload_bound_n_k_covers_all_jobs_correspondence (Task Job : eqType) :
  PropSPropRel (src_workload_bound_n_k_covers_all_jobs Task Job) (tgt_workload_bound_n_k_covers_all_jobs Task Job).
Proof.
  unfold src_workload_bound_n_k_covers_all_jobs, tgt_workload_bound_n_k_covers_all_jobs.
  apply: cpw_forall_par => task_costR task_costL Htask_cost.
  apply: cpw_forall_par => task_periodR task_periodL Htask_period.
  apply: cpw_forall_par => task_deadlineR task_deadlineL Htask_deadline.
  apply: cpw_forall_par => jaR jaL Hja. apply: cpw_forall_par => cR cL Hc.
  apply: ct_forall_identity => job_task.
  apply: cpw_forall_arr => aR aL Ha.
  apply: cpw_forall_ncpus_sched => nR nL Hn sR sL Hs.
  apply: ct_imp; first exact (cpw_GS_jobs_come_from_arrival_sequence Job nR nL Hn sR sL Hs aR aL Ha).
  apply: ct_imp; first exact (cpw_GS_jobs_must_arrive_to_execute Job nR nL Hn sR sL Hs jaR jaL Hja).
  apply: ct_imp; first exact (cpw_GS_completed_jobs_dont_execute Job nR nL Hn sR sL Hs cR cL Hc).
  apply: ct_imp; first exact (cpw_sporadic_task_model Task Job task_periodR task_periodL Htask_period jaR jaL Hja job_task aR aL Ha).
  apply: ct_forall_identity => tsk.
  apply: ct_imp; first exact (cpw_valid_sporadic_task Task task_costR task_costL Htask_cost task_periodR task_periodL Htask_period task_deadlineR task_deadlineL Htask_deadline tsk).
  apply: ct_forall_nat => t1R t1L H1. apply: ct_forall_nat => dR dL Hd.
  apply: ct_forall_nat => RR RL HR.
  apply: ct_imp; first exact (cpw_rt_bound Task Job nR nL Hn sR sL Hs jaR jaL Hja cR cL Hc job_task aR aL Ha tsk _ _ _ _ _ _ H1 Hd HR).
  apply: ct_forall_nat => mR mL Hm.
  have Hs' := sorted Task Job nR nL Hn sR sL Hs jaR jaL Hja job_task tsk _ _ _ _ H1 Hd.
  apply: ct_imp; first exact (sub_nat_eq_correspondence _ _ _ _ (cpw_list_size Job _ _ Hs') (cpw_add2 _ _ Hm)).
  apply: ct_forall_identity => elem.
  exact (sub_nat_le_correspondence _ _ _ _ (cpw_add2 _ _ Hm) (WorkloadBound_max_jobs_correspondence Task task_periodR task_periodL Htask_period tsk _ _ HR _ _ Hd)).
Qed.

Definition src_workload_bound_holds (Task Job : eqType) : Prop :=
  forall task_cost task_period task_deadline : Task -> Time.time,
    ltac:(type_of_term (@WorkloadBound.workload_bound_holds Task task_cost task_period task_deadline Job)).
Definition tgt_workload_bound_holds (Task Job : eqType) : SProp :=
  forall task_cost task_period task_deadline : Task -> Lean.Nat,
    ltac:(type_of_term (I.Prosa_Classic_Analysis_Global_Parallel_WorkloadBound_WorkloadBound_workload_bound_holds Task (ct_decidable_eq Task) task_cost task_period task_deadline Job (ct_decidable_eq Job))).
Theorem WorkloadBound_workload_bound_holds_correspondence (Task Job : eqType) :
  PropSPropRel (src_workload_bound_holds Task Job) (tgt_workload_bound_holds Task Job).
Proof.
  unfold src_workload_bound_holds, tgt_workload_bound_holds.
  apply: cpw_forall_par => task_costR task_costL Htask_cost.
  apply: cpw_forall_par => task_periodR task_periodL Htask_period.
  apply: cpw_forall_par => task_deadlineR task_deadlineL Htask_deadline.
  apply: cpw_forall_par => jaR jaL Hja. apply: cpw_forall_par => cR cL Hc.
  apply: ct_forall_identity => job_task.
  apply: cpw_forall_par => jdR jdL Hjd.
  apply: cpw_forall_arr => aR aL Ha.
  apply: ct_imp; first exact (cpw_valid_params Task Job task_costR task_costL Htask_cost task_deadlineR task_deadlineL Htask_deadline cR cL Hc jdR jdL Hjd job_task aR aL Ha).
  apply: cpw_forall_ncpus_sched => nR nL Hn sR sL Hs.
  apply: ct_imp; first exact (cpw_GS_jobs_come_from_arrival_sequence Job nR nL Hn sR sL Hs aR aL Ha).
  apply: ct_imp; first exact (cpw_GS_jobs_must_arrive_to_execute Job nR nL Hn sR sL Hs jaR jaL Hja).
  apply: ct_imp; first exact (cpw_GS_completed_jobs_dont_execute Job nR nL Hn sR sL Hs cR cL Hc).
  apply: ct_imp; first exact (cpw_sporadic_task_model Task Job task_periodR task_periodL Htask_period jaR jaL Hja job_task aR aL Ha).
  apply: ct_forall_identity => tsk.
  apply: ct_imp; first exact (cpw_valid_sporadic_task Task task_costR task_costL Htask_cost task_periodR task_periodL Htask_period task_deadlineR task_deadlineL Htask_deadline tsk).
  apply: ct_forall_nat => t1R t1L H1. apply: ct_forall_nat => dR dL Hd.
  apply: ct_forall_nat => RR RL HR.
  apply: ct_imp; first exact (cpw_rt_bound Task Job nR nL Hn sR sL Hs jaR jaL Hja cR cL Hc job_task aR aL Ha tsk _ _ _ _ _ _ H1 Hd HR).
  apply: ct_forall_nat => mR mL Hm.
  have Hs' := sorted Task Job nR nL Hn sR sL Hs jaR jaL Hja job_task tsk _ _ _ _ H1 Hd.
  apply: ct_imp; first exact (sub_nat_eq_correspondence _ _ _ _ (cpw_list_size Job _ _ Hs') (cpw_add2 _ _ Hm)).
  apply: ct_forall_identity => elem.
  apply: sub_nat_le_correspondence; last exact (WorkloadBound_W_correspondence Task task_costR task_costL Htask_cost task_periodR task_periodL Htask_period tsk _ _ HR _ _ Hd).
  apply: (cpw_ico _ _ _ _ _ _ (sub_nat_rel_canonical 0) (cpw_add2 _ _ Hm)) => iR iL Hi.
  rewrite (getD Job _ _ Hs' elem _ _ Hi). exact (cpw_GS_service_during Job nR nL Hn sR sL Hs (nth elem _ iR) _ _ _ _ H1 (cpw_t2 _ _ _ _ H1 Hd)).
Qed.

Definition src_workload_bounded_by_W (Task Job : eqType) : Prop :=
  forall task_cost task_period task_deadline : Task -> Time.time,
    ltac:(type_of_term (@WorkloadBound.workload_bounded_by_W Task task_cost task_period task_deadline Job)).
Definition tgt_workload_bounded_by_W (Task Job : eqType) : SProp :=
  forall task_cost task_period task_deadline : Task -> Lean.Nat,
    ltac:(type_of_term (I.Prosa_Classic_Analysis_Global_Parallel_WorkloadBound_WorkloadBound_workload_bounded_by_W Task (ct_decidable_eq Task) task_cost task_period task_deadline Job (ct_decidable_eq Job))).
Theorem WorkloadBound_workload_bounded_by_W_correspondence (Task Job : eqType) :
  PropSPropRel (src_workload_bounded_by_W Task Job) (tgt_workload_bounded_by_W Task Job).
Proof.
  unfold src_workload_bounded_by_W, tgt_workload_bounded_by_W.
  apply: cpw_forall_par => task_costR task_costL Htask_cost.
  apply: cpw_forall_par => task_periodR task_periodL Htask_period.
  apply: cpw_forall_par => task_deadlineR task_deadlineL Htask_deadline.
  apply: cpw_forall_par => jaR jaL Hja. apply: cpw_forall_par => cR cL Hc.
  apply: ct_forall_identity => job_task.
  apply: cpw_forall_par => jdR jdL Hjd.
  apply: cpw_forall_arr => aR aL Ha.
  apply: ct_imp; first exact (cpw_valid_params Task Job task_costR task_costL Htask_cost task_deadlineR task_deadlineL Htask_deadline cR cL Hc jdR jdL Hjd job_task aR aL Ha).
  apply: cpw_forall_ncpus_sched => nR nL Hn sR sL Hs.
  apply: ct_imp; first exact (cpw_GS_jobs_come_from_arrival_sequence Job nR nL Hn sR sL Hs aR aL Ha).
  apply: ct_imp; first exact (cpw_GS_jobs_must_arrive_to_execute Job nR nL Hn sR sL Hs jaR jaL Hja).
  apply: ct_imp; first exact (cpw_GS_completed_jobs_dont_execute Job nR nL Hn sR sL Hs cR cL Hc).
  apply: ct_imp; first exact (cpw_sporadic_task_model Task Job task_periodR task_periodL Htask_period jaR jaL Hja job_task aR aL Ha).
  apply: ct_forall_identity => tsk.
  apply: ct_imp; first exact (cpw_valid_sporadic_task Task task_costR task_costL Htask_cost task_periodR task_periodL Htask_period task_deadlineR task_deadlineL Htask_deadline tsk).
  apply: ct_forall_nat => t1R t1L H1. apply: ct_forall_nat => dR dL Hd.
  apply: ct_forall_nat => RR RL HR.
  apply: ct_imp; first exact (cpw_rt_bound Task Job nR nL Hn sR sL Hs jaR jaL Hja cR cL Hc job_task aR aL Ha tsk _ _ _ _ _ _ H1 Hd HR).
  exact (sub_nat_le_correspondence _ _ _ _ (cpw_workload Task Job nR nL Hn sR sL Hs job_task tsk _ _ _ _ H1 (cpw_t2 _ _ _ _ H1 Hd))
           (WorkloadBound_W_correspondence Task task_costR task_costL Htask_cost task_periodR task_periodL Htask_period tsk _ _ HR _ _ Hd)).
Qed.
