From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq fintype bigop.
From prosa Require Import classic.model.time classic.util.notation classic.model.arrival.basic.arrival_sequence classic.model.arrival.basic.job classic.model.schedule.global.basic.schedule classic.model.schedule.global.schedulability classic.model.schedule.uni.schedule classic.model.schedule.uni.schedulability classic.model.schedule.partitioned.schedule classic.model.schedule.partitioned.schedulability.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedClassicPartitionedSchedulability.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence ClassicPartitionedSchedulabilityBase ClassicPartitionedSchedulabilityList ClassicPartitionedSchedulabilityOrd.

Module I := ImportedClassicPartitionedSchedulability.
Local Open Scope nat_scope.

(** Certificates for [classic/model/schedule/partitioned/schedulability.v] (ProsaBuddy classic, commit f692cb7).

    Inputs: the job and task types are [eqType]s, identified, with the Lean [DecidableEq] instances given by the
    eqTypes' decision procedures ([ct_decidable_eq]); [job_task] identified; times and processor counts by
    [SubNatRel]; processors by [CoOrdRel]; global schedules pointwise on related processors and times through the
    option map (each processor's slice is then a related uniprocessor schedule); task sequences elementwise; processor
    assignments [Task -> processor] pointwise by [CoOrdRel]; all with two-way totals.  The imported global and
    uniprocessor schedule, schedulability and partitioning definitions are related as in the accepted classic
    certificates (re-bound below, through the restated interface [ClassicPartitionedSchedulabilityInterface]).

    Statements: the source side is the exact elaborated type of the pinned lemma (via [type of]; the source proof
    is not used). *)

Ltac type_of_term t := let T := type of t in exact T.
Notation cid := (fun z => z).

(* ------------------------------------------------------------------ *)
(** * Helpers (re-bound to this export from the accepted classic certificates) *)

(** Base definitions (as in the accepted classic base library), provided here when this export's library lacks them. *)

(* ------------------------------------------------------------------ *)
(** * Generic helpers *)

Lemma cpg_forall_cover (A B : Type) (Rel : A -> B -> SProp) (toB : A -> B) (toA : B -> A)
    (HB : forall a, Rel a (toB a)) (HA : forall b, Rel (toA b) b) (PR : A -> Prop) (PL : B -> SProp) :
  (forall a b, Rel a b -> PropSPropRel (PR a) (PL b)) -> PropSPropRel (forall a, PR a) (forall b, PL b).
Proof.
  intro H. apply prop_sprop_rel_intro.
  - intros HR b. exact (prop_to_sprop _ _ (H _ _ (HA b)) (HR _)).
  - intro HL. apply strictly_inhabits. intro a. exact (sprop_to_prop _ _ (H _ _ (HB a)) (HL _)).
Qed.

Lemma cpg_mem (T : eqType) x s sL : ClListRel cid s sL ->
  PropSPropRel (x \in s) (I.Membership_mem T (I.List T) (I.List_instMembership T) sL x).
Proof. exact (cl_mem_rel_list T T cid cid (fun _ => Logic.eq_refl _) x s sL). Qed.

Lemma cpg_uniq (T : eqType) s sL : ClListRel cid s sL -> PropSPropRel (uniq s) (I.List_Nodup T sL).
Proof. exact (cl_uniq_rel_list T T cid cid (fun _ => Logic.eq_refl _) (fun _ => Logic.eq_refl _) s sL). Qed.

Lemma cpg_list_size (T : Type) s sL : ClListRel (B := T) cid s sL -> SubNatRel (size s) (I.List_length T sL).
Proof. intro H. destruct H. exact (cl_size cid s). Qed.

Lemma cpg_lean_eq_logic (A : Type) (x y : A) : Lean.eq x y -> Logic.eq x y.
Proof. exact (imported_eq_to_coq_eq x y). Qed.

(** Transport along the target equality (definitional UIP), into relevant and SProp-valued families. *)
Definition cpg_tr {A : Type} {x y : A} (E : Lean.eq x y) (P : A -> Type) (h : P x) : P y :=
  match E in Lean.eq _ z return P z with Lean.eq_refl => h end.
Definition cpg_trs {A : Type} {x y : A} (E : Lean.eq x y) (P : A -> SProp) (h : P x) : P y :=
  match E in Lean.eq _ z return P z with Lean.eq_refl => h end.

(** Options: [cl_opt] is injective and [x == Some j] is [cl_opt x = some j]. *)
Lemma cpg_opt_inj (A : Type) (o1 o2 : option A) : Logic.eq (cl_opt o1) (cl_opt o2) -> Logic.eq o1 o2.
Proof. intro E. by rewrite -(cl_unopt_opt o1) -(cl_unopt_opt o2) E. Qed.

Lemma cpg_opt_eq_rel (A : Type) (o1 o2 : option A) :
  PropSPropRel (Logic.eq o1 o2) (Lean.eq (cl_opt o1) (cl_opt o2)).
Proof.
  apply prop_sprop_rel_intro.
  - intro E. rewrite E. exact (@Lean.eq_refl _ _).
  - intro E. apply strictly_inhabits. exact (cpg_opt_inj A o1 o2 (imported_eq_to_coq_eq _ _ E)).
Qed.

Lemma cpg_opt_eqb_rel (A : eqType) (o1 o2 : option A) :
  PropSPropRel (is_true (o1 == o2)) (Lean.eq (cl_opt o1) (cl_opt o2)).
Proof.
  apply prop_sprop_rel_intro.
  - move=> /eqP E. rewrite E. exact (@Lean.eq_refl _ _).
  - intro E. apply strictly_inhabits. apply/eqP. exact (cpg_opt_inj A o1 o2 (imported_eq_to_coq_eq _ _ E)).
Qed.

(* ------------------------------------------------------------------ *)
(** * Half-open sums and concatenations over [nat] (as in the accepted sum / arrival_sequence certificates) *)

Fixpoint cpg_natl (s : seq nat) : I.List_inst1 Lean.Nat :=
  match s with [::] => I.List_nil_inst1 _ | x :: s' => I.List_cons_inst1 _ (sub_nat_to_imported x) (cpg_natl s') end.

Lemma cpg_iota_range : forall n s,
  Logic.eq (I.List_range' (sub_nat_to_imported s) (sub_nat_to_imported n) (Lean.Nat_succ Lean.Nat_zero)) (cpg_natl (iota s n)).
Proof.
  elim => [|n IH] s; first reflexivity.
  change (Logic.eq (I.List_cons_inst1 _ (sub_nat_to_imported s)
      (I.List_range' (sub_nat_to_imported (S s)) (sub_nat_to_imported n) (Lean.Nat_succ Lean.Nat_zero)))
    (I.List_cons_inst1 _ (sub_nat_to_imported s) (cpg_natl (iota (S s) n)))).
  by rewrite IH.
Qed.

Lemma cpg_foldr_add (f : Lean.Nat -> Lean.Nat) (g : nat -> nat) (Hf : forall k, Logic.eq (f (sub_nat_to_imported k)) (sub_nat_to_imported (g k))) :
  forall s, Logic.eq (I.List_foldr_inst3 Lean.Nat Lean.Nat Lean.Nat_add Lean.Nat_zero (I.List_map_inst3 Lean.Nat Lean.Nat f (cpg_natl s)))
                     (sub_nat_to_imported (foldr addn 0 (map g s))).
Proof.
  elim => [|k s IH] //=.
  change (Logic.eq (Lean.Nat_add (f (sub_nat_to_imported k))
            (I.List_foldr_inst3 Lean.Nat Lean.Nat Lean.Nat_add Lean.Nat_zero (I.List_map_inst3 Lean.Nat Lean.Nat f (cpg_natl s))))
         (sub_nat_to_imported (g k + foldr addn 0 (map g s)))).
  rewrite IH Hf. exact (imported_eq_to_coq_eq _ _ (sub_add_canonical _ _)).
Qed.

Lemma cpg_big_fold (xs : seq nat) (F : nat -> nat) : Logic.eq (\sum_(i <- xs) F i) (foldr addn 0 (map F xs)).
Proof. elim: xs => [|x xs IH]; first by rewrite big_nil. by rewrite big_cons IH. Qed.

Definition CpgFunRel (FR : nat -> nat) (FL : Lean.Nat -> Lean.Nat) : SProp :=
  forall kR kL, SubNatRel kR kL -> SubNatRel (FR kR) (FL kL).

Lemma cpg_fun_canonical FR FL (HF : CpgFunRel FR FL) k : Logic.eq (FL (sub_nat_to_imported k)) (sub_nat_to_imported (FR k)).
Proof. exact (co_nat_logic _ _ (HF _ _ (sub_nat_rel_canonical k))). Qed.

Lemma cpg_ico mR mL nR nL FR FL (Hm : SubNatRel mR mL) (Hn : SubNatRel nR nL) (HF : CpgFunRel FR FL) :
  SubNatRel (\sum_(mR <= i < nR) FR i)
    (I.List_foldr_inst3 Lean.Nat Lean.Nat Lean.Nat_add Lean.Nat_zero
       (I.List_map_inst3 Lean.Nat Lean.Nat FL (I.List_range' mL (I.Nat_sub nL mL) (Lean.Nat_succ Lean.Nat_zero)))).
Proof.
  rewrite (co_nat_logic _ _ Hm) (co_nat_logic _ _ Hn).
  have -> : Logic.eq (I.Nat_sub (sub_nat_to_imported nR) (sub_nat_to_imported mR)) (sub_nat_to_imported (nR - mR))
    := ct_sub_canonical nR mR.
  rewrite cpg_iota_range.
  apply: coq_eq_to_imported_eq. apply: Logic.eq_sym. rewrite (cpg_foldr_add FL FR (cpg_fun_canonical FR FL HF)).
  by rewrite cpg_big_fold.
Qed.

Lemma cpg_map_natl {B : Type} (f : Lean.Nat -> B) : forall s,
  Logic.eq (I.List_map_inst1 Lean.Nat B f (cpg_natl s)) (cl_map (fun k => f (sub_nat_to_imported k)) s).
Proof.
  elim => [|k s IH] //=.
  change (Logic.eq (I.List_cons B (f (sub_nat_to_imported k)) (I.List_map_inst1 Lean.Nat B f (cpg_natl s)))
                   (I.List_cons B (f (sub_nat_to_imported k)) (cl_map (fun k => f (sub_nat_to_imported k)) s))).
  by rewrite IH.
Qed.

Lemma cpg_big_seq {A : Type} (F : nat -> seq A) : forall s : seq nat,
  Logic.eq (\big[cat/[::]]_(i <- s) F i) (flatten (map F s)).
Proof. elim => [|x s IH]; first by rewrite big_nil. by rewrite big_cons IH. Qed.

Definition CpgNatFamRel (A : Type) (fR : nat -> seq A) (fL : Lean.Nat -> I.List A) : SProp :=
  forall nR nL, SubNatRel nR nL -> ClListRel cid (fR nR) (fL nL).

Lemma cpg_bigcat_nat_rel (A : Type) fR fL (Hf : CpgNatFamRel A fR fL) mR mL nR nL :
  SubNatRel mR mL -> SubNatRel nR nL ->
  ClListRel cid (\big[cat/[::]]_(mR <= t < nR) fR t) (I.Prosa_Util_Notation_bigCat A mL nL fL).
Proof.
  intros Hm Hn. have E1 := co_nat_logic _ _ Hm. have E2 := co_nat_logic _ _ Hn. subst mL nL.
  apply: coq_eq_to_imported_eq. apply: Logic.eq_sym.
  rewrite (imported_eq_to_coq_eq _ _ (I.Prosa_Validation_ClassicPartitionedSchedulabilityInterface_bigCat_range'
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
  rewrite cpg_big_seq /index_iota Hi -map_comp.
  reflexivity.
Qed.

Lemma cpg_notin_target (T : eqType) x s : Logic.eq (x \in s) false ->
  I.Not (I.Membership_mem T (I.List T) (I.List_instMembership T) (cl_map cid s) x).
Proof.
  intros Hx H. apply: ct_coq_false_to_target.
  have Hm := sprop_to_prop _ _ (cpg_mem T x s _ (cl_lean_eq _ _ _ (Logic.eq_refl _))) H.
  rewrite Hx in Hm. discriminate.
Qed.

(** [undup] against Mathlib's [List.dedup] (step equations exported with their proofs). *)
Lemma cpg_undup_rel (T : eqType) : forall s sL, ClListRel cid s sL ->
  ClListRel cid (undup s) (I.List_dedup T (ct_decidable_eq T) sL).
Proof.
  intros s sL Hs. have E := cl_list_logic _ _ _ Hs. subst sL. apply: coq_eq_to_imported_eq. clear Hs.
  elim: s => [|x s IH].
  - exact (Logic.eq_sym (imported_eq_to_coq_eq _ _ (I.Prosa_Validation_ClassicPartitionedSchedulabilityInterface_dedup_nil T (ct_decidable_eq T)))).
  - change (Logic.eq (cl_map cid (if x \in s then undup s else x :: undup s))
      (I.List_dedup T (ct_decidable_eq T) (I.List_cons T x (cl_map cid s)))).
    case Hx: (x \in s).
    + rewrite (imported_eq_to_coq_eq _ _ (I.Prosa_Validation_ClassicPartitionedSchedulabilityInterface_dedup_cons_mem
                 T (ct_decidable_eq T) x (cl_map cid s)
                 (prop_to_sprop _ _ (cpg_mem T x s _ (cl_lean_eq _ _ _ (Logic.eq_refl _))) Hx))).
      exact IH.
    + rewrite (imported_eq_to_coq_eq _ _ (I.Prosa_Validation_ClassicPartitionedSchedulabilityInterface_dedup_cons_not_mem
                 T (ct_decidable_eq T) x (cl_map cid s) (cpg_notin_target T x s Hx))).
      change (Logic.eq (I.List_cons T x (cl_map cid (undup s))) (I.List_cons T x (I.List_dedup T (ct_decidable_eq T) (cl_map cid s)))).
      by rewrite IH.
Qed.

(* ------------------------------------------------------------------ *)
(** * Schedules, arrival sequences, parameters *)

Definition CpgParRel (T : Type) (pR : T -> nat) (pL : T -> Lean.Nat) : SProp := forall x, SubNatRel (pR x) (pL x).

Lemma cpg_forall_par (T : Type) (PR : (T -> nat) -> Prop) (PL : (T -> Lean.Nat) -> SProp) :
  (forall pR pL, CpgParRel T pR pL -> PropSPropRel (PR pR) (PL pL)) -> PropSPropRel (forall p, PR p) (forall p, PL p).
Proof.
  exact (cpg_forall_cover _ _ (CpgParRel T) (fun pR j => sub_nat_to_imported (pR j)) (fun pL j => sub_nat_to_rocq (pL j))
           (fun pR j => sub_nat_rel_canonical (pR j)) (fun pL j => sub_nat_rel_surjective (pL j)) PR PL).
Qed.

Section Sched.
Variables (Job : eqType) (nR : nat) (nL : Lean.Nat).
Hypothesis Hn : SubNatRel nR nL.
Notation dJ := (ct_decidable_eq Job).
Notation LSched := (I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_schedule Job dJ nL).

Definition CpgSchedRel (sR : Schedule.schedule Job nR) (sL : LSched) : SProp :=
  forall oR oL, CoOrdRel nR nL oR oL -> forall tR tL, SubNatRel tR tL -> Lean.eq (cl_opt (sR oR tR)) (sL oL tL).

Definition cpg_sched_to_target (sR : Schedule.schedule Job nR) : LSched :=
  fun oL tL => cl_opt (sR (co_fin_to_ord nR nL Hn oL) (sub_nat_to_rocq tL)).

Definition cpg_sched_to_source (sL : LSched) : Schedule.schedule Job nR :=
  fun oR tR => cl_unopt (sL (co_ord_to_fin nR nL Hn oR) (sub_nat_to_imported tR)).

Lemma cpg_sched_canonical sR : CpgSchedRel sR (cpg_sched_to_target sR).
Proof.
  intros oR oL Ho tR tL Ht. apply: coq_eq_to_imported_eq. rewrite /cpg_sched_to_target (co_nat_input _ _ Ht).
  by rewrite (co_ord_eq _ _ _ _ _ Ho (co_ord_surjective nR nL Hn oL)).
Qed.

Lemma cpg_sched_surjective sL : CpgSchedRel (cpg_sched_to_source sL) sL.
Proof.
  intros oR oL Ho tR tL Ht. apply: coq_eq_to_imported_eq. rewrite /cpg_sched_to_source cl_opt_unopt.
  rewrite (co_nat_logic _ _ Ht). by rewrite (co_fin_rel_eq _ _ _ _ _ (co_ord_canonical nR nL Hn oR) Ho).
Qed.

Lemma cpg_forall_sched (PR : Schedule.schedule Job nR -> Prop) (PL : LSched -> SProp) :
  (forall sR sL, CpgSchedRel sR sL -> PropSPropRel (PR sR) (PL sL)) -> PropSPropRel (forall s, PR s) (forall s, PL s).
Proof. exact (cpg_forall_cover _ _ CpgSchedRel cpg_sched_to_target cpg_sched_to_source cpg_sched_canonical cpg_sched_surjective PR PL). Qed.

End Sched.

Section Arr.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).
Notation LArr := (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrival_sequence Job dJ).

Definition CpgArrRel (aR : ArrivalSequence.arrival_sequence Job) (aL : LArr) : SProp :=
  forall tR tL, SubNatRel tR tL -> ClListRel cid (aR tR) (aL tL).

Definition cpg_arr_to_target (aR : ArrivalSequence.arrival_sequence Job) : LArr :=
  fun tL => cl_map cid (aR (sub_nat_to_rocq tL)).

Definition cpg_arr_to_source (aL : LArr) : ArrivalSequence.arrival_sequence Job :=
  fun tR => cl_unmap cid (aL (sub_nat_to_imported tR)).

Lemma cpg_arr_canonical aR : CpgArrRel aR (cpg_arr_to_target aR).
Proof.
  intros tR tL Ht. have E := co_nat_logic _ _ Ht. subst tL.
  apply: coq_eq_to_imported_eq. rewrite /cpg_arr_to_target sub_nat_rocq_roundtrip. reflexivity.
Qed.

Lemma cpg_arr_surjective aL : CpgArrRel (cpg_arr_to_source aL) aL.
Proof.
  intros tR tL Ht. have E := co_nat_logic _ _ Ht. subst tL.
  apply: coq_eq_to_imported_eq. exact (cl_map_unmap cid cid (fun _ => Logic.eq_refl _) _).
Qed.

Lemma cpg_arrives_in aR aL (Ha : CpgArrRel aR aL) j :
  PropSPropRel (ArrivalSequence.arrives_in aR j)
    (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrives_in Job dJ aL j).
Proof. apply: ct_exists_nat => tR tL Ht. exact (cpg_mem Job j _ _ (Ha tR tL Ht)). Qed.

End Arr.

(* ------------------------------------------------------------------ *)
(** * Definitions *)

Section Defs.
Variables (Job : eqType) (nR : nat) (nL : Lean.Nat).
Hypothesis Hn : SubNatRel nR nL.
Notation dJ := (ct_decidable_eq Job).
Variables (sR : Schedule.schedule Job nR)
  (sL : I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_schedule Job dJ nL).
Hypothesis Hs : CpgSchedRel Job nR nL sR sL.

Lemma cpg_GS_scheduled_on j oR oL (Ho : CoOrdRel nR nL oR oL) tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (Schedule.scheduled_on sR j oR tR)
    (I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_scheduled_on Job dJ nL sL j oL tL).
Proof.
  apply: ct_decide_bool.
  exact (cpg_tr (Hs oR oL Ho tR tL Ht) (fun z => PropSPropRel (sR oR tR == Some j) (Lean.eq z (cl_opt (Some j))))
           (cpg_opt_eqb_rel Job (sR oR tR) (Some j))).
Qed.

Lemma cpg_GS_service_at j tR tL (Ht : SubNatRel tR tL) :
  SubNatRel (Schedule.service_at sR j tR)
    (I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_service_at Job dJ nL sL j tL).
Proof.
  apply: coq_eq_to_imported_eq.
  rewrite (imported_eq_to_coq_eq _ _ (I.Prosa_Validation_ClassicPartitionedSchedulabilityInterface_service_at_sum Job dJ nL sL j tL)).
  apply: imported_eq_to_coq_eq.
  rewrite /Schedule.service_at big_mkcond /=.
  apply: (co_sum_rel nR nL Hn). intros oR oL Ho.
  have H := cpg_GS_scheduled_on j oR oL Ho tR tL Ht.
  rewrite (ct_bool_rel_logic _ _ H). destruct (Schedule.scheduled_on sR j oR tR).
  - exact (sub_nat_rel_canonical 1).
  - exact (sub_nat_rel_canonical 0).
Qed.

Lemma cpg_service_at_fun j : CpgFunRel (fun t => Schedule.service_at sR j t)
    (fun t => I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_service_at Job dJ nL sL j t).
Proof. intros kR kL Hk. exact (cpg_GS_service_at j kR kL Hk). Qed.

Lemma cpg_GS_service j tR tL (Ht : SubNatRel tR tL) :
  SubNatRel (Schedule.service sR j tR)
    (I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_service Job dJ nL sL j tL).
Proof. exact (cpg_ico 0 _ tR tL _ _ (sub_nat_rel_canonical 0) Ht (cpg_service_at_fun j)). Qed.

Lemma cpg_GS_service_during j t1R t1L t2R t2L (H1 : SubNatRel t1R t1L) (H2 : SubNatRel t2R t2L) :
  SubNatRel (Schedule.service_during sR j t1R t2R)
    (I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_service_during Job dJ nL sL j t1L t2L).
Proof. exact (cpg_ico _ _ _ _ _ _ H1 H2 (cpg_service_at_fun j)). Qed.

Lemma cpg_GS_completed cR cL (Hc : CpgParRel Job cR cL) j tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (Schedule.completed cR sR j tR)
    (I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_completed Job dJ cL nL sL j tL).
Proof. exact (ct_decide_le _ _ _ _ (Hc j) (cpg_GS_service j tR tL Ht)). Qed.

End Defs.

Section TaskDefs.
Variables (Task Job : eqType) (nR : nat) (nL : Lean.Nat).
Hypothesis Hn : SubNatRel nR nL.
Notation dT := (ct_decidable_eq Task).
Notation dJ := (ct_decidable_eq Job).
Variables (sR : Schedule.schedule Job nR)
  (sL : I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_schedule Job dJ nL).
Hypothesis Hs : CpgSchedRel Job nR nL sR sL.
Variable job_task : Job -> Task.

End TaskDefs.

Lemma cpg_GS_processor nR nL (Hn : SubNatRel nR nL) :
  And (forall o : Schedule.processor nR, CoOrdRel nR nL o (co_ord_to_fin nR nL Hn o))
      (forall o : I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_processor nL,
         CoOrdRel nR nL (co_fin_to_ord nR nL Hn o) o).
Proof. exact (And_intro _ _ (co_ord_canonical nR nL Hn) (co_ord_surjective nR nL Hn)). Qed.

Lemma cpg_GS_schedule (Job : eqType) nR nL (Hn : SubNatRel nR nL) :
  And (forall s : Schedule.schedule Job nR, CpgSchedRel Job nR nL s (cpg_sched_to_target Job nR nL Hn s))
      (forall s : I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_schedule Job (ct_decidable_eq Job) nL,
         CpgSchedRel Job nR nL (cpg_sched_to_source Job nR nL Hn s) s).
Proof. exact (And_intro _ _ (cpg_sched_canonical Job nR nL Hn) (cpg_sched_surjective Job nR nL Hn)). Qed.

(* ------------------------------------------------------------------ *)
(** * Statements *)

(** The common prefix [forall num_cpus (sched : schedule Job num_cpus)]. *)
Lemma cpg_forall_ncpus_sched (Job : eqType)
    (PR : forall n : nat, Schedule.schedule Job n -> Prop)
    (PL : forall n : Lean.Nat, I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_schedule Job (ct_decidable_eq Job) n -> SProp) :
  (forall nR nL (Hn : SubNatRel nR nL) sR sL, CpgSchedRel Job nR nL sR sL -> PropSPropRel (PR nR sR) (PL nL sL)) ->
  PropSPropRel (forall n s, PR n s) (forall n s, PL n s).
Proof.
  intro H. apply: ct_forall_nat => nR nL Hn. exact (cpg_forall_sched Job nR nL Hn _ _ (H nR nL Hn)).
Qed.

Section PartdefsDefs.
Variables (Task Job : eqType) (nR : nat) (nL : Lean.Nat).
Hypothesis Hn : SubNatRel nR nL.
Notation dT := (ct_decidable_eq Task).
Notation dJ := (ct_decidable_eq Job).
Variables (sR : Schedule.schedule Job nR)
  (sL : I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_schedule Job dJ nL).
Hypothesis Hs : CpgSchedRel Job nR nL sR sL.

Notation SO := (cpg_GS_scheduled_on Job nR nL sR sL Hs).

Lemma cpg_PT_job_local_to_processor j aR aL (Ha : CoOrdRel nR nL aR aL) :
  PropSPropRel (Partitioned.job_local_to_processor sR j aR) (I.Prosa_Classic_Model_Schedule_Partitioned_Schedule_Partitioned_job_local_to_processor Job dJ nL sL j aL).
Proof.
  apply: ct_forall_nat => tR tL Ht. apply: (co_forall_ord nR nL Hn) => oR oL Ho.
  apply: ct_imp; first exact (ct_bool_truth _ _ (SO j oR oL Ho tR tL Ht)).
  exact (co_ord_eq_rel _ _ _ _ _ _ Ho Ha).
Qed.

Lemma cpg_PT_task_local_to_processor (job_task : Job -> Task) tsk aR aL (Ha : CoOrdRel nR nL aR aL) :
  PropSPropRel (Partitioned.task_local_to_processor job_task sR tsk aR) (I.Prosa_Classic_Model_Schedule_Partitioned_Schedule_Partitioned_task_local_to_processor Task dT Job dJ job_task nL sL tsk aL).
Proof.
  apply: ct_forall_identity => j.
  apply: ct_imp; first exact (ct_eq_rel Task (job_task j) tsk).
  exact (cpg_PT_job_local_to_processor j aR aL Ha).
Qed.

Lemma cpg_PT_partitioned_schedule (job_task : Job -> Task) tsR tsL (Hts : ClListRel cid tsR tsL)
    aR aL (Ha : forall tsk, CoOrdRel nR nL (aR tsk) (aL tsk)) :
  PropSPropRel (Partitioned.partitioned_schedule job_task sR tsR aR) (I.Prosa_Classic_Model_Schedule_Partitioned_Schedule_Partitioned_partitioned_schedule Task dT Job dJ job_task nL sL tsL aL).
Proof.
  apply: ct_forall_identity => tsk.
  apply: ct_imp; first exact (cpg_mem Task tsk _ _ Hts).
  exact (cpg_PT_task_local_to_processor job_task tsk _ _ (Ha tsk)).
Qed.

End PartdefsDefs.

(* ------------------------------------------------------------------ *)
(** * Generic covers and helpers *)

Lemma cpu_forall_cover (A B : Type) (Rel : A -> B -> SProp) (toB : A -> B) (toA : B -> A)
    (HB : forall a, Rel a (toB a)) (HA : forall b, Rel (toA b) b) (PR : A -> Prop) (PL : B -> SProp) :
  (forall a b, Rel a b -> PropSPropRel (PR a) (PL b)) -> PropSPropRel (forall a, PR a) (forall b, PL b).
Proof.
  intro H. apply prop_sprop_rel_intro.
  - intros HR b. exact (prop_to_sprop _ _ (H _ _ (HA b)) (HR _)).
  - intro HL. apply strictly_inhabits. intro a. exact (sprop_to_prop _ _ (H _ _ (HB a)) (HL _)).
Qed.

Lemma cpu_false_rel : PropSPropRel Logic.False I.False.
Proof.
  apply prop_sprop_rel_intro.
  - exact ct_coq_false_to_target.
  - exact ct_target_false_to_strict.
Qed.

Lemma cpu_ne (T : Type) (x y : T) : PropSPropRel (x <> y) (I.Ne T x y).
Proof. exact (ct_imp _ _ _ _ (ct_eq_rel T x y) cpu_false_rel). Qed.

Lemma cpu_mem (T : eqType) x s sL : ClListRel cid s sL ->
  PropSPropRel (x \in s) (I.Membership_mem T (I.List T) (I.List_instMembership T) sL x).
Proof. exact (cl_mem_rel_list T T cid cid (fun _ => Logic.eq_refl _) x s sL). Qed.

Lemma cpu_uniq (T : eqType) s sL : ClListRel cid s sL -> PropSPropRel (uniq s) (I.List_Nodup T sL).
Proof. exact (cl_uniq_rel_list T T cid cid (fun _ => Logic.eq_refl _) (fun _ => Logic.eq_refl _) s sL). Qed.

Lemma cpu_unmap_rel (T : Type) (l : I.List T) : ClListRel cid (cl_unmap cid l) l.
Proof. apply: coq_eq_to_imported_eq. exact (cl_map_unmap cid cid (fun _ => Logic.eq_refl _) l). Qed.

Lemma cpu_cl_map_inj (T : Type) (s1 s2 : seq T) : Logic.eq (cl_map cid s1) (cl_map cid s2) -> Logic.eq s1 s2.
Proof.
  intro E. rewrite -(cl_unmap_map cid cid (fun _ => Logic.eq_refl _) s1) -(cl_unmap_map cid cid (fun _ => Logic.eq_refl _) s2).
  by rewrite E.
Qed.

Lemma cpu_succ_rel nR nL : SubNatRel nR nL ->
  SubNatRel nR.+1 (I.HAdd_hAdd_inst7 Lean.Nat Lean.Nat Lean.Nat (I.instHAdd_inst1 Lean.Nat I.instAddNat) nL
                     (I.OfNat_ofNat_inst1 Lean.Nat 1 (I.instOfNatNat 1))).
Proof. intro Hn. exact (sub_imported_eq_congr Lean.Nat_succ _ _ Hn). Qed.

(* ------------------------------------------------------------------ *)
(** * Big concatenation over a half-open interval (as in the accepted arrival_sequence certificate) *)

Lemma cpu_forall_list (T : Type) (PR : seq T -> Prop) (PL : I.List T -> SProp) :
  (forall sR sL, ClListRel (B := T) cid sR sL -> PropSPropRel (PR sR) (PL sL)) -> PropSPropRel (forall s, PR s) (forall s, PL s).
Proof.
  exact (cpu_forall_cover _ _ (fun sR sL => ClListRel (B := T) cid sR sL) (cl_map cid) (cl_unmap cid)
           (fun s => @Lean.eq_refl _ _) (fun l => cpu_unmap_rel T l) PR PL).
Qed.

Definition CpuParRel (T : Type) (pR : T -> nat) (pL : T -> Lean.Nat) : SProp := forall x, SubNatRel (pR x) (pL x).

Lemma cpu_forall_par (T : Type) (PR : (T -> nat) -> Prop) (PL : (T -> Lean.Nat) -> SProp) :
  (forall pR pL, CpuParRel T pR pL -> PropSPropRel (PR pR) (PL pL)) -> PropSPropRel (forall p, PR p) (forall p, PL p).
Proof.
  exact (cpu_forall_cover _ _ (CpuParRel T) (fun pR j => sub_nat_to_imported (pR j)) (fun pL j => sub_nat_to_rocq (pL j))
           (fun pR j => sub_nat_rel_canonical (pR j)) (fun pL j => sub_nat_rel_surjective (pL j)) PR PL).
Qed.

Fixpoint cpu_natl (s : seq nat) : I.List_inst1 Lean.Nat :=
  match s with [::] => I.List_nil_inst1 _ | x :: s' => I.List_cons_inst1 _ (sub_nat_to_imported x) (cpu_natl s') end.

Definition cpu_one : Lean.Nat := I.OfNat_ofNat_inst1 Lean.Nat 1 (I.instOfNatNat 1).

Lemma cpu_iota_range : forall n s,
  Logic.eq (I.List_range' (sub_nat_to_imported s) (sub_nat_to_imported n) cpu_one) (cpu_natl (iota s n)).
Proof.
  elim => [|n IH] s; first reflexivity.
  change (Logic.eq (I.List_cons_inst1 _ (sub_nat_to_imported s)
      (I.List_range' (sub_nat_to_imported (S s)) (sub_nat_to_imported n) cpu_one))
    (I.List_cons_inst1 _ (sub_nat_to_imported s) (cpu_natl (iota (S s) n)))).
  by rewrite IH.
Qed.

Lemma cpu_map_natl {B : Type} (f : Lean.Nat -> B) : forall s,
  Logic.eq (I.List_map_inst1 Lean.Nat B f (cpu_natl s)) (cl_map (fun k => f (sub_nat_to_imported k)) s).
Proof.
  elim => [|k s IH] //=.
  change (Logic.eq (I.List_cons B (f (sub_nat_to_imported k)) (I.List_map_inst1 Lean.Nat B f (cpu_natl s)))
                   (I.List_cons B (f (sub_nat_to_imported k)) (cl_map (fun k => f (sub_nat_to_imported k)) s))).
  by rewrite IH.
Qed.

Lemma cpu_cl_map_comp {A B C : Type} (f : A -> B) (g : B -> C) : forall s : seq A,
  Logic.eq (cl_map (fun x => g (f x)) s) (cl_map g (map f s)).
Proof. elim => [|x s IH] //=. by rewrite IH. Qed.

Lemma cpu_cl_map_ext {A B : Type} (f g : A -> B) (H : forall x, Logic.eq (f x) (g x)) : forall s : seq A,
  Logic.eq (cl_map f s) (cl_map g s).
Proof. elim => [|x s IH] //=. by rewrite H IH. Qed.

Lemma cpu_cl_append {A : Type} : forall s1 s2 : seq A,
  Logic.eq (cl_map cid (s1 ++ s2)) (I.List_append A (cl_map cid s1) (cl_map cid s2)).
Proof.
  elim => [|x s1 IH] s2; first reflexivity.
  change (Logic.eq (I.List_cons A x (cl_map cid (s1 ++ s2))) (I.List_cons A x (I.List_append A (cl_map cid s1) (cl_map cid s2)))).
  by rewrite IH.
Qed.

Lemma cpu_flatten {A : Type} : forall L : seq (seq A),
  Logic.eq (I.List_flatten A (cl_map (cl_map cid) L)) (cl_map cid (flatten L)).
Proof.
  elim => [|s L IH] //=.
  change (Logic.eq (I.List_append A (cl_map cid s) (I.List_flatten A (cl_map (cl_map cid) L))) (cl_map cid (s ++ flatten L))).
  rewrite IH cpu_cl_append. reflexivity.
Qed.

Lemma cpu_big_seq {A : Type} (F : nat -> seq A) : forall s : seq nat,
  Logic.eq (\big[cat/[::]]_(i <- s) F i) (flatten (map F s)).
Proof. elim => [|x s IH]; first by rewrite big_nil. by rewrite big_cons IH. Qed.

Definition CpuFamRel (A : Type) (fR : nat -> seq A) (fL : Lean.Nat -> I.List A) : SProp :=
  forall nR nL, SubNatRel nR nL -> ClListRel cid (fR nR) (fL nL).

Lemma cpu_bigcat_rel (A : Type) fR fL (Hf : CpuFamRel A fR fL) mR mL nR nL :
  SubNatRel mR mL -> SubNatRel nR nL ->
  ClListRel cid (\big[cat/[::]]_(mR <= t < nR) fR t) (I.Prosa_Util_Notation_bigCat A mL nL fL).
Proof.
  intros Hm Hn. have E1 := cl_nat_logic _ _ Hm. have E2 := cl_nat_logic _ _ Hn. subst mL nL.
  apply: coq_eq_to_imported_eq. apply: Logic.eq_sym.
  rewrite (imported_eq_to_coq_eq _ _ (I.Prosa_Validation_ClassicPartitionedSchedulabilityInterface_bigCat_range'
             A (sub_nat_to_imported mR) (sub_nat_to_imported nR) fL)).
  have Hd : Logic.eq (I.HSub_hSub_inst7 Lean.Nat Lean.Nat Lean.Nat (I.instHSub_inst1 Lean.Nat I.instSubNat)
                       (sub_nat_to_imported nR) (sub_nat_to_imported mR)) (sub_nat_to_imported (nR - mR)) :=
    ct_sub_canonical nR mR.
  rewrite Hd.
  change (I.OfNat_ofNat_inst1 Lean.Nat 0 (I.instOfNatNat 0)) with (sub_nat_to_imported 0).
  rewrite (cpu_iota_range (nR - mR) 0) cpu_map_natl. cbv beta.
  have Hpt : forall k, Logic.eq
      (fL (I.HAdd_hAdd_inst7 Lean.Nat Lean.Nat Lean.Nat (I.instHAdd_inst1 Lean.Nat I.instAddNat)
             (sub_nat_to_imported mR) (sub_nat_to_imported k)))
      (cl_map cid (fR (mR + k))).
  { intro k. exact (cl_list_logic _ _ _ (Hf _ _ (sub_add_correspondence mR _ k _
       (sub_nat_rel_canonical mR) (sub_nat_rel_canonical k)))). }
  rewrite (cpu_cl_map_ext _ _ Hpt) (cpu_cl_map_comp (fun k => fR (mR + k)) (cl_map cid)) cpu_flatten.
  have Hi : Logic.eq (iota mR (nR - mR)) (map (addn mR) (iota 0 (nR - mR))) by rewrite -iotaDl addn0.
  rewrite cpu_big_seq /index_iota Hi -map_comp.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(** * Arrival sequences and parameters *)

Section Rel.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).
Notation LArr := (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrival_sequence Job dJ).

Definition CpuArrRel (aR : ArrivalSequence.arrival_sequence Job) (aL : LArr) : SProp :=
  forall tR tL, SubNatRel tR tL -> ClListRel cid (aR tR) (aL tL).

Definition cpu_arr_to_target (aR : ArrivalSequence.arrival_sequence Job) : LArr :=
  fun tL => cl_map cid (aR (sub_nat_to_rocq tL)).

Definition cpu_arr_to_source (aL : LArr) : ArrivalSequence.arrival_sequence Job :=
  fun tR => cl_unmap cid (aL (sub_nat_to_imported tR)).

Lemma cpu_arr_canonical aR : CpuArrRel aR (cpu_arr_to_target aR).
Proof.
  intros tR tL Ht. have E := cl_nat_logic _ _ Ht. subst tL.
  apply: coq_eq_to_imported_eq. rewrite /cpu_arr_to_target sub_nat_rocq_roundtrip. reflexivity.
Qed.

Lemma cpu_arr_surjective aL : CpuArrRel (cpu_arr_to_source aL) aL.
Proof.
  intros tR tL Ht. have E := cl_nat_logic _ _ Ht. subst tL.
  apply: coq_eq_to_imported_eq. exact (cl_map_unmap cid cid (fun _ => Logic.eq_refl _) _).
Qed.

Lemma cpu_forall_arr (PR : ArrivalSequence.arrival_sequence Job -> Prop) (PL : LArr -> SProp) :
  (forall aR aL, CpuArrRel aR aL -> PropSPropRel (PR aR) (PL aL)) -> PropSPropRel (forall a, PR a) (forall a, PL a).
Proof. exact (cpu_forall_cover _ _ CpuArrRel cpu_arr_to_target cpu_arr_to_source cpu_arr_canonical cpu_arr_surjective PR PL). Qed.

End Rel.

(** The imported [ArrivalSequence] definitions this file's statements mention, related on related inputs. *)
Section ArrivalDefs.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).

Lemma cpu_arrives_in aR aL (Ha : CpuArrRel Job aR aL) j :
  PropSPropRel (ArrivalSequence.arrives_in aR j)
    (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrives_in Job dJ aL j).
Proof. apply: ct_exists_nat => tR tL Ht. exact (cpu_mem Job j _ _ (Ha tR tL Ht)). Qed.

End ArrivalDefs.

Section ArrivalDefs2.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).

End ArrivalDefs2.

Fixpoint cpu_snatl (s : seq nat) : I.List_inst1 Lean.Nat :=
  match s with [::] => I.List_nil_inst1 _ | x :: s' => I.List_cons_inst1 _ (sub_nat_to_imported x) (cpu_snatl s') end.

Lemma cpu_siota_range : forall n s,
  Logic.eq (I.List_range' (sub_nat_to_imported s) (sub_nat_to_imported n) (Lean.Nat_succ Lean.Nat_zero)) (cpu_snatl (iota s n)).
Proof.
  elim => [|n IH] s; first reflexivity.
  change (Logic.eq (I.List_cons_inst1 _ (sub_nat_to_imported s)
      (I.List_range' (sub_nat_to_imported (S s)) (sub_nat_to_imported n) (Lean.Nat_succ Lean.Nat_zero)))
    (I.List_cons_inst1 _ (sub_nat_to_imported s) (cpu_snatl (iota (S s) n)))).
  by rewrite IH.
Qed.

Lemma cpu_foldr_add (f : Lean.Nat -> Lean.Nat) (g : nat -> nat) (Hf : forall k, Logic.eq (f (sub_nat_to_imported k)) (sub_nat_to_imported (g k))) :
  forall s, Logic.eq (I.List_foldr_inst3 Lean.Nat Lean.Nat Lean.Nat_add Lean.Nat_zero (I.List_map_inst3 Lean.Nat Lean.Nat f (cpu_snatl s)))
                     (sub_nat_to_imported (foldr addn 0 (map g s))).
Proof.
  elim => [|k s IH] //=.
  change (Logic.eq (Lean.Nat_add (f (sub_nat_to_imported k))
            (I.List_foldr_inst3 Lean.Nat Lean.Nat Lean.Nat_add Lean.Nat_zero (I.List_map_inst3 Lean.Nat Lean.Nat f (cpu_snatl s))))
         (sub_nat_to_imported (g k + foldr addn 0 (map g s)))).
  rewrite IH Hf. exact (imported_eq_to_coq_eq _ _ (sub_add_canonical _ _)).
Qed.

Lemma cpu_big_fold (xs : seq nat) (F : nat -> nat) : Logic.eq (\sum_(i <- xs) F i) (foldr addn 0 (map F xs)).
Proof. elim: xs => [|x xs IH]; first by rewrite big_nil. by rewrite big_cons IH. Qed.

Definition CpuFunRel (FR : nat -> nat) (FL : Lean.Nat -> Lean.Nat) : SProp :=
  forall kR kL, SubNatRel kR kL -> SubNatRel (FR kR) (FL kL).

Lemma cpu_fun_canonical FR FL (HF : CpuFunRel FR FL) k : Logic.eq (FL (sub_nat_to_imported k)) (sub_nat_to_imported (FR k)).
Proof. exact (cl_nat_logic _ _ (HF _ _ (sub_nat_rel_canonical k))). Qed.

Lemma cpu_nat_sub_canonical (a b : nat) :
  Logic.eq (I.Nat_sub (sub_nat_to_imported a) (sub_nat_to_imported b)) (sub_nat_to_imported (a - b)).
Proof.
  elim: b => [|b IH]; first by rewrite subn0.
  change (Logic.eq (I.Nat_pred (I.Nat_sub (sub_nat_to_imported a) (sub_nat_to_imported b))) (sub_nat_to_imported (a - b.+1))).
  rewrite IH subnS. case: (a - b) => [|k]; reflexivity.
Qed.

Lemma cpu_ico mR mL nR nL FR FL (Hm : SubNatRel mR mL) (Hn : SubNatRel nR nL) (HF : CpuFunRel FR FL) :
  SubNatRel (\sum_(mR <= i < nR) FR i)
    (I.List_foldr_inst3 Lean.Nat Lean.Nat Lean.Nat_add Lean.Nat_zero
       (I.List_map_inst3 Lean.Nat Lean.Nat FL (I.List_range' mL (I.Nat_sub nL mL) (Lean.Nat_succ Lean.Nat_zero)))).
Proof.
  rewrite (cl_nat_logic _ _ Hm) (cl_nat_logic _ _ Hn).
  have -> : Logic.eq (I.Nat_sub (sub_nat_to_imported nR) (sub_nat_to_imported mR)) (sub_nat_to_imported (nR - mR))
    := cpu_nat_sub_canonical nR mR.
  rewrite cpu_siota_range.
  apply: coq_eq_to_imported_eq. apply: Logic.eq_sym. rewrite (cpu_foldr_add FL FR (cpu_fun_canonical FR FL HF)).
  by rewrite cpu_big_fold.
Qed.

(* ------------------------------------------------------------------ *)
(** * Options and uniprocessor schedules *)

(** Transport along the target equality (definitional UIP), as in the accepted global schedule certificate. *)
Definition cpu_tr {A : Type} {x y : A} (E : Lean.eq x y) (P : A -> Type) (h : P x) : P y :=
  match E in Lean.eq _ z return P z with Lean.eq_refl => h end.

Definition cpu_trs {A : Type} {x y : A} (E : Lean.eq x y) (P : A -> SProp) (h : P x) : P y :=
  match E in Lean.eq _ z return P z with Lean.eq_refl => h end.

Lemma cpu_opt_inj (A : Type) (o1 o2 : option A) : Logic.eq (cl_opt o1) (cl_opt o2) -> Logic.eq o1 o2.
Proof. intro E. by rewrite -(cl_unopt_opt o1) -(cl_unopt_opt o2) E. Qed.

Lemma cpu_opt_eqb_rel (A : eqType) (o1 o2 : option A) :
  PropSPropRel (is_true (o1 == o2)) (Lean.eq (cl_opt o1) (cl_opt o2)).
Proof.
  apply prop_sprop_rel_intro.
  - move=> /eqP E. rewrite E. exact (@Lean.eq_refl _ _).
  - intro E. apply strictly_inhabits. apply/eqP. exact (cpu_opt_inj A o1 o2 (imported_eq_to_coq_eq _ _ E)).
Qed.

Section Sched.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).
Notation LSched := (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job dJ).

Definition CpuSchedRel (sR : UniprocessorSchedule.schedule Job) (sL : LSched) : SProp :=
  forall tR tL, SubNatRel tR tL -> Lean.eq (cl_opt (sR tR)) (sL tL).

Definition cpu_sched_to_target (sR : UniprocessorSchedule.schedule Job) : LSched := fun tL => cl_opt (sR (sub_nat_to_rocq tL)).
Definition cpu_sched_to_source (sL : LSched) : UniprocessorSchedule.schedule Job := fun tR => cl_unopt (sL (sub_nat_to_imported tR)).

Lemma cpu_sched_canonical sR : CpuSchedRel sR (cpu_sched_to_target sR).
Proof. intros tR tL Ht. apply: coq_eq_to_imported_eq. by rewrite /cpu_sched_to_target (cl_nat_input _ _ Ht). Qed.

Lemma cpu_sched_surjective sL : CpuSchedRel (cpu_sched_to_source sL) sL.
Proof.
  intros tR tL Ht. apply: coq_eq_to_imported_eq. rewrite /cpu_sched_to_source cl_opt_unopt.
  by rewrite (cl_nat_logic _ _ Ht).
Qed.

Lemma cpu_forall_sched (PR : UniprocessorSchedule.schedule Job -> Prop) (PL : LSched -> SProp) :
  (forall sR sL, CpuSchedRel sR sL -> PropSPropRel (PR sR) (PL sL)) -> PropSPropRel (forall s, PR s) (forall s, PL s).
Proof. exact (cpu_forall_cover _ _ CpuSchedRel cpu_sched_to_target cpu_sched_to_source cpu_sched_canonical cpu_sched_surjective PR PL). Qed.

End Sched.

(* ------------------------------------------------------------------ *)
(** * Definitions *)

Lemma cpu_US_schedule (Job : eqType) :
  And (forall sR : UniprocessorSchedule.schedule Job, CpuSchedRel Job sR (cpu_sched_to_target Job sR))
      (forall sL : I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job (ct_decidable_eq Job), CpuSchedRel Job (cpu_sched_to_source Job sL) sL).
Proof. exact (And_intro _ _ (cpu_sched_canonical Job) (cpu_sched_surjective Job)). Qed.

Section USchedDefs.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).
Variables (sR : UniprocessorSchedule.schedule Job) (sL : I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job dJ).
Hypothesis Hs : CpuSchedRel Job sR sL.

Lemma cpu_US_scheduled_at j tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (UniprocessorSchedule.scheduled_at sR j tR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_scheduled_at Job dJ sL j tL).
Proof.
  apply: ct_decide_bool.
  exact (cpu_tr (Hs tR tL Ht) (fun z => PropSPropRel (sR tR == Some j) (Lean.eq z (cl_opt (Some j))))
           (cpu_opt_eqb_rel Job (sR tR) (Some j))).
Qed.

Lemma cpu_US_service_at j tR tL (Ht : SubNatRel tR tL) :
  SubNatRel (UniprocessorSchedule.service_at sR j tR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_service_at Job dJ sL j tL).
Proof. exact (ct_bool_to_nat _ _ (cpu_US_scheduled_at j tR tL Ht)). Qed.

Lemma cpu_service_at_fun j : CpuFunRel (fun t => UniprocessorSchedule.service_at sR j t) (fun t => I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_service_at Job dJ sL j t).
Proof. intros kR kL Hk. exact (cpu_US_service_at j kR kL Hk). Qed.

Lemma cpu_US_service_during j t1R t1L (H1 : SubNatRel t1R t1L) t2R t2L (H2 : SubNatRel t2R t2L) :
  SubNatRel (UniprocessorSchedule.service_during sR j t1R t2R) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_service_during Job dJ sL j t1L t2L).
Proof. exact (cpu_ico _ _ _ _ _ _ H1 H2 (cpu_service_at_fun j)). Qed.

Lemma cpu_US_service j tR tL (Ht : SubNatRel tR tL) :
  SubNatRel (UniprocessorSchedule.service sR j tR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_service Job dJ sL j tL).
Proof. exact (cpu_US_service_during j 0 _ (sub_nat_rel_canonical 0) tR tL Ht). Qed.

Lemma cpu_US_completed_by cR cL (Hc : CpuParRel Job cR cL) j tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (UniprocessorSchedule.completed_by cR sR j tR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_completed_by Job dJ cL sL j tL).
Proof. exact (ct_decide_le _ _ _ _ (Hc j) (cpu_US_service j tR tL Ht)). Qed.

End USchedDefs.


(* ------------------------------------------------------------------ *)
(** * Global and uniprocessor views of one processor *)

Lemma cpp_uni_rel (Job : eqType) nR nL sR sL (Hs : CpgSchedRel Job nR nL sR sL) oR oL (Ho : CoOrdRel nR nL oR oL) :
  CpuSchedRel Job (sR oR) (sL oL).
Proof. intros tR tL Ht. exact (Hs oR oL Ho tR tL Ht). Qed.

(** Processor assignments [Task -> 'I_n], pointwise by [CoOrdRel], with two-way totals. *)
Lemma cpp_forall_assign (Task : Type) nR nL (Hn : SubNatRel nR nL)
    (PR : (Task -> 'I_nR) -> Prop) (PL : (Task -> Fin nL) -> SProp) :
  (forall aR aL, (forall tsk, CoOrdRel nR nL (aR tsk) (aL tsk)) -> PropSPropRel (PR aR) (PL aL)) ->
  PropSPropRel (forall a, PR a) (forall a, PL a).
Proof.
  exact (cpg_forall_cover _ _ (fun aR aL => forall tsk, CoOrdRel nR nL (aR tsk) (aL tsk))
           (fun aR tsk => co_ord_to_fin nR nL Hn (aR tsk)) (fun aL tsk => co_fin_to_ord nR nL Hn (aL tsk))
           (fun aR tsk => co_ord_canonical nR nL Hn (aR tsk)) (fun aL tsk => co_ord_surjective nR nL Hn (aL tsk)) PR PL).
Qed.

(** The task-level deadline predicates (global and uniprocessor), as in the accepted classic schedulability certificates. *)
Section Miss.
Variables (Task Job : eqType) (nR : nat) (nL : Lean.Nat).
Hypothesis Hn : SubNatRel nR nL.
Variables (sR : Schedule.schedule Job nR)
  (sL : I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_schedule Job (ct_decidable_eq Job) nL).
Hypothesis Hs : CpgSchedRel Job nR nL sR sL.
Variables (jaR : Job -> nat) (jaL : Job -> Lean.Nat) (cR : Job -> nat) (cL : Job -> Lean.Nat) (dR : Job -> nat) (dL : Job -> Lean.Nat).
Hypotheses (Hja : CpgParRel Job jaR jaL) (Hc : CpgParRel Job cR cL) (Hd : CpgParRel Job dR dL).
Variable job_task : Job -> Task.
Variables (aR : ArrivalSequence.arrival_sequence Job)
  (aL : I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrival_sequence Job (ct_decidable_eq Job)).
Hypothesis Ha : CpgArrRel Job aR aL.

Lemma cpp_global_miss tsk :
  PropSPropRel (prosa.classic.model.schedule.global.schedulability.Schedulability.task_misses_no_deadline jaR cR dR job_task aR sR tsk)
    (I.Prosa_Classic_Model_Schedule_Global_Schedulability_Schedulability_task_misses_no_deadline
       Task Job (ct_decidable_eq Task) (ct_decidable_eq Job) jaL cL dL job_task aL nL sL tsk).
Proof.
  apply: ct_forall_identity => j.
  apply: ct_imp; first exact (cpg_arrives_in Job aR aL Ha j).
  apply: ct_imp; first exact (ct_eq_rel Task (job_task j) tsk).
  exact (ct_bool_truth _ _ (cpg_GS_completed Job nR nL Hn sR sL Hs cR cL Hc j _ _ (sub_add_correspondence _ _ _ _ (Hja j) (Hd j)))).
Qed.

Lemma cpp_uni_miss oR oL (Ho : CoOrdRel nR nL oR oL) tsk :
  PropSPropRel (prosa.classic.model.schedule.uni.schedulability.Schedulability.task_misses_no_deadline jaR cR dR job_task aR (sR oR) tsk)
    (I.Prosa_Classic_Model_Schedule_Uni_Schedulability_Schedulability_task_misses_no_deadline
       Job (ct_decidable_eq Job) jaL cL dL Task (ct_decidable_eq Task) job_task aL (sL oL) tsk).
Proof.
  apply: ct_forall_identity => j.
  apply: ct_imp; first exact (cpg_arrives_in Job aR aL Ha j).
  apply: ct_imp; first exact (ct_eq_rel Task (job_task j) tsk).
  exact (ct_bool_truth _ _ (cpu_US_completed_by Job (sR oR) (sL oL) (cpp_uni_rel Job nR nL sR sL Hs oR oL Ho) cR cL Hc j _ _
           (sub_add_correspondence _ _ _ _ (Hja j) (Hd j)))).
Qed.
End Miss.

(* ------------------------------------------------------------------ *)
(** * Statements *)

Definition src_same_per_processor_service (Task Job : eqType) : Prop :=
  ltac:(type_of_term (@PartitionSchedulability.same_per_processor_service Task Job)).
Definition tgt_same_per_processor_service (Task Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Model_Schedule_Partitioned_Schedulability_PartitionSchedulability_same_per_processor_service Task (ct_decidable_eq Task) Job (ct_decidable_eq Job))).

Theorem PartitionSchedulability_same_per_processor_service_correspondence (Task Job : eqType) :
  PropSPropRel (src_same_per_processor_service Task Job) (tgt_same_per_processor_service Task Job).
Proof.
  unfold src_same_per_processor_service, tgt_same_per_processor_service.
  apply: ct_forall_identity => job_task. apply: cpu_forall_arr => aR aL Ha.
  apply: cpg_forall_ncpus_sched => nR nL Hn sR sL Hs. apply: cpu_forall_list => tsR tsL Hts.
  apply: ct_imp.
  { apply: ct_forall_identity => j. apply: ct_imp; first exact (cpg_arrives_in Job aR aL Ha j).
    exact (cpg_mem Task (job_task j) _ _ Hts). }
  apply: (cpp_forall_assign Task nR nL Hn) => acR acL Hac.
  apply: ct_imp; first exact (cpg_PT_partitioned_schedule Task Job nR nL Hn sR sL Hs job_task _ _ Hts acR acL Hac).
  apply: ct_forall_identity => j.
  apply: ct_imp; first exact (cpg_arrives_in Job aR aL Ha j).
  apply: ct_forall_nat => t1R t1L H1. apply: ct_forall_nat => t2R t2L H2.
  have Ho := Hac (job_task j).
  exact (sub_nat_eq_correspondence _ _ _ _ (cpg_GS_service_during Job nR nL Hn sR sL Hs j _ _ _ _ H1 H2)
           (cpu_US_service_during Job _ _ (cpp_uni_rel Job nR nL sR sL Hs _ _ Ho) j _ _ H1 _ _ H2)).
Qed.

Definition src_schedulable_at_system_level (Task Job : eqType) : Prop :=
  ltac:(type_of_term (@PartitionSchedulability.schedulable_at_system_level Task Job)).
Definition tgt_schedulable_at_system_level (Task Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Model_Schedule_Partitioned_Schedulability_PartitionSchedulability_schedulable_at_system_level Task (ct_decidable_eq Task) Job (ct_decidable_eq Job))).

Theorem PartitionSchedulability_schedulable_at_system_level_correspondence (Task Job : eqType) :
  PropSPropRel (src_schedulable_at_system_level Task Job) (tgt_schedulable_at_system_level Task Job).
Proof.
  unfold src_schedulable_at_system_level, tgt_schedulable_at_system_level.
  apply: cpg_forall_par => jaR jaL Hja. apply: cpg_forall_par => cR cL Hc. apply: cpg_forall_par => dR dL Hd.
  apply: ct_forall_identity => job_task. apply: cpu_forall_arr => aR aL Ha.
  apply: cpg_forall_ncpus_sched => nR nL Hn sR sL Hs. apply: cpu_forall_list => tsR tsL Hts.
  apply: ct_imp.
  { apply: ct_forall_identity => j. apply: ct_imp; first exact (cpg_arrives_in Job aR aL Ha j).
    exact (cpg_mem Task (job_task j) _ _ Hts). }
  apply: (cpp_forall_assign Task nR nL Hn) => acR acL Hac.
  apply: ct_imp; first exact (cpg_PT_partitioned_schedule Task Job nR nL Hn sR sL Hs job_task _ _ Hts acR acL Hac).
  apply: ct_imp.
  { apply: ct_forall_identity => tsk. apply: ct_imp; first exact (cpg_mem Task tsk _ _ Hts).
    exact (cpp_uni_miss Task Job nR nL sR sL Hs jaR jaL cR cL dR dL Hja Hc Hd job_task aR aL Ha _ _ (Hac tsk) tsk). }
  apply: ct_forall_identity => tsk. apply: ct_imp; first exact (cpg_mem Task tsk _ _ Hts).
  exact (cpp_global_miss Task Job nR nL Hn sR sL Hs jaR jaL cR cL dR dL Hja Hc Hd job_task aR aL Ha tsk).
Qed.
