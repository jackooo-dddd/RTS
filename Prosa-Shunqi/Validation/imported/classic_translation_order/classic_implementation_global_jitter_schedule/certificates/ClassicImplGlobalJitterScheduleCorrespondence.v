From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq fintype bigop path div.
From prosa Require Import classic.model.time classic.model.schedule.global.basic.schedule classic.model.schedule.global.transformation.construction classic.util.list classic.model.priority classic.model.arrival.basic.job classic.model.arrival.basic.arrival_sequence classic.model.arrival.jitter.arrival_sequence classic.model.schedule.global.jitter.schedule classic.model.schedule.global.jitter.platform classic.implementation.global.jitter.schedule.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedClassicImplGlobalJitterSchedule.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence ClassicImplGlobalJitterScheduleBase ClassicImplGlobalJitterScheduleList ClassicImplGlobalJitterScheduleOrd.



Module I := ImportedClassicImplGlobalJitterSchedule.
Local Open Scope nat_scope.

(** Certificates for [classic/implementation/global/jitter/schedule.v] (ProsaBuddy classic, commit f692cb7).

    Inputs: the job type is an [eqType], identified, with the Lean [DecidableEq] instance given by its decision procedure
    ([ct_decidable_eq]); times by [SubNatRel]; processor counts by [SubNatRel]; processors by [CoOrdRel]; global schedules pointwise
    through the option map (two-way
    totals).  The construction function [build_schedule : schedule Job num_cpus -> schedule Job num_cpus] is a higher-order input (a function of schedules): as in the
    accepted v0.6 [implementation/facts/generic_schedule.v] certificate, the definitions and statements are related
    specialised at related inputs (see the section [Construction] below); [schedule_prefix] is related by induction,
    closed by its kernel-checked Lean recursion equations exported with the artifact.

    Statements: the source side is the exact elaborated type of the pinned lemma (via [type of]; the source proof is not
    used), specialised at the related inputs. *)

Ltac type_of_term t := let T := type of t in exact T.
Notation cid := (fun z => z).

(* ------------------------------------------------------------------ *)
(** * Helpers (re-bound to this export from the accepted classic certificates) *)

(** Base definitions (as in the accepted classic base library), provided here when this export's library lacks them. *)

(* ------------------------------------------------------------------ *)
(** * Generic helpers *)

Lemma cgq_forall_cover (A B : Type) (Rel : A -> B -> SProp) (toB : A -> B) (toA : B -> A)
    (HB : forall a, Rel a (toB a)) (HA : forall b, Rel (toA b) b) (PR : A -> Prop) (PL : B -> SProp) :
  (forall a b, Rel a b -> PropSPropRel (PR a) (PL b)) -> PropSPropRel (forall a, PR a) (forall b, PL b).
Proof.
  intro H. apply prop_sprop_rel_intro.
  - intros HR b. exact (prop_to_sprop _ _ (H _ _ (HA b)) (HR _)).
  - intro HL. apply strictly_inhabits. intro a. exact (sprop_to_prop _ _ (H _ _ (HB a)) (HL _)).
Qed.

Lemma cgq_mem (T : eqType) x s sL : ClListRel cid s sL ->
  PropSPropRel (x \in s) (I.Membership_mem T (I.List T) (I.List_instMembership T) sL x).
Proof. exact (cl_mem_rel_list T T cid cid (fun _ => Logic.eq_refl _) x s sL). Qed.

Lemma cgq_uniq (T : eqType) s sL : ClListRel cid s sL -> PropSPropRel (uniq s) (I.List_Nodup T sL).
Proof. exact (cl_uniq_rel_list T T cid cid (fun _ => Logic.eq_refl _) (fun _ => Logic.eq_refl _) s sL). Qed.

Lemma cgq_list_size (T : Type) s sL : ClListRel (B := T) cid s sL -> SubNatRel (size s) (I.List_length T sL).
Proof. intro H. destruct H. exact (cl_size cid s). Qed.

Lemma cgq_lean_eq_logic (A : Type) (x y : A) : Lean.eq x y -> Logic.eq x y.
Proof. exact (imported_eq_to_coq_eq x y). Qed.

(** Transport along the target equality (definitional UIP), into relevant and SProp-valued families. *)
Definition cgq_tr {A : Type} {x y : A} (E : Lean.eq x y) (P : A -> Type) (h : P x) : P y :=
  match E in Lean.eq _ z return P z with Lean.eq_refl => h end.
Definition cgq_trs {A : Type} {x y : A} (E : Lean.eq x y) (P : A -> SProp) (h : P x) : P y :=
  match E in Lean.eq _ z return P z with Lean.eq_refl => h end.

(** Options: [cl_opt] is injective and [x == Some j] is [cl_opt x = some j]. *)
Lemma cgq_opt_inj (A : Type) (o1 o2 : option A) : Logic.eq (cl_opt o1) (cl_opt o2) -> Logic.eq o1 o2.
Proof. intro E. by rewrite -(cl_unopt_opt o1) -(cl_unopt_opt o2) E. Qed.

Lemma cgq_opt_eq_rel (A : Type) (o1 o2 : option A) :
  PropSPropRel (Logic.eq o1 o2) (Lean.eq (cl_opt o1) (cl_opt o2)).
Proof.
  apply prop_sprop_rel_intro.
  - intro E. rewrite E. exact (@Lean.eq_refl _ _).
  - intro E. apply strictly_inhabits. exact (cgq_opt_inj A o1 o2 (imported_eq_to_coq_eq _ _ E)).
Qed.

Lemma cgq_opt_eqb_rel (A : eqType) (o1 o2 : option A) :
  PropSPropRel (is_true (o1 == o2)) (Lean.eq (cl_opt o1) (cl_opt o2)).
Proof.
  apply prop_sprop_rel_intro.
  - move=> /eqP E. rewrite E. exact (@Lean.eq_refl _ _).
  - intro E. apply strictly_inhabits. apply/eqP. exact (cgq_opt_inj A o1 o2 (imported_eq_to_coq_eq _ _ E)).
Qed.

(* ------------------------------------------------------------------ *)
(** * Half-open sums and concatenations over [nat] (as in the accepted sum / arrival_sequence certificates) *)

Fixpoint cgq_natl (s : seq nat) : I.List_inst1 Lean.Nat :=
  match s with [::] => I.List_nil_inst1 _ | x :: s' => I.List_cons_inst1 _ (sub_nat_to_imported x) (cgq_natl s') end.

Lemma cgq_iota_range : forall n s,
  Logic.eq (I.List_range' (sub_nat_to_imported s) (sub_nat_to_imported n) (Lean.Nat_succ Lean.Nat_zero)) (cgq_natl (iota s n)).
Proof.
  elim => [|n IH] s; first reflexivity.
  change (Logic.eq (I.List_cons_inst1 _ (sub_nat_to_imported s)
      (I.List_range' (sub_nat_to_imported (S s)) (sub_nat_to_imported n) (Lean.Nat_succ Lean.Nat_zero)))
    (I.List_cons_inst1 _ (sub_nat_to_imported s) (cgq_natl (iota (S s) n)))).
  by rewrite IH.
Qed.

Lemma cgq_foldr_add (f : Lean.Nat -> Lean.Nat) (g : nat -> nat) (Hf : forall k, Logic.eq (f (sub_nat_to_imported k)) (sub_nat_to_imported (g k))) :
  forall s, Logic.eq (I.List_foldr_inst3 Lean.Nat Lean.Nat Lean.Nat_add Lean.Nat_zero (I.List_map_inst3 Lean.Nat Lean.Nat f (cgq_natl s)))
                     (sub_nat_to_imported (foldr addn 0 (map g s))).
Proof.
  elim => [|k s IH] //=.
  change (Logic.eq (Lean.Nat_add (f (sub_nat_to_imported k))
            (I.List_foldr_inst3 Lean.Nat Lean.Nat Lean.Nat_add Lean.Nat_zero (I.List_map_inst3 Lean.Nat Lean.Nat f (cgq_natl s))))
         (sub_nat_to_imported (g k + foldr addn 0 (map g s)))).
  rewrite IH Hf. exact (imported_eq_to_coq_eq _ _ (sub_add_canonical _ _)).
Qed.

Lemma cgq_big_fold (xs : seq nat) (F : nat -> nat) : Logic.eq (\sum_(i <- xs) F i) (foldr addn 0 (map F xs)).
Proof. elim: xs => [|x xs IH]; first by rewrite big_nil. by rewrite big_cons IH. Qed.

Definition CgqFunRel (FR : nat -> nat) (FL : Lean.Nat -> Lean.Nat) : SProp :=
  forall kR kL, SubNatRel kR kL -> SubNatRel (FR kR) (FL kL).

Lemma cgq_fun_canonical FR FL (HF : CgqFunRel FR FL) k : Logic.eq (FL (sub_nat_to_imported k)) (sub_nat_to_imported (FR k)).
Proof. exact (co_nat_logic _ _ (HF _ _ (sub_nat_rel_canonical k))). Qed.

Lemma cgq_ico mR mL nR nL FR FL (Hm : SubNatRel mR mL) (Hn : SubNatRel nR nL) (HF : CgqFunRel FR FL) :
  SubNatRel (\sum_(mR <= i < nR) FR i)
    (I.List_foldr_inst3 Lean.Nat Lean.Nat Lean.Nat_add Lean.Nat_zero
       (I.List_map_inst3 Lean.Nat Lean.Nat FL (I.List_range' mL (I.Nat_sub nL mL) (Lean.Nat_succ Lean.Nat_zero)))).
Proof.
  rewrite (co_nat_logic _ _ Hm) (co_nat_logic _ _ Hn).
  have -> : Logic.eq (I.Nat_sub (sub_nat_to_imported nR) (sub_nat_to_imported mR)) (sub_nat_to_imported (nR - mR))
    := ct_sub_canonical nR mR.
  rewrite cgq_iota_range.
  apply: coq_eq_to_imported_eq. apply: Logic.eq_sym. rewrite (cgq_foldr_add FL FR (cgq_fun_canonical FR FL HF)).
  by rewrite cgq_big_fold.
Qed.

Lemma cgq_map_natl {B : Type} (f : Lean.Nat -> B) : forall s,
  Logic.eq (I.List_map_inst1 Lean.Nat B f (cgq_natl s)) (cl_map (fun k => f (sub_nat_to_imported k)) s).
Proof.
  elim => [|k s IH] //=.
  change (Logic.eq (I.List_cons B (f (sub_nat_to_imported k)) (I.List_map_inst1 Lean.Nat B f (cgq_natl s)))
                   (I.List_cons B (f (sub_nat_to_imported k)) (cl_map (fun k => f (sub_nat_to_imported k)) s))).
  by rewrite IH.
Qed.

Lemma cgq_big_seq {A : Type} (F : nat -> seq A) : forall s : seq nat,
  Logic.eq (\big[cat/[::]]_(i <- s) F i) (flatten (map F s)).
Proof. elim => [|x s IH]; first by rewrite big_nil. by rewrite big_cons IH. Qed.

Definition CgqNatFamRel (A : Type) (fR : nat -> seq A) (fL : Lean.Nat -> I.List A) : SProp :=
  forall nR nL, SubNatRel nR nL -> ClListRel cid (fR nR) (fL nL).

Lemma cgq_bigcat_nat_rel (A : Type) fR fL (Hf : CgqNatFamRel A fR fL) mR mL nR nL :
  SubNatRel mR mL -> SubNatRel nR nL ->
  ClListRel cid (\big[cat/[::]]_(mR <= t < nR) fR t) (I.Prosa_Util_Notation_bigCat A mL nL fL).
Proof.
  intros Hm Hn. have E1 := co_nat_logic _ _ Hm. have E2 := co_nat_logic _ _ Hn. subst mL nL.
  apply: coq_eq_to_imported_eq. apply: Logic.eq_sym.
  rewrite (imported_eq_to_coq_eq _ _ (I.Prosa_Validation_ClassicImplGlobalJitterScheduleInterface_bigCat_range'
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
  rewrite cgq_big_seq /index_iota Hi -map_comp.
  reflexivity.
Qed.

Lemma cgq_notin_target (T : eqType) x s : Logic.eq (x \in s) false ->
  I.Not (I.Membership_mem T (I.List T) (I.List_instMembership T) (cl_map cid s) x).
Proof.
  intros Hx H. apply: ct_coq_false_to_target.
  have Hm := sprop_to_prop _ _ (cgq_mem T x s _ (cl_lean_eq _ _ _ (Logic.eq_refl _))) H.
  rewrite Hx in Hm. discriminate.
Qed.

(** [undup] against Mathlib's [List.dedup] (step equations exported with their proofs). *)
Lemma cgq_undup_rel (T : eqType) : forall s sL, ClListRel cid s sL ->
  ClListRel cid (undup s) (I.List_dedup T (ct_decidable_eq T) sL).
Proof.
  intros s sL Hs. have E := cl_list_logic _ _ _ Hs. subst sL. apply: coq_eq_to_imported_eq. clear Hs.
  elim: s => [|x s IH].
  - exact (Logic.eq_sym (imported_eq_to_coq_eq _ _ (I.Prosa_Validation_ClassicImplGlobalJitterScheduleInterface_dedup_nil T (ct_decidable_eq T)))).
  - change (Logic.eq (cl_map cid (if x \in s then undup s else x :: undup s))
      (I.List_dedup T (ct_decidable_eq T) (I.List_cons T x (cl_map cid s)))).
    case Hx: (x \in s).
    + rewrite (imported_eq_to_coq_eq _ _ (I.Prosa_Validation_ClassicImplGlobalJitterScheduleInterface_dedup_cons_mem
                 T (ct_decidable_eq T) x (cl_map cid s)
                 (prop_to_sprop _ _ (cgq_mem T x s _ (cl_lean_eq _ _ _ (Logic.eq_refl _))) Hx))).
      exact IH.
    + rewrite (imported_eq_to_coq_eq _ _ (I.Prosa_Validation_ClassicImplGlobalJitterScheduleInterface_dedup_cons_not_mem
                 T (ct_decidable_eq T) x (cl_map cid s) (cgq_notin_target T x s Hx))).
      change (Logic.eq (I.List_cons T x (cl_map cid (undup s))) (I.List_cons T x (I.List_dedup T (ct_decidable_eq T) (cl_map cid s)))).
      by rewrite IH.
Qed.

(* ------------------------------------------------------------------ *)
(** * Schedules, arrival sequences, parameters *)

Definition CgqParRel (T : Type) (pR : T -> nat) (pL : T -> Lean.Nat) : SProp := forall x, SubNatRel (pR x) (pL x).

Lemma cgq_forall_par (T : Type) (PR : (T -> nat) -> Prop) (PL : (T -> Lean.Nat) -> SProp) :
  (forall pR pL, CgqParRel T pR pL -> PropSPropRel (PR pR) (PL pL)) -> PropSPropRel (forall p, PR p) (forall p, PL p).
Proof.
  exact (cgq_forall_cover _ _ (CgqParRel T) (fun pR j => sub_nat_to_imported (pR j)) (fun pL j => sub_nat_to_rocq (pL j))
           (fun pR j => sub_nat_rel_canonical (pR j)) (fun pL j => sub_nat_rel_surjective (pL j)) PR PL).
Qed.

Section Sched.
Variables (Job : eqType) (nR : nat) (nL : Lean.Nat).
Hypothesis Hn : SubNatRel nR nL.
Notation dJ := (ct_decidable_eq Job).
Notation LSched := (I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_schedule Job dJ nL).

Definition CgqSchedRel (sR : Schedule.schedule Job nR) (sL : LSched) : SProp :=
  forall oR oL, CoOrdRel nR nL oR oL -> forall tR tL, SubNatRel tR tL -> Lean.eq (cl_opt (sR oR tR)) (sL oL tL).

Definition cgq_sched_to_target (sR : Schedule.schedule Job nR) : LSched :=
  fun oL tL => cl_opt (sR (co_fin_to_ord nR nL Hn oL) (sub_nat_to_rocq tL)).

Definition cgq_sched_to_source (sL : LSched) : Schedule.schedule Job nR :=
  fun oR tR => cl_unopt (sL (co_ord_to_fin nR nL Hn oR) (sub_nat_to_imported tR)).

Lemma cgq_sched_canonical sR : CgqSchedRel sR (cgq_sched_to_target sR).
Proof.
  intros oR oL Ho tR tL Ht. apply: coq_eq_to_imported_eq. rewrite /cgq_sched_to_target (co_nat_input _ _ Ht).
  by rewrite (co_ord_eq _ _ _ _ _ Ho (co_ord_surjective nR nL Hn oL)).
Qed.

Lemma cgq_sched_surjective sL : CgqSchedRel (cgq_sched_to_source sL) sL.
Proof.
  intros oR oL Ho tR tL Ht. apply: coq_eq_to_imported_eq. rewrite /cgq_sched_to_source cl_opt_unopt.
  rewrite (co_nat_logic _ _ Ht). by rewrite (co_fin_rel_eq _ _ _ _ _ (co_ord_canonical nR nL Hn oR) Ho).
Qed.

Lemma cgq_forall_sched (PR : Schedule.schedule Job nR -> Prop) (PL : LSched -> SProp) :
  (forall sR sL, CgqSchedRel sR sL -> PropSPropRel (PR sR) (PL sL)) -> PropSPropRel (forall s, PR s) (forall s, PL s).
Proof. exact (cgq_forall_cover _ _ CgqSchedRel cgq_sched_to_target cgq_sched_to_source cgq_sched_canonical cgq_sched_surjective PR PL). Qed.

End Sched.

Section Arr.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).
Notation LArr := (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrival_sequence Job dJ).

Definition CgqArrRel (aR : ArrivalSequence.arrival_sequence Job) (aL : LArr) : SProp :=
  forall tR tL, SubNatRel tR tL -> ClListRel cid (aR tR) (aL tL).

Definition cgq_arr_to_target (aR : ArrivalSequence.arrival_sequence Job) : LArr :=
  fun tL => cl_map cid (aR (sub_nat_to_rocq tL)).

Definition cgq_arr_to_source (aL : LArr) : ArrivalSequence.arrival_sequence Job :=
  fun tR => cl_unmap cid (aL (sub_nat_to_imported tR)).

Lemma cgq_arr_canonical aR : CgqArrRel aR (cgq_arr_to_target aR).
Proof.
  intros tR tL Ht. have E := co_nat_logic _ _ Ht. subst tL.
  apply: coq_eq_to_imported_eq. rewrite /cgq_arr_to_target sub_nat_rocq_roundtrip. reflexivity.
Qed.

Lemma cgq_arr_surjective aL : CgqArrRel (cgq_arr_to_source aL) aL.
Proof.
  intros tR tL Ht. have E := co_nat_logic _ _ Ht. subst tL.
  apply: coq_eq_to_imported_eq. exact (cl_map_unmap cid cid (fun _ => Logic.eq_refl _) _).
Qed.

Lemma cgq_arrives_in aR aL (Ha : CgqArrRel aR aL) j :
  PropSPropRel (ArrivalSequence.arrives_in aR j)
    (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrives_in Job dJ aL j).
Proof. apply: ct_exists_nat => tR tL Ht. exact (cgq_mem Job j _ _ (Ha tR tL Ht)). Qed.

End Arr.

(* ------------------------------------------------------------------ *)
(** * Definitions *)

Section Defs.
Variables (Job : eqType) (nR : nat) (nL : Lean.Nat).
Hypothesis Hn : SubNatRel nR nL.
Notation dJ := (ct_decidable_eq Job).
Variables (sR : Schedule.schedule Job nR)
  (sL : I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_schedule Job dJ nL).
Hypothesis Hs : CgqSchedRel Job nR nL sR sL.

Lemma cgq_GS_scheduled_on j oR oL (Ho : CoOrdRel nR nL oR oL) tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (Schedule.scheduled_on sR j oR tR)
    (I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_scheduled_on Job dJ nL sL j oL tL).
Proof.
  apply: ct_decide_bool.
  exact (cgq_tr (Hs oR oL Ho tR tL Ht) (fun z => PropSPropRel (sR oR tR == Some j) (Lean.eq z (cl_opt (Some j))))
           (cgq_opt_eqb_rel Job (sR oR tR) (Some j))).
Qed.

Lemma cgq_GS_scheduled j tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (Schedule.scheduled sR j tR)
    (I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_scheduled Job dJ nL sL j tL).
Proof.
  apply: (co_exists_rel nR nL Hn). intros oR oL Ho. exact (cgq_GS_scheduled_on j oR oL Ho tR tL Ht).
Qed.

Lemma cgq_GS_service_at j tR tL (Ht : SubNatRel tR tL) :
  SubNatRel (Schedule.service_at sR j tR)
    (I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_service_at Job dJ nL sL j tL).
Proof.
  apply: coq_eq_to_imported_eq.
  rewrite (imported_eq_to_coq_eq _ _ (I.Prosa_Validation_ClassicImplGlobalJitterScheduleInterface_service_at_sum Job dJ nL sL j tL)).
  apply: imported_eq_to_coq_eq.
  rewrite /Schedule.service_at big_mkcond /=.
  apply: (co_sum_rel nR nL Hn). intros oR oL Ho.
  have H := cgq_GS_scheduled_on j oR oL Ho tR tL Ht.
  rewrite (ct_bool_rel_logic _ _ H). destruct (Schedule.scheduled_on sR j oR tR).
  - exact (sub_nat_rel_canonical 1).
  - exact (sub_nat_rel_canonical 0).
Qed.

Lemma cgq_service_at_fun j : CgqFunRel (fun t => Schedule.service_at sR j t)
    (fun t => I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_service_at Job dJ nL sL j t).
Proof. intros kR kL Hk. exact (cgq_GS_service_at j kR kL Hk). Qed.

Lemma cgq_GS_service j tR tL (Ht : SubNatRel tR tL) :
  SubNatRel (Schedule.service sR j tR)
    (I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_service Job dJ nL sL j tL).
Proof. exact (cgq_ico 0 _ tR tL _ _ (sub_nat_rel_canonical 0) Ht (cgq_service_at_fun j)). Qed.

Lemma cgq_GS_completed cR cL (Hc : CgqParRel Job cR cL) j tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (Schedule.completed cR sR j tR)
    (I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_completed Job dJ cL nL sL j tL).
Proof. exact (ct_decide_le _ _ _ _ (Hc j) (cgq_GS_service j tR tL Ht)). Qed.

Lemma cgq_GS_sequential_jobs :
  PropSPropRel (Schedule.sequential_jobs sR)
    (I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_sequential_jobs Job dJ nL sL).
Proof.
  apply: ct_forall_identity => j. apply: ct_forall_nat => tR tL Ht.
  apply: (co_forall_ord nR nL Hn) => o1R o1L H1. apply: (co_forall_ord nR nL Hn) => o2R o2L H2.
  apply: ct_imp.
  { exact (cgq_tr (Hs o1R o1L H1 tR tL Ht) (fun z => PropSPropRel (sR o1R tR = Some j) (Lean.eq z (cl_opt (Some j))))
             (cgq_opt_eq_rel Job (sR o1R tR) (Some j))). }
  apply: ct_imp.
  { exact (cgq_tr (Hs o2R o2L H2 tR tL Ht) (fun z => PropSPropRel (sR o2R tR = Some j) (Lean.eq z (cl_opt (Some j))))
             (cgq_opt_eq_rel Job (sR o2R tR) (Some j))). }
  exact (co_ord_eq_rel _ _ _ _ _ _ H1 H2).
Qed.

Lemma cgq_GS_completed_jobs_dont_execute cR cL (Hc : CgqParRel Job cR cL) :
  PropSPropRel (Schedule.completed_jobs_dont_execute cR sR)
    (I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_completed_jobs_dont_execute Job dJ cL nL sL).
Proof.
  apply: ct_forall_identity => j. apply: ct_forall_nat => tR tL Ht.
  exact (sub_nat_le_correspondence _ _ _ _ (cgq_GS_service j tR tL Ht) (Hc j)).
Qed.

Lemma cgq_GS_jobs_come_from_arrival_sequence arrR arrL (Harr : CgqArrRel Job arrR arrL) :
  PropSPropRel (Schedule.jobs_come_from_arrival_sequence sR arrR)
    (I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_jobs_come_from_arrival_sequence Job dJ nL sL arrL).
Proof.
  apply: ct_forall_identity => j. apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (ct_bool_truth _ _ (cgq_GS_scheduled j tR tL Ht)).
  exact (cgq_arrives_in Job arrR arrL Harr j).
Qed.

End Defs.

Section TaskDefs.
Variables (Task Job : eqType) (nR : nat) (nL : Lean.Nat).
Hypothesis Hn : SubNatRel nR nL.
Notation dT := (ct_decidable_eq Task).
Notation dJ := (ct_decidable_eq Job).
Variables (sR : Schedule.schedule Job nR)
  (sL : I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_schedule Job dJ nL).
Hypothesis Hs : CgqSchedRel Job nR nL sR sL.
Variable job_task : Job -> Task.

End TaskDefs.

Lemma cgq_GS_processor nR nL (Hn : SubNatRel nR nL) :
  And (forall o : Schedule.processor nR, CoOrdRel nR nL o (co_ord_to_fin nR nL Hn o))
      (forall o : I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_processor nL,
         CoOrdRel nR nL (co_fin_to_ord nR nL Hn o) o).
Proof. exact (And_intro _ _ (co_ord_canonical nR nL Hn) (co_ord_surjective nR nL Hn)). Qed.

Lemma cgq_GS_schedule (Job : eqType) nR nL (Hn : SubNatRel nR nL) :
  And (forall s : Schedule.schedule Job nR, CgqSchedRel Job nR nL s (cgq_sched_to_target Job nR nL Hn s))
      (forall s : I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_schedule Job (ct_decidable_eq Job) nL,
         CgqSchedRel Job nR nL (cgq_sched_to_source Job nR nL Hn s) s).
Proof. exact (And_intro _ _ (cgq_sched_canonical Job nR nL Hn) (cgq_sched_surjective Job nR nL Hn)). Qed.

(* ------------------------------------------------------------------ *)
(** * Statements *)

(** The common prefix [forall num_cpus (sched : schedule Job num_cpus)]. *)
Lemma cgq_forall_ncpus_sched (Job : eqType)
    (PR : forall n : nat, Schedule.schedule Job n -> Prop)
    (PL : forall n : Lean.Nat, I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_schedule Job (ct_decidable_eq Job) n -> SProp) :
  (forall nR nL (Hn : SubNatRel nR nL) sR sL, CgqSchedRel Job nR nL sR sL -> PropSPropRel (PR nR sR) (PL nL sL)) ->
  PropSPropRel (forall n s, PR n s) (forall n s, PL n s).
Proof.
  intro H. apply: ct_forall_nat => nR nL Hn. exact (cgq_forall_sched Job nR nL Hn _ _ (H nR nL Hn)).
Qed.

Section GjschedDefs.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).

Lemma cgq_GJ_actual_arrival aR aL (Ha : CgqParRel Job aR aL) jjR jjL (Hjj : CgqParRel Job jjR jjL) j :
  SubNatRel (ScheduleWithJitter.actual_arrival aR jjR j) (I.Prosa_Classic_Model_Schedule_Global_Jitter_Schedule_ScheduleWithJitter_actual_arrival Job dJ aL jjL j).
Proof. exact (sub_add_correspondence _ _ _ _ (Ha j) (Hjj j)). Qed.

Lemma cgq_GJ_jitter_has_passed aR aL (Ha : CgqParRel Job aR aL) jjR jjL (Hjj : CgqParRel Job jjR jjL) j
    tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (ScheduleWithJitter.jitter_has_passed aR jjR j tR) (I.Prosa_Classic_Model_Schedule_Global_Jitter_Schedule_ScheduleWithJitter_jitter_has_passed Job dJ aL jjL j tL).
Proof. exact (ct_decide_le _ _ _ _ (cgq_GJ_actual_arrival aR aL Ha jjR jjL Hjj j) Ht). Qed.

Section GjschedSched.
Variables (nR : nat) (nL : Lean.Nat).
Hypothesis Hn : SubNatRel nR nL.
Variables (sR : Schedule.schedule Job nR)
  (sL : I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_schedule Job dJ nL).
Hypothesis Hs : CgqSchedRel Job nR nL sR sL.

Lemma cgq_GJ_pending aR aL (Ha : CgqParRel Job aR aL) cR cL (Hc : CgqParRel Job cR cL)
    jjR jjL (Hjj : CgqParRel Job jjR jjL) j tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (ScheduleWithJitter.pending aR cR jjR sR j tR) (I.Prosa_Classic_Model_Schedule_Global_Jitter_Schedule_ScheduleWithJitter_pending Job dJ aL cL jjL nL sL j tL).
Proof.
  exact (ct_bool_and _ _ _ _ (cgq_GJ_jitter_has_passed aR aL Ha jjR jjL Hjj j tR tL Ht)
           (ct_bool_not _ _ (cgq_GS_completed Job nR nL Hn sR sL Hs cR cL Hc j tR tL Ht))).
Qed.

Lemma cgq_GJ_backlogged aR aL (Ha : CgqParRel Job aR aL) cR cL (Hc : CgqParRel Job cR cL)
    jjR jjL (Hjj : CgqParRel Job jjR jjL) j tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (ScheduleWithJitter.backlogged aR cR jjR sR j tR) (I.Prosa_Classic_Model_Schedule_Global_Jitter_Schedule_ScheduleWithJitter_backlogged Job dJ aL cL jjL nL sL j tL).
Proof.
  exact (ct_bool_and _ _ _ _ (cgq_GJ_pending aR aL Ha cR cL Hc jjR jjL Hjj j tR tL Ht)
           (ct_bool_not _ _ (cgq_GS_scheduled Job nR nL Hn sR sL Hs j tR tL Ht))).
Qed.

Lemma cgq_GJ_jobs_execute_after_jitter aR aL (Ha : CgqParRel Job aR aL) jjR jjL (Hjj : CgqParRel Job jjR jjL) :
  PropSPropRel (ScheduleWithJitter.jobs_execute_after_jitter aR jjR sR) (I.Prosa_Classic_Model_Schedule_Global_Jitter_Schedule_ScheduleWithJitter_jobs_execute_after_jitter Job dJ aL jjL nL sL).
Proof.
  apply: ct_forall_identity => j. apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (ct_bool_truth _ _ (cgq_GS_scheduled Job nR nL Hn sR sL Hs j tR tL Ht)).
  exact (ct_bool_truth _ _ (cgq_GJ_jitter_has_passed aR aL Ha jjR jjL Hjj j tR tL Ht)).
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
Hypothesis Hs : CgqSchedRel Job nR nL sR sL.
Variable job_task : Job -> Task.

End GjschedTaskDefs.

(** Priority relations (as in the accepted classic priority certificate). *)
Definition CgqRelRel (T : Type) (rR : T -> T -> bool) (rL : T -> T -> I.Bool) : SProp :=
  forall a b, CtBoolRel (rR a b) (rL a b).

Lemma cgq_rel_canonical (T : Type) (rR : T -> T -> bool) : CgqRelRel T rR (fun a b => ct_b2l (rR a b)).
Proof. intros a b. exact (ct_bool_canonical _). Qed.

Lemma cgq_rel_surjective (T : Type) (rL : T -> T -> I.Bool) : CgqRelRel T (fun a b => ct_l2b (rL a b)) rL.
Proof. intros a b. exact (ct_bool_surjective _). Qed.

Lemma cgq_forall_rel (T : Type) (PR : (T -> T -> bool) -> Prop) (PL : (T -> T -> I.Bool) -> SProp) :
  (forall rR rL, CgqRelRel T rR rL -> PropSPropRel (PR rR) (PL rL)) -> PropSPropRel (forall r, PR r) (forall r, PL r).
Proof.
  exact (cgq_forall_cover _ _ (CgqRelRel T) (fun rR a b => ct_b2l (rR a b)) (fun rL a b => ct_l2b (rL a b))
           (cgq_rel_canonical T) (cgq_rel_surjective T) PR PL).
Qed.

Definition CgqJldpRel (T : Type) (rR : nat -> T -> T -> bool) (rL : Lean.Nat -> T -> T -> I.Bool) : SProp :=
  forall tR tL, SubNatRel tR tL -> CgqRelRel T (rR tR) (rL tL).

Lemma cgq_jldp_canonical (T : Type) (rR : nat -> T -> T -> bool) :
  CgqJldpRel T rR (fun tL a b => ct_b2l (rR (sub_nat_to_rocq tL) a b)).
Proof.
  intros tR tL Ht a b. have E := cl_nat_logic _ _ Ht. subst tL. rewrite sub_nat_rocq_roundtrip.
  exact (ct_bool_canonical _).
Qed.

Lemma cgq_jldp_surjective (T : Type) (rL : Lean.Nat -> T -> T -> I.Bool) :
  CgqJldpRel T (fun tR a b => ct_l2b (rL (sub_nat_to_imported tR) a b)) rL.
Proof. intros tR tL Ht a b. have E := cl_nat_logic _ _ Ht. subst tL. exact (ct_bool_surjective _). Qed.

(* ------------------------------------------------------------------ *)
(** * Arrival sequences *)

Lemma cgq_forall_jldp (T : Type) (PR : (nat -> T -> T -> bool) -> Prop) (PL : (Lean.Nat -> T -> T -> I.Bool) -> SProp) :
  (forall rR rL, CgqJldpRel T rR rL -> PropSPropRel (PR rR) (PL rL)) -> PropSPropRel (forall r, PR r) (forall r, PL r).
Proof.
  exact (cgq_forall_cover _ _ (CgqJldpRel T) (fun rR tL a b => ct_b2l (rR (sub_nat_to_rocq tL) a b))
           (fun rL tR a b => ct_l2b (rL (sub_nat_to_imported tR) a b)) (cgq_jldp_canonical T) (cgq_jldp_surjective T) PR PL).
Qed.

Section PriodefsDefs.
Variables (Task Job : eqType).
Notation dT := (ct_decidable_eq Task).
Notation dJ := (ct_decidable_eq Job).

Lemma cgq_PR_JLDP_policy :
  And (forall rR : Priority.JLDP_policy Job, CgqJldpRel Job rR (fun tL a b => ct_b2l (rR (sub_nat_to_rocq tL) a b)))
      (forall rL : I.Prosa_Classic_Model_Priority_Priority_JLDP_policy Job dJ,
         CgqJldpRel Job (fun tR a b => ct_l2b (rL (sub_nat_to_imported tR) a b)) rL).
Proof. exact (And_intro _ _ (cgq_jldp_canonical Job) (cgq_jldp_surjective Job)). Qed.

Lemma cgq_transitive (T : Type) rR rL (Hr : CgqRelRel T rR rL) :
  PropSPropRel (transitive rR) (I.Prosa_Classic_Model_Priority_Priority_transitiveB T rL).
Proof.
  apply: ct_forall_identity => y. apply: ct_forall_identity => x. apply: ct_forall_identity => z.
  apply: ct_imp; first exact (ct_bool_truth _ _ (Hr x y)).
  apply: ct_imp; first exact (ct_bool_truth _ _ (Hr y z)).
  exact (ct_bool_truth _ _ (Hr x z)).
Qed.

Lemma cgq_PR_JLDP_is_transitive rR rL (Hr : CgqJldpRel Job rR rL) :
  PropSPropRel (Priority.JLDP_is_transitive rR) (I.Prosa_Classic_Model_Priority_Priority_JLDP_is_transitive Job dJ rL).
Proof. apply: ct_forall_nat => tR tL Ht. exact (cgq_transitive Job _ _ (Hr tR tL Ht)). Qed.

End PriodefsDefs.

(* ------------------------------------------------------------------ *)
(** * Options and transports *)

Lemma cgq_opt_rel_eq (A : Type) (o1 o2 : option A) l1 l2 :
  Lean.eq (cl_opt o1) l1 -> Lean.eq (cl_opt o2) l2 -> PropSPropRel (Logic.eq o1 o2) (Lean.eq l1 l2).
Proof.
  intros H1 H2. destruct H1. destruct H2. apply prop_sprop_rel_intro.
  - intro E. rewrite E. exact (@Lean.eq_refl _ _).
  - intro E. apply strictly_inhabits. exact (cgq_opt_inj A o1 o2 (imported_eq_to_coq_eq _ _ E)).
Qed.

Definition cgq_lsym {A : Type} {x y : A} (E : Lean.eq x y) : Lean.eq y x :=
  match E in Lean.eq _ z return Lean.eq z x with Lean.eq_refl => @Lean.eq_refl _ _ end.

Lemma cgq_src_transport {A : Type} (P : A -> SProp) (x y : A) : Logic.eq x y -> P x -> P y.
Proof. intro E. destruct E. exact (fun p => p). Qed.

(* ------------------------------------------------------------------ *)
(** * Construction from prefixes, specialised at related inputs

    As in the accepted v0.6 [implementation/facts/generic_schedule.v] certificate and the accepted classic
    uniprocessor construction certificate: the construction function [build_schedule : schedule Job num_cpus ->
    schedule Job num_cpus] is a higher-order input; the certificates below are stated for any source function and any
    Lean function mapping related schedules to related schedules ([Hbuild]), at related processor counts ([Hn]) and
    related base schedules ([Hbase]).  Inside the statements every quantified schedule, processor, instant and job is
    covered in both directions. *)

Section GCConstruction.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).
Variables (nR : nat) (nL : Lean.Nat).
Hypothesis Hn : SubNatRel nR nL.
Notation LSched := (I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_schedule Job dJ nL).
Variable buildR : Schedule.schedule Job nR -> Schedule.schedule Job nR.
Variable buildL : LSched -> LSched.
Hypothesis Hbuild : forall sR sL, CgqSchedRel Job nR nL sR sL -> CgqSchedRel Job nR nL (buildR sR) (buildL sL).
Variables (baseR : Schedule.schedule Job nR) (baseL : LSched).
Hypothesis Hbase : CgqSchedRel Job nR nL baseR baseL.

Lemma cgq_GC_update_schedule prevR prevL (Hprev : CgqSchedRel Job nR nL prevR prevL) mR mL (Hm : SubNatRel mR mL) :
  CgqSchedRel Job nR nL (@ScheduleConstruction.update_schedule Job nR buildR prevR mR) (I.Prosa_Classic_Model_Schedule_Global_Transformation_Construction_ScheduleConstruction_update_schedule Job dJ nL buildL prevL mL).
Proof.
  intros oR oL Ho tR tL Ht. unfold ScheduleConstruction.update_schedule, I.Prosa_Classic_Model_Schedule_Global_Transformation_Construction_ScheduleConstruction_update_schedule. cbv beta.
  apply: coq_eq_to_imported_eq.
  rewrite (ct_bool_rel_logic _ _ (ct_decide_eq_nat _ _ _ _ Ht Hm)).
  case: (tR == mR).
  - exact (imported_eq_to_coq_eq _ _ (Hbuild prevR prevL Hprev oR oL Ho tR tL Ht)).
  - exact (imported_eq_to_coq_eq _ _ (Hprev oR oL Ho tR tL Ht)).
Qed.

Lemma cgq_prefix_canonical (kR : nat) :
  CgqSchedRel Job nR nL (@ScheduleConstruction.schedule_prefix Job nR buildR baseR kR) (I.Prosa_Classic_Model_Schedule_Global_Transformation_Construction_ScheduleConstruction_schedule_prefix Job dJ nL buildL baseL (sub_nat_to_imported kR)).
Proof.
  induction kR as [|k IH].
  - refine (cgq_trs (cgq_lsym (I.Prosa_Validation_ClassicImplGlobalJitterScheduleInterface_production_schedule_prefix_zero Job dJ nL buildL baseL))
              (fun z => CgqSchedRel Job nR nL _ z) _).
    exact (cgq_GC_update_schedule baseR baseL Hbase 0 _ (sub_nat_rel_canonical 0)).
  - assert (Hk1 : SubNatRel k.+1 (I.HAdd_hAdd_inst7 Lean.Nat Lean.Nat Lean.Nat (I.instHAdd_inst1 Lean.Nat I.instAddNat)
                                 (sub_nat_to_imported k) (I.OfNat_ofNat_inst1 Lean.Nat 1 (I.instOfNatNat 1)))).
    { exact (cgq_src_transport (fun x => SubNatRel x _) _ _ (addn1 k)
               (sub_add_correspondence _ _ _ _ (sub_nat_rel_canonical k) (sub_nat_rel_canonical 1))). }
    refine (cgq_trs Hk1 (fun z => CgqSchedRel Job nR nL (@ScheduleConstruction.schedule_prefix Job nR buildR baseR k.+1) (I.Prosa_Classic_Model_Schedule_Global_Transformation_Construction_ScheduleConstruction_schedule_prefix Job dJ nL buildL baseL z)) _).
    refine (cgq_trs (cgq_lsym (I.Prosa_Validation_ClassicImplGlobalJitterScheduleInterface_production_schedule_prefix_succ Job dJ nL buildL baseL (sub_nat_to_imported k)))
              (fun z => CgqSchedRel Job nR nL _ z) _).
    exact (cgq_GC_update_schedule _ _ IH _ _ Hk1).
Qed.

Lemma cgq_GC_schedule_prefix kR kL (Hk : SubNatRel kR kL) :
  CgqSchedRel Job nR nL (@ScheduleConstruction.schedule_prefix Job nR buildR baseR kR) (I.Prosa_Classic_Model_Schedule_Global_Transformation_Construction_ScheduleConstruction_schedule_prefix Job dJ nL buildL baseL kL).
Proof. exact (cgq_trs Hk (fun z => CgqSchedRel Job nR nL _ (I.Prosa_Classic_Model_Schedule_Global_Transformation_Construction_ScheduleConstruction_schedule_prefix Job dJ nL buildL baseL z)) (cgq_prefix_canonical kR)). Qed.

Lemma cgq_GC_build_schedule_from_prefixes :
  CgqSchedRel Job nR nL (@ScheduleConstruction.build_schedule_from_prefixes Job nR buildR baseR) (I.Prosa_Classic_Model_Schedule_Global_Transformation_Construction_ScheduleConstruction_build_schedule_from_prefixes Job dJ nL buildL baseL).
Proof. intros oR oL Ho tR tL Ht. exact (cgq_GC_schedule_prefix tR tL Ht oR oL Ho tR tL Ht). Qed.

Notation SCH := cgq_GC_build_schedule_from_prefixes.

(** ** Statements *)

End GCConstruction.

(* ------------------------------------------------------------------ *)
(** * MathComp [sort] and the restated Lean merge sort

    The Lean file restates MathComp's [merge], [merge_sort_push], [merge_sort_pop], [merge_sort_rec] and [sort]
    equation by equation ([mc_*], structurally recursive).  Each Lean defining equation is a kernel-checked [rfl]
    fixture theorem ([xms_*]); the source equations hold by computation.  The sorts are related for every relation
    [leT] (pointwise related Boolean relations), by induction on the arguments. *)

Local Notation EQ H := (imported_eq_to_coq_eq _ _ H).

Lemma cgq_ite_any (b : bool) bL (Hb : CtBoolRel b bL) (A : Type) (x y : A) :
  Logic.eq (I.ite A (Lean.eq bL I.Bool_true) (I.instDecidableEqBool bL I.Bool_true) x y) (if b then x else y).
Proof. rewrite (ct_bool_rel_logic _ _ Hb). clear Hb. by case: b. Qed.

Section McSort.
Variables (T : Type) (leR : T -> T -> bool) (leL : T -> T -> I.Bool).
Hypothesis Hle : forall a b, CtBoolRel (leR a b) (leL a b).
Local Notation M := (cl_map (fun z : T => z)).
Local Notation MM := (cl_map (cl_map (fun z : T => z))).

Lemma cgq_mc_merge : forall s1 s2, Logic.eq (I.Prosa_Classic_Implementation_Global_Jitter_Schedule_ConcreteScheduler_mc_merge T leL (M s1) (M s2)) (M (merge leR s1 s2)).
Proof.
  elim => [|x1 s1 IH] s2.
  - rewrite (EQ (I.Prosa_Validation_ClassicImplGlobalJitterScheduleInterface_xms_merge_nil T leL (M s2))). by case: s2.
  - elim: s2 => [|x2 s2 IH2].
    + exact (EQ (I.Prosa_Validation_ClassicImplGlobalJitterScheduleInterface_xms_merge_cons_nil T leL x1 (M s1))).
    + rewrite (EQ (I.Prosa_Validation_ClassicImplGlobalJitterScheduleInterface_xms_merge_cons_cons T leL x1 (M s1) x2 (M s2))).
      rewrite (cgq_ite_any _ _ (Hle x1 x2)).
      have -> : Logic.eq (merge leR (x1 :: s1) (x2 :: s2))
                  (if leR x1 x2 then x1 :: merge leR s1 (x2 :: s2) else x2 :: merge leR (x1 :: s1) s2) by [].
      case: (leR x1 x2).
      * change (Logic.eq (I.List_cons T x1 (I.Prosa_Classic_Implementation_Global_Jitter_Schedule_ConcreteScheduler_mc_merge T leL (M s1) (M (x2 :: s2)))) (M (x1 :: merge leR s1 (x2 :: s2)))).
        by rewrite IH.
      * change (Logic.eq (I.List_cons T x2 (I.Prosa_Classic_Implementation_Global_Jitter_Schedule_ConcreteScheduler_mc_merge T leL (M (x1 :: s1)) (M s2))) (M (x2 :: merge leR (x1 :: s1) s2))).
        by rewrite IH2.
Qed.

Lemma cgq_mc_push : forall ss s1, Logic.eq (I.Prosa_Classic_Implementation_Global_Jitter_Schedule_ConcreteScheduler_mc_merge_sort_push T leL (M s1) (MM ss)) (MM (merge_sort_push leR s1 ss)).
Proof.
  elim => [|[|x s2] ss IH] s1.
  - exact (EQ (I.Prosa_Validation_ClassicImplGlobalJitterScheduleInterface_xms_push_nil T leL (M s1))).
  - exact (EQ (I.Prosa_Validation_ClassicImplGlobalJitterScheduleInterface_xms_push_nil_cons T leL (M s1) (MM ss))).
  - rewrite (EQ (I.Prosa_Validation_ClassicImplGlobalJitterScheduleInterface_xms_push_cons_cons T leL (M s1) x (M s2) (MM ss))).
    change (Logic.eq (I.List_cons (I.List T) (I.List_nil T)
                        (I.Prosa_Classic_Implementation_Global_Jitter_Schedule_ConcreteScheduler_mc_merge_sort_push T leL (I.Prosa_Classic_Implementation_Global_Jitter_Schedule_ConcreteScheduler_mc_merge T leL (M (x :: s2)) (M s1)) (MM ss)))
                     (MM ([::] :: merge_sort_push leR (merge leR (x :: s2) s1) ss))).
    by rewrite cgq_mc_merge IH.
Qed.

Lemma cgq_mc_pop : forall ss s1, Logic.eq (I.Prosa_Classic_Implementation_Global_Jitter_Schedule_ConcreteScheduler_mc_merge_sort_pop T leL (M s1) (MM ss)) (M (merge_sort_pop leR s1 ss)).
Proof.
  elim => [|s2 ss IH] s1.
  - exact (EQ (I.Prosa_Validation_ClassicImplGlobalJitterScheduleInterface_xms_pop_nil T leL (M s1))).
  - rewrite (EQ (I.Prosa_Validation_ClassicImplGlobalJitterScheduleInterface_xms_pop_cons T leL (M s1) (M s2) (MM ss))) cgq_mc_merge. exact (IH _).
Qed.

Lemma cgq_mc_rec : forall n s, size s <= n -> forall ss,
  Logic.eq (I.Prosa_Classic_Implementation_Global_Jitter_Schedule_ConcreteScheduler_mc_merge_sort_rec T leL (MM ss) (M s)) (M (merge_sort_rec leR ss s)).
Proof.
  elim => [|n IH] [|x1 [|x2 s]] Hs ss //.
  - exact (Logic.eq_trans (EQ (I.Prosa_Validation_ClassicImplGlobalJitterScheduleInterface_xms_rec_nil T leL (MM ss))) (cgq_mc_pop ss [::])).
  - exact (Logic.eq_trans (EQ (I.Prosa_Validation_ClassicImplGlobalJitterScheduleInterface_xms_rec_nil T leL (MM ss))) (cgq_mc_pop ss [::])).
  - exact (Logic.eq_trans (EQ (I.Prosa_Validation_ClassicImplGlobalJitterScheduleInterface_xms_rec_one T leL (MM ss) x1)) (cgq_mc_pop ss [:: x1])).
  - rewrite (EQ (I.Prosa_Validation_ClassicImplGlobalJitterScheduleInterface_xms_rec_two T leL (MM ss) x1 x2 (M s))) (cgq_ite_any _ _ (Hle x1 x2)).
    have Hs' : size s <= n by move: Hs => /=; rewrite !ltnS => /ltnW.
    have -> : Logic.eq (merge_sort_rec leR ss [:: x1, x2 & s])
                (merge_sort_rec leR (merge_sort_push leR (if leR x1 x2 then [:: x1; x2] else [:: x2; x1]) ss) s) by [].
    case: (leR x1 x2).
    + change (Logic.eq (I.Prosa_Classic_Implementation_Global_Jitter_Schedule_ConcreteScheduler_mc_merge_sort_rec T leL (I.Prosa_Classic_Implementation_Global_Jitter_Schedule_ConcreteScheduler_mc_merge_sort_push T leL (M [:: x1; x2]) (MM ss)) (M s))
                       (M (merge_sort_rec leR (merge_sort_push leR [:: x1; x2] ss) s))).
      by rewrite cgq_mc_push IH.
    + change (Logic.eq (I.Prosa_Classic_Implementation_Global_Jitter_Schedule_ConcreteScheduler_mc_merge_sort_rec T leL (I.Prosa_Classic_Implementation_Global_Jitter_Schedule_ConcreteScheduler_mc_merge_sort_push T leL (M [:: x2; x1]) (MM ss)) (M s))
                       (M (merge_sort_rec leR (merge_sort_push leR [:: x2; x1] ss) s))).
      by rewrite cgq_mc_push IH.
Qed.

Lemma cgq_mc_sort s : Logic.eq (I.Prosa_Classic_Implementation_Global_Jitter_Schedule_ConcreteScheduler_mc_sort T leL (M s)) (M (sort leR s)).
Proof.
  rewrite (EQ (I.Prosa_Validation_ClassicImplGlobalJitterScheduleInterface_xms_sort T leL (M s))).
  exact (cgq_mc_rec (size s) s (leqnn _) [::]).
Qed.

Lemma cgq_sort_rel s sL (Hs : ClListRel (fun z : T => z) s sL) :
  ClListRel (fun z : T => z) (sort leR s) (I.Prosa_Classic_Implementation_Global_Jitter_Schedule_ConcreteScheduler_mc_sort T leL sL).
Proof.
  apply: coq_eq_to_imported_eq. rewrite (cl_list_logic _ _ _ Hs). exact (Logic.eq_sym (cgq_mc_sort s)).
Qed.

End McSort.

(* ------------------------------------------------------------------ *)
(** * Arrivals, [nth_or_none] and the platform predicates (as in the accepted classic arrival_sequence, util list and
    global platform certificates, re-stated for this export) *)

Lemma cgq_forall_arr (Job : eqType) PR PL :
  (forall aR aL, CgqArrRel Job aR aL -> PropSPropRel (PR aR) (PL aL)) -> PropSPropRel (forall a, PR a) (forall a, PL a).
Proof. exact (cgq_forall_cover _ _ (CgqArrRel Job) (cgq_arr_to_target Job) (cgq_arr_to_source Job) (cgq_arr_canonical Job) (cgq_arr_surjective Job) PR PL). Qed.

Lemma cgq_consistent (Job : eqType) pR pL (Hp : CgqParRel Job pR pL) aR aL (Ha : CgqArrRel Job aR aL) :
  PropSPropRel (ArrivalSequence.arrival_times_are_consistent pR aR)
    (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrival_times_are_consistent Job (ct_decidable_eq Job) pL aL).
Proof.
  apply: ct_forall_identity => j. apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (ct_bool_truth _ _ (ct_decide_bool _ _ _ (cgq_mem Job j _ _ (Ha tR tL Ht)))).
  exact (sub_nat_eq_correspondence _ _ _ _ (Hp j) Ht).
Qed.

Lemma cgq_is_a_set (Job : eqType) aR aL (Ha : CgqArrRel Job aR aL) :
  PropSPropRel (ArrivalSequence.arrival_sequence_is_a_set aR)
    (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrival_sequence_is_a_set Job (ct_decidable_eq Job) aL).
Proof. apply: ct_forall_nat => tR tL Ht. exact (cgq_uniq Job _ _ (Ha tR tL Ht)). Qed.

Lemma cgq_jobs_arrived_before (Job : eqType) aR aL (Ha : CgqArrRel Job aR aL) tR tL (Ht : SubNatRel tR tL) :
  ClListRel cid (ArrivalSequence.jobs_arrived_before aR tR)
    (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_jobs_arrived_before Job (ct_decidable_eq Job) aL tL).
Proof. exact (cgq_bigcat_nat_rel Job (fun t => aR t) (fun t => aL t) Ha 0 _ tR tL (sub_nat_rel_canonical 0) Ht). Qed.

Section JitterArr.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).
Notation LAJ := I.Prosa_Classic_Model_Arrival_Jitter_ArrivalSequence_ArrivalSequenceWithJitter_actual_arrival.

Lemma cgq_AJ_actual_arrival pR pL (Hp : CgqParRel Job pR pL) qR qL (Hq : CgqParRel Job qR qL) j :
  SubNatRel (ArrivalSequenceWithJitter.actual_arrival pR qR j) (LAJ Job dJ pL qL j).
Proof. exact (sub_add_correspondence _ _ _ _ (Hp j) (Hq j)). Qed.

Lemma cgq_AJ_actual_arrivals_between pR pL (Hp : CgqParRel Job pR pL) qR qL (Hq : CgqParRel Job qR qL)
    aR aL (Ha : CgqArrRel Job aR aL) t1R t1L (H1 : SubNatRel t1R t1L) t2R t2L (H2 : SubNatRel t2R t2L) :
  ClListRel cid (ArrivalSequenceWithJitter.actual_arrivals_between pR qR aR t1R t2R)
    (I.Prosa_Classic_Model_Arrival_Jitter_ArrivalSequence_ArrivalSequenceWithJitter_actual_arrivals_between Job dJ pL qL aL t1L t2L).
Proof.
  apply: coq_eq_to_imported_eq.
  have E := cl_list_logic _ _ _ (cgq_jobs_arrived_before Job aR aL Ha t2R t2L H2).
  have F := cl_filter cid _
              (fun j => I.Bool_and
                 (I.Decidable_decide (I.LE_le_inst1 Lean.Nat I.instLENat t1L (LAJ Job dJ pL qL j)) (I.Nat_decLe t1L (LAJ Job dJ pL qL j)))
                 (I.Decidable_decide (I.LT_lt_inst1 Lean.Nat I.instLTNat (LAJ Job dJ pL qL j) t2L) (I.Nat_decLt (LAJ Job dJ pL qL j) t2L)))
              (fun j => ct_bool_and _ _ _ _ (ct_decide_le _ _ _ _ H1 (cgq_AJ_actual_arrival pR pL Hp qR qL Hq j))
                                          (ct_decide_lt _ _ _ _ (cgq_AJ_actual_arrival pR pL Hp qR qL Hq j) H2))
              (ArrivalSequence.jobs_arrived_before aR t2R).
  rewrite -E in F. exact F.
Qed.

Lemma cgq_AJ_actual_arrivals_up_to pR pL (Hp : CgqParRel Job pR pL) qR qL (Hq : CgqParRel Job qR qL)
    aR aL (Ha : CgqArrRel Job aR aL) tR tL (Ht : SubNatRel tR tL) :
  ClListRel cid (ArrivalSequenceWithJitter.actual_arrivals_up_to pR qR aR tR)
    (I.Prosa_Classic_Model_Arrival_Jitter_ArrivalSequence_ArrivalSequenceWithJitter_actual_arrivals_up_to Job dJ pL qL aL tL).
Proof.
  exact (cgq_AJ_actual_arrivals_between pR pL Hp qR qL Hq aR aL Ha 0 _ (sub_nat_rel_canonical 0) tR.+1 _
           (sub_imported_eq_congr Lean.Nat_succ _ _ Ht)).
Qed.

End JitterArr.

Lemma cgq_nth_or_none (A : Type) : forall (s : seq A) n,
  Logic.eq (cl_opt (nth_or_none s n)) (I.Prosa_Classic_Util_List_nth_or_none A (cl_map cid s) (sub_nat_to_imported n)).
Proof. elim => [|x s IH] [|n] //=. Qed.

Lemma cgq_nth_or_none_rel (A : Type) s sL (Hs : ClListRel cid s sL) n nL (Hn : SubNatRel n nL) :
  Lean.eq (cl_opt (nth_or_none s n)) (I.Prosa_Classic_Util_List_nth_or_none A sL nL).
Proof.
  apply: coq_eq_to_imported_eq. rewrite (cl_list_logic _ _ _ Hs) (co_nat_logic _ _ Hn). exact (cgq_nth_or_none A s n).
Qed.

(** MathComp [total r] against its Lean statement [∀ x y, (r x y || r y x) = true]. *)
Lemma cgq_total (T : Type) rR rL (Hr : CgqRelRel T rR rL) :
  PropSPropRel (total rR) (forall x y, Lean.eq (I.Bool_or (rL x y) (rL y x)) I.Bool_true).
Proof.
  rewrite /total. apply: ct_forall_identity => x. apply: ct_forall_identity => y.
  exact (ct_bool_truth _ _ (ct_bool_or _ _ _ _ (Hr x y) (Hr y x))).
Qed.

Section PlatDefs.
Variables (Job : eqType) (nR : nat) (nL : Lean.Nat).
Hypothesis Hn : SubNatRel nR nL.
Notation dJ := (ct_decidable_eq Job).
Variables (sR : Schedule.schedule Job nR) (sL : I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_schedule Job dJ nL).
Hypothesis Hs : CgqSchedRel Job nR nL sR sL.
Variables (jaR : Job -> nat) (jaL : Job -> Lean.Nat) (cR : Job -> nat) (cL : Job -> Lean.Nat).
Hypotheses (Hja : CgqParRel Job jaR jaL) (Hc : CgqParRel Job cR cL).
Variables (jjR : Job -> nat) (jjL : Job -> Lean.Nat).
Hypothesis Hjj : CgqParRel Job jjR jjL.
Variables (aR : ArrivalSequence.arrival_sequence Job)
  (aL : I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrival_sequence Job dJ).
Hypothesis Ha : CgqArrRel Job aR aL.

Lemma cgq_PL_work_conserving :
  PropSPropRel (Platform.work_conserving jaR cR jjR aR sR)
    (I.Prosa_Classic_Model_Schedule_Global_Jitter_Platform_Platform_work_conserving Job dJ jaL cL jjL aL nL sL).
Proof.
  apply: ct_forall_identity => j. apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (cgq_arrives_in Job aR aL Ha j).
  apply: ct_imp; first exact (ct_bool_truth _ _ (cgq_GJ_backlogged Job nR nL Hn sR sL Hs jaR jaL Hja cR cL Hc jjR jjL Hjj j tR tL Ht)).
  apply: (co_forall_ord nR nL Hn) => oR oL Ho.
  apply: ct_exists_identity => j_other.
  exact (ct_bool_truth _ _ (cgq_GS_scheduled_on Job nR nL sR sL Hs j_other oR oL Ho tR tL Ht)).
Qed.

Lemma cgq_PL_respects_JLDP_policy hpR hpL (Hhp : CgqJldpRel Job hpR hpL) :
  PropSPropRel (Platform.respects_JLDP_policy jaR cR jjR aR sR hpR)
    (I.Prosa_Classic_Model_Schedule_Global_Jitter_Platform_Platform_respects_JLDP_policy Job dJ jaL cL jjL aL nL sL hpL).
Proof.
  apply: ct_forall_identity => j. apply: ct_forall_identity => j_hp. apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (cgq_arrives_in Job aR aL Ha j).
  apply: ct_imp; first exact (ct_bool_truth _ _ (cgq_GJ_backlogged Job nR nL Hn sR sL Hs jaR jaL Hja cR cL Hc jjR jjL Hjj j tR tL Ht)).
  apply: ct_imp; first exact (ct_bool_truth _ _ (cgq_GS_scheduled Job nR nL Hn sR sL Hs j_hp tR tL Ht)).
  exact (ct_bool_truth _ _ (Hhp tR tL Ht j_hp j)).
Qed.

End PlatDefs.

(* ------------------------------------------------------------------ *)
(** * Definitions *)

Section Defs.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).
Variables (jaR : Job -> nat) (jaL : Job -> Lean.Nat) (cR : Job -> nat) (cL : Job -> Lean.Nat).
Hypotheses (Hja : CgqParRel Job jaR jaL) (Hc : CgqParRel Job cR cL).
Variables (jjR : Job -> nat) (jjL : Job -> Lean.Nat).
Hypothesis Hjj : CgqParRel Job jjR jjL.
Variables (nR : nat) (nL : Lean.Nat).
Hypothesis Hn : SubNatRel nR nL.
Variables (aR : ArrivalSequence.arrival_sequence Job)
  (aL : I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrival_sequence Job dJ).
Hypothesis Ha : CgqArrRel Job aR aL.
Variables (hR : nat -> Job -> Job -> bool) (hL : Lean.Nat -> Job -> Job -> I.Bool).
Hypothesis Hh : CgqJldpRel Job hR hL.

Theorem ConcreteScheduler_pending_jobs_correspondence sR sL (Hs : CgqSchedRel Job nR nL sR sL) tR tL (Ht : SubNatRel tR tL) :
  ClListRel cid (@ConcreteScheduler.pending_jobs Job jaR cR jjR nR aR sR tR) (I.Prosa_Classic_Implementation_Global_Jitter_Schedule_ConcreteScheduler_pending_jobs Job dJ jaL cL jjL nL aL sL tL).
Proof.
  apply: coq_eq_to_imported_eq.
  have E := cl_list_logic _ _ _ (cgq_AJ_actual_arrivals_up_to Job jaR jaL Hja jjR jjL Hjj aR aL Ha tR tL Ht).
  have F := cl_filter cid _ (fun j => I.Prosa_Classic_Model_Schedule_Global_Jitter_Schedule_ScheduleWithJitter_pending Job dJ jaL cL jjL nL sL j tL)
              (fun j => cgq_GJ_pending Job nR nL Hn sR sL Hs jaR jaL Hja cR cL Hc jjR jjL Hjj j tR tL Ht) (ArrivalSequenceWithJitter.actual_arrivals_up_to jaR jjR aR tR).
  rewrite -E in F. exact F.
Qed.

Theorem ConcreteScheduler_sorted_pending_jobs_correspondence sR sL (Hs : CgqSchedRel Job nR nL sR sL) tR tL (Ht : SubNatRel tR tL) :
  ClListRel cid (@ConcreteScheduler.sorted_pending_jobs Job jaR cR jjR nR aR hR sR tR) (I.Prosa_Classic_Implementation_Global_Jitter_Schedule_ConcreteScheduler_sorted_pending_jobs Job dJ jaL cL jjL nL aL hL sL tL).
Proof. exact (cgq_sort_rel Job (hR tR) (hL tL) (Hh tR tL Ht) _ _ (ConcreteScheduler_pending_jobs_correspondence sR sL Hs tR tL Ht)). Qed.

Theorem ConcreteScheduler_nth_highest_priority_job_correspondence sR sL (Hs : CgqSchedRel Job nR nL sR sL) oR oL (Ho : CoOrdRel nR nL oR oL)
    tR tL (Ht : SubNatRel tR tL) :
  Lean.eq (cl_opt (@ConcreteScheduler.nth_highest_priority_job Job jaR cR jjR nR aR hR sR oR tR)) (I.Prosa_Classic_Implementation_Global_Jitter_Schedule_ConcreteScheduler_nth_highest_priority_job Job dJ jaL cL jjL nL aL hL sL oL tL).
Proof. exact (cgq_nth_or_none_rel Job _ _ (ConcreteScheduler_sorted_pending_jobs_correspondence sR sL Hs tR tL Ht) _ _ Ho). Qed.

Lemma cgq_empty : CgqSchedRel Job nR nL (fun _ _ => None) (fun _ _ => I.Option_none Job).
Proof. intros oR oL Ho tR tL Ht. exact (@Lean.eq_refl _ _). Qed.

Theorem ConcreteScheduler_scheduler_correspondence :
  CgqSchedRel Job nR nL (@ConcreteScheduler.scheduler Job jaR cR jjR nR aR hR) (I.Prosa_Classic_Implementation_Global_Jitter_Schedule_ConcreteScheduler_scheduler Job dJ jaL cL jjL nL aL hL).
Proof.
  exact (cgq_GC_build_schedule_from_prefixes Job nR nL _ _
           (fun sR sL Hs oR oL Ho tR tL Ht => ConcreteScheduler_nth_highest_priority_job_correspondence sR sL Hs oR oL Ho tR tL Ht) _ _ cgq_empty).
Qed.

End Defs.

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
  | |- SubNatRel (?f ?x) (?g ?x) => match goal with H : CgqParRel _ f g |- _ => exact (H x) end
  | |- CtBoolRel (?f ?x ?y) (?g ?x ?y) => match goal with H : CgqRelRel _ f g |- _ => exact (H x y) end
  | |- CtBoolRel (?f ?t ?x ?y) (?g ?u ?x ?y) => match goal with H : CgqJldpRel _ f g |- _ => eapply H end
  end.

Ltac crel_isnat T := first [ unify T nat | unify T Lean.Nat ].

Ltac crel_intro_defs T :=
  lazymatch T with
  | Schedule.processor ?n -> _ -> option _ => match goal with Hn : SubNatRel n _ |- _ => apply: (cgq_forall_sched _ _ _ Hn); intros ? ? ? end
  | ArrivalSequence.arrival_sequence _ => apply: (cgq_forall_arr _); intros ? ? ?
  | Schedule.schedule _ ?n => match goal with Hn : SubNatRel n _ |- _ => apply: (cgq_forall_sched _ _ _ Hn); intros ? ? ? end
  | Schedule.processor ?n => match goal with Hn : SubNatRel n _ |- _ => apply: (co_forall_ord _ _ Hn); intros ? ? ? end
  | ordinal ?n => match goal with Hn : SubNatRel n _ |- _ => apply: (co_forall_ord _ _ Hn); intros ? ? ? end
  | Priority.JLDP_policy _ => apply: (cgq_forall_jldp _); intros ? ? ?
  | _ => apply: ct_forall_identity; intro
  end.

Ltac crel_intro T :=
  tryif crel_isnat T then (apply: ct_forall_nat; intros ? ? ?) else
  lazymatch T with
  | ?A -> ?B => tryif crel_isnat B then (apply: cgq_forall_par; intros ? ? ?) else crel_intro_defs T
  | _ => crel_intro_defs T
  end.

Ltac crel :=
  first
  [ assumption
  | crel_hyp; crel
  | lazymatch goal with
    | |- forall _, _ => intro; crel
    | |- CgqSchedRel _ _ _ (ConcreteScheduler.scheduler _ _ _ _ _ _) _ => eapply ConcreteScheduler_scheduler_correspondence; crel
    | |- Lean.eq (cl_opt (Some _)) _ => exact (@Lean.eq_refl _ _)
    | |- Lean.eq (cl_opt (ConcreteScheduler.nth_highest_priority_job _ _ _ _ _ _ _ _ _)) _ => eapply ConcreteScheduler_nth_highest_priority_job_correspondence; crel
    | |- Lean.eq (cl_opt (nth_or_none _ _)) _ => eapply cgq_nth_or_none_rel; crel
    | |- Lean.eq (cl_opt (ConcreteScheduler.scheduler _ _ _ _ _ _ _ _)) _ => eapply ConcreteScheduler_scheduler_correspondence; crel
    | |- Lean.eq (cl_opt (?s ?o ?t)) _ => match goal with H : CgqSchedRel _ _ _ s _ |- _ => eapply H; crel end
    | |- CgqRelRel _ (?r ?t) (?l ?u) => match goal with H : CgqJldpRel _ r l |- _ => eapply H; crel end
    | |- SubNatRel (nat_of_ord ?o) _ => match goal with H : CoOrdRel _ _ o _ |- _ => exact H end
    | |- PropSPropRel (@Logic.eq (option _) _ _) _ => eapply cgq_opt_rel_eq; crel
    | |- ClListRel _ (ConcreteScheduler.sorted_pending_jobs _ _ _ _ _ _ _ _) _ => eapply ConcreteScheduler_sorted_pending_jobs_correspondence; crel
    | |- SubNatRel ?a _ => crel_n a
    | |- CtBoolRel ?b _ => crel_b b
    | |- ClListRel _ ?l _ => crel_l l
    | |- PropSPropRel (@Logic.eq (option _) _ _) _ => eapply cgq_opt_rel_eq; crel
  | |- PropSPropRel ?P _ => crel_p P
    end ]
with crel_n a :=
  lazymatch a with
  | addn _ _ => eapply sub_add_correspondence; crel
  | subn _ _ => first [ eapply ct_sub_rel; crel | fail; crel ]
  | muln _ _ => first [ fail; crel | eapply sub_mul_correspondence; crel ]
  | modn _ _ => fail; crel
  | S _ => fail; crel
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
with crel_eq_defs := first [ eapply ct_eq_rel | eapply cgq_opt_rel_eq; crel ]
with crel_n_defs := first [ eapply cgq_list_size; crel ]
with crel_b_defs := first [ eapply cgq_GJ_backlogged; crel
    | eapply cgq_GJ_pending; crel
    | eapply cgq_GS_scheduled; crel
    | eapply cgq_GS_completed; crel ]
with crel_l_defs := first [ fail ]
with crel_p_defs := first [ eapply cgq_total; crel
    | eapply cgq_PR_JLDP_is_transitive; crel
    | eapply cgq_arrives_in; crel
    | eapply cgq_consistent; crel
    | eapply cgq_is_a_set; crel
    | eapply cgq_GS_jobs_come_from_arrival_sequence; crel
    | eapply cgq_GJ_jobs_execute_after_jitter; crel
    | eapply cgq_GS_sequential_jobs; crel
    | eapply cgq_GS_completed_jobs_dont_execute; crel
    | eapply cgq_PL_work_conserving; crel
    | eapply cgq_PL_respects_JLDP_policy; crel
    | eapply cgq_mem; crel
    | eapply cgq_uniq; crel ].

Ltac crel_spine :=
  repeat lazymatch goal with
  | |- PropSPropRel (forall x : ?T, _) _ =>
      lazymatch type of T with Prop => eapply ct_imp; [ crel | idtac ] | _ => crel_intro T end
  end.

(* ------------------------------------------------------------------ *)
(** * Statements *)

Definition src_scheduler_depends_only_on_prefix (Job : eqType) : Prop :=
  ltac:(type_of_term (@ConcreteScheduler.scheduler_depends_only_on_prefix Job)).
Definition tgt_scheduler_depends_only_on_prefix (Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Implementation_Global_Jitter_Schedule_ConcreteScheduler_scheduler_depends_only_on_prefix Job (ct_decidable_eq Job))).
Theorem ConcreteScheduler_scheduler_depends_only_on_prefix_correspondence (Job : eqType) :
  PropSPropRel (src_scheduler_depends_only_on_prefix Job) (tgt_scheduler_depends_only_on_prefix Job).
Proof. unfold src_scheduler_depends_only_on_prefix, tgt_scheduler_depends_only_on_prefix. crel_spine. crel. Unshelve. all: crel. Qed.

Definition src_scheduler_uses_construction_function (Job : eqType) : Prop :=
  ltac:(type_of_term (@ConcreteScheduler.scheduler_uses_construction_function Job)).
Definition tgt_scheduler_uses_construction_function (Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Implementation_Global_Jitter_Schedule_ConcreteScheduler_scheduler_uses_construction_function Job (ct_decidable_eq Job))).
Theorem ConcreteScheduler_scheduler_uses_construction_function_correspondence (Job : eqType) :
  PropSPropRel (src_scheduler_uses_construction_function Job) (tgt_scheduler_uses_construction_function Job).
Proof. unfold src_scheduler_uses_construction_function, tgt_scheduler_uses_construction_function. crel_spine. crel. Unshelve. all: crel. Qed.

Definition src_scheduler_nth_or_none_mapping (Job : eqType) : Prop :=
  ltac:(type_of_term (@ConcreteScheduler.scheduler_nth_or_none_mapping Job)).
Definition tgt_scheduler_nth_or_none_mapping (Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Implementation_Global_Jitter_Schedule_ConcreteScheduler_scheduler_nth_or_none_mapping Job (ct_decidable_eq Job))).
Theorem ConcreteScheduler_scheduler_nth_or_none_mapping_correspondence (Job : eqType) :
  PropSPropRel (src_scheduler_nth_or_none_mapping Job) (tgt_scheduler_nth_or_none_mapping Job).
Proof. unfold src_scheduler_nth_or_none_mapping, tgt_scheduler_nth_or_none_mapping. crel_spine. crel. Unshelve. all: crel. Qed.

Definition src_scheduler_nth_or_none_backlogged (Job : eqType) : Prop :=
  ltac:(type_of_term (@ConcreteScheduler.scheduler_nth_or_none_backlogged Job)).
Definition tgt_scheduler_nth_or_none_backlogged (Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Implementation_Global_Jitter_Schedule_ConcreteScheduler_scheduler_nth_or_none_backlogged Job (ct_decidable_eq Job))).
Theorem ConcreteScheduler_scheduler_nth_or_none_backlogged_correspondence (Job : eqType) :
  PropSPropRel (src_scheduler_nth_or_none_backlogged Job) (tgt_scheduler_nth_or_none_backlogged Job).
Proof. unfold src_scheduler_nth_or_none_backlogged, tgt_scheduler_nth_or_none_backlogged. crel_spine. crel. Unshelve. all: crel. Qed.

Definition src_scheduler_jobs_come_from_arrival_sequence (Job : eqType) : Prop :=
  ltac:(type_of_term (@ConcreteScheduler.scheduler_jobs_come_from_arrival_sequence Job)).
Definition tgt_scheduler_jobs_come_from_arrival_sequence (Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Implementation_Global_Jitter_Schedule_ConcreteScheduler_scheduler_jobs_come_from_arrival_sequence Job (ct_decidable_eq Job))).
Theorem ConcreteScheduler_scheduler_jobs_come_from_arrival_sequence_correspondence (Job : eqType) :
  PropSPropRel (src_scheduler_jobs_come_from_arrival_sequence Job) (tgt_scheduler_jobs_come_from_arrival_sequence Job).
Proof. unfold src_scheduler_jobs_come_from_arrival_sequence, tgt_scheduler_jobs_come_from_arrival_sequence. crel_spine. crel. Unshelve. all: crel. Qed.

Definition src_scheduler_jobs_execute_after_jitter (Job : eqType) : Prop :=
  ltac:(type_of_term (@ConcreteScheduler.scheduler_jobs_execute_after_jitter Job)).
Definition tgt_scheduler_jobs_execute_after_jitter (Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Implementation_Global_Jitter_Schedule_ConcreteScheduler_scheduler_jobs_execute_after_jitter Job (ct_decidable_eq Job))).
Theorem ConcreteScheduler_scheduler_jobs_execute_after_jitter_correspondence (Job : eqType) :
  PropSPropRel (src_scheduler_jobs_execute_after_jitter Job) (tgt_scheduler_jobs_execute_after_jitter Job).
Proof. unfold src_scheduler_jobs_execute_after_jitter, tgt_scheduler_jobs_execute_after_jitter. crel_spine. crel. Unshelve. all: crel. Qed.

Definition src_scheduler_sequential_jobs (Job : eqType) : Prop :=
  ltac:(type_of_term (@ConcreteScheduler.scheduler_sequential_jobs Job)).
Definition tgt_scheduler_sequential_jobs (Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Implementation_Global_Jitter_Schedule_ConcreteScheduler_scheduler_sequential_jobs Job (ct_decidable_eq Job))).
Theorem ConcreteScheduler_scheduler_sequential_jobs_correspondence (Job : eqType) :
  PropSPropRel (src_scheduler_sequential_jobs Job) (tgt_scheduler_sequential_jobs Job).
Proof. unfold src_scheduler_sequential_jobs, tgt_scheduler_sequential_jobs. crel_spine. crel. Unshelve. all: crel. Qed.

Definition src_scheduler_completed_jobs_dont_execute (Job : eqType) : Prop :=
  ltac:(type_of_term (@ConcreteScheduler.scheduler_completed_jobs_dont_execute Job)).
Definition tgt_scheduler_completed_jobs_dont_execute (Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Implementation_Global_Jitter_Schedule_ConcreteScheduler_scheduler_completed_jobs_dont_execute Job (ct_decidable_eq Job))).
Theorem ConcreteScheduler_scheduler_completed_jobs_dont_execute_correspondence (Job : eqType) :
  PropSPropRel (src_scheduler_completed_jobs_dont_execute Job) (tgt_scheduler_completed_jobs_dont_execute Job).
Proof. unfold src_scheduler_completed_jobs_dont_execute, tgt_scheduler_completed_jobs_dont_execute. crel_spine. crel. Unshelve. all: crel. Qed.

Definition src_scheduler_work_conserving (Job : eqType) : Prop :=
  ltac:(type_of_term (@ConcreteScheduler.scheduler_work_conserving Job)).
Definition tgt_scheduler_work_conserving (Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Implementation_Global_Jitter_Schedule_ConcreteScheduler_scheduler_work_conserving Job (ct_decidable_eq Job))).
Theorem ConcreteScheduler_scheduler_work_conserving_correspondence (Job : eqType) :
  PropSPropRel (src_scheduler_work_conserving Job) (tgt_scheduler_work_conserving Job).
Proof. unfold src_scheduler_work_conserving, tgt_scheduler_work_conserving. crel_spine. crel. Unshelve. all: crel. Qed.

Definition src_scheduler_respects_policy (Job : eqType) : Prop :=
  ltac:(type_of_term (@ConcreteScheduler.scheduler_respects_policy Job)).
Definition tgt_scheduler_respects_policy (Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Implementation_Global_Jitter_Schedule_ConcreteScheduler_scheduler_respects_policy Job (ct_decidable_eq Job))).
Theorem ConcreteScheduler_scheduler_respects_policy_correspondence (Job : eqType) :
  PropSPropRel (src_scheduler_respects_policy Job) (tgt_scheduler_respects_policy Job).
Proof. unfold src_scheduler_respects_policy, tgt_scheduler_respects_policy. crel_spine. crel. Unshelve. all: crel. Qed.
