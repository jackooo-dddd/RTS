From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq fintype bigop path div.
From prosa Require Import classic.model.time classic.model.schedule.global.basic.schedule classic.model.schedule.global.transformation.construction util.seqset classic.util.list classic.model.priority classic.model.arrival.basic.arrival_sequence classic.model.arrival.basic.task classic.model.schedule.apa.affinity classic.model.schedule.apa.platform classic.implementation.apa.schedule.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedClassicImplApaSchedule.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence ClassicImplApaScheduleBase ClassicImplApaScheduleList ClassicImplApaScheduleOrd ClassicImplApaScheduleList1.



Module I := ImportedClassicImplApaSchedule.
Local Open Scope nat_scope.

(** Certificates for [classic/implementation/apa/schedule.v] (ProsaBuddy classic, commit f692cb7).

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

(** Transport along the target equality (definitional UIP), into relevant and SProp-valued families. *)
Definition cs_tr {A : Type} {x y : A} (E : Lean.eq x y) (P : A -> Type) (h : P x) : P y :=
  match E in Lean.eq _ z return P z with Lean.eq_refl => h end.
Definition cs_trs {A : Type} {x y : A} (E : Lean.eq x y) (P : A -> SProp) (h : P x) : P y :=
  match E in Lean.eq _ z return P z with Lean.eq_refl => h end.

(** Options: [cl_opt] is injective and [x == Some j] is [cl_opt x = some j]. *)
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

(* ------------------------------------------------------------------ *)
(** * Half-open sums and concatenations over [nat] (as in the accepted sum / arrival_sequence certificates) *)

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
  rewrite (imported_eq_to_coq_eq _ _ (I.Prosa_Validation_ClassicImplApaScheduleInterface_bigCat_range'
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

(** [undup] against Mathlib's [List.dedup] (step equations exported with their proofs). *)
Lemma cs_undup_rel (T : eqType) : forall s sL, ClListRel cid s sL ->
  ClListRel cid (undup s) (I.List_dedup T (ct_decidable_eq T) sL).
Proof.
  intros s sL Hs. have E := cl_list_logic _ _ _ Hs. subst sL. apply: coq_eq_to_imported_eq. clear Hs.
  elim: s => [|x s IH].
  - exact (Logic.eq_sym (imported_eq_to_coq_eq _ _ (I.Prosa_Validation_ClassicImplApaScheduleInterface_dedup_nil T (ct_decidable_eq T)))).
  - change (Logic.eq (cl_map cid (if x \in s then undup s else x :: undup s))
      (I.List_dedup T (ct_decidable_eq T) (I.List_cons T x (cl_map cid s)))).
    case Hx: (x \in s).
    + rewrite (imported_eq_to_coq_eq _ _ (I.Prosa_Validation_ClassicImplApaScheduleInterface_dedup_cons_mem
                 T (ct_decidable_eq T) x (cl_map cid s)
                 (prop_to_sprop _ _ (cs_mem T x s _ (cl_lean_eq _ _ _ (Logic.eq_refl _))) Hx))).
      exact IH.
    + rewrite (imported_eq_to_coq_eq _ _ (I.Prosa_Validation_ClassicImplApaScheduleInterface_dedup_cons_not_mem
                 T (ct_decidable_eq T) x (cl_map cid s) (cs_notin_target T x s Hx))).
      change (Logic.eq (I.List_cons T x (cl_map cid (undup s))) (I.List_cons T x (I.List_dedup T (ct_decidable_eq T) (cl_map cid s)))).
      by rewrite IH.
Qed.

(* ------------------------------------------------------------------ *)
(** * Schedules, arrival sequences, parameters *)

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

(* ------------------------------------------------------------------ *)
(** * Definitions *)

Section Defs.
Variables (Job : eqType) (nR : nat) (nL : Lean.Nat).
Hypothesis Hn : SubNatRel nR nL.
Notation dJ := (ct_decidable_eq Job).
Variables (sR : Schedule.schedule Job nR)
  (sL : I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_schedule Job dJ nL).
Hypothesis Hs : CsSchedRel Job nR nL sR sL.

Lemma cs_GS_scheduled_on j oR oL (Ho : CoOrdRel nR nL oR oL) tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (Schedule.scheduled_on sR j oR tR)
    (I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_scheduled_on Job dJ nL sL j oL tL).
Proof.
  apply: ct_decide_bool.
  exact (cs_tr (Hs oR oL Ho tR tL Ht) (fun z => PropSPropRel (sR oR tR == Some j) (Lean.eq z (cl_opt (Some j))))
           (cs_opt_eqb_rel Job (sR oR tR) (Some j))).
Qed.

Lemma cs_GS_scheduled j tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (Schedule.scheduled sR j tR)
    (I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_scheduled Job dJ nL sL j tL).
Proof.
  apply: (co_exists_rel nR nL Hn). intros oR oL Ho. exact (cs_GS_scheduled_on j oR oL Ho tR tL Ht).
Qed.

Lemma cs_GS_service_at j tR tL (Ht : SubNatRel tR tL) :
  SubNatRel (Schedule.service_at sR j tR)
    (I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_service_at Job dJ nL sL j tL).
Proof.
  apply: coq_eq_to_imported_eq.
  rewrite (imported_eq_to_coq_eq _ _ (I.Prosa_Validation_ClassicImplApaScheduleInterface_service_at_sum Job dJ nL sL j tL)).
  apply: imported_eq_to_coq_eq.
  rewrite /Schedule.service_at big_mkcond /=.
  apply: (co_sum_rel nR nL Hn). intros oR oL Ho.
  have H := cs_GS_scheduled_on j oR oL Ho tR tL Ht.
  rewrite (ct_bool_rel_logic _ _ H). destruct (Schedule.scheduled_on sR j oR tR).
  - exact (sub_nat_rel_canonical 1).
  - exact (sub_nat_rel_canonical 0).
Qed.

Lemma cs_service_at_fun j : CsFunRel (fun t => Schedule.service_at sR j t)
    (fun t => I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_service_at Job dJ nL sL j t).
Proof. intros kR kL Hk. exact (cs_GS_service_at j kR kL Hk). Qed.

Lemma cs_GS_service j tR tL (Ht : SubNatRel tR tL) :
  SubNatRel (Schedule.service sR j tR)
    (I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_service Job dJ nL sL j tL).
Proof. exact (cs_ico 0 _ tR tL _ _ (sub_nat_rel_canonical 0) Ht (cs_service_at_fun j)). Qed.

Lemma cs_GS_completed cR cL (Hc : CsParRel Job cR cL) j tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (Schedule.completed cR sR j tR)
    (I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_completed Job dJ cL nL sL j tL).
Proof. exact (ct_decide_le _ _ _ _ (Hc j) (cs_GS_service j tR tL Ht)). Qed.

Lemma cs_GS_pending aR aL (Ha : CsParRel Job aR aL) cR cL (Hc : CsParRel Job cR cL) j tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (Schedule.pending aR cR sR j tR)
    (I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_pending Job dJ aL cL nL sL j tL).
Proof.
  exact (ct_bool_and _ _ _ _ (ct_decide_le _ _ _ _ (Ha j) Ht)
           (ct_bool_not _ _ (cs_GS_completed cR cL Hc j tR tL Ht))).
Qed.

Lemma cs_GS_backlogged aR aL (Ha : CsParRel Job aR aL) cR cL (Hc : CsParRel Job cR cL) j tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (Schedule.backlogged aR cR sR j tR)
    (I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_backlogged Job dJ aL cL nL sL j tL).
Proof.
  exact (ct_bool_and _ _ _ _ (cs_GS_pending aR aL Ha cR cL Hc j tR tL Ht)
           (ct_bool_not _ _ (cs_GS_scheduled j tR tL Ht))).
Qed.

Lemma cs_GS_sequential_jobs :
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

Lemma cs_GS_jobs_must_arrive_to_execute aR aL (Ha : CsParRel Job aR aL) :
  PropSPropRel (Schedule.jobs_must_arrive_to_execute aR sR)
    (I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_jobs_must_arrive_to_execute Job dJ aL nL sL).
Proof.
  apply: ct_forall_identity => j. apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (ct_bool_truth _ _ (cs_GS_scheduled j tR tL Ht)).
  exact (ct_bool_truth _ _ (ct_decide_le _ _ _ _ (Ha j) Ht)).
Qed.

Lemma cs_GS_completed_jobs_dont_execute cR cL (Hc : CsParRel Job cR cL) :
  PropSPropRel (Schedule.completed_jobs_dont_execute cR sR)
    (I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_completed_jobs_dont_execute Job dJ cL nL sL).
Proof.
  apply: ct_forall_identity => j. apply: ct_forall_nat => tR tL Ht.
  exact (sub_nat_le_correspondence _ _ _ _ (cs_GS_service j tR tL Ht) (Hc j)).
Qed.

Lemma cs_GS_jobs_come_from_arrival_sequence arrR arrL (Harr : CsArrRel Job arrR arrL) :
  PropSPropRel (Schedule.jobs_come_from_arrival_sequence sR arrR)
    (I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_jobs_come_from_arrival_sequence Job dJ nL sL arrL).
Proof.
  apply: ct_forall_identity => j. apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (ct_bool_truth _ _ (cs_GS_scheduled j tR tL Ht)).
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

Lemma cs_GS_processor nR nL (Hn : SubNatRel nR nL) :
  And (forall o : Schedule.processor nR, CoOrdRel nR nL o (co_ord_to_fin nR nL Hn o))
      (forall o : I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_processor nL,
         CoOrdRel nR nL (co_fin_to_ord nR nL Hn o) o).
Proof. exact (And_intro _ _ (co_ord_canonical nR nL Hn) (co_ord_surjective nR nL Hn)). Qed.

Lemma cs_GS_schedule (Job : eqType) nR nL (Hn : SubNatRel nR nL) :
  And (forall s : Schedule.schedule Job nR, CsSchedRel Job nR nL s (cs_sched_to_target Job nR nL Hn s))
      (forall s : I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_schedule Job (ct_decidable_eq Job) nL,
         CsSchedRel Job nR nL (cs_sched_to_source Job nR nL Hn s) s).
Proof. exact (And_intro _ _ (cs_sched_canonical Job nR nL Hn) (cs_sched_surjective Job nR nL Hn)). Qed.

(* ------------------------------------------------------------------ *)
(** * Statements *)

(** The common prefix [forall num_cpus (sched : schedule Job num_cpus)]. *)
Lemma cs_forall_ncpus_sched (Job : eqType)
    (PR : forall n : nat, Schedule.schedule Job n -> Prop)
    (PL : forall n : Lean.Nat, I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_schedule Job (ct_decidable_eq Job) n -> SProp) :
  (forall nR nL (Hn : SubNatRel nR nL) sR sL, CsSchedRel Job nR nL sR sL -> PropSPropRel (PR nR sR) (PL nL sL)) ->
  PropSPropRel (forall n s, PR n s) (forall n s, PL n s).
Proof.
  intro H. apply: ct_forall_nat => nR nL Hn. exact (cs_forall_sched Job nR nL Hn _ _ (H nR nL Hn)).
Qed.

(** Priority relations (as in the accepted classic priority certificate). *)
Definition CsRelRel (T : Type) (rR : T -> T -> bool) (rL : T -> T -> I.Bool) : SProp :=
  forall a b, CtBoolRel (rR a b) (rL a b).

Lemma cs_rel_canonical (T : Type) (rR : T -> T -> bool) : CsRelRel T rR (fun a b => ct_b2l (rR a b)).
Proof. intros a b. exact (ct_bool_canonical _). Qed.

Lemma cs_rel_surjective (T : Type) (rL : T -> T -> I.Bool) : CsRelRel T (fun a b => ct_l2b (rL a b)) rL.
Proof. intros a b. exact (ct_bool_surjective _). Qed.

Lemma cs_forall_rel (T : Type) (PR : (T -> T -> bool) -> Prop) (PL : (T -> T -> I.Bool) -> SProp) :
  (forall rR rL, CsRelRel T rR rL -> PropSPropRel (PR rR) (PL rL)) -> PropSPropRel (forall r, PR r) (forall r, PL r).
Proof.
  exact (cs_forall_cover _ _ (CsRelRel T) (fun rR a b => ct_b2l (rR a b)) (fun rL a b => ct_l2b (rL a b))
           (cs_rel_canonical T) (cs_rel_surjective T) PR PL).
Qed.

Definition CsJldpRel (T : Type) (rR : nat -> T -> T -> bool) (rL : Lean.Nat -> T -> T -> I.Bool) : SProp :=
  forall tR tL, SubNatRel tR tL -> CsRelRel T (rR tR) (rL tL).

Lemma cs_jldp_canonical (T : Type) (rR : nat -> T -> T -> bool) :
  CsJldpRel T rR (fun tL a b => ct_b2l (rR (sub_nat_to_rocq tL) a b)).
Proof.
  intros tR tL Ht a b. have E := cl_nat_logic _ _ Ht. subst tL. rewrite sub_nat_rocq_roundtrip.
  exact (ct_bool_canonical _).
Qed.

Lemma cs_jldp_surjective (T : Type) (rL : Lean.Nat -> T -> T -> I.Bool) :
  CsJldpRel T (fun tR a b => ct_l2b (rL (sub_nat_to_imported tR) a b)) rL.
Proof. intros tR tL Ht a b. have E := cl_nat_logic _ _ Ht. subst tL. exact (ct_bool_surjective _). Qed.

(* ------------------------------------------------------------------ *)
(** * Arrival sequences *)

Lemma cs_forall_jldp (T : Type) (PR : (nat -> T -> T -> bool) -> Prop) (PL : (Lean.Nat -> T -> T -> I.Bool) -> SProp) :
  (forall rR rL, CsJldpRel T rR rL -> PropSPropRel (PR rR) (PL rL)) -> PropSPropRel (forall r, PR r) (forall r, PL r).
Proof.
  exact (cs_forall_cover _ _ (CsJldpRel T) (fun rR tL a b => ct_b2l (rR (sub_nat_to_rocq tL) a b))
           (fun rL tR a b => ct_l2b (rL (sub_nat_to_imported tR) a b)) (cs_jldp_canonical T) (cs_jldp_surjective T) PR PL).
Qed.

Section PriodefsDefs.
Variables (Task Job : eqType).
Notation dT := (ct_decidable_eq Task).
Notation dJ := (ct_decidable_eq Job).

Lemma cs_PR_JLDP_policy :
  And (forall rR : Priority.JLDP_policy Job, CsJldpRel Job rR (fun tL a b => ct_b2l (rR (sub_nat_to_rocq tL) a b)))
      (forall rL : I.Prosa_Classic_Model_Priority_Priority_JLDP_policy Job dJ,
         CsJldpRel Job (fun tR a b => ct_l2b (rL (sub_nat_to_imported tR) a b)) rL).
Proof. exact (And_intro _ _ (cs_jldp_canonical Job) (cs_jldp_surjective Job)). Qed.

Lemma cs_transitive (T : Type) rR rL (Hr : CsRelRel T rR rL) :
  PropSPropRel (transitive rR) (I.Prosa_Classic_Model_Priority_Priority_transitiveB T rL).
Proof.
  apply: ct_forall_identity => y. apply: ct_forall_identity => x. apply: ct_forall_identity => z.
  apply: ct_imp; first exact (ct_bool_truth _ _ (Hr x y)).
  apply: ct_imp; first exact (ct_bool_truth _ _ (Hr y z)).
  exact (ct_bool_truth _ _ (Hr x z)).
Qed.

Lemma cs_PR_JLDP_is_transitive rR rL (Hr : CsJldpRel Job rR rL) :
  PropSPropRel (Priority.JLDP_is_transitive rR) (I.Prosa_Classic_Model_Priority_Priority_JLDP_is_transitive Job dJ rL).
Proof. apply: ct_forall_nat => tR tL Ht. exact (cs_transitive Job _ _ (Hr tR tL Ht)). Qed.

End PriodefsDefs.

(* ------------------------------------------------------------------ *)
(** * Options and transports *)

Lemma cs_opt_rel_eq (A : Type) (o1 o2 : option A) l1 l2 :
  Lean.eq (cl_opt o1) l1 -> Lean.eq (cl_opt o2) l2 -> PropSPropRel (Logic.eq o1 o2) (Lean.eq l1 l2).
Proof.
  intros H1 H2. destruct H1. destruct H2. apply prop_sprop_rel_intro.
  - intro E. rewrite E. exact (@Lean.eq_refl _ _).
  - intro E. apply strictly_inhabits. exact (cs_opt_inj A o1 o2 (imported_eq_to_coq_eq _ _ E)).
Qed.

Definition cs_lsym {A : Type} {x y : A} (E : Lean.eq x y) : Lean.eq y x :=
  match E in Lean.eq _ z return Lean.eq z x with Lean.eq_refl => @Lean.eq_refl _ _ end.

Lemma cs_src_transport {A : Type} (P : A -> SProp) (x y : A) : Logic.eq x y -> P x -> P y.
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
Hypothesis Hbuild : forall sR sL, CsSchedRel Job nR nL sR sL -> CsSchedRel Job nR nL (buildR sR) (buildL sL).
Variables (baseR : Schedule.schedule Job nR) (baseL : LSched).
Hypothesis Hbase : CsSchedRel Job nR nL baseR baseL.

Lemma cs_GC_update_schedule prevR prevL (Hprev : CsSchedRel Job nR nL prevR prevL) mR mL (Hm : SubNatRel mR mL) :
  CsSchedRel Job nR nL (@ScheduleConstruction.update_schedule Job nR buildR prevR mR) (I.Prosa_Classic_Model_Schedule_Global_Transformation_Construction_ScheduleConstruction_update_schedule Job dJ nL buildL prevL mL).
Proof.
  intros oR oL Ho tR tL Ht. unfold ScheduleConstruction.update_schedule, I.Prosa_Classic_Model_Schedule_Global_Transformation_Construction_ScheduleConstruction_update_schedule. cbv beta.
  apply: coq_eq_to_imported_eq.
  rewrite (ct_bool_rel_logic _ _ (ct_decide_eq_nat _ _ _ _ Ht Hm)).
  case: (tR == mR).
  - exact (imported_eq_to_coq_eq _ _ (Hbuild prevR prevL Hprev oR oL Ho tR tL Ht)).
  - exact (imported_eq_to_coq_eq _ _ (Hprev oR oL Ho tR tL Ht)).
Qed.

Lemma cs_prefix_canonical (kR : nat) :
  CsSchedRel Job nR nL (@ScheduleConstruction.schedule_prefix Job nR buildR baseR kR) (I.Prosa_Classic_Model_Schedule_Global_Transformation_Construction_ScheduleConstruction_schedule_prefix Job dJ nL buildL baseL (sub_nat_to_imported kR)).
Proof.
  induction kR as [|k IH].
  - refine (cs_trs (cs_lsym (I.Prosa_Validation_ClassicImplApaScheduleInterface_production_schedule_prefix_zero Job dJ nL buildL baseL))
              (fun z => CsSchedRel Job nR nL _ z) _).
    exact (cs_GC_update_schedule baseR baseL Hbase 0 _ (sub_nat_rel_canonical 0)).
  - assert (Hk1 : SubNatRel k.+1 (I.HAdd_hAdd_inst7 Lean.Nat Lean.Nat Lean.Nat (I.instHAdd_inst1 Lean.Nat I.instAddNat)
                                 (sub_nat_to_imported k) (I.OfNat_ofNat_inst1 Lean.Nat 1 (I.instOfNatNat 1)))).
    { exact (cs_src_transport (fun x => SubNatRel x _) _ _ (addn1 k)
               (sub_add_correspondence _ _ _ _ (sub_nat_rel_canonical k) (sub_nat_rel_canonical 1))). }
    refine (cs_trs Hk1 (fun z => CsSchedRel Job nR nL (@ScheduleConstruction.schedule_prefix Job nR buildR baseR k.+1) (I.Prosa_Classic_Model_Schedule_Global_Transformation_Construction_ScheduleConstruction_schedule_prefix Job dJ nL buildL baseL z)) _).
    refine (cs_trs (cs_lsym (I.Prosa_Validation_ClassicImplApaScheduleInterface_production_schedule_prefix_succ Job dJ nL buildL baseL (sub_nat_to_imported k)))
              (fun z => CsSchedRel Job nR nL _ z) _).
    exact (cs_GC_update_schedule _ _ IH _ _ Hk1).
Qed.

Lemma cs_GC_schedule_prefix kR kL (Hk : SubNatRel kR kL) :
  CsSchedRel Job nR nL (@ScheduleConstruction.schedule_prefix Job nR buildR baseR kR) (I.Prosa_Classic_Model_Schedule_Global_Transformation_Construction_ScheduleConstruction_schedule_prefix Job dJ nL buildL baseL kL).
Proof. exact (cs_trs Hk (fun z => CsSchedRel Job nR nL _ (I.Prosa_Classic_Model_Schedule_Global_Transformation_Construction_ScheduleConstruction_schedule_prefix Job dJ nL buildL baseL z)) (cs_prefix_canonical kR)). Qed.

Lemma cs_GC_build_schedule_from_prefixes :
  CsSchedRel Job nR nL (@ScheduleConstruction.build_schedule_from_prefixes Job nR buildR baseR) (I.Prosa_Classic_Model_Schedule_Global_Transformation_Construction_ScheduleConstruction_build_schedule_from_prefixes Job dJ nL buildL baseL).
Proof. intros oR oL Ho tR tL Ht. exact (cs_GC_schedule_prefix tR tL Ht oR oL Ho tR tL Ht). Qed.

Notation SCH := cs_GC_build_schedule_from_prefixes.

(** ** Statements *)

End GCConstruction.

(* ------------------------------------------------------------------ *)
(** * MathComp [sort] and the restated Lean merge sort

    The Lean file restates MathComp's [merge], [merge_sort_push], [merge_sort_pop], [merge_sort_rec] and [sort]
    equation by equation ([mc_*], structurally recursive).  Each Lean defining equation is a kernel-checked [rfl]
    fixture theorem ([xms_*]); the source equations hold by computation.  The sorts are related for every relation
    [leT] (pointwise related Boolean relations), by induction on the arguments. *)

Local Notation EQ H := (imported_eq_to_coq_eq _ _ H).

Lemma cs_ite_any (b : bool) bL (Hb : CtBoolRel b bL) (A : Type) (x y : A) :
  Logic.eq (I.ite A (Lean.eq bL I.Bool_true) (I.instDecidableEqBool bL I.Bool_true) x y) (if b then x else y).
Proof. rewrite (ct_bool_rel_logic _ _ Hb). clear Hb. by case: b. Qed.

Section McSort.
Variables (T : Type) (leR : T -> T -> bool) (leL : T -> T -> I.Bool).
Hypothesis Hle : forall a b, CtBoolRel (leR a b) (leL a b).
Local Notation M := (cl_map (fun z : T => z)).
Local Notation MM := (cl_map (cl_map (fun z : T => z))).

Lemma cs_mc_merge : forall s1 s2, Logic.eq (I.Prosa_Classic_Implementation_Apa_Schedule_ConcreteScheduler_mc_merge T leL (M s1) (M s2)) (M (merge leR s1 s2)).
Proof.
  elim => [|x1 s1 IH] s2.
  - rewrite (EQ (I.Prosa_Validation_ClassicImplApaScheduleInterface_xms_merge_nil T leL (M s2))). by case: s2.
  - elim: s2 => [|x2 s2 IH2].
    + exact (EQ (I.Prosa_Validation_ClassicImplApaScheduleInterface_xms_merge_cons_nil T leL x1 (M s1))).
    + rewrite (EQ (I.Prosa_Validation_ClassicImplApaScheduleInterface_xms_merge_cons_cons T leL x1 (M s1) x2 (M s2))).
      rewrite (cs_ite_any _ _ (Hle x1 x2)).
      have -> : Logic.eq (merge leR (x1 :: s1) (x2 :: s2))
                  (if leR x1 x2 then x1 :: merge leR s1 (x2 :: s2) else x2 :: merge leR (x1 :: s1) s2) by [].
      case: (leR x1 x2).
      * change (Logic.eq (I.List_cons T x1 (I.Prosa_Classic_Implementation_Apa_Schedule_ConcreteScheduler_mc_merge T leL (M s1) (M (x2 :: s2)))) (M (x1 :: merge leR s1 (x2 :: s2)))).
        by rewrite IH.
      * change (Logic.eq (I.List_cons T x2 (I.Prosa_Classic_Implementation_Apa_Schedule_ConcreteScheduler_mc_merge T leL (M (x1 :: s1)) (M s2))) (M (x2 :: merge leR (x1 :: s1) s2))).
        by rewrite IH2.
Qed.

Lemma cs_mc_push : forall ss s1, Logic.eq (I.Prosa_Classic_Implementation_Apa_Schedule_ConcreteScheduler_mc_merge_sort_push T leL (M s1) (MM ss)) (MM (merge_sort_push leR s1 ss)).
Proof.
  elim => [|[|x s2] ss IH] s1.
  - exact (EQ (I.Prosa_Validation_ClassicImplApaScheduleInterface_xms_push_nil T leL (M s1))).
  - exact (EQ (I.Prosa_Validation_ClassicImplApaScheduleInterface_xms_push_nil_cons T leL (M s1) (MM ss))).
  - rewrite (EQ (I.Prosa_Validation_ClassicImplApaScheduleInterface_xms_push_cons_cons T leL (M s1) x (M s2) (MM ss))).
    change (Logic.eq (I.List_cons (I.List T) (I.List_nil T)
                        (I.Prosa_Classic_Implementation_Apa_Schedule_ConcreteScheduler_mc_merge_sort_push T leL (I.Prosa_Classic_Implementation_Apa_Schedule_ConcreteScheduler_mc_merge T leL (M (x :: s2)) (M s1)) (MM ss)))
                     (MM ([::] :: merge_sort_push leR (merge leR (x :: s2) s1) ss))).
    by rewrite cs_mc_merge IH.
Qed.

Lemma cs_mc_pop : forall ss s1, Logic.eq (I.Prosa_Classic_Implementation_Apa_Schedule_ConcreteScheduler_mc_merge_sort_pop T leL (M s1) (MM ss)) (M (merge_sort_pop leR s1 ss)).
Proof.
  elim => [|s2 ss IH] s1.
  - exact (EQ (I.Prosa_Validation_ClassicImplApaScheduleInterface_xms_pop_nil T leL (M s1))).
  - rewrite (EQ (I.Prosa_Validation_ClassicImplApaScheduleInterface_xms_pop_cons T leL (M s1) (M s2) (MM ss))) cs_mc_merge. exact (IH _).
Qed.

Lemma cs_mc_rec : forall n s, size s <= n -> forall ss,
  Logic.eq (I.Prosa_Classic_Implementation_Apa_Schedule_ConcreteScheduler_mc_merge_sort_rec T leL (MM ss) (M s)) (M (merge_sort_rec leR ss s)).
Proof.
  elim => [|n IH] [|x1 [|x2 s]] Hs ss //.
  - exact (Logic.eq_trans (EQ (I.Prosa_Validation_ClassicImplApaScheduleInterface_xms_rec_nil T leL (MM ss))) (cs_mc_pop ss [::])).
  - exact (Logic.eq_trans (EQ (I.Prosa_Validation_ClassicImplApaScheduleInterface_xms_rec_nil T leL (MM ss))) (cs_mc_pop ss [::])).
  - exact (Logic.eq_trans (EQ (I.Prosa_Validation_ClassicImplApaScheduleInterface_xms_rec_one T leL (MM ss) x1)) (cs_mc_pop ss [:: x1])).
  - rewrite (EQ (I.Prosa_Validation_ClassicImplApaScheduleInterface_xms_rec_two T leL (MM ss) x1 x2 (M s))) (cs_ite_any _ _ (Hle x1 x2)).
    have Hs' : size s <= n by move: Hs => /=; rewrite !ltnS => /ltnW.
    have -> : Logic.eq (merge_sort_rec leR ss [:: x1, x2 & s])
                (merge_sort_rec leR (merge_sort_push leR (if leR x1 x2 then [:: x1; x2] else [:: x2; x1]) ss) s) by [].
    case: (leR x1 x2).
    + change (Logic.eq (I.Prosa_Classic_Implementation_Apa_Schedule_ConcreteScheduler_mc_merge_sort_rec T leL (I.Prosa_Classic_Implementation_Apa_Schedule_ConcreteScheduler_mc_merge_sort_push T leL (M [:: x1; x2]) (MM ss)) (M s))
                       (M (merge_sort_rec leR (merge_sort_push leR [:: x1; x2] ss) s))).
      by rewrite cs_mc_push IH.
    + change (Logic.eq (I.Prosa_Classic_Implementation_Apa_Schedule_ConcreteScheduler_mc_merge_sort_rec T leL (I.Prosa_Classic_Implementation_Apa_Schedule_ConcreteScheduler_mc_merge_sort_push T leL (M [:: x2; x1]) (MM ss)) (M s))
                       (M (merge_sort_rec leR (merge_sort_push leR [:: x2; x1] ss) s))).
      by rewrite cs_mc_push IH.
Qed.

Lemma cs_mc_sort s : Logic.eq (I.Prosa_Classic_Implementation_Apa_Schedule_ConcreteScheduler_mc_sort T leL (M s)) (M (sort leR s)).
Proof.
  rewrite (EQ (I.Prosa_Validation_ClassicImplApaScheduleInterface_xms_sort T leL (M s))).
  exact (cs_mc_rec (size s) s (leqnn _) [::]).
Qed.

Lemma cs_sort_rel s sL (Hs : ClListRel (fun z : T => z) s sL) :
  ClListRel (fun z : T => z) (sort leR s) (I.Prosa_Classic_Implementation_Apa_Schedule_ConcreteScheduler_mc_sort T leL sL).
Proof.
  apply: coq_eq_to_imported_eq. rewrite (cl_list_logic _ _ _ Hs). exact (Logic.eq_sym (cs_mc_sort s)).
Qed.

End McSort.

(* ------------------------------------------------------------------ *)
(** * Affinities (as in the accepted classic affinity certificate) *)

Section Aff.
Variables (nR : nat) (nL : Lean.Nat).
Hypothesis Hn : SubNatRel nR nL.
Notation c := (co_ord_to_fin nR nL Hn).
Notation d := (co_fin_to_ord nR nL Hn).
Notation LAff := (I.Prosa_Classic_Model_Schedule_Apa_Affinity_Affinity_affinity nL).

Lemma caf_cd (y : Fin nL) : Logic.eq (c (d y)) y.
Proof. exact (co_fin_rel_eq _ _ _ _ _ (co_ord_canonical nR nL Hn (d y)) (co_ord_surjective nR nL Hn y)). Qed.

Lemma caf_dc (x : 'I_nR) : Logic.eq (d (c x)) x.
Proof. exact (co_ord_eq _ _ _ _ _ (co_ord_surjective nR nL Hn (c x)) (co_ord_canonical nR nL Hn x)). Qed.

Lemma caf_c_rel (x : 'I_nR) (y : Fin nL) : CoOrdRel nR nL x y -> Logic.eq (c x) y.
Proof. intro H. exact (co_fin_rel_eq _ _ _ _ _ (co_ord_canonical nR nL Hn x) H). Qed.

(** Affinities are related through their underlying sequences, elementwise by the ordinal conversion
    (Lean lists of [Fin n] at the universe instance [List_inst1], [ClassicAffinityList1]). *)
Notation LVal := (I.Prosa_Util_Seqset_set_val_inst1 (Fin nL) (I.instDecidableEqFin nL)).

Definition CafRel (aR : Affinity.affinity nR) (aL : LAff) : SProp :=
  ClListRel1 c (@prosa.util.seqset._set_seq _ aR) (LVal aL).

Definition caf_to_target (aR : Affinity.affinity nR) : LAff :=
  I.Prosa_Util_Seqset_set_mk_inst1 (Fin nL) (I.instDecidableEqFin nL) (cl1_map c (@prosa.util.seqset._set_seq _ aR))
    (prop_to_sprop _ _ (cl1_uniq_rel _ _ c d caf_dc caf_cd _) (@prosa.util.seqset.set_uniq _ aR)).

Definition caf_to_source (aL : LAff) : Affinity.affinity nR :=
  @prosa.util.seqset.Build_set _ (cl1_unmap d (LVal aL))
    (interpret_strict _ (cl1_uniq_backward _ _ c d caf_cd _
                           (@I.nodup2 (Fin nL) (I.instDecidableEqFin nL) aL))).

Lemma caf_canonical aR : CafRel aR (caf_to_target aR).
Proof. exact (@Lean.eq_refl _ _). Qed.

Lemma caf_surjective aL : CafRel (caf_to_source aL) aL.
Proof. apply: coq_eq_to_imported_eq. exact (cl1_map_unmap c d caf_cd _). Qed.

Lemma caf_forall (PR : Affinity.affinity nR -> Prop) (PL : LAff -> SProp) :
  (forall aR aL, CafRel aR aL -> PropSPropRel (PR aR) (PL aL)) -> PropSPropRel (forall a, PR a) (forall a, PL a).
Proof. exact (cs_forall_cover _ _ CafRel caf_to_target caf_to_source caf_canonical caf_surjective PR PL). Qed.

Lemma caf_mem aR aL (Ha : CafRel aR aL) oR oL (Ho : CoOrdRel nR nL oR oL) :
  PropSPropRel (oR \in aR)
    (I.Membership_mem_inst3 (Fin nL) LAff (I.Prosa_Util_Seqset_instMembershipSet_inst1 (Fin nL) (I.instDecidableEqFin nL)) aL oL).
Proof.
  have E := caf_c_rel _ _ Ho. subst oL.
  exact (cl1_mem_rel_list _ _ c d caf_dc oR _ _ Ha).
Qed.

End Aff.

Section TaskAff.
Variables (Task : eqType) (nR : nat) (nL : Lean.Nat).
Hypothesis Hn : SubNatRel nR nL.
Notation LTAff := (I.Prosa_Classic_Model_Schedule_Apa_Affinity_Affinity_task_affinity Task (ct_decidable_eq Task) nL).

Definition CtafRel (aR : Affinity.task_affinity Task nR) (aL : LTAff) : SProp :=
  forall tsk, CafRel nR nL Hn (aR tsk) (aL tsk).

Lemma cai_forall_taff (PR : Affinity.task_affinity Task nR -> Prop) (PL : LTAff -> SProp) :
  (forall aR aL, CtafRel aR aL -> PropSPropRel (PR aR) (PL aL)) -> PropSPropRel (forall a, PR a) (forall a, PL a).
Proof.
  exact (cs_forall_cover _ _ CtafRel (fun a tsk => caf_to_target nR nL Hn (a tsk)) (fun a tsk => caf_to_source nR nL Hn (a tsk))
           (fun a tsk => caf_canonical nR nL Hn (a tsk)) (fun a tsk => caf_surjective nR nL Hn (a tsk)) PR PL).
Qed.

Lemma cai_can_execute_on aR aL (Ha : CtafRel aR aL) tsk oR oL (Ho : CoOrdRel nR nL oR oL) :
  CtBoolRel (Affinity.can_execute_on aR tsk oR)
    (I.Prosa_Classic_Model_Schedule_Apa_Affinity_Affinity_can_execute_on Task (ct_decidable_eq Task) nL aL tsk oL).
Proof. exact (ct_decide_bool _ _ _ (caf_mem nR nL Hn _ _ (Ha tsk) oR oL Ho)). Qed.

End TaskAff.

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

(* ------------------------------------------------------------------ *)
(** * Processor mappings: lists of (processor, optional job) pairs

    A source mapping [seq ('I_nR * option Job)] is related to the Lean [List (Fin nL × Option Job)] elementwise by the
    pair conversion [cas_pp] (ordinal conversion on the processor, the option map on the job); the conversion is
    injective with a left inverse.  The list operations of the schedule construction ([replace_first],
    [set_pair_2nd], [foldl], [zip], [nseq], [pairs_to_function]) are related through it. *)

Section ApaPairs.
Variables (nR : nat) (nL : Lean.Nat).
Hypothesis Hn : SubNatRel nR nL.
Variable Job : eqType.
Notation c := (co_ord_to_fin nR nL Hn).
Notation d := (co_fin_to_ord nR nL Hn).
Notation PP := (I.Prod_inst1 (I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_processor nL) (I.Option Job)).

Definition cas_pp (p : 'I_nR * option Job) : PP := I.Prod_mk_inst1 (I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_processor nL) (I.Option Job) (c p.1) (cl_opt p.2).

Definition cas_unopt (o : I.Option Job) : option Job := match o with I.Option_some x => Some x | I.Option_none => None end.

Definition cas_unpp (q : PP) : 'I_nR * option Job := (d (I.Prod_fst_inst1 (I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_processor nL) (I.Option Job) q), cas_unopt (I.Prod_snd_inst1 (I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_processor nL) (I.Option Job) q)).

Lemma cas_dc (x : 'I_nR) : Logic.eq (d (c x)) x.
Proof. exact (co_ord_eq _ _ _ _ _ (co_ord_surjective nR nL Hn (c x)) (co_ord_canonical nR nL Hn x)). Qed.

Lemma cas_pp_left (p : 'I_nR * option Job) : Logic.eq (cas_unpp (cas_pp p)) p.
Proof. destruct p as [o [j|]]; rewrite /cas_unpp /cas_pp /= cas_dc; reflexivity. Qed.

Lemma cas_pp_inj p q : Logic.eq (cas_pp p) (cas_pp q) -> Logic.eq p q.
Proof. intro E. by rewrite -(cas_pp_left p) -(cas_pp_left q) E. Qed.

(** [replace_first] with a converted element type. *)
Lemma cas_replace_first (PR : 'I_nR * option Job -> bool) (PL : PP -> I.Bool) (HP : forall x, CtBoolRel (PR x) (PL (cas_pp x)))
    (fR : 'I_nR * option Job -> 'I_nR * option Job) (fL : PP -> PP) (Hf : forall x, Logic.eq (cas_pp (fR x)) (fL (cas_pp x))) :
  forall s, Logic.eq (cl_map cas_pp (replace_first PR fR s)) (I.Prosa_Classic_Util_List_replace_first PP PL fL (cl_map cas_pp s)).
Proof.
  elim => [|x s IH] //=.
  have -> : Logic.eq (I.Prosa_Classic_Util_List_replace_first PP PL fL (I.List_cons PP (cas_pp x) (cl_map cas_pp s)))
      (match PL (cas_pp x) with
       | I.Bool_true => I.List_cons PP (fL (cas_pp x)) (cl_map cas_pp s)
       | I.Bool_false => I.List_cons PP (cas_pp x) (I.Prosa_Classic_Util_List_replace_first PP PL fL (cl_map cas_pp s)) end).
  { cbn. destruct (PL (cas_pp x)); reflexivity. }
  rewrite (ct_bool_rel_logic _ _ (HP x)). case: (PR x) => /=; first by rewrite Hf. by rewrite IH.
Qed.

(** [foldl] of a mapping update over a job sequence. *)
Lemma cas_foldl (fR : seq ('I_nR * option Job) -> Job -> seq ('I_nR * option Job)) (fL : I.List PP -> Job -> I.List PP)
    (Hf : forall m j, Logic.eq (cl_map cas_pp (fR m j)) (fL (cl_map cas_pp m) j)) :
  forall (l : seq Job) m, Logic.eq (cl_map cas_pp (foldl fR m l)) (I.List_foldl (I.List PP) Job fL (cl_map cas_pp m) (cl_map cid l)).
Proof. elim => [|x l IH] m //=. by rewrite IH Hf. Qed.

(** The index of a converted key. *)
Lemma cas_dec_rel (y x : 'I_nR) :
  CtBoolRel (y == x) (I.Decidable_decide (Lean.eq (c y) (c x)) (I.instDecidableEqFin nL (c y) (c x))).
Proof.
  apply: ct_decide_bool.
  have E := co_ord_eq_rel nR nL y x (c y) (c x) (co_ord_canonical nR nL Hn y) (co_ord_canonical nR nL Hn x).
  apply prop_sprop_rel_intro.
  - move=> /eqP H. exact (prop_to_sprop _ _ E H).
  - intro H. apply strictly_inhabits. apply/eqP. exact (sprop_to_prop _ _ E H).
Qed.

Lemma cas_findIdx_go (x : 'I_nR) :
  forall (s : seq 'I_nR) n,
  Logic.eq (I.List_findIdx_go_inst1 (I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_processor nL) (fun y => I.BEq_beq_inst1 (I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_processor nL) (I.instBEqOfDecidableEq_inst1 (I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_processor nL) (I.instDecidableEqFin nL)) y (c x))
              (cl1_map c s) (sub_nat_to_imported n))
           (sub_nat_to_imported (n + index x s)).
Proof.
  elim => [|y s IH] n.
  - by rewrite addn0.
  - have -> : Logic.eq (I.List_findIdx_go_inst1 (I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_processor nL) (fun y => I.BEq_beq_inst1 (I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_processor nL) (I.instBEqOfDecidableEq_inst1 (I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_processor nL) (I.instDecidableEqFin nL)) y (c x))
                 (cl1_map c (y :: s)) (sub_nat_to_imported n))
       (match I.Decidable_decide (Lean.eq (c y) (c x)) (I.instDecidableEqFin nL (c y) (c x)) with
        | I.Bool_true => sub_nat_to_imported n
        | I.Bool_false => I.List_findIdx_go_inst1 (I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_processor nL) (fun y => I.BEq_beq_inst1 (I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_processor nL) (I.instBEqOfDecidableEq_inst1 (I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_processor nL) (I.instDecidableEqFin nL)) y (c x))
                            (cl1_map c s) (sub_nat_to_imported n.+1) end).
    { cbn. destruct (I.instDecidableEqFin nL (c y) (c x)); reflexivity. }
    rewrite (ct_bool_rel_logic _ _ (cas_dec_rel y x)) /= eq_sym. case: (x == y) => /=.
    + by rewrite addn0.
    + rewrite (IH n.+1). by rewrite addSnnS.
Qed.

Lemma cas_index (x : 'I_nR) s :
  SubNatRel (index x s) (I.List_idxOf_inst1 (I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_processor nL) (I.instBEqOfDecidableEq_inst1 (I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_processor nL) (I.instDecidableEqFin nL)) (c x) (cl1_map c s)).
Proof. apply: cl_lean_eq. exact (Logic.eq_sym (cas_findIdx_go x s 0)). Qed.

End ApaPairs.

(* ------------------------------------------------------------------ *)
(** * Mappings: memberships, processors, sortedness and option covers *)

Section ApaMap.
Variables (nR : nat) (nL : Lean.Nat).
Hypothesis Hn : SubNatRel nR nL.
Variable Job : eqType.
Notation pp := (cas_pp nR nL Hn Job).
Notation PP := (I.Prod_inst1 (I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_processor nL) (I.Option Job)).

Lemma cas_unpp_pp (q : PP) : Logic.eq (pp (cas_unpp nR nL Hn Job q)) q.
Proof.
  destruct q as [o x]. rewrite /cas_pp /cas_unpp /=.
  rewrite (co_fin_rel_eq _ _ _ _ _ (co_ord_canonical nR nL Hn (co_fin_to_ord nR nL Hn o)) (co_ord_surjective nR nL Hn o)).
  by case: x.
Qed.

Lemma cas_pair_mem m mL (Hm : ClListRel pp m mL) o oL (Ho : CoOrdRel nR nL o oL) (x : option Job) :
  PropSPropRel ((o, x) \in m)
    (I.Membership_mem PP (I.List PP) (I.List_instMembership PP) mL (I.Prod_mk_inst1 (I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_processor nL) (I.Option Job) oL (cl_opt x))).
Proof.
  have E := co_fin_rel_eq _ _ _ _ _ (co_ord_canonical nR nL Hn o) Ho. destruct E.
  exact (cl_mem_rel_list _ _ pp (cas_unpp nR nL Hn Job) (cas_pp_left nR nL Hn Job) (o, x) m mL Hm).
Qed.

Lemma cas_map_fst : forall m : seq ('I_nR * option Job),
  Logic.eq (I.List_map_inst2 PP (I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_processor nL) (I.Prod_fst_inst1 (I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_processor nL) (I.Option Job)) (cl_map pp m)) (cl1_map (co_ord_to_fin nR nL Hn) (unzip1 m)).
Proof.
  elim => [|x m IH]; first reflexivity.
  exact (f_equal (I.List_cons_inst1 (I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_processor nL) (co_ord_to_fin nR nL Hn x.1)) IH).
Qed.

Lemma cas_uniq_unzip1 m mL (Hm : ClListRel pp m mL) :
  PropSPropRel (uniq (unzip1 m))
    (I.List_Nodup_inst1 (I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_processor nL) (I.List_map_inst2 PP (I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_processor nL) (I.Prod_fst_inst1 (I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_processor nL) (I.Option Job)) mL)).
Proof.
  have E := cl_list_logic _ _ _ Hm. subst mL.
  refine (match Logic.eq_sym (cas_map_fst m) in Logic.eq _ z
            return PropSPropRel (uniq (unzip1 m)) (I.List_Nodup_inst1 (I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_processor nL) z) with Logic.eq_refl => _ end).
  exact (cl1_uniq_rel _ _ (co_ord_to_fin nR nL Hn) (co_fin_to_ord nR nL Hn) (cas_dc nR nL Hn)
           (fun y => co_fin_rel_eq _ _ _ _ _ (co_ord_canonical nR nL Hn (co_fin_to_ord nR nL Hn y)) (co_ord_surjective nR nL Hn y)) _).
Qed.

Lemma cas_exists_opt (PR : option Job -> Prop) (PL : I.Option Job -> SProp) :
  (forall xR, PropSPropRel (PR xR) (PL (cl_opt xR))) -> PropSPropRel (exists x, PR x) (I.Exists (I.Option Job) PL).
Proof.
  intro H. apply prop_sprop_rel_intro.
  - intros [x Hx]. exact (I.Exists_intro _ _ (cl_opt x) (prop_to_sprop _ _ (H x) Hx)).
  - intros [y Hy]. apply strictly_inhabits. exists (cl_unopt y).
    apply (sprop_to_prop _ _ (H (cl_unopt y))). rewrite cl_opt_unopt. exact Hy.
Qed.
(** [enum 'I_n] against [List.finRange n], through the values of their elements. *)
Lemma cas_map_val : forall s : seq 'I_nR,
  Logic.eq (I.List_map_inst3 (Fin nL) Lean.Nat (I.Fin_val nL) (cl1_map (co_ord_to_fin nR nL Hn) s)) (co_natl (map (@nat_of_ord nR) s)).
Proof.
  elim => [|x s IH]; first reflexivity.
  have Ex : Logic.eq (I.Fin_val nL (co_ord_to_fin nR nL Hn x)) (sub_nat_to_imported (nat_of_ord x)) :=
    co_nat_logic _ _ (co_ord_canonical nR nL Hn x).
  exact (f_equal2 (I.List_cons_inst1 Lean.Nat) Ex IH).
Qed.

Lemma cas_val_inj : forall L1 L2 : I.List_inst1 (Fin nL),
  Logic.eq (I.List_map_inst3 (Fin nL) Lean.Nat (I.Fin_val nL) L1) (I.List_map_inst3 (Fin nL) Lean.Nat (I.Fin_val nL) L2) -> Logic.eq L1 L2.
Proof.
  elim => [|a L1 IH] [|b L2] //= E; try discriminate E.
  injection E => E2 E1. rewrite (co_fin_eq nL a b E1) (IH L2 E2). reflexivity.
Qed.

Lemma cas_enum : Logic.eq (cl1_map (co_ord_to_fin nR nL Hn) (enum 'I_nR)) (I.List_finRange nL).
Proof.
  apply: cas_val_inj. rewrite cas_map_val val_enum_ord.
  have E := co_nat_logic _ _ Hn. destruct (Logic.eq_sym E).
  refine (Logic.eq_trans (Logic.eq_sym (co_iota_range nR 0)) _).
  exact (Logic.eq_sym (imported_eq_to_coq_eq _ _ (I.Prosa_Validation_ClassicImplApaScheduleInterface_finRange_map_val (sub_nat_to_imported nR)))).
Qed.

Lemma cas_zip : forall (s1 : seq 'I_nR) (s2 : seq (option Job)),
  Logic.eq (cl_map pp (zip s1 s2)) (I.List_zip_inst1 (I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_processor nL) (I.Option Job) (cl1_map (co_ord_to_fin nR nL Hn) s1) (cl_map cl_opt s2)).
Proof.
  elim => [|x s IH] [|y t]; try reflexivity.
  exact (f_equal (I.List_cons PP (pp (x, y))) (IH t)).
Qed.

Lemma cas_empty :
  Logic.eq (cl_map pp (zip (enum 'I_nR) (nseq nR None)))
    (I.List_zip_inst1 (I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_processor nL) (I.Option Job) (I.List_finRange nL) (I.List_replicate (I.Option Job) nL (I.Option_none Job))).
Proof.
  rewrite cas_zip cas_enum (cl_nseq cl_opt None nR).
  have E := co_nat_logic _ _ Hn. destruct (Logic.eq_sym E). reflexivity.
Qed.

(** [pairs_to_function] on a converted mapping. *)
Lemma cas_map_snd : forall m : seq ('I_nR * option Job),
  Logic.eq (I.List_map PP (I.Option Job) (I.Prod_snd_inst1 (I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_processor nL) (I.Option Job)) (cl_map pp m)) (cl_map cl_opt (unzip2 m)).
Proof.
  elim => [|x m IH]; first reflexivity.
  exact (f_equal (I.List_cons (I.Option Job) (cl_opt x.2)) IH).
Qed.

Lemma cas_p2f (m : seq ('I_nR * option Job)) (o : 'I_nR) :
  Logic.eq (cl_opt (pairs_to_function None m o))
    (I.Prosa_Classic_Util_List_pairs_to_function_inst1 (I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_processor nL) (I.instDecidableEqFin nL) (I.Option Job) (I.Option_none Job)
       (cl_map pp m) (co_ord_to_fin nR nL Hn o)).
Proof.
  rewrite /pairs_to_function. unfold I.Prosa_Classic_Util_List_pairs_to_function_inst1.
  rewrite cas_map_fst cas_map_snd (cl_nat_logic _ _ (cas_index nR nL Hn o (unzip1 m))).
  exact (cl_nth cl_opt None (unzip2 m) (index o (unzip1 m))).
Qed.

End ApaMap.

Section ApaSorted.
Variables (T : Type) (leR : T -> T -> bool) (leL : T -> T -> I.Bool).
Hypothesis HR : forall a b, CtBoolRel (leR a b) (leL a b).
Notation RL := (fun a b : T => Lean.eq (leL a b) I.Bool_true).

Fixpoint cas_path_forward (x : T) (s : seq T) : path leR x s -> I.List_IsChain T RL (I.List_cons T x (cl_map cid s)) :=
  match s as s0 return path leR x s0 -> I.List_IsChain T RL (I.List_cons T x (cl_map cid s0)) with
  | [::] => fun _ => I.List_IsChain_singleton T RL x
  | y :: s' => fun H =>
      I.List_IsChain_cons_cons T RL x y (cl_map cid s')
        (prop_to_sprop _ _ (ct_bool_truth _ _ (HR x y)) (elimTF andP H).1)
        (cas_path_forward y s' (elimTF andP H).2)
  end.

Lemma cas_sorted s : PropSPropRel (sorted leR s) (I.List_IsChain T RL (cl_map cid s)).
Proof.
  apply prop_sprop_rel_intro.
  - destruct s as [|x s]; intro H; [exact (I.List_IsChain_nil T RL) | exact (cas_path_forward x s H)].
  - exact (cta_sorted_backward T leR leL HR s).
Qed.

End ApaSorted.

Lemma cas_sorted_list (T : Type) (leR : T -> T -> bool) (leL : T -> T -> I.Bool)
  (HR : forall a b, CtBoolRel (leR a b) (leL a b)) s sL (Hs : ClListRel cid s sL) :
  PropSPropRel (sorted leR s) (I.List_IsChain T (fun a b : T => Lean.eq (leL a b) I.Bool_true) sL).
Proof. have E := cl_list_logic _ _ _ Hs. subst sL. exact (cas_sorted T leR leL HR s). Qed.

(** Boolean negation against Lean's [Not]. *)
Lemma cas_notb (b : bool) (P : SProp) (M : PropSPropRel (is_true b) P) : PropSPropRel (is_true (~~ b)) (I.Not P).
Proof.
  apply prop_sprop_rel_intro.
  - move=> /negP N HL. exact (ct_coq_false_to_target (N (sprop_to_prop _ _ M HL))).
  - intro N. apply strictly_inhabits. apply/negP => Hm.
    exact (interpret_strict _ (ct_target_false_to_strict (N (prop_to_sprop _ _ M Hm)))).
Qed.

(* ------------------------------------------------------------------ *)
(** * Arrivals and the APA platform predicates (as in the accepted classic arrival_sequence and APA platform
    certificates, re-stated for this export) *)

Lemma cs_forall_arr (Job : eqType) PR PL :
  (forall aR aL, CsArrRel Job aR aL -> PropSPropRel (PR aR) (PL aL)) -> PropSPropRel (forall a, PR a) (forall a, PL a).
Proof. exact (cs_forall_cover _ _ (CsArrRel Job) (cs_arr_to_target Job) (cs_arr_to_source Job) (cs_arr_canonical Job) (cs_arr_surjective Job) PR PL). Qed.

Lemma cs_consistent (Job : eqType) pR pL (Hp : CsParRel Job pR pL) aR aL (Ha : CsArrRel Job aR aL) :
  PropSPropRel (ArrivalSequence.arrival_times_are_consistent pR aR)
    (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrival_times_are_consistent Job (ct_decidable_eq Job) pL aL).
Proof.
  apply: ct_forall_identity => j. apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (ct_bool_truth _ _ (ct_decide_bool _ _ _ (cs_mem Job j _ _ (Ha tR tL Ht)))).
  exact (sub_nat_eq_correspondence _ _ _ _ (Hp j) Ht).
Qed.

Lemma cs_is_a_set (Job : eqType) aR aL (Ha : CsArrRel Job aR aL) :
  PropSPropRel (ArrivalSequence.arrival_sequence_is_a_set aR)
    (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrival_sequence_is_a_set Job (ct_decidable_eq Job) aL).
Proof. apply: ct_forall_nat => tR tL Ht. exact (cs_uniq Job _ _ (Ha tR tL Ht)). Qed.

Lemma cs_jobs_arrived_up_to (Job : eqType) aR aL (Ha : CsArrRel Job aR aL) tR tL (Ht : SubNatRel tR tL) :
  ClListRel cid (ArrivalSequence.jobs_arrived_up_to aR tR)
    (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_jobs_arrived_up_to Job (ct_decidable_eq Job) aL tL).
Proof.
  exact (cs_bigcat_nat_rel Job (fun t => aR t) (fun t => aL t) Ha 0 _ tR.+1 _ (sub_nat_rel_canonical 0)
           (sub_imported_eq_congr Lean.Nat_succ _ _ Ht)).
Qed.

Lemma cs_total (T : Type) rR rL (Hr : CsRelRel T rR rL) :
  PropSPropRel (total rR) (forall x y, Lean.eq (I.Bool_or (rL x y) (rL y x)) I.Bool_true).
Proof.
  rewrite /total. apply: ct_forall_identity => x. apply: ct_forall_identity => y.
  exact (ct_bool_truth _ _ (ct_bool_or _ _ _ _ (Hr x y) (Hr y x))).
Qed.

Section ApaPlat.
Variables (Task Job : eqType) (nR : nat) (nL : Lean.Nat).
Hypothesis Hn : SubNatRel nR nL.
Notation dT := (ct_decidable_eq Task).
Notation dJ := (ct_decidable_eq Job).
Variables (sR : Schedule.schedule Job nR) (sL : I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_schedule Job dJ nL).
Hypothesis Hs : CsSchedRel Job nR nL sR sL.
Variables (jaR : Job -> nat) (jaL : Job -> Lean.Nat) (cR : Job -> nat) (cL : Job -> Lean.Nat).
Hypotheses (Hja : CsParRel Job jaR jaL) (Hc : CsParRel Job cR cL).
Variable job_task : Job -> Task.
Variables (aR : ArrivalSequence.arrival_sequence Job)
  (aL : I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrival_sequence Job dJ).
Hypothesis Ha : CsArrRel Job aR aL.
Variables (alR : Affinity.task_affinity Task nR) (alL : I.Prosa_Classic_Model_Schedule_Apa_Affinity_Affinity_task_affinity Task dT nL).
Hypothesis Hal : CtafRel Task nR nL Hn alR alL.
Notation bl := (cs_GS_backlogged Job nR nL Hn sR sL Hs jaR jaL Hja cR cL Hc).
Notation son := (cs_GS_scheduled_on Job nR nL sR sL Hs).
Notation cex := (cai_can_execute_on Task nR nL Hn alR alL Hal).

Lemma cs_PL_apa_work_conserving :
  PropSPropRel (Platform.apa_work_conserving jaR cR job_task aR sR alR)
    (I.Prosa_Classic_Model_Schedule_Apa_Platform_Platform_apa_work_conserving Task Job dT dJ jaL cL job_task aL nL sL alL).
Proof.
  apply: ct_forall_identity => j. apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (cs_arrives_in Job aR aL Ha j).
  apply: ct_imp; first exact (ct_bool_truth _ _ (bl j tR tL Ht)).
  apply: (co_forall_ord nR nL Hn) => oR oL Ho.
  apply: ct_imp; first exact (ct_bool_truth _ _ (cex (job_task j) oR oL Ho)).
  apply: ct_exists_identity => j_other.
  exact (ct_bool_truth _ _ (son j_other oR oL Ho tR tL Ht)).
Qed.

Lemma cs_PL_respects_affinity :
  PropSPropRel (Platform.respects_affinity job_task sR alR) (I.Prosa_Classic_Model_Schedule_Apa_Platform_Platform_respects_affinity Task Job dT dJ job_task nL sL alL).
Proof.
  apply: ct_forall_identity => j. apply: (co_forall_ord nR nL Hn) => oR oL Ho. apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (ct_bool_truth _ _ (son j oR oL Ho tR tL Ht)).
  exact (ct_bool_truth _ _ (cex (job_task j) oR oL Ho)).
Qed.

Lemma cs_PL_respects_JLDP_policy_under_weak_APA hpR hpL (Hhp : CsJldpRel Job hpR hpL) :
  PropSPropRel (Platform.respects_JLDP_policy_under_weak_APA jaR cR job_task aR sR alR hpR)
    (I.Prosa_Classic_Model_Schedule_Apa_Platform_Platform_respects_JLDP_policy_under_weak_APA Task Job dT dJ jaL cL job_task aL nL sL alL hpL).
Proof.
  apply: ct_forall_identity => j. apply: ct_forall_identity => j_hp. apply: (co_forall_ord nR nL Hn) => oR oL Ho.
  apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (cs_arrives_in Job aR aL Ha j).
  apply: ct_imp; first exact (ct_bool_truth _ _ (bl j tR tL Ht)).
  apply: ct_imp; first exact (ct_bool_truth _ _ (son j_hp oR oL Ho tR tL Ht)).
  apply: ct_imp; first exact (ct_bool_truth _ _ (cex (job_task j) oR oL Ho)).
  exact (ct_bool_truth _ _ (Hhp tR tL Ht j_hp j)).
Qed.

End ApaPlat.

(* ------------------------------------------------------------------ *)
(** * Definitions *)

Section Defs.
Variables (Job Task : eqType).
Notation dJ := (ct_decidable_eq Job).
Notation dT := (ct_decidable_eq Task).
Variables (jaR : Job -> nat) (jaL : Job -> Lean.Nat) (cR : Job -> nat) (cL : Job -> Lean.Nat).
Hypotheses (Hja : CsParRel Job jaR jaL) (Hc : CsParRel Job cR cL).
Variable job_task : Job -> Task.
Variables (nR : nat) (nL : Lean.Nat).
Hypothesis Hn : SubNatRel nR nL.
Variables (aR : ArrivalSequence.arrival_sequence Job)
  (aL : I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrival_sequence Job dJ).
Hypothesis Ha : CsArrRel Job aR aL.
Variables (alR : Affinity.task_affinity Task nR) (alL : I.Prosa_Classic_Model_Schedule_Apa_Affinity_Affinity_task_affinity Task dT nL).
Hypothesis Hal : CtafRel Task nR nL Hn alR alL.
Variables (hR : nat -> Job -> Job -> bool) (hL : Lean.Nat -> Job -> Job -> I.Bool).
Hypothesis Hh : CsJldpRel Job hR hL.
Notation pp := (cas_pp nR nL Hn Job).

Theorem ConcreteScheduler_pending_jobs_correspondence sR sL (Hs : CsSchedRel Job nR nL sR sL) tR tL (Ht : SubNatRel tR tL) :
  ClListRel cid (@ConcreteScheduler.pending_jobs Job jaR cR nR aR sR tR) (I.Prosa_Classic_Implementation_Apa_Schedule_ConcreteScheduler_pending_jobs Job dJ jaL cL nL aL sL tL).
Proof.
  apply: coq_eq_to_imported_eq.
  have E := cl_list_logic _ _ _ (cs_jobs_arrived_up_to Job aR aL Ha tR tL Ht).
  have F := cl_filter cid _ (fun j => I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_pending Job dJ jaL cL nL sL j tL)
              (fun j => cs_GS_pending Job nR nL Hn sR sL Hs jaR jaL Hja cR cL Hc j tR tL Ht) (ArrivalSequence.jobs_arrived_up_to aR tR).
  rewrite -E in F. exact F.
Qed.

Theorem ConcreteScheduler_sorted_pending_jobs_correspondence sR sL (Hs : CsSchedRel Job nR nL sR sL) tR tL (Ht : SubNatRel tR tL) :
  ClListRel cid (@ConcreteScheduler.sorted_pending_jobs Job jaR cR nR aR hR sR tR) (I.Prosa_Classic_Implementation_Apa_Schedule_ConcreteScheduler_sorted_pending_jobs Job dJ jaL cL nL aL hL sL tL).
Proof. exact (cs_sort_rel Job (hR tR) (hL tL) (Hh tR tL Ht) _ _ (ConcreteScheduler_pending_jobs_correspondence sR sL Hs tR tL Ht)). Qed.

Theorem ConcreteScheduler_should_be_scheduled_correspondence tR tL (Ht : SubNatRel tR tL) j x :
  CtBoolRel (@ConcreteScheduler.should_be_scheduled Job Task job_task nR alR hR tR j x)
    (I.Prosa_Classic_Implementation_Apa_Schedule_ConcreteScheduler_should_be_scheduled Job dJ Task dT job_task nL alL hL tL j (pp x)).
Proof.
  destruct x as [o [j'|]].
  - exact (ct_bool_and _ _ _ _ (cai_can_execute_on Task nR nL Hn alR alL Hal (job_task j) o _ (co_ord_canonical nR nL Hn o))
             (ct_bool_not _ _ (Hh tR tL Ht j' j))).
  - exact (cai_can_execute_on Task nR nL Hn alR alL Hal (job_task j) o _ (co_ord_canonical nR nL Hn o)).
Qed.

Lemma cas_update_eq tR tL (Ht : SubNatRel tR tL) m j :
  Logic.eq (cl_map pp (@ConcreteScheduler.update_available_cpu Job Task job_task nR alR hR tR m j))
    (I.Prosa_Classic_Implementation_Apa_Schedule_ConcreteScheduler_update_available_cpu Job dJ Task dT job_task nL alL hL tL (cl_map pp m) j).
Proof.
  exact (cas_replace_first nR nL Hn Job _ _ (ConcreteScheduler_should_be_scheduled_correspondence tR tL Ht j) _ _
           (fun x => match x with (o, y) => Logic.eq_refl _ end) m).
Qed.

Theorem ConcreteScheduler_update_available_cpu_correspondence tR tL (Ht : SubNatRel tR tL) mR mL (Hm : ClListRel pp mR mL) j :
  ClListRel pp (@ConcreteScheduler.update_available_cpu Job Task job_task nR alR hR tR mR j)
    (I.Prosa_Classic_Implementation_Apa_Schedule_ConcreteScheduler_update_available_cpu Job dJ Task dT job_task nL alL hL tL mL j).
Proof. apply: coq_eq_to_imported_eq. rewrite (cl_list_logic _ _ _ Hm). exact (cas_update_eq tR tL Ht mR j). Qed.

Lemma cas_sched_list_eq tR tL (Ht : SubNatRel tR tL) l :
  Logic.eq (cl_map pp (@ConcreteScheduler.schedule_jobs_from_list Job Task job_task nR alR hR tR l))
    (I.Prosa_Classic_Implementation_Apa_Schedule_ConcreteScheduler_schedule_jobs_from_list Job dJ Task dT job_task nL alL hL tL (cl_map cid l)).
Proof.
  rewrite /ConcreteScheduler.schedule_jobs_from_list. unfold I.Prosa_Classic_Implementation_Apa_Schedule_ConcreteScheduler_schedule_jobs_from_list.
  rewrite (cas_foldl nR nL Hn Job _ _ (cas_update_eq tR tL Ht) l) cas_empty. reflexivity.
Qed.

Theorem ConcreteScheduler_schedule_jobs_from_list_correspondence tR tL (Ht : SubNatRel tR tL) lR lL (Hl : ClListRel cid lR lL) :
  ClListRel pp (@ConcreteScheduler.schedule_jobs_from_list Job Task job_task nR alR hR tR lR)
    (I.Prosa_Classic_Implementation_Apa_Schedule_ConcreteScheduler_schedule_jobs_from_list Job dJ Task dT job_task nL alL hL tL lL).
Proof. apply: coq_eq_to_imported_eq. rewrite (cl_list_logic _ _ _ Hl). exact (cas_sched_list_eq tR tL Ht lR). Qed.

Theorem ConcreteScheduler_apa_schedule_correspondence sR sL (Hs : CsSchedRel Job nR nL sR sL) oR oL (Ho : CoOrdRel nR nL oR oL)
    tR tL (Ht : SubNatRel tR tL) :
  Lean.eq (cl_opt (@ConcreteScheduler.apa_schedule Job Task jaR cR job_task nR aR alR hR sR oR tR))
    (I.Prosa_Classic_Implementation_Apa_Schedule_ConcreteScheduler_apa_schedule Job dJ Task dT jaL cL job_task nL aL alL hL sL oL tL).
Proof.
  apply: coq_eq_to_imported_eq.
  have E := co_fin_rel_eq _ _ _ _ _ (co_ord_canonical nR nL Hn oR) Ho. destruct E.
  rewrite /ConcreteScheduler.apa_schedule. unfold I.Prosa_Classic_Implementation_Apa_Schedule_ConcreteScheduler_apa_schedule.
  rewrite (cl_list_logic _ _ _ (ConcreteScheduler_sorted_pending_jobs_correspondence sR sL Hs tR tL Ht)) -(cas_sched_list_eq tR tL Ht).
  exact (cas_p2f nR nL Hn Job _ oR).
Qed.

Lemma cs_empty : CsSchedRel Job nR nL (fun _ _ => None) (fun _ _ => I.Option_none Job).
Proof. intros oR oL Ho tR tL Ht. exact (@Lean.eq_refl _ _). Qed.

Theorem ConcreteScheduler_scheduler_correspondence :
  CsSchedRel Job nR nL (@ConcreteScheduler.scheduler Job Task jaR cR job_task nR aR alR hR) (I.Prosa_Classic_Implementation_Apa_Schedule_ConcreteScheduler_scheduler Job dJ Task dT jaL cL job_task nL aL alL hL).
Proof.
  exact (cs_GC_build_schedule_from_prefixes Job nR nL _ _
           (fun sR sL Hs oR oL Ho tR tL Ht => ConcreteScheduler_apa_schedule_correspondence sR sL Hs oR oL Ho tR tL Ht) _ _ cs_empty).
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
  | |- SubNatRel (?f ?x) (?g ?x) => match goal with H : CsParRel _ f g |- _ => exact (H x) end
  | |- CtBoolRel (?f ?x ?y) (?g ?x ?y) => match goal with H : CsRelRel _ f g |- _ => exact (H x y) end
  | |- CtBoolRel (?f ?t ?x ?y) (?g ?u ?x ?y) => match goal with H : CsJldpRel _ f g |- _ => eapply H end
  end.

Ltac crel_isnat T := first [ unify T nat | unify T Lean.Nat ].

Ltac crel_intro_defs T :=
  lazymatch T with
  | Schedule.processor ?n -> _ -> option _ => match goal with Hn : SubNatRel n _ |- _ => apply: (cs_forall_sched _ _ _ Hn); intros ? ? ? end
  | ArrivalSequence.arrival_sequence _ => apply: (cs_forall_arr _); intros ? ? ?
  | Schedule.processor ?n => match goal with Hn : SubNatRel n _ |- _ => apply: (co_forall_ord _ _ Hn); intros ? ? ? end
  | ordinal ?n => match goal with Hn : SubNatRel n _ |- _ => apply: (co_forall_ord _ _ Hn); intros ? ? ? end
  | Priority.JLDP_policy _ => apply: (cs_forall_jldp _); intros ? ? ?
  | Affinity.task_affinity _ ?n => match goal with Hn : SubNatRel n _ |- _ => apply: (cai_forall_taff _ _ _ Hn); intros ? ? ? end
  | Equality.sort (fintype_ordinal__canonical__eqtype_Equality ?n) => match goal with Hn : SubNatRel n _ |- _ => apply: (co_forall_ord _ _ Hn); intros ? ? ? end
  | pred_sort (seq_predType _) => apply: (cl_forall_list cid cid (fun _ => Logic.eq_refl _)); intros ? ? ?
  | seq _ => apply: (cl_forall_list cid cid (fun _ => Logic.eq_refl _)); intros ? ? ?
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
  | crel_hyp; crel
  | lazymatch goal with
    | |- forall _, _ => intro; crel
    | |- CsSchedRel _ _ _ (ConcreteScheduler.scheduler _ _ _ _ _ _ _) _ => eapply ConcreteScheduler_scheduler_correspondence; crel
    | |- Lean.eq (cl_opt (Some _)) _ => exact (@Lean.eq_refl _ _)
    | |- Lean.eq (cl_opt (ConcreteScheduler.apa_schedule _ _ _ _ _ _ _ _ _ _)) _ => eapply ConcreteScheduler_apa_schedule_correspondence; crel
    | |- Lean.eq (cl_opt (ConcreteScheduler.scheduler _ _ _ _ _ _ _ _ _)) _ => eapply ConcreteScheduler_scheduler_correspondence; crel
    | |- Lean.eq (cl_opt (?s ?o ?t)) _ => match goal with H : CsSchedRel _ _ _ s _ |- _ => eapply H; crel end
    | |- ClListRel _ (ConcreteScheduler.schedule_jobs_from_list _ _ _ _ _ _) _ => eapply ConcreteScheduler_schedule_jobs_from_list_correspondence; crel
    | |- ClListRel _ (ConcreteScheduler.sorted_pending_jobs _ _ _ _ _ _ _) _ => eapply ConcreteScheduler_sorted_pending_jobs_correspondence; crel
    | |- CsRelRel _ (?r ?t) (?l ?u) => match goal with H : CsJldpRel _ r l |- _ => eapply H; crel end
    | |- PropSPropRel (@Logic.eq (option _) _ _) _ => eapply cs_opt_rel_eq; crel
    | |- PropSPropRel (@Logic.eq (ordinal _) _ _) _ => eapply co_ord_eq_rel; crel
    | |- PropSPropRel (@ex (option _) _) _ => apply: cas_exists_opt; intro; cbv beta; crel
    | |- PropSPropRel (@ex (Equality.sort (Datatypes_option__canonical__eqtype_Equality _)) _) _ => apply: cas_exists_opt; intro; cbv beta; crel
    | |- PropSPropRel (@Logic.eq (Equality.sort (fintype_ordinal__canonical__eqtype_Equality _)) _ _) _ => eapply co_ord_eq_rel; crel
    | |- CoOrdRel _ _ _ _ => assumption
    | |- SubNatRel ?a _ => crel_n a
    | |- CtBoolRel ?b _ => crel_b b
    | |- ClListRel _ ?l _ => crel_l l
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
with crel_eq_defs := first [ eapply ct_eq_rel | eapply cs_opt_rel_eq; crel ]
with crel_n_defs := first [ eapply cs_list_size; crel ]
with crel_b_defs := first [ eapply cs_GS_backlogged; crel
    | eapply cs_GS_scheduled; crel
    | eapply cs_GS_scheduled_on; crel
    | eapply cs_GS_pending; crel
    | eapply cs_GS_completed; crel
    | eapply cai_can_execute_on; crel
    | eapply ct_decide_bool; crel ]
with crel_l_defs := first [ fail ]
with crel_p_defs := first [ eapply cas_pair_mem; crel
    | eapply cas_notb; crel
    | eapply cas_uniq_unzip1; crel
    | eapply cas_sorted; crel
    | eapply cas_sorted_list; crel
    | eapply cs_total; crel
    | eapply cs_PR_JLDP_is_transitive; crel
    | eapply cs_arrives_in; crel
    | eapply cs_consistent; crel
    | eapply cs_is_a_set; crel
    | eapply cs_GS_jobs_come_from_arrival_sequence; crel
    | eapply cs_GS_jobs_must_arrive_to_execute; crel
    | eapply cs_GS_sequential_jobs; crel
    | eapply cs_GS_completed_jobs_dont_execute; crel
    | eapply cs_PL_apa_work_conserving; crel
    | eapply cs_PL_respects_affinity; crel
    | eapply cs_PL_respects_JLDP_policy_under_weak_APA; crel
    | eapply cs_mem; crel
    | eapply cs_uniq; crel ].

Ltac crel_spine :=
  repeat lazymatch goal with
  | |- PropSPropRel (forall x : ?T, _) _ =>
      lazymatch type of T with Prop => eapply ct_imp; [ crel | idtac ] | _ => crel_intro T end
  end.

(* ------------------------------------------------------------------ *)
(** * Statements *)

Definition src_scheduler_depends_only_on_prefix (Job Task : eqType) : Prop :=
  ltac:(type_of_term (@ConcreteScheduler.scheduler_depends_only_on_prefix Job Task)).
Definition tgt_scheduler_depends_only_on_prefix (Job Task : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Implementation_Apa_Schedule_ConcreteScheduler_scheduler_depends_only_on_prefix Job (ct_decidable_eq Job) Task (ct_decidable_eq Task))).
Theorem ConcreteScheduler_scheduler_depends_only_on_prefix_correspondence (Job Task : eqType) :
  PropSPropRel (src_scheduler_depends_only_on_prefix Job Task) (tgt_scheduler_depends_only_on_prefix Job Task).
Proof. unfold src_scheduler_depends_only_on_prefix, tgt_scheduler_depends_only_on_prefix. crel_spine. crel. Unshelve. all: crel. Qed.

Definition src_scheduler_uses_construction_function (Job Task : eqType) : Prop :=
  ltac:(type_of_term (@ConcreteScheduler.scheduler_uses_construction_function Job Task)).
Definition tgt_scheduler_uses_construction_function (Job Task : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Implementation_Apa_Schedule_ConcreteScheduler_scheduler_uses_construction_function Job (ct_decidable_eq Job) Task (ct_decidable_eq Task))).
Theorem ConcreteScheduler_scheduler_uses_construction_function_correspondence (Job Task : eqType) :
  PropSPropRel (src_scheduler_uses_construction_function Job Task) (tgt_scheduler_uses_construction_function Job Task).
Proof. unfold src_scheduler_uses_construction_function, tgt_scheduler_uses_construction_function. crel_spine. crel. Unshelve. all: crel. Qed.

Definition src_scheduler_uniq_cpus (Job Task : eqType) : Prop :=
  ltac:(type_of_term (@ConcreteScheduler.scheduler_uniq_cpus Job Task)).
Definition tgt_scheduler_uniq_cpus (Job Task : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Implementation_Apa_Schedule_ConcreteScheduler_scheduler_uniq_cpus Job (ct_decidable_eq Job) Task (ct_decidable_eq Task))).
Theorem ConcreteScheduler_scheduler_uniq_cpus_correspondence (Job Task : eqType) :
  PropSPropRel (src_scheduler_uniq_cpus Job Task) (tgt_scheduler_uniq_cpus Job Task).
Proof. unfold src_scheduler_uniq_cpus, tgt_scheduler_uniq_cpus. crel_spine. crel. Unshelve. all: crel. Qed.

Definition src_scheduler_job_in_mapping (Job Task : eqType) : Prop :=
  ltac:(type_of_term (@ConcreteScheduler.scheduler_job_in_mapping Job Task)).
Definition tgt_scheduler_job_in_mapping (Job Task : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Implementation_Apa_Schedule_ConcreteScheduler_scheduler_job_in_mapping Job (ct_decidable_eq Job) Task (ct_decidable_eq Task))).
Theorem ConcreteScheduler_scheduler_job_in_mapping_correspondence (Job Task : eqType) :
  PropSPropRel (src_scheduler_job_in_mapping Job Task) (tgt_scheduler_job_in_mapping Job Task).
Proof. unfold src_scheduler_job_in_mapping, tgt_scheduler_job_in_mapping. crel_spine. crel. Unshelve. all: crel. Qed.

Definition src_scheduler_mapping_respects_affinity (Job Task : eqType) : Prop :=
  ltac:(type_of_term (@ConcreteScheduler.scheduler_mapping_respects_affinity Job Task)).
Definition tgt_scheduler_mapping_respects_affinity (Job Task : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Implementation_Apa_Schedule_ConcreteScheduler_scheduler_mapping_respects_affinity Job (ct_decidable_eq Job) Task (ct_decidable_eq Task))).
Theorem ConcreteScheduler_scheduler_mapping_respects_affinity_correspondence (Job Task : eqType) :
  PropSPropRel (src_scheduler_mapping_respects_affinity Job Task) (tgt_scheduler_mapping_respects_affinity Job Task).
Proof. unfold src_scheduler_mapping_respects_affinity, tgt_scheduler_mapping_respects_affinity. crel_spine. crel. Unshelve. all: crel. Qed.

Definition src_scheduler_has_no_duplicate_jobs (Job Task : eqType) : Prop :=
  ltac:(type_of_term (@ConcreteScheduler.scheduler_has_no_duplicate_jobs Job Task)).
Definition tgt_scheduler_has_no_duplicate_jobs (Job Task : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Implementation_Apa_Schedule_ConcreteScheduler_scheduler_has_no_duplicate_jobs Job (ct_decidable_eq Job) Task (ct_decidable_eq Task))).
Theorem ConcreteScheduler_scheduler_has_no_duplicate_jobs_correspondence (Job Task : eqType) :
  PropSPropRel (src_scheduler_has_no_duplicate_jobs Job Task) (tgt_scheduler_has_no_duplicate_jobs Job Task).
Proof. unfold src_scheduler_has_no_duplicate_jobs, tgt_scheduler_has_no_duplicate_jobs. crel_spine. crel. Unshelve. all: crel. Qed.

Definition src_scheduler_scheduled_on (Job Task : eqType) : Prop :=
  ltac:(type_of_term (@ConcreteScheduler.scheduler_scheduled_on Job Task)).
Definition tgt_scheduler_scheduled_on (Job Task : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Implementation_Apa_Schedule_ConcreteScheduler_scheduler_scheduled_on Job (ct_decidable_eq Job) Task (ct_decidable_eq Task))).
Theorem ConcreteScheduler_scheduler_scheduled_on_correspondence (Job Task : eqType) :
  PropSPropRel (src_scheduler_scheduled_on Job Task) (tgt_scheduler_scheduled_on Job Task).
Proof. unfold src_scheduler_scheduled_on, tgt_scheduler_scheduled_on. crel_spine. crel. Unshelve. all: crel. Qed.

Definition src_scheduler_has_cpus (Job Task : eqType) : Prop :=
  ltac:(type_of_term (@ConcreteScheduler.scheduler_has_cpus Job Task)).
Definition tgt_scheduler_has_cpus (Job Task : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Implementation_Apa_Schedule_ConcreteScheduler_scheduler_has_cpus Job (ct_decidable_eq Job) Task (ct_decidable_eq Task))).
Theorem ConcreteScheduler_scheduler_has_cpus_correspondence (Job Task : eqType) :
  PropSPropRel (src_scheduler_has_cpus Job Task) (tgt_scheduler_has_cpus Job Task).
Proof. unfold src_scheduler_has_cpus, tgt_scheduler_has_cpus. crel_spine. crel. Unshelve. all: crel. Qed.

Definition src_scheduler_mapping_is_work_conserving (Job Task : eqType) : Prop :=
  ltac:(type_of_term (@ConcreteScheduler.scheduler_mapping_is_work_conserving Job Task)).
Definition tgt_scheduler_mapping_is_work_conserving (Job Task : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Implementation_Apa_Schedule_ConcreteScheduler_scheduler_mapping_is_work_conserving Job (ct_decidable_eq Job) Task (ct_decidable_eq Task))).
Theorem ConcreteScheduler_scheduler_mapping_is_work_conserving_correspondence (Job Task : eqType) :
  PropSPropRel (src_scheduler_mapping_is_work_conserving Job Task) (tgt_scheduler_mapping_is_work_conserving Job Task).
Proof. unfold src_scheduler_mapping_is_work_conserving, tgt_scheduler_mapping_is_work_conserving. crel_spine. crel. Unshelve. all: crel. Qed.

Definition src_scheduler_priority (Job Task : eqType) : Prop :=
  ltac:(type_of_term (@ConcreteScheduler.scheduler_priority Job Task)).
Definition tgt_scheduler_priority (Job Task : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Implementation_Apa_Schedule_ConcreteScheduler_scheduler_priority Job (ct_decidable_eq Job) Task (ct_decidable_eq Task))).
Theorem ConcreteScheduler_scheduler_priority_correspondence (Job Task : eqType) :
  PropSPropRel (src_scheduler_priority Job Task) (tgt_scheduler_priority Job Task).
Proof. unfold src_scheduler_priority, tgt_scheduler_priority. crel_spine. crel. Unshelve. all: crel. Qed.

Definition src_scheduler_jobs_come_from_arrival_sequence (Job Task : eqType) : Prop :=
  ltac:(type_of_term (@ConcreteScheduler.scheduler_jobs_come_from_arrival_sequence Job Task)).
Definition tgt_scheduler_jobs_come_from_arrival_sequence (Job Task : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Implementation_Apa_Schedule_ConcreteScheduler_scheduler_jobs_come_from_arrival_sequence Job (ct_decidable_eq Job) Task (ct_decidable_eq Task))).
Theorem ConcreteScheduler_scheduler_jobs_come_from_arrival_sequence_correspondence (Job Task : eqType) :
  PropSPropRel (src_scheduler_jobs_come_from_arrival_sequence Job Task) (tgt_scheduler_jobs_come_from_arrival_sequence Job Task).
Proof. unfold src_scheduler_jobs_come_from_arrival_sequence, tgt_scheduler_jobs_come_from_arrival_sequence. crel_spine. crel. Unshelve. all: crel. Qed.

Definition src_scheduler_jobs_must_arrive_to_execute (Job Task : eqType) : Prop :=
  ltac:(type_of_term (@ConcreteScheduler.scheduler_jobs_must_arrive_to_execute Job Task)).
Definition tgt_scheduler_jobs_must_arrive_to_execute (Job Task : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Implementation_Apa_Schedule_ConcreteScheduler_scheduler_jobs_must_arrive_to_execute Job (ct_decidable_eq Job) Task (ct_decidable_eq Task))).
Theorem ConcreteScheduler_scheduler_jobs_must_arrive_to_execute_correspondence (Job Task : eqType) :
  PropSPropRel (src_scheduler_jobs_must_arrive_to_execute Job Task) (tgt_scheduler_jobs_must_arrive_to_execute Job Task).
Proof. unfold src_scheduler_jobs_must_arrive_to_execute, tgt_scheduler_jobs_must_arrive_to_execute. crel_spine. crel. Unshelve. all: crel. Qed.

Definition src_scheduler_sequential_jobs (Job Task : eqType) : Prop :=
  ltac:(type_of_term (@ConcreteScheduler.scheduler_sequential_jobs Job Task)).
Definition tgt_scheduler_sequential_jobs (Job Task : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Implementation_Apa_Schedule_ConcreteScheduler_scheduler_sequential_jobs Job (ct_decidable_eq Job) Task (ct_decidable_eq Task))).
Theorem ConcreteScheduler_scheduler_sequential_jobs_correspondence (Job Task : eqType) :
  PropSPropRel (src_scheduler_sequential_jobs Job Task) (tgt_scheduler_sequential_jobs Job Task).
Proof. unfold src_scheduler_sequential_jobs, tgt_scheduler_sequential_jobs. crel_spine. crel. Unshelve. all: crel. Qed.

Definition src_scheduler_completed_jobs_dont_execute (Job Task : eqType) : Prop :=
  ltac:(type_of_term (@ConcreteScheduler.scheduler_completed_jobs_dont_execute Job Task)).
Definition tgt_scheduler_completed_jobs_dont_execute (Job Task : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Implementation_Apa_Schedule_ConcreteScheduler_scheduler_completed_jobs_dont_execute Job (ct_decidable_eq Job) Task (ct_decidable_eq Task))).
Theorem ConcreteScheduler_scheduler_completed_jobs_dont_execute_correspondence (Job Task : eqType) :
  PropSPropRel (src_scheduler_completed_jobs_dont_execute Job Task) (tgt_scheduler_completed_jobs_dont_execute Job Task).
Proof. unfold src_scheduler_completed_jobs_dont_execute, tgt_scheduler_completed_jobs_dont_execute. crel_spine. crel. Unshelve. all: crel. Qed.

Definition src_scheduler_apa_work_conserving (Job Task : eqType) : Prop :=
  ltac:(type_of_term (@ConcreteScheduler.scheduler_apa_work_conserving Job Task)).
Definition tgt_scheduler_apa_work_conserving (Job Task : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Implementation_Apa_Schedule_ConcreteScheduler_scheduler_apa_work_conserving Job (ct_decidable_eq Job) Task (ct_decidable_eq Task))).
Theorem ConcreteScheduler_scheduler_apa_work_conserving_correspondence (Job Task : eqType) :
  PropSPropRel (src_scheduler_apa_work_conserving Job Task) (tgt_scheduler_apa_work_conserving Job Task).
Proof. unfold src_scheduler_apa_work_conserving, tgt_scheduler_apa_work_conserving. crel_spine. crel. Unshelve. all: crel. Qed.

Definition src_scheduler_respects_affinity (Job Task : eqType) : Prop :=
  ltac:(type_of_term (@ConcreteScheduler.scheduler_respects_affinity Job Task)).
Definition tgt_scheduler_respects_affinity (Job Task : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Implementation_Apa_Schedule_ConcreteScheduler_scheduler_respects_affinity Job (ct_decidable_eq Job) Task (ct_decidable_eq Task))).
Theorem ConcreteScheduler_scheduler_respects_affinity_correspondence (Job Task : eqType) :
  PropSPropRel (src_scheduler_respects_affinity Job Task) (tgt_scheduler_respects_affinity Job Task).
Proof. unfold src_scheduler_respects_affinity, tgt_scheduler_respects_affinity. crel_spine. crel. Unshelve. all: crel. Qed.

Definition src_scheduler_respects_policy (Job Task : eqType) : Prop :=
  ltac:(type_of_term (@ConcreteScheduler.scheduler_respects_policy Job Task)).
Definition tgt_scheduler_respects_policy (Job Task : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Implementation_Apa_Schedule_ConcreteScheduler_scheduler_respects_policy Job (ct_decidable_eq Job) Task (ct_decidable_eq Task))).
Theorem ConcreteScheduler_scheduler_respects_policy_correspondence (Job Task : eqType) :
  PropSPropRel (src_scheduler_respects_policy Job Task) (tgt_scheduler_respects_policy Job Task).
Proof. unfold src_scheduler_respects_policy, tgt_scheduler_respects_policy. crel_spine. crel. Unshelve. all: crel. Qed.
