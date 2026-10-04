From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq fintype bigop.
From prosa Require Import classic.model.time classic.util.notation classic.model.arrival.basic.arrival_sequence classic.model.arrival.basic.job classic.model.schedule.global.basic.schedule classic.model.schedule.global.jitter.schedule.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedClassicGlobalJitterSchedule.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence ClassicGlobalJitterScheduleBase ClassicGlobalJitterScheduleList ClassicGlobalJitterScheduleOrd.

Module I := ImportedClassicGlobalJitterSchedule.
Local Open Scope nat_scope.

(** Certificates for [classic/model/schedule/global/jitter/schedule.v] (ProsaBuddy classic, commit f692cb7).

    Inputs: the job and task types are [eqType]s, identified, with the Lean [DecidableEq] instances given by the
    eqTypes' decision procedures ([ct_decidable_eq]); [job_task] identified; times and processor counts by
    [SubNatRel]; processors by [CoOrdRel]; schedules pointwise on related processors and times through the option map
    ([CgjSchedRel]); job/task parameters pointwise through [SubNatRel]; all with two-way totals.  The imported global
    [Schedule] / [ScheduleOfSporadicTask] definitions are related as in the accepted classic global schedule
    certificate (re-bound below, through the restated kernel-checked equations and kernel-guarded body projections
    of [ClassicGlobalJitterScheduleInterface]); the statement [cumulative_service_before_jitter_zero], whose type
    contains a [Finset.Ico] sum, is exported through a kernel-checked normalization guard.

    Statements: the source side is the exact elaborated type of the pinned lemma (via [type of]; the source proof
    is not used).  For [cumulative_service_le_task_cost], whose binder lists put [task_cost task_deadline] before the
    job type, the job type is fixed as an [eqType] with its canonical Lean instance and the two task parameters stay
    universally quantified on both sides (as in the accepted classic global schedule certificate). *)

Ltac type_of_term t := let T := type of t in exact T.
Notation cid := (fun z => z).

(* ------------------------------------------------------------------ *)
(** * Helpers (re-bound to this export from the accepted classic certificates) *)

(** Base definitions (as in the accepted classic base library), provided here when this export's library lacks them. *)

(* ------------------------------------------------------------------ *)
(** * Generic helpers *)

Lemma cgj_forall_cover (A B : Type) (Rel : A -> B -> SProp) (toB : A -> B) (toA : B -> A)
    (HB : forall a, Rel a (toB a)) (HA : forall b, Rel (toA b) b) (PR : A -> Prop) (PL : B -> SProp) :
  (forall a b, Rel a b -> PropSPropRel (PR a) (PL b)) -> PropSPropRel (forall a, PR a) (forall b, PL b).
Proof.
  intro H. apply prop_sprop_rel_intro.
  - intros HR b. exact (prop_to_sprop _ _ (H _ _ (HA b)) (HR _)).
  - intro HL. apply strictly_inhabits. intro a. exact (sprop_to_prop _ _ (H _ _ (HB a)) (HL _)).
Qed.

Lemma cgj_mem (T : eqType) x s sL : ClListRel cid s sL ->
  PropSPropRel (x \in s) (I.Membership_mem T (I.List T) (I.List_instMembership T) sL x).
Proof. exact (cl_mem_rel_list T T cid cid (fun _ => Logic.eq_refl _) x s sL). Qed.

Lemma cgj_uniq (T : eqType) s sL : ClListRel cid s sL -> PropSPropRel (uniq s) (I.List_Nodup T sL).
Proof. exact (cl_uniq_rel_list T T cid cid (fun _ => Logic.eq_refl _) (fun _ => Logic.eq_refl _) s sL). Qed.

Lemma cgj_list_size (T : Type) s sL : ClListRel (B := T) cid s sL -> SubNatRel (size s) (I.List_length T sL).
Proof. intro H. destruct H. exact (cl_size cid s). Qed.

Lemma cgj_lean_eq_logic (A : Type) (x y : A) : Lean.eq x y -> Logic.eq x y.
Proof. exact (imported_eq_to_coq_eq x y). Qed.

(** Transport along the target equality (definitional UIP), into relevant and SProp-valued families. *)
Definition cgj_tr {A : Type} {x y : A} (E : Lean.eq x y) (P : A -> Type) (h : P x) : P y :=
  match E in Lean.eq _ z return P z with Lean.eq_refl => h end.
Definition cgj_trs {A : Type} {x y : A} (E : Lean.eq x y) (P : A -> SProp) (h : P x) : P y :=
  match E in Lean.eq _ z return P z with Lean.eq_refl => h end.

(** Options: [cl_opt] is injective and [x == Some j] is [cl_opt x = some j]. *)
Lemma cgj_opt_inj (A : Type) (o1 o2 : option A) : Logic.eq (cl_opt o1) (cl_opt o2) -> Logic.eq o1 o2.
Proof. intro E. by rewrite -(cl_unopt_opt o1) -(cl_unopt_opt o2) E. Qed.

Lemma cgj_opt_eq_rel (A : Type) (o1 o2 : option A) :
  PropSPropRel (Logic.eq o1 o2) (Lean.eq (cl_opt o1) (cl_opt o2)).
Proof.
  apply prop_sprop_rel_intro.
  - intro E. rewrite E. exact (@Lean.eq_refl _ _).
  - intro E. apply strictly_inhabits. exact (cgj_opt_inj A o1 o2 (imported_eq_to_coq_eq _ _ E)).
Qed.

Lemma cgj_opt_eqb_rel (A : eqType) (o1 o2 : option A) :
  PropSPropRel (is_true (o1 == o2)) (Lean.eq (cl_opt o1) (cl_opt o2)).
Proof.
  apply prop_sprop_rel_intro.
  - move=> /eqP E. rewrite E. exact (@Lean.eq_refl _ _).
  - intro E. apply strictly_inhabits. apply/eqP. exact (cgj_opt_inj A o1 o2 (imported_eq_to_coq_eq _ _ E)).
Qed.

(* ------------------------------------------------------------------ *)
(** * Half-open sums and concatenations over [nat] (as in the accepted sum / arrival_sequence certificates) *)

Fixpoint cgj_natl (s : seq nat) : I.List_inst1 Lean.Nat :=
  match s with [::] => I.List_nil_inst1 _ | x :: s' => I.List_cons_inst1 _ (sub_nat_to_imported x) (cgj_natl s') end.

Lemma cgj_iota_range : forall n s,
  Logic.eq (I.List_range' (sub_nat_to_imported s) (sub_nat_to_imported n) (Lean.Nat_succ Lean.Nat_zero)) (cgj_natl (iota s n)).
Proof.
  elim => [|n IH] s; first reflexivity.
  change (Logic.eq (I.List_cons_inst1 _ (sub_nat_to_imported s)
      (I.List_range' (sub_nat_to_imported (S s)) (sub_nat_to_imported n) (Lean.Nat_succ Lean.Nat_zero)))
    (I.List_cons_inst1 _ (sub_nat_to_imported s) (cgj_natl (iota (S s) n)))).
  by rewrite IH.
Qed.

Lemma cgj_foldr_add (f : Lean.Nat -> Lean.Nat) (g : nat -> nat) (Hf : forall k, Logic.eq (f (sub_nat_to_imported k)) (sub_nat_to_imported (g k))) :
  forall s, Logic.eq (I.List_foldr_inst3 Lean.Nat Lean.Nat Lean.Nat_add Lean.Nat_zero (I.List_map_inst3 Lean.Nat Lean.Nat f (cgj_natl s)))
                     (sub_nat_to_imported (foldr addn 0 (map g s))).
Proof.
  elim => [|k s IH] //=.
  change (Logic.eq (Lean.Nat_add (f (sub_nat_to_imported k))
            (I.List_foldr_inst3 Lean.Nat Lean.Nat Lean.Nat_add Lean.Nat_zero (I.List_map_inst3 Lean.Nat Lean.Nat f (cgj_natl s))))
         (sub_nat_to_imported (g k + foldr addn 0 (map g s)))).
  rewrite IH Hf. exact (imported_eq_to_coq_eq _ _ (sub_add_canonical _ _)).
Qed.

Lemma cgj_big_fold (xs : seq nat) (F : nat -> nat) : Logic.eq (\sum_(i <- xs) F i) (foldr addn 0 (map F xs)).
Proof. elim: xs => [|x xs IH]; first by rewrite big_nil. by rewrite big_cons IH. Qed.

Definition CgjFunRel (FR : nat -> nat) (FL : Lean.Nat -> Lean.Nat) : SProp :=
  forall kR kL, SubNatRel kR kL -> SubNatRel (FR kR) (FL kL).

Lemma cgj_fun_canonical FR FL (HF : CgjFunRel FR FL) k : Logic.eq (FL (sub_nat_to_imported k)) (sub_nat_to_imported (FR k)).
Proof. exact (co_nat_logic _ _ (HF _ _ (sub_nat_rel_canonical k))). Qed.

Lemma cgj_ico mR mL nR nL FR FL (Hm : SubNatRel mR mL) (Hn : SubNatRel nR nL) (HF : CgjFunRel FR FL) :
  SubNatRel (\sum_(mR <= i < nR) FR i)
    (I.List_foldr_inst3 Lean.Nat Lean.Nat Lean.Nat_add Lean.Nat_zero
       (I.List_map_inst3 Lean.Nat Lean.Nat FL (I.List_range' mL (I.Nat_sub nL mL) (Lean.Nat_succ Lean.Nat_zero)))).
Proof.
  rewrite (co_nat_logic _ _ Hm) (co_nat_logic _ _ Hn).
  have -> : Logic.eq (I.Nat_sub (sub_nat_to_imported nR) (sub_nat_to_imported mR)) (sub_nat_to_imported (nR - mR))
    := ct_sub_canonical nR mR.
  rewrite cgj_iota_range.
  apply: coq_eq_to_imported_eq. apply: Logic.eq_sym. rewrite (cgj_foldr_add FL FR (cgj_fun_canonical FR FL HF)).
  by rewrite cgj_big_fold.
Qed.

Lemma cgj_map_natl {B : Type} (f : Lean.Nat -> B) : forall s,
  Logic.eq (I.List_map_inst1 Lean.Nat B f (cgj_natl s)) (cl_map (fun k => f (sub_nat_to_imported k)) s).
Proof.
  elim => [|k s IH] //=.
  change (Logic.eq (I.List_cons B (f (sub_nat_to_imported k)) (I.List_map_inst1 Lean.Nat B f (cgj_natl s)))
                   (I.List_cons B (f (sub_nat_to_imported k)) (cl_map (fun k => f (sub_nat_to_imported k)) s))).
  by rewrite IH.
Qed.

Lemma cgj_big_seq {A : Type} (F : nat -> seq A) : forall s : seq nat,
  Logic.eq (\big[cat/[::]]_(i <- s) F i) (flatten (map F s)).
Proof. elim => [|x s IH]; first by rewrite big_nil. by rewrite big_cons IH. Qed.

Definition CgjNatFamRel (A : Type) (fR : nat -> seq A) (fL : Lean.Nat -> I.List A) : SProp :=
  forall nR nL, SubNatRel nR nL -> ClListRel cid (fR nR) (fL nL).

Lemma cgj_bigcat_nat_rel (A : Type) fR fL (Hf : CgjNatFamRel A fR fL) mR mL nR nL :
  SubNatRel mR mL -> SubNatRel nR nL ->
  ClListRel cid (\big[cat/[::]]_(mR <= t < nR) fR t) (I.Prosa_Util_Notation_bigCat A mL nL fL).
Proof.
  intros Hm Hn. have E1 := co_nat_logic _ _ Hm. have E2 := co_nat_logic _ _ Hn. subst mL nL.
  apply: coq_eq_to_imported_eq. apply: Logic.eq_sym.
  rewrite (imported_eq_to_coq_eq _ _ (I.Prosa_Validation_ClassicGlobalJitterScheduleInterface_bigCat_range'
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
  rewrite cgj_big_seq /index_iota Hi -map_comp.
  reflexivity.
Qed.

Lemma cgj_notin_target (T : eqType) x s : Logic.eq (x \in s) false ->
  I.Not (I.Membership_mem T (I.List T) (I.List_instMembership T) (cl_map cid s) x).
Proof.
  intros Hx H. apply: ct_coq_false_to_target.
  have Hm := sprop_to_prop _ _ (cgj_mem T x s _ (cl_lean_eq _ _ _ (Logic.eq_refl _))) H.
  rewrite Hx in Hm. discriminate.
Qed.

(** [undup] against Mathlib's [List.dedup] (step equations exported with their proofs). *)
Lemma cgj_undup_rel (T : eqType) : forall s sL, ClListRel cid s sL ->
  ClListRel cid (undup s) (I.List_dedup T (ct_decidable_eq T) sL).
Proof.
  intros s sL Hs. have E := cl_list_logic _ _ _ Hs. subst sL. apply: coq_eq_to_imported_eq. clear Hs.
  elim: s => [|x s IH].
  - exact (Logic.eq_sym (imported_eq_to_coq_eq _ _ (I.Prosa_Validation_ClassicGlobalJitterScheduleInterface_dedup_nil T (ct_decidable_eq T)))).
  - change (Logic.eq (cl_map cid (if x \in s then undup s else x :: undup s))
      (I.List_dedup T (ct_decidable_eq T) (I.List_cons T x (cl_map cid s)))).
    case Hx: (x \in s).
    + rewrite (imported_eq_to_coq_eq _ _ (I.Prosa_Validation_ClassicGlobalJitterScheduleInterface_dedup_cons_mem
                 T (ct_decidable_eq T) x (cl_map cid s)
                 (prop_to_sprop _ _ (cgj_mem T x s _ (cl_lean_eq _ _ _ (Logic.eq_refl _))) Hx))).
      exact IH.
    + rewrite (imported_eq_to_coq_eq _ _ (I.Prosa_Validation_ClassicGlobalJitterScheduleInterface_dedup_cons_not_mem
                 T (ct_decidable_eq T) x (cl_map cid s) (cgj_notin_target T x s Hx))).
      change (Logic.eq (I.List_cons T x (cl_map cid (undup s))) (I.List_cons T x (I.List_dedup T (ct_decidable_eq T) (cl_map cid s)))).
      by rewrite IH.
Qed.

(* ------------------------------------------------------------------ *)
(** * Schedules, arrival sequences, parameters *)

Definition CgjParRel (T : Type) (pR : T -> nat) (pL : T -> Lean.Nat) : SProp := forall x, SubNatRel (pR x) (pL x).

Lemma cgj_forall_par (T : Type) (PR : (T -> nat) -> Prop) (PL : (T -> Lean.Nat) -> SProp) :
  (forall pR pL, CgjParRel T pR pL -> PropSPropRel (PR pR) (PL pL)) -> PropSPropRel (forall p, PR p) (forall p, PL p).
Proof.
  exact (cgj_forall_cover _ _ (CgjParRel T) (fun pR j => sub_nat_to_imported (pR j)) (fun pL j => sub_nat_to_rocq (pL j))
           (fun pR j => sub_nat_rel_canonical (pR j)) (fun pL j => sub_nat_rel_surjective (pL j)) PR PL).
Qed.

Section Sched.
Variables (Job : eqType) (nR : nat) (nL : Lean.Nat).
Hypothesis Hn : SubNatRel nR nL.
Notation dJ := (ct_decidable_eq Job).
Notation LSched := (I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_schedule Job dJ nL).

Definition CgjSchedRel (sR : Schedule.schedule Job nR) (sL : LSched) : SProp :=
  forall oR oL, CoOrdRel nR nL oR oL -> forall tR tL, SubNatRel tR tL -> Lean.eq (cl_opt (sR oR tR)) (sL oL tL).

Definition cgj_sched_to_target (sR : Schedule.schedule Job nR) : LSched :=
  fun oL tL => cl_opt (sR (co_fin_to_ord nR nL Hn oL) (sub_nat_to_rocq tL)).

Definition cgj_sched_to_source (sL : LSched) : Schedule.schedule Job nR :=
  fun oR tR => cl_unopt (sL (co_ord_to_fin nR nL Hn oR) (sub_nat_to_imported tR)).

Lemma cgj_sched_canonical sR : CgjSchedRel sR (cgj_sched_to_target sR).
Proof.
  intros oR oL Ho tR tL Ht. apply: coq_eq_to_imported_eq. rewrite /cgj_sched_to_target (co_nat_input _ _ Ht).
  by rewrite (co_ord_eq _ _ _ _ _ Ho (co_ord_surjective nR nL Hn oL)).
Qed.

Lemma cgj_sched_surjective sL : CgjSchedRel (cgj_sched_to_source sL) sL.
Proof.
  intros oR oL Ho tR tL Ht. apply: coq_eq_to_imported_eq. rewrite /cgj_sched_to_source cl_opt_unopt.
  rewrite (co_nat_logic _ _ Ht). by rewrite (co_fin_rel_eq _ _ _ _ _ (co_ord_canonical nR nL Hn oR) Ho).
Qed.

Lemma cgj_forall_sched (PR : Schedule.schedule Job nR -> Prop) (PL : LSched -> SProp) :
  (forall sR sL, CgjSchedRel sR sL -> PropSPropRel (PR sR) (PL sL)) -> PropSPropRel (forall s, PR s) (forall s, PL s).
Proof. exact (cgj_forall_cover _ _ CgjSchedRel cgj_sched_to_target cgj_sched_to_source cgj_sched_canonical cgj_sched_surjective PR PL). Qed.

End Sched.

(* ------------------------------------------------------------------ *)
(** * Definitions *)

Section Defs.
Variables (Job : eqType) (nR : nat) (nL : Lean.Nat).
Hypothesis Hn : SubNatRel nR nL.
Notation dJ := (ct_decidable_eq Job).
Variables (sR : Schedule.schedule Job nR)
  (sL : I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_schedule Job dJ nL).
Hypothesis Hs : CgjSchedRel Job nR nL sR sL.

Lemma cgj_GS_scheduled_on j oR oL (Ho : CoOrdRel nR nL oR oL) tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (Schedule.scheduled_on sR j oR tR)
    (I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_scheduled_on Job dJ nL sL j oL tL).
Proof.
  apply: ct_decide_bool.
  exact (cgj_tr (Hs oR oL Ho tR tL Ht) (fun z => PropSPropRel (sR oR tR == Some j) (Lean.eq z (cl_opt (Some j))))
           (cgj_opt_eqb_rel Job (sR oR tR) (Some j))).
Qed.

Lemma cgj_GS_scheduled j tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (Schedule.scheduled sR j tR)
    (I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_scheduled Job dJ nL sL j tL).
Proof.
  apply: (co_exists_rel nR nL Hn). intros oR oL Ho. exact (cgj_GS_scheduled_on j oR oL Ho tR tL Ht).
Qed.

Lemma cgj_GS_service_at j tR tL (Ht : SubNatRel tR tL) :
  SubNatRel (Schedule.service_at sR j tR)
    (I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_service_at Job dJ nL sL j tL).
Proof.
  apply: coq_eq_to_imported_eq.
  rewrite (imported_eq_to_coq_eq _ _ (I.Prosa_Validation_ClassicGlobalJitterScheduleInterface_service_at_sum Job dJ nL sL j tL)).
  apply: imported_eq_to_coq_eq.
  rewrite /Schedule.service_at big_mkcond /=.
  apply: (co_sum_rel nR nL Hn). intros oR oL Ho.
  have H := cgj_GS_scheduled_on j oR oL Ho tR tL Ht.
  rewrite (ct_bool_rel_logic _ _ H). destruct (Schedule.scheduled_on sR j oR tR).
  - exact (sub_nat_rel_canonical 1).
  - exact (sub_nat_rel_canonical 0).
Qed.

Lemma cgj_service_at_fun j : CgjFunRel (fun t => Schedule.service_at sR j t)
    (fun t => I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_service_at Job dJ nL sL j t).
Proof. intros kR kL Hk. exact (cgj_GS_service_at j kR kL Hk). Qed.

Lemma cgj_GS_service j tR tL (Ht : SubNatRel tR tL) :
  SubNatRel (Schedule.service sR j tR)
    (I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_service Job dJ nL sL j tL).
Proof. exact (cgj_ico 0 _ tR tL _ _ (sub_nat_rel_canonical 0) Ht (cgj_service_at_fun j)). Qed.

Lemma cgj_GS_service_during j t1R t1L t2R t2L (H1 : SubNatRel t1R t1L) (H2 : SubNatRel t2R t2L) :
  SubNatRel (Schedule.service_during sR j t1R t2R)
    (I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_service_during Job dJ nL sL j t1L t2L).
Proof. exact (cgj_ico _ _ _ _ _ _ H1 H2 (cgj_service_at_fun j)). Qed.

Lemma cgj_GS_completed cR cL (Hc : CgjParRel Job cR cL) j tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (Schedule.completed cR sR j tR)
    (I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_completed Job dJ cL nL sL j tL).
Proof. exact (ct_decide_le _ _ _ _ (Hc j) (cgj_GS_service j tR tL Ht)). Qed.

Lemma cgj_make_sequence (o : option Job) :
  ClListRel cid (make_sequence o) (I.Prosa_Classic_Util_Notation_make_sequence Job (cl_opt o)).
Proof. destruct o as [x|]; exact (@Lean.eq_refl _ _). Qed.

Lemma cgj_GS_jobs_scheduled_at tR tL (Ht : SubNatRel tR tL) :
  ClListRel cid (Schedule.jobs_scheduled_at sR tR)
    (I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_jobs_scheduled_at Job dJ nL sL tL).
Proof.
  apply: (co_bigcat_rel Job nR nL Hn). intros oR oL Ho.
  exact (cgj_trs (Hs oR oL Ho tR tL Ht)
           (fun z => ClListRel cid (make_sequence (sR oR tR)) (I.Prosa_Classic_Util_Notation_make_sequence Job z))
           (cgj_make_sequence (sR oR tR))).
Qed.

Lemma cgj_GS_jobs_scheduled_between t1R t1L t2R t2L (H1 : SubNatRel t1R t1L) (H2 : SubNatRel t2R t2L) :
  ClListRel cid (Schedule.jobs_scheduled_between sR t1R t2R)
    (I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_jobs_scheduled_between Job dJ nL sL t1L t2L).
Proof.
  apply: cgj_undup_rel. apply: (cgj_bigcat_nat_rel Job (fun t => Schedule.jobs_scheduled_at sR t) _ _ _ _ _ _ H1 H2).
  intros kR kL Hk. exact (cgj_GS_jobs_scheduled_at kR kL Hk).
Qed.

Lemma cgj_GS_jobs_must_arrive_to_execute aR aL (Ha : CgjParRel Job aR aL) :
  PropSPropRel (Schedule.jobs_must_arrive_to_execute aR sR)
    (I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_jobs_must_arrive_to_execute Job dJ aL nL sL).
Proof.
  apply: ct_forall_identity => j. apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (ct_bool_truth _ _ (cgj_GS_scheduled j tR tL Ht)).
  exact (ct_bool_truth _ _ (ct_decide_le _ _ _ _ (Ha j) Ht)).
Qed.

Lemma cgj_GS_completed_jobs_dont_execute cR cL (Hc : CgjParRel Job cR cL) :
  PropSPropRel (Schedule.completed_jobs_dont_execute cR sR)
    (I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_completed_jobs_dont_execute Job dJ cL nL sL).
Proof.
  apply: ct_forall_identity => j. apply: ct_forall_nat => tR tL Ht.
  exact (sub_nat_le_correspondence _ _ _ _ (cgj_GS_service j tR tL Ht) (Hc j)).
Qed.

End Defs.

Section TaskDefs.
Variables (Task Job : eqType) (nR : nat) (nL : Lean.Nat).
Hypothesis Hn : SubNatRel nR nL.
Notation dT := (ct_decidable_eq Task).
Notation dJ := (ct_decidable_eq Job).
Variables (sR : Schedule.schedule Job nR)
  (sL : I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_schedule Job dJ nL).
Hypothesis Hs : CgjSchedRel Job nR nL sR sL.
Variable job_task : Job -> Task.

End TaskDefs.

Lemma cgj_GS_processor nR nL (Hn : SubNatRel nR nL) :
  And (forall o : Schedule.processor nR, CoOrdRel nR nL o (co_ord_to_fin nR nL Hn o))
      (forall o : I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_processor nL,
         CoOrdRel nR nL (co_fin_to_ord nR nL Hn o) o).
Proof. exact (And_intro _ _ (co_ord_canonical nR nL Hn) (co_ord_surjective nR nL Hn)). Qed.

Lemma cgj_GS_schedule (Job : eqType) nR nL (Hn : SubNatRel nR nL) :
  And (forall s : Schedule.schedule Job nR, CgjSchedRel Job nR nL s (cgj_sched_to_target Job nR nL Hn s))
      (forall s : I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_schedule Job (ct_decidable_eq Job) nL,
         CgjSchedRel Job nR nL (cgj_sched_to_source Job nR nL Hn s) s).
Proof. exact (And_intro _ _ (cgj_sched_canonical Job nR nL Hn) (cgj_sched_surjective Job nR nL Hn)). Qed.

(* ------------------------------------------------------------------ *)
(** * Statements *)

(** The common prefix [forall num_cpus (sched : schedule Job num_cpus)]. *)
Lemma cgj_forall_ncpus_sched (Job : eqType)
    (PR : forall n : nat, Schedule.schedule Job n -> Prop)
    (PL : forall n : Lean.Nat, I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_schedule Job (ct_decidable_eq Job) n -> SProp) :
  (forall nR nL (Hn : SubNatRel nR nL) sR sL, CgjSchedRel Job nR nL sR sL -> PropSPropRel (PR nR sR) (PL nL sL)) ->
  PropSPropRel (forall n s, PR n s) (forall n s, PL n s).
Proof.
  intro H. apply: ct_forall_nat => nR nL Hn. exact (cgj_forall_sched Job nR nL Hn _ _ (H nR nL Hn)).
Qed.

Notation sa := cgj_GS_service_at.
Notation sd := cgj_GS_service_during.
Notation sc := cgj_GS_scheduled.

(** The imported [Job] definitions (as in the accepted classic job certificate). *)
Section JobDefs.
Notation c0 := (sub_nat_rel_canonical 0).
Variables (Task Job : eqType).
Notation dT := (ct_decidable_eq Task).
Notation dJ := (ct_decidable_eq Job).

Lemma cgj_J_job_cost_positive cR cL (Hc : CgjParRel Job cR cL) j :
  CtBoolRel (Job.job_cost_positive cR j) (I.Prosa_Classic_Model_Arrival_Basic_Job_Job_job_cost_positive Job dJ cL j).
Proof. exact (ct_decide_lt _ _ _ _ c0 (Hc j)). Qed.

Lemma cgj_J_job_deadline_positive dR dL (Hd : CgjParRel Job dR dL) j :
  CtBoolRel (Job.job_deadline_positive dR j) (I.Prosa_Classic_Model_Arrival_Basic_Job_Job_job_deadline_positive Job dJ dL j).
Proof. exact (ct_decide_lt _ _ _ _ c0 (Hd j)). Qed.

Lemma cgj_J_job_cost_le_deadline cR cL dR dL (Hc : CgjParRel Job cR cL) (Hd : CgjParRel Job dR dL) j :
  CtBoolRel (Job.job_cost_le_deadline cR dR j) (I.Prosa_Classic_Model_Arrival_Basic_Job_Job_job_cost_le_deadline Job dJ cL dL j).
Proof. exact (ct_decide_le _ _ _ _ (Hc j) (Hd j)). Qed.

Lemma cgj_J_valid_realtime_job cR cL dR dL (Hc : CgjParRel Job cR cL) (Hd : CgjParRel Job dR dL) j :
  PropSPropRel (Job.valid_realtime_job cR dR j) (I.Prosa_Classic_Model_Arrival_Basic_Job_Job_valid_realtime_job Job dJ cL dL j).
Proof.
  apply: ct_and; first exact (ct_bool_truth _ _ (cgj_J_job_cost_positive cR cL Hc j)).
  apply: ct_and; first exact (ct_bool_truth _ _ (cgj_J_job_cost_le_deadline cR cL dR dL Hc Hd j)).
  exact (ct_bool_truth _ _ (cgj_J_job_deadline_positive dR dL Hd j)).
Qed.

Lemma cgj_J_job_cost_le_task_cost tcR tcL (Htc : CgjParRel Task tcR tcL) cR cL (Hc : CgjParRel Job cR cL)
    (job_task : Job -> Task) j :
  CtBoolRel (Job.job_cost_le_task_cost tcR cR job_task j)
    (I.Prosa_Classic_Model_Arrival_Basic_Job_Job_job_cost_le_task_cost Task dT tcL Job dJ cL job_task j).
Proof. exact (ct_decide_le _ _ _ _ (Hc j) (Htc (job_task j))). Qed.

Lemma cgj_J_job_deadline_eq_task_deadline tdR tdL (Htd : CgjParRel Task tdR tdL) dR dL (Hd : CgjParRel Job dR dL)
    (job_task : Job -> Task) j :
  PropSPropRel (Job.job_deadline_eq_task_deadline tdR dR job_task j)
    (I.Prosa_Classic_Model_Arrival_Basic_Job_Job_job_deadline_eq_task_deadline Task dT tdL Job dJ dL job_task j).
Proof. exact (sub_nat_eq_correspondence _ _ _ _ (Hd j) (Htd (job_task j))). Qed.

Lemma cgj_J_valid_sporadic_job tcR tcL tdR tdL (Htc : CgjParRel Task tcR tcL) (Htd : CgjParRel Task tdR tdL)
    cR cL dR dL (Hc : CgjParRel Job cR cL) (Hd : CgjParRel Job dR dL) (job_task : Job -> Task) j :
  PropSPropRel (Job.valid_sporadic_job tcR tdR cR dR job_task j)
    (I.Prosa_Classic_Model_Arrival_Basic_Job_Job_valid_sporadic_job Task dT tcL tdL Job dJ cL dL job_task j).
Proof.
  apply: ct_and; first exact (cgj_J_valid_realtime_job cR cL dR dL Hc Hd j).
  apply: ct_and; first exact (ct_bool_truth _ _ (cgj_J_job_cost_le_task_cost tcR tcL Htc cR cL Hc job_task j)).
  exact (cgj_J_job_deadline_eq_task_deadline tdR tdL Htd dR dL Hd job_task j).
Qed.

End JobDefs.



(* ------------------------------------------------------------------ *)
(** * Definitions *)

Section Defs.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).

Theorem ScheduleWithJitter_actual_arrival_correspondence aR aL (Ha : CgjParRel Job aR aL) jjR jjL (Hjj : CgjParRel Job jjR jjL) j :
  SubNatRel (ScheduleWithJitter.actual_arrival aR jjR j) (I.Prosa_Classic_Model_Schedule_Global_Jitter_Schedule_ScheduleWithJitter_actual_arrival Job dJ aL jjL j).
Proof. exact (sub_add_correspondence _ _ _ _ (Ha j) (Hjj j)). Qed.

Theorem ScheduleWithJitter_jitter_has_passed_correspondence aR aL (Ha : CgjParRel Job aR aL) jjR jjL (Hjj : CgjParRel Job jjR jjL) j
    tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (ScheduleWithJitter.jitter_has_passed aR jjR j tR) (I.Prosa_Classic_Model_Schedule_Global_Jitter_Schedule_ScheduleWithJitter_jitter_has_passed Job dJ aL jjL j tL).
Proof. exact (ct_decide_le _ _ _ _ (ScheduleWithJitter_actual_arrival_correspondence aR aL Ha jjR jjL Hjj j) Ht). Qed.

Theorem ScheduleWithJitter_actual_arrival_before_correspondence aR aL (Ha : CgjParRel Job aR aL) jjR jjL (Hjj : CgjParRel Job jjR jjL) j
    tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (ScheduleWithJitter.actual_arrival_before aR jjR j tR) (I.Prosa_Classic_Model_Schedule_Global_Jitter_Schedule_ScheduleWithJitter_actual_arrival_before Job dJ aL jjL j tL).
Proof. exact (ct_decide_lt _ _ _ _ (ScheduleWithJitter_actual_arrival_correspondence aR aL Ha jjR jjL Hjj j) Ht). Qed.

Section Sched.
Variables (nR : nat) (nL : Lean.Nat).
Hypothesis Hn : SubNatRel nR nL.
Variables (sR : Schedule.schedule Job nR)
  (sL : I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_schedule Job dJ nL).
Hypothesis Hs : CgjSchedRel Job nR nL sR sL.

Theorem ScheduleWithJitter_pending_correspondence aR aL (Ha : CgjParRel Job aR aL) cR cL (Hc : CgjParRel Job cR cL)
    jjR jjL (Hjj : CgjParRel Job jjR jjL) j tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (ScheduleWithJitter.pending aR cR jjR sR j tR) (I.Prosa_Classic_Model_Schedule_Global_Jitter_Schedule_ScheduleWithJitter_pending Job dJ aL cL jjL nL sL j tL).
Proof.
  exact (ct_bool_and _ _ _ _ (ScheduleWithJitter_jitter_has_passed_correspondence aR aL Ha jjR jjL Hjj j tR tL Ht)
           (ct_bool_not _ _ (cgj_GS_completed Job nR nL Hn sR sL Hs cR cL Hc j tR tL Ht))).
Qed.

Theorem ScheduleWithJitter_backlogged_correspondence aR aL (Ha : CgjParRel Job aR aL) cR cL (Hc : CgjParRel Job cR cL)
    jjR jjL (Hjj : CgjParRel Job jjR jjL) j tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (ScheduleWithJitter.backlogged aR cR jjR sR j tR) (I.Prosa_Classic_Model_Schedule_Global_Jitter_Schedule_ScheduleWithJitter_backlogged Job dJ aL cL jjL nL sL j tL).
Proof.
  exact (ct_bool_and _ _ _ _ (ScheduleWithJitter_pending_correspondence aR aL Ha cR cL Hc jjR jjL Hjj j tR tL Ht)
           (ct_bool_not _ _ (cgj_GS_scheduled Job nR nL Hn sR sL Hs j tR tL Ht))).
Qed.

Theorem ScheduleWithJitter_jobs_execute_after_jitter_correspondence aR aL (Ha : CgjParRel Job aR aL) jjR jjL (Hjj : CgjParRel Job jjR jjL) :
  PropSPropRel (ScheduleWithJitter.jobs_execute_after_jitter aR jjR sR) (I.Prosa_Classic_Model_Schedule_Global_Jitter_Schedule_ScheduleWithJitter_jobs_execute_after_jitter Job dJ aL jjL nL sL).
Proof.
  apply: ct_forall_identity => j. apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (ct_bool_truth _ _ (cgj_GS_scheduled Job nR nL Hn sR sL Hs j tR tL Ht)).
  exact (ct_bool_truth _ _ (ScheduleWithJitter_jitter_has_passed_correspondence aR aL Ha jjR jjL Hjj j tR tL Ht)).
Qed.
End Sched.
End Defs.

Section TaskDefs.
Variables (Task Job : eqType) (nR : nat) (nL : Lean.Nat).
Hypothesis Hn : SubNatRel nR nL.
Notation dT := (ct_decidable_eq Task).
Notation dJ := (ct_decidable_eq Job).
Variables (sR : Schedule.schedule Job nR)
  (sL : I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_schedule Job dJ nL).
Hypothesis Hs : CgjSchedRel Job nR nL sR sL.
Variable job_task : Job -> Task.

Theorem ScheduleOfSporadicTaskWithJitter_task_scheduled_on_correspondence tsk oR oL (Ho : CoOrdRel nR nL oR oL) tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (ScheduleOfSporadicTaskWithJitter.task_scheduled_on job_task sR tsk oR tR) (I.Prosa_Classic_Model_Schedule_Global_Jitter_Schedule_ScheduleOfSporadicTaskWithJitter_task_scheduled_on Task Job dT dJ job_task nL sL tsk oL tL).
Proof.
  refine (cgj_trs (Hs oR oL Ho tR tL Ht)
            (fun z => CtBoolRel (ScheduleOfSporadicTaskWithJitter.task_scheduled_on job_task sR tsk oR tR)
                        (match z with
                         | I.Option_some j => I.Decidable_decide (Lean.eq (job_task j) tsk) (dT (job_task j) tsk)
                         | I.Option_none => I.Bool_false end)) _).
  rewrite /ScheduleOfSporadicTaskWithJitter.task_scheduled_on. destruct (sR oR tR) as [x|].
  - exact (ct_decide_eq Task (job_task x) tsk).
  - exact (ct_bool_canonical false).
Qed.

Theorem ScheduleOfSporadicTaskWithJitter_task_is_scheduled_correspondence tsk tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (ScheduleOfSporadicTaskWithJitter.task_is_scheduled job_task sR tsk tR) (I.Prosa_Classic_Model_Schedule_Global_Jitter_Schedule_ScheduleOfSporadicTaskWithJitter_task_is_scheduled Task Job dT dJ job_task nL sL tsk tL).
Proof.
  apply: (co_exists_rel nR nL Hn). intros oR oL Ho.
  exact (ScheduleOfSporadicTaskWithJitter_task_scheduled_on_correspondence tsk oR oL Ho tR tL Ht).
Qed.

Theorem ScheduleOfSporadicTaskWithJitter_jobs_of_task_scheduled_between_correspondence tsk t1R t1L t2R t2L
    (H1 : SubNatRel t1R t1L) (H2 : SubNatRel t2R t2L) :
  ClListRel cid (ScheduleOfSporadicTaskWithJitter.jobs_of_task_scheduled_between job_task sR tsk t1R t2R)
    (I.Prosa_Classic_Model_Schedule_Global_Jitter_Schedule_ScheduleOfSporadicTaskWithJitter_jobs_of_task_scheduled_between Task Job dT dJ job_task nL sL tsk t1L t2L).
Proof.
  apply: coq_eq_to_imported_eq.
  refine (Logic.eq_trans (cl_filter cid (fun j => job_task j == tsk)
                            (fun j => I.Decidable_decide (Lean.eq (job_task j) tsk) (dT (job_task j) tsk))
                            (fun j => ct_decide_eq Task (job_task j) tsk) _) _).
  exact (f_equal (I.List_filter Job (fun j => I.Decidable_decide (Lean.eq (job_task j) tsk) (dT (job_task j) tsk)))
           (Logic.eq_sym (cl_list_logic _ _ _ (cgj_GS_jobs_scheduled_between Job nR nL Hn sR sL Hs _ _ _ _ H1 H2)))).
Qed.

Theorem ScheduleOfSporadicTaskWithJitter_jobs_of_same_task_dont_execute_in_parallel_correspondence :
  PropSPropRel (ScheduleOfSporadicTaskWithJitter.jobs_of_same_task_dont_execute_in_parallel job_task sR)
    (I.Prosa_Classic_Model_Schedule_Global_Jitter_Schedule_ScheduleOfSporadicTaskWithJitter_jobs_of_same_task_dont_execute_in_parallel Task Job dT dJ job_task nL sL).
Proof.
  apply: ct_forall_identity => j. apply: ct_forall_identity => j'. apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (ct_eq_rel Task (job_task j) (job_task j')).
  apply: ct_imp; first exact (ct_bool_truth _ _ (cgj_GS_scheduled Job nR nL Hn sR sL Hs j tR tL Ht)).
  apply: ct_imp; first exact (ct_bool_truth _ _ (cgj_GS_scheduled Job nR nL Hn sR sL Hs j' tR tL Ht)).
  exact (ct_eq_rel Job j j').
Qed.
End TaskDefs.

(* ------------------------------------------------------------------ *)
(** * Statements *)

Notation SCH := cgj_GS_scheduled.
Notation c0 := (sub_nat_rel_canonical 0).

Definition src_scheduled_implies_pending (Job : eqType) : Prop :=
  ltac:(type_of_term (@ScheduleWithJitter.scheduled_implies_pending Job)).
Definition tgt_scheduled_implies_pending (Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Model_Schedule_Global_Jitter_Schedule_ScheduleWithJitter_scheduled_implies_pending Job (ct_decidable_eq Job))).

Theorem ScheduleWithJitter_scheduled_implies_pending_correspondence (Job : eqType) :
  PropSPropRel (src_scheduled_implies_pending Job) (tgt_scheduled_implies_pending Job).
Proof.
  unfold src_scheduled_implies_pending, tgt_scheduled_implies_pending.
  apply: cgj_forall_par => aR aL Ha. apply: cgj_forall_par => cR cL Hc. apply: cgj_forall_par => jjR jjL Hjj.
  apply: cgj_forall_ncpus_sched => nR nL Hn sR sL Hs.
  apply: ct_imp; first exact (ScheduleWithJitter_jobs_execute_after_jitter_correspondence Job nR nL Hn sR sL Hs aR aL Ha jjR jjL Hjj).
  apply: ct_imp; first exact (cgj_GS_completed_jobs_dont_execute Job nR nL Hn sR sL Hs cR cL Hc).
  apply: ct_forall_identity => j. apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (ct_bool_truth _ _ (SCH Job nR nL Hn sR sL Hs j tR tL Ht)).
  exact (ct_bool_truth _ _ (ScheduleWithJitter_pending_correspondence Job nR nL Hn sR sL Hs aR aL Ha cR cL Hc jjR jjL Hjj j tR tL Ht)).
Qed.

Definition src_arrival_before_jitter (Job : eqType) : Prop :=
  ltac:(type_of_term (@ScheduleWithJitter.arrival_before_jitter Job)).
Definition tgt_arrival_before_jitter (Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Model_Schedule_Global_Jitter_Schedule_ScheduleWithJitter_arrival_before_jitter Job (ct_decidable_eq Job))).

Theorem ScheduleWithJitter_arrival_before_jitter_correspondence (Job : eqType) :
  PropSPropRel (src_arrival_before_jitter Job) (tgt_arrival_before_jitter Job).
Proof.
  unfold src_arrival_before_jitter, tgt_arrival_before_jitter.
  apply: cgj_forall_par => aR aL Ha. apply: cgj_forall_par => jjR jjL Hjj.
  apply: cgj_forall_ncpus_sched => nR nL Hn sR sL Hs.
  apply: ct_imp; first exact (ScheduleWithJitter_jobs_execute_after_jitter_correspondence Job nR nL Hn sR sL Hs aR aL Ha jjR jjL Hjj).
  exact (cgj_GS_jobs_must_arrive_to_execute Job nR nL Hn sR sL Hs aR aL Ha).
Qed.

Definition src_service_before_jitter_zero (Job : eqType) : Prop :=
  ltac:(type_of_term (@ScheduleWithJitter.service_before_jitter_zero Job)).
Definition tgt_service_before_jitter_zero (Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Model_Schedule_Global_Jitter_Schedule_ScheduleWithJitter_service_before_jitter_zero Job (ct_decidable_eq Job))).

Theorem ScheduleWithJitter_service_before_jitter_zero_correspondence (Job : eqType) :
  PropSPropRel (src_service_before_jitter_zero Job) (tgt_service_before_jitter_zero Job).
Proof.
  unfold src_service_before_jitter_zero, tgt_service_before_jitter_zero.
  apply: cgj_forall_par => aR aL Ha. apply: cgj_forall_par => jjR jjL Hjj.
  apply: cgj_forall_ncpus_sched => nR nL Hn sR sL Hs.
  apply: ct_imp; first exact (ScheduleWithJitter_jobs_execute_after_jitter_correspondence Job nR nL Hn sR sL Hs aR aL Ha jjR jjL Hjj).
  apply: ct_forall_identity => j. apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (sub_nat_lt_correspondence _ _ _ _ Ht (sub_add_correspondence _ _ _ _ (Ha j) (Hjj j))).
  exact (sub_nat_eq_correspondence _ _ _ _ (cgj_GS_service_at Job nR nL Hn sR sL Hs j tR tL Ht) c0).
Qed.

Definition src_cumulative_service_before_jitter_zero (Job : eqType) : Prop :=
  ltac:(type_of_term (@ScheduleWithJitter.cumulative_service_before_jitter_zero Job)).
Definition tgt_cumulative_service_before_jitter_zero (Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Model_Schedule_Global_Jitter_Schedule_ScheduleWithJitter_cumulative_service_before_jitter_zero Job (ct_decidable_eq Job))).

Theorem ScheduleWithJitter_cumulative_service_before_jitter_zero_correspondence (Job : eqType) :
  PropSPropRel (src_cumulative_service_before_jitter_zero Job) (tgt_cumulative_service_before_jitter_zero Job).
Proof.
  unfold src_cumulative_service_before_jitter_zero, tgt_cumulative_service_before_jitter_zero.
  apply: cgj_forall_par => aR aL Ha. apply: cgj_forall_par => jjR jjL Hjj.
  apply: cgj_forall_ncpus_sched => nR nL Hn sR sL Hs.
  apply: ct_imp; first exact (ScheduleWithJitter_jobs_execute_after_jitter_correspondence Job nR nL Hn sR sL Hs aR aL Ha jjR jjL Hjj).
  apply: ct_forall_identity => j. apply: ct_forall_nat => t1R t1L H1. apply: ct_forall_nat => t2R t2L H2.
  apply: ct_imp; first exact (sub_nat_le_correspondence _ _ _ _ H2 (sub_add_correspondence _ _ _ _ (Ha j) (Hjj j))).
  exact (sub_nat_eq_correspondence _ _ _ _ (cgj_ico _ _ _ _ _ _ H1 H2 (cgj_service_at_fun Job nR nL Hn sR sL Hs j)) c0).
Qed.

Definition src_cumulative_service_le_task_cost (Task Job : eqType) : Prop :=
  forall task_cost task_deadline : Task -> Time.time,
    ltac:(type_of_term (@ScheduleOfSporadicTaskWithJitter.cumulative_service_le_task_cost Task task_cost task_deadline Job)).
Definition tgt_cumulative_service_le_task_cost (Task Job : eqType) : SProp :=
  forall task_cost task_deadline : Task -> Lean.Nat,
    ltac:(type_of_term (I.Prosa_Classic_Model_Schedule_Global_Jitter_Schedule_ScheduleOfSporadicTaskWithJitter_cumulative_service_le_task_cost Task (ct_decidable_eq Task) task_cost task_deadline
                          Job (ct_decidable_eq Job))).

Theorem ScheduleOfSporadicTaskWithJitter_cumulative_service_le_task_cost_correspondence (Task Job : eqType) :
  PropSPropRel (src_cumulative_service_le_task_cost Task Job) (tgt_cumulative_service_le_task_cost Task Job).
Proof.
  unfold src_cumulative_service_le_task_cost, tgt_cumulative_service_le_task_cost.
  apply: cgj_forall_par => tcR tcL Htc. apply: cgj_forall_par => tdR tdL Htd.
  apply: cgj_forall_par => cR cL Hc. apply: cgj_forall_par => dR dL Hd. apply: ct_forall_identity => job_task.
  apply: cgj_forall_ncpus_sched => nR nL Hn sR sL Hs.
  apply: ct_imp; first exact (cgj_GS_completed_jobs_dont_execute Job nR nL Hn sR sL Hs cR cL Hc).
  apply: ct_forall_identity => tsk. apply: ct_forall_identity => j.
  apply: ct_imp; first exact (ct_eq_rel Task (job_task j) tsk).
  apply: ct_imp; first exact (cgj_J_valid_sporadic_job Task Job tcR tcL tdR tdL Htc Htd cR cL dR dL Hc Hd job_task j).
  apply: ct_forall_nat => tR tL Ht. apply: ct_forall_nat => t'R t'L Ht'.
  exact (sub_nat_le_correspondence _ _ _ _ (cgj_GS_service_during Job nR nL Hn sR sL Hs j tR tL t'R t'L Ht Ht') (Htc tsk)).
Qed.
