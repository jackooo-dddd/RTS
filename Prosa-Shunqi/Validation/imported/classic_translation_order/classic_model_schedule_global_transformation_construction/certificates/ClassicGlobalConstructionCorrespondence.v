From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq fintype bigop.
From prosa Require Import classic.model.time classic.model.schedule.global.basic.schedule classic.model.schedule.global.transformation.construction.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedClassicGlobalConstruction.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence ClassicGlobalConstructionBase ClassicGlobalConstructionList ClassicGlobalConstructionOrd.

Module I := ImportedClassicGlobalConstruction.
Local Open Scope nat_scope.

(** Certificates for [classic/model/schedule/global/transformation/construction.v] (ProsaBuddy classic, commit f692cb7).

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

Lemma cgc_forall_cover (A B : Type) (Rel : A -> B -> SProp) (toB : A -> B) (toA : B -> A)
    (HB : forall a, Rel a (toB a)) (HA : forall b, Rel (toA b) b) (PR : A -> Prop) (PL : B -> SProp) :
  (forall a b, Rel a b -> PropSPropRel (PR a) (PL b)) -> PropSPropRel (forall a, PR a) (forall b, PL b).
Proof.
  intro H. apply prop_sprop_rel_intro.
  - intros HR b. exact (prop_to_sprop _ _ (H _ _ (HA b)) (HR _)).
  - intro HL. apply strictly_inhabits. intro a. exact (sprop_to_prop _ _ (H _ _ (HB a)) (HL _)).
Qed.

Lemma cgc_mem (T : eqType) x s sL : ClListRel cid s sL ->
  PropSPropRel (x \in s) (I.Membership_mem T (I.List T) (I.List_instMembership T) sL x).
Proof. exact (cl_mem_rel_list T T cid cid (fun _ => Logic.eq_refl _) x s sL). Qed.

Lemma cgc_uniq (T : eqType) s sL : ClListRel cid s sL -> PropSPropRel (uniq s) (I.List_Nodup T sL).
Proof. exact (cl_uniq_rel_list T T cid cid (fun _ => Logic.eq_refl _) (fun _ => Logic.eq_refl _) s sL). Qed.

Lemma cgc_list_size (T : Type) s sL : ClListRel (B := T) cid s sL -> SubNatRel (size s) (I.List_length T sL).
Proof. intro H. destruct H. exact (cl_size cid s). Qed.

Lemma cgc_lean_eq_logic (A : Type) (x y : A) : Lean.eq x y -> Logic.eq x y.
Proof. exact (imported_eq_to_coq_eq x y). Qed.

(** Transport along the target equality (definitional UIP), into relevant and SProp-valued families. *)
Definition cgc_tr {A : Type} {x y : A} (E : Lean.eq x y) (P : A -> Type) (h : P x) : P y :=
  match E in Lean.eq _ z return P z with Lean.eq_refl => h end.
Definition cgc_trs {A : Type} {x y : A} (E : Lean.eq x y) (P : A -> SProp) (h : P x) : P y :=
  match E in Lean.eq _ z return P z with Lean.eq_refl => h end.

(** Options: [cl_opt] is injective and [x == Some j] is [cl_opt x = some j]. *)
Lemma cgc_opt_inj (A : Type) (o1 o2 : option A) : Logic.eq (cl_opt o1) (cl_opt o2) -> Logic.eq o1 o2.
Proof. intro E. by rewrite -(cl_unopt_opt o1) -(cl_unopt_opt o2) E. Qed.

Lemma cgc_opt_eq_rel (A : Type) (o1 o2 : option A) :
  PropSPropRel (Logic.eq o1 o2) (Lean.eq (cl_opt o1) (cl_opt o2)).
Proof.
  apply prop_sprop_rel_intro.
  - intro E. rewrite E. exact (@Lean.eq_refl _ _).
  - intro E. apply strictly_inhabits. exact (cgc_opt_inj A o1 o2 (imported_eq_to_coq_eq _ _ E)).
Qed.

Lemma cgc_opt_eqb_rel (A : eqType) (o1 o2 : option A) :
  PropSPropRel (is_true (o1 == o2)) (Lean.eq (cl_opt o1) (cl_opt o2)).
Proof.
  apply prop_sprop_rel_intro.
  - move=> /eqP E. rewrite E. exact (@Lean.eq_refl _ _).
  - intro E. apply strictly_inhabits. apply/eqP. exact (cgc_opt_inj A o1 o2 (imported_eq_to_coq_eq _ _ E)).
Qed.

(* ------------------------------------------------------------------ *)
(** * Half-open sums and concatenations over [nat] (as in the accepted sum / arrival_sequence certificates) *)

Fixpoint cgc_natl (s : seq nat) : I.List_inst1 Lean.Nat :=
  match s with [::] => I.List_nil_inst1 _ | x :: s' => I.List_cons_inst1 _ (sub_nat_to_imported x) (cgc_natl s') end.

Lemma cgc_iota_range : forall n s,
  Logic.eq (I.List_range' (sub_nat_to_imported s) (sub_nat_to_imported n) (Lean.Nat_succ Lean.Nat_zero)) (cgc_natl (iota s n)).
Proof.
  elim => [|n IH] s; first reflexivity.
  change (Logic.eq (I.List_cons_inst1 _ (sub_nat_to_imported s)
      (I.List_range' (sub_nat_to_imported (S s)) (sub_nat_to_imported n) (Lean.Nat_succ Lean.Nat_zero)))
    (I.List_cons_inst1 _ (sub_nat_to_imported s) (cgc_natl (iota (S s) n)))).
  by rewrite IH.
Qed.

Lemma cgc_foldr_add (f : Lean.Nat -> Lean.Nat) (g : nat -> nat) (Hf : forall k, Logic.eq (f (sub_nat_to_imported k)) (sub_nat_to_imported (g k))) :
  forall s, Logic.eq (I.List_foldr_inst3 Lean.Nat Lean.Nat Lean.Nat_add Lean.Nat_zero (I.List_map_inst3 Lean.Nat Lean.Nat f (cgc_natl s)))
                     (sub_nat_to_imported (foldr addn 0 (map g s))).
Proof.
  elim => [|k s IH] //=.
  change (Logic.eq (Lean.Nat_add (f (sub_nat_to_imported k))
            (I.List_foldr_inst3 Lean.Nat Lean.Nat Lean.Nat_add Lean.Nat_zero (I.List_map_inst3 Lean.Nat Lean.Nat f (cgc_natl s))))
         (sub_nat_to_imported (g k + foldr addn 0 (map g s)))).
  rewrite IH Hf. exact (imported_eq_to_coq_eq _ _ (sub_add_canonical _ _)).
Qed.

Lemma cgc_big_fold (xs : seq nat) (F : nat -> nat) : Logic.eq (\sum_(i <- xs) F i) (foldr addn 0 (map F xs)).
Proof. elim: xs => [|x xs IH]; first by rewrite big_nil. by rewrite big_cons IH. Qed.

Definition CgcFunRel (FR : nat -> nat) (FL : Lean.Nat -> Lean.Nat) : SProp :=
  forall kR kL, SubNatRel kR kL -> SubNatRel (FR kR) (FL kL).

Lemma cgc_fun_canonical FR FL (HF : CgcFunRel FR FL) k : Logic.eq (FL (sub_nat_to_imported k)) (sub_nat_to_imported (FR k)).
Proof. exact (co_nat_logic _ _ (HF _ _ (sub_nat_rel_canonical k))). Qed.

Lemma cgc_ico mR mL nR nL FR FL (Hm : SubNatRel mR mL) (Hn : SubNatRel nR nL) (HF : CgcFunRel FR FL) :
  SubNatRel (\sum_(mR <= i < nR) FR i)
    (I.List_foldr_inst3 Lean.Nat Lean.Nat Lean.Nat_add Lean.Nat_zero
       (I.List_map_inst3 Lean.Nat Lean.Nat FL (I.List_range' mL (I.Nat_sub nL mL) (Lean.Nat_succ Lean.Nat_zero)))).
Proof.
  rewrite (co_nat_logic _ _ Hm) (co_nat_logic _ _ Hn).
  have -> : Logic.eq (I.Nat_sub (sub_nat_to_imported nR) (sub_nat_to_imported mR)) (sub_nat_to_imported (nR - mR))
    := ct_sub_canonical nR mR.
  rewrite cgc_iota_range.
  apply: coq_eq_to_imported_eq. apply: Logic.eq_sym. rewrite (cgc_foldr_add FL FR (cgc_fun_canonical FR FL HF)).
  by rewrite cgc_big_fold.
Qed.

Lemma cgc_map_natl {B : Type} (f : Lean.Nat -> B) : forall s,
  Logic.eq (I.List_map_inst1 Lean.Nat B f (cgc_natl s)) (cl_map (fun k => f (sub_nat_to_imported k)) s).
Proof.
  elim => [|k s IH] //=.
  change (Logic.eq (I.List_cons B (f (sub_nat_to_imported k)) (I.List_map_inst1 Lean.Nat B f (cgc_natl s)))
                   (I.List_cons B (f (sub_nat_to_imported k)) (cl_map (fun k => f (sub_nat_to_imported k)) s))).
  by rewrite IH.
Qed.

Lemma cgc_big_seq {A : Type} (F : nat -> seq A) : forall s : seq nat,
  Logic.eq (\big[cat/[::]]_(i <- s) F i) (flatten (map F s)).
Proof. elim => [|x s IH]; first by rewrite big_nil. by rewrite big_cons IH. Qed.

Definition CgcNatFamRel (A : Type) (fR : nat -> seq A) (fL : Lean.Nat -> I.List A) : SProp :=
  forall nR nL, SubNatRel nR nL -> ClListRel cid (fR nR) (fL nL).

Lemma cgc_bigcat_nat_rel (A : Type) fR fL (Hf : CgcNatFamRel A fR fL) mR mL nR nL :
  SubNatRel mR mL -> SubNatRel nR nL ->
  ClListRel cid (\big[cat/[::]]_(mR <= t < nR) fR t) (I.Prosa_Util_Notation_bigCat A mL nL fL).
Proof.
  intros Hm Hn. have E1 := co_nat_logic _ _ Hm. have E2 := co_nat_logic _ _ Hn. subst mL nL.
  apply: coq_eq_to_imported_eq. apply: Logic.eq_sym.
  rewrite (imported_eq_to_coq_eq _ _ (I.Prosa_Validation_ClassicGlobalConstructionInterface_bigCat_range'
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
  rewrite cgc_big_seq /index_iota Hi -map_comp.
  reflexivity.
Qed.

Lemma cgc_notin_target (T : eqType) x s : Logic.eq (x \in s) false ->
  I.Not (I.Membership_mem T (I.List T) (I.List_instMembership T) (cl_map cid s) x).
Proof.
  intros Hx H. apply: ct_coq_false_to_target.
  have Hm := sprop_to_prop _ _ (cgc_mem T x s _ (cl_lean_eq _ _ _ (Logic.eq_refl _))) H.
  rewrite Hx in Hm. discriminate.
Qed.

(** [undup] against Mathlib's [List.dedup] (step equations exported with their proofs). *)
Lemma cgc_undup_rel (T : eqType) : forall s sL, ClListRel cid s sL ->
  ClListRel cid (undup s) (I.List_dedup T (ct_decidable_eq T) sL).
Proof.
  intros s sL Hs. have E := cl_list_logic _ _ _ Hs. subst sL. apply: coq_eq_to_imported_eq. clear Hs.
  elim: s => [|x s IH].
  - exact (Logic.eq_sym (imported_eq_to_coq_eq _ _ (I.Prosa_Validation_ClassicGlobalConstructionInterface_dedup_nil T (ct_decidable_eq T)))).
  - change (Logic.eq (cl_map cid (if x \in s then undup s else x :: undup s))
      (I.List_dedup T (ct_decidable_eq T) (I.List_cons T x (cl_map cid s)))).
    case Hx: (x \in s).
    + rewrite (imported_eq_to_coq_eq _ _ (I.Prosa_Validation_ClassicGlobalConstructionInterface_dedup_cons_mem
                 T (ct_decidable_eq T) x (cl_map cid s)
                 (prop_to_sprop _ _ (cgc_mem T x s _ (cl_lean_eq _ _ _ (Logic.eq_refl _))) Hx))).
      exact IH.
    + rewrite (imported_eq_to_coq_eq _ _ (I.Prosa_Validation_ClassicGlobalConstructionInterface_dedup_cons_not_mem
                 T (ct_decidable_eq T) x (cl_map cid s) (cgc_notin_target T x s Hx))).
      change (Logic.eq (I.List_cons T x (cl_map cid (undup s))) (I.List_cons T x (I.List_dedup T (ct_decidable_eq T) (cl_map cid s)))).
      by rewrite IH.
Qed.

(* ------------------------------------------------------------------ *)
(** * Schedules, arrival sequences, parameters *)

Definition CgcParRel (T : Type) (pR : T -> nat) (pL : T -> Lean.Nat) : SProp := forall x, SubNatRel (pR x) (pL x).

Lemma cgc_forall_par (T : Type) (PR : (T -> nat) -> Prop) (PL : (T -> Lean.Nat) -> SProp) :
  (forall pR pL, CgcParRel T pR pL -> PropSPropRel (PR pR) (PL pL)) -> PropSPropRel (forall p, PR p) (forall p, PL p).
Proof.
  exact (cgc_forall_cover _ _ (CgcParRel T) (fun pR j => sub_nat_to_imported (pR j)) (fun pL j => sub_nat_to_rocq (pL j))
           (fun pR j => sub_nat_rel_canonical (pR j)) (fun pL j => sub_nat_rel_surjective (pL j)) PR PL).
Qed.

Section Sched.
Variables (Job : eqType) (nR : nat) (nL : Lean.Nat).
Hypothesis Hn : SubNatRel nR nL.
Notation dJ := (ct_decidable_eq Job).
Notation LSched := (I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_schedule Job dJ nL).

Definition CgcSchedRel (sR : Schedule.schedule Job nR) (sL : LSched) : SProp :=
  forall oR oL, CoOrdRel nR nL oR oL -> forall tR tL, SubNatRel tR tL -> Lean.eq (cl_opt (sR oR tR)) (sL oL tL).

Definition cgc_sched_to_target (sR : Schedule.schedule Job nR) : LSched :=
  fun oL tL => cl_opt (sR (co_fin_to_ord nR nL Hn oL) (sub_nat_to_rocq tL)).

Definition cgc_sched_to_source (sL : LSched) : Schedule.schedule Job nR :=
  fun oR tR => cl_unopt (sL (co_ord_to_fin nR nL Hn oR) (sub_nat_to_imported tR)).

Lemma cgc_sched_canonical sR : CgcSchedRel sR (cgc_sched_to_target sR).
Proof.
  intros oR oL Ho tR tL Ht. apply: coq_eq_to_imported_eq. rewrite /cgc_sched_to_target (co_nat_input _ _ Ht).
  by rewrite (co_ord_eq _ _ _ _ _ Ho (co_ord_surjective nR nL Hn oL)).
Qed.

Lemma cgc_sched_surjective sL : CgcSchedRel (cgc_sched_to_source sL) sL.
Proof.
  intros oR oL Ho tR tL Ht. apply: coq_eq_to_imported_eq. rewrite /cgc_sched_to_source cl_opt_unopt.
  rewrite (co_nat_logic _ _ Ht). by rewrite (co_fin_rel_eq _ _ _ _ _ (co_ord_canonical nR nL Hn oR) Ho).
Qed.

Lemma cgc_forall_sched (PR : Schedule.schedule Job nR -> Prop) (PL : LSched -> SProp) :
  (forall sR sL, CgcSchedRel sR sL -> PropSPropRel (PR sR) (PL sL)) -> PropSPropRel (forall s, PR s) (forall s, PL s).
Proof. exact (cgc_forall_cover _ _ CgcSchedRel cgc_sched_to_target cgc_sched_to_source cgc_sched_canonical cgc_sched_surjective PR PL). Qed.

End Sched.

(* ------------------------------------------------------------------ *)
(** * Definitions *)

Section Defs.
Variables (Job : eqType) (nR : nat) (nL : Lean.Nat).
Hypothesis Hn : SubNatRel nR nL.
Notation dJ := (ct_decidable_eq Job).
Variables (sR : Schedule.schedule Job nR)
  (sL : I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_schedule Job dJ nL).
Hypothesis Hs : CgcSchedRel Job nR nL sR sL.

Lemma cgc_GS_scheduled_on j oR oL (Ho : CoOrdRel nR nL oR oL) tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (Schedule.scheduled_on sR j oR tR)
    (I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_scheduled_on Job dJ nL sL j oL tL).
Proof.
  apply: ct_decide_bool.
  exact (cgc_tr (Hs oR oL Ho tR tL Ht) (fun z => PropSPropRel (sR oR tR == Some j) (Lean.eq z (cl_opt (Some j))))
           (cgc_opt_eqb_rel Job (sR oR tR) (Some j))).
Qed.

Lemma cgc_GS_service_at j tR tL (Ht : SubNatRel tR tL) :
  SubNatRel (Schedule.service_at sR j tR)
    (I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_service_at Job dJ nL sL j tL).
Proof.
  apply: coq_eq_to_imported_eq.
  rewrite (imported_eq_to_coq_eq _ _ (I.Prosa_Validation_ClassicGlobalConstructionInterface_service_at_sum Job dJ nL sL j tL)).
  apply: imported_eq_to_coq_eq.
  rewrite /Schedule.service_at big_mkcond /=.
  apply: (co_sum_rel nR nL Hn). intros oR oL Ho.
  have H := cgc_GS_scheduled_on j oR oL Ho tR tL Ht.
  rewrite (ct_bool_rel_logic _ _ H). destruct (Schedule.scheduled_on sR j oR tR).
  - exact (sub_nat_rel_canonical 1).
  - exact (sub_nat_rel_canonical 0).
Qed.

Lemma cgc_service_at_fun j : CgcFunRel (fun t => Schedule.service_at sR j t)
    (fun t => I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_service_at Job dJ nL sL j t).
Proof. intros kR kL Hk. exact (cgc_GS_service_at j kR kL Hk). Qed.

Lemma cgc_GS_service j tR tL (Ht : SubNatRel tR tL) :
  SubNatRel (Schedule.service sR j tR)
    (I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_service Job dJ nL sL j tL).
Proof. exact (cgc_ico 0 _ tR tL _ _ (sub_nat_rel_canonical 0) Ht (cgc_service_at_fun j)). Qed.

End Defs.

Section TaskDefs.
Variables (Task Job : eqType) (nR : nat) (nL : Lean.Nat).
Hypothesis Hn : SubNatRel nR nL.
Notation dT := (ct_decidable_eq Task).
Notation dJ := (ct_decidable_eq Job).
Variables (sR : Schedule.schedule Job nR)
  (sL : I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_schedule Job dJ nL).
Hypothesis Hs : CgcSchedRel Job nR nL sR sL.
Variable job_task : Job -> Task.

End TaskDefs.

Lemma cgc_GS_processor nR nL (Hn : SubNatRel nR nL) :
  And (forall o : Schedule.processor nR, CoOrdRel nR nL o (co_ord_to_fin nR nL Hn o))
      (forall o : I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_processor nL,
         CoOrdRel nR nL (co_fin_to_ord nR nL Hn o) o).
Proof. exact (And_intro _ _ (co_ord_canonical nR nL Hn) (co_ord_surjective nR nL Hn)). Qed.

Lemma cgc_GS_schedule (Job : eqType) nR nL (Hn : SubNatRel nR nL) :
  And (forall s : Schedule.schedule Job nR, CgcSchedRel Job nR nL s (cgc_sched_to_target Job nR nL Hn s))
      (forall s : I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_schedule Job (ct_decidable_eq Job) nL,
         CgcSchedRel Job nR nL (cgc_sched_to_source Job nR nL Hn s) s).
Proof. exact (And_intro _ _ (cgc_sched_canonical Job nR nL Hn) (cgc_sched_surjective Job nR nL Hn)). Qed.

(* ------------------------------------------------------------------ *)
(** * Statements *)

(** The common prefix [forall num_cpus (sched : schedule Job num_cpus)]. *)
Lemma cgc_forall_ncpus_sched (Job : eqType)
    (PR : forall n : nat, Schedule.schedule Job n -> Prop)
    (PL : forall n : Lean.Nat, I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_schedule Job (ct_decidable_eq Job) n -> SProp) :
  (forall nR nL (Hn : SubNatRel nR nL) sR sL, CgcSchedRel Job nR nL sR sL -> PropSPropRel (PR nR sR) (PL nL sL)) ->
  PropSPropRel (forall n s, PR n s) (forall n s, PL n s).
Proof.
  intro H. apply: ct_forall_nat => nR nL Hn. exact (cgc_forall_sched Job nR nL Hn _ _ (H nR nL Hn)).
Qed.



(* ------------------------------------------------------------------ *)
(** * Options and transports *)

Lemma cgc_opt_rel_eq (A : Type) (o1 o2 : option A) l1 l2 :
  Lean.eq (cl_opt o1) l1 -> Lean.eq (cl_opt o2) l2 -> PropSPropRel (Logic.eq o1 o2) (Lean.eq l1 l2).
Proof.
  intros H1 H2. destruct H1. destruct H2. apply prop_sprop_rel_intro.
  - intro E. rewrite E. exact (@Lean.eq_refl _ _).
  - intro E. apply strictly_inhabits. exact (cgc_opt_inj A o1 o2 (imported_eq_to_coq_eq _ _ E)).
Qed.

Definition cgc_lsym {A : Type} {x y : A} (E : Lean.eq x y) : Lean.eq y x :=
  match E in Lean.eq _ z return Lean.eq z x with Lean.eq_refl => @Lean.eq_refl _ _ end.

Lemma cgc_src_transport {A : Type} (P : A -> SProp) (x y : A) : Logic.eq x y -> P x -> P y.
Proof. intro E. destruct E. exact (fun p => p). Qed.

(* ------------------------------------------------------------------ *)
(** * Construction from prefixes, specialised at related inputs

    As in the accepted v0.6 [implementation/facts/generic_schedule.v] certificate and the accepted classic
    uniprocessor construction certificate: the construction function [build_schedule : schedule Job num_cpus ->
    schedule Job num_cpus] is a higher-order input; the certificates below are stated for any source function and any
    Lean function mapping related schedules to related schedules ([Hbuild]), at related processor counts ([Hn]) and
    related base schedules ([Hbase]).  Inside the statements every quantified schedule, processor, instant and job is
    covered in both directions. *)

Section Construction.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).
Variables (nR : nat) (nL : Lean.Nat).
Hypothesis Hn : SubNatRel nR nL.
Notation LSched := (I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_schedule Job dJ nL).
Variable buildR : Schedule.schedule Job nR -> Schedule.schedule Job nR.
Variable buildL : LSched -> LSched.
Hypothesis Hbuild : forall sR sL, CgcSchedRel Job nR nL sR sL -> CgcSchedRel Job nR nL (buildR sR) (buildL sL).
Variables (baseR : Schedule.schedule Job nR) (baseL : LSched).
Hypothesis Hbase : CgcSchedRel Job nR nL baseR baseL.

Theorem ScheduleConstruction_update_schedule_correspondence prevR prevL (Hprev : CgcSchedRel Job nR nL prevR prevL) mR mL (Hm : SubNatRel mR mL) :
  CgcSchedRel Job nR nL (@ScheduleConstruction.update_schedule Job nR buildR prevR mR) (I.Prosa_Classic_Model_Schedule_Global_Transformation_Construction_ScheduleConstruction_update_schedule Job dJ nL buildL prevL mL).
Proof.
  intros oR oL Ho tR tL Ht. unfold ScheduleConstruction.update_schedule, I.Prosa_Classic_Model_Schedule_Global_Transformation_Construction_ScheduleConstruction_update_schedule. cbv beta.
  apply: coq_eq_to_imported_eq.
  rewrite (ct_bool_rel_logic _ _ (ct_decide_eq_nat _ _ _ _ Ht Hm)).
  case: (tR == mR).
  - exact (imported_eq_to_coq_eq _ _ (Hbuild prevR prevL Hprev oR oL Ho tR tL Ht)).
  - exact (imported_eq_to_coq_eq _ _ (Hprev oR oL Ho tR tL Ht)).
Qed.

Lemma cgc_prefix_canonical (kR : nat) :
  CgcSchedRel Job nR nL (@ScheduleConstruction.schedule_prefix Job nR buildR baseR kR) (I.Prosa_Classic_Model_Schedule_Global_Transformation_Construction_ScheduleConstruction_schedule_prefix Job dJ nL buildL baseL (sub_nat_to_imported kR)).
Proof.
  induction kR as [|k IH].
  - refine (cgc_trs (cgc_lsym (I.Prosa_Validation_ClassicGlobalConstructionInterface_production_schedule_prefix_zero Job dJ nL buildL baseL))
              (fun z => CgcSchedRel Job nR nL _ z) _).
    exact (ScheduleConstruction_update_schedule_correspondence baseR baseL Hbase 0 _ (sub_nat_rel_canonical 0)).
  - assert (Hk1 : SubNatRel k.+1 (I.HAdd_hAdd_inst7 Lean.Nat Lean.Nat Lean.Nat (I.instHAdd_inst1 Lean.Nat I.instAddNat)
                                 (sub_nat_to_imported k) (I.OfNat_ofNat_inst1 Lean.Nat 1 (I.instOfNatNat 1)))).
    { exact (cgc_src_transport (fun x => SubNatRel x _) _ _ (addn1 k)
               (sub_add_correspondence _ _ _ _ (sub_nat_rel_canonical k) (sub_nat_rel_canonical 1))). }
    refine (cgc_trs Hk1 (fun z => CgcSchedRel Job nR nL (@ScheduleConstruction.schedule_prefix Job nR buildR baseR k.+1) (I.Prosa_Classic_Model_Schedule_Global_Transformation_Construction_ScheduleConstruction_schedule_prefix Job dJ nL buildL baseL z)) _).
    refine (cgc_trs (cgc_lsym (I.Prosa_Validation_ClassicGlobalConstructionInterface_production_schedule_prefix_succ Job dJ nL buildL baseL (sub_nat_to_imported k)))
              (fun z => CgcSchedRel Job nR nL _ z) _).
    exact (ScheduleConstruction_update_schedule_correspondence _ _ IH _ _ Hk1).
Qed.

Theorem ScheduleConstruction_schedule_prefix_correspondence kR kL (Hk : SubNatRel kR kL) :
  CgcSchedRel Job nR nL (@ScheduleConstruction.schedule_prefix Job nR buildR baseR kR) (I.Prosa_Classic_Model_Schedule_Global_Transformation_Construction_ScheduleConstruction_schedule_prefix Job dJ nL buildL baseL kL).
Proof. exact (cgc_trs Hk (fun z => CgcSchedRel Job nR nL _ (I.Prosa_Classic_Model_Schedule_Global_Transformation_Construction_ScheduleConstruction_schedule_prefix Job dJ nL buildL baseL z)) (cgc_prefix_canonical kR)). Qed.

Theorem ScheduleConstruction_build_schedule_from_prefixes_correspondence :
  CgcSchedRel Job nR nL (@ScheduleConstruction.build_schedule_from_prefixes Job nR buildR baseR) (I.Prosa_Classic_Model_Schedule_Global_Transformation_Construction_ScheduleConstruction_build_schedule_from_prefixes Job dJ nL buildL baseL).
Proof. intros oR oL Ho tR tL Ht. exact (ScheduleConstruction_schedule_prefix_correspondence tR tL Ht oR oL Ho tR tL Ht). Qed.

Notation SCH := ScheduleConstruction_build_schedule_from_prefixes_correspondence.

(** ** Statements *)

Definition src_prefix_construction_same_prefix : Prop :=
  ltac:(type_of_term (@ScheduleConstruction.prefix_construction_same_prefix Job nR buildR baseR)).
Definition tgt_prefix_construction_same_prefix : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Model_Schedule_Global_Transformation_Construction_ScheduleConstruction_prefix_construction_same_prefix Job dJ nL buildL baseL)).
Theorem ScheduleConstruction_prefix_construction_same_prefix_correspondence :
  PropSPropRel src_prefix_construction_same_prefix tgt_prefix_construction_same_prefix.
Proof.
  unfold src_prefix_construction_same_prefix, tgt_prefix_construction_same_prefix.
  apply: ct_forall_nat => tR tL Ht. apply: ct_forall_nat => kR kL Hk.
  apply: (co_forall_ord nR nL Hn) => oR oL Ho.
  apply: ct_imp; first exact (sub_nat_le_correspondence _ _ _ _ Ht Hk).
  exact (cgc_opt_rel_eq _ _ _ _ _ (ScheduleConstruction_schedule_prefix_correspondence kR kL Hk oR oL Ho tR tL Ht) (SCH oR oL Ho tR tL Ht)).
Qed.

Definition src_service_dependent_schedule_construction : Prop :=
  ltac:(type_of_term (@ScheduleConstruction.service_dependent_schedule_construction Job nR buildR baseR)).
Definition tgt_service_dependent_schedule_construction : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Model_Schedule_Global_Transformation_Construction_ScheduleConstruction_service_dependent_schedule_construction Job dJ nL buildL baseL)).
Theorem ScheduleConstruction_service_dependent_schedule_construction_correspondence :
  PropSPropRel src_service_dependent_schedule_construction tgt_service_dependent_schedule_construction.
Proof.
  unfold src_service_dependent_schedule_construction, tgt_service_dependent_schedule_construction.
  apply: ct_imp.
  { apply: (cgc_forall_sched Job nR nL Hn) => s1R s1L Hs1. apply: (cgc_forall_sched Job nR nL Hn) => s2R s2L Hs2.
    apply: (co_forall_ord nR nL Hn) => oR oL Ho. apply: ct_forall_nat => tR tL Ht.
    apply: ct_imp.
    { apply: ct_forall_identity => j.
      exact (sub_nat_eq_correspondence _ _ _ _ (cgc_GS_service Job nR nL Hn s1R s1L Hs1 j tR tL Ht)
               (cgc_GS_service Job nR nL Hn s2R s2L Hs2 j tR tL Ht)). }
    exact (cgc_opt_rel_eq _ _ _ _ _ (Hbuild s1R s1L Hs1 oR oL Ho tR tL Ht) (Hbuild s2R s2L Hs2 oR oL Ho tR tL Ht)). }
  apply: (co_forall_ord nR nL Hn) => oR oL Ho. apply: ct_forall_nat => tR tL Ht.
  exact (cgc_opt_rel_eq _ _ _ _ _ (SCH oR oL Ho tR tL Ht) (Hbuild _ _ SCH oR oL Ho tR tL Ht)).
Qed.

Definition src_prefix_dependent_schedule_construction : Prop :=
  ltac:(type_of_term (@ScheduleConstruction.prefix_dependent_schedule_construction Job nR buildR baseR)).
Definition tgt_prefix_dependent_schedule_construction : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Model_Schedule_Global_Transformation_Construction_ScheduleConstruction_prefix_dependent_schedule_construction Job dJ nL buildL baseL)).
Theorem ScheduleConstruction_prefix_dependent_schedule_construction_correspondence :
  PropSPropRel src_prefix_dependent_schedule_construction tgt_prefix_dependent_schedule_construction.
Proof.
  unfold src_prefix_dependent_schedule_construction, tgt_prefix_dependent_schedule_construction.
  apply: ct_imp.
  { apply: (cgc_forall_sched Job nR nL Hn) => s1R s1L Hs1. apply: (cgc_forall_sched Job nR nL Hn) => s2R s2L Hs2.
    apply: (co_forall_ord nR nL Hn) => oR oL Ho. apply: ct_forall_nat => tR tL Ht.
    apply: ct_imp.
    { apply: ct_forall_nat => t0R t0L Ht0. apply: (co_forall_ord nR nL Hn) => o0R o0L Ho0.
      apply: ct_imp; first exact (sub_nat_lt_correspondence _ _ _ _ Ht0 Ht).
      exact (cgc_opt_rel_eq _ _ _ _ _ (Hs1 o0R o0L Ho0 t0R t0L Ht0) (Hs2 o0R o0L Ho0 t0R t0L Ht0)). }
    exact (cgc_opt_rel_eq _ _ _ _ _ (Hbuild s1R s1L Hs1 oR oL Ho tR tL Ht) (Hbuild s2R s2L Hs2 oR oL Ho tR tL Ht)). }
  apply: (co_forall_ord nR nL Hn) => oR oL Ho. apply: ct_forall_nat => tR tL Ht.
  exact (cgc_opt_rel_eq _ _ _ _ _ (SCH oR oL Ho tR tL Ht) (Hbuild _ _ SCH oR oL Ho tR tL Ht)).
Qed.
End Construction.
