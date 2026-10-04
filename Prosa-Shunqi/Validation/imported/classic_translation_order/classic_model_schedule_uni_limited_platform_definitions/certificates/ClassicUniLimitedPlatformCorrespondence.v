From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq fintype bigop.
From prosa Require Import util.epsilon classic.model.time classic.model.arrival.basic.arrival_sequence classic.model.priority classic.model.schedule.uni.schedule classic.model.schedule.uni.basic.platform classic.model.schedule.uni.limited.platform.definitions.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedClassicUniLimitedPlatform.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence ClassicUniLimitedPlatformBase ClassicUniLimitedPlatformList.

Module I := ImportedClassicUniLimitedPlatform.
Local Open Scope nat_scope.

(** Certificates for [classic/model/schedule/uni/limited/platform/definitions.v] (ProsaBuddy classic, commit f692cb7).

    Inputs: the job and task types are [eqType]s, identified, with the Lean [DecidableEq] instances given by the
    eqTypes' decision procedures ([ct_decidable_eq]); [job_task] identified; times by [SubNatRel]; job/task parameters
    pointwise through [SubNatRel]; preemption models [Job -> time -> bool] pointwise on related times and Booleans;
    uniprocessor schedules pointwise through the option map; arrival sequences pointwise on related times; priority
    policies pointwise on Booleans; all with two-way totals.  The imported uniprocessor schedule and platform
    definitions are related as in the accepted classic certificates (re-bound below).

    Statements: the source side is the exact elaborated type of the pinned lemma (via [type of]; the source proof
    is not used). *)

Ltac type_of_term t := let T := type of t in exact T.
Notation cid := (fun z => z).

(* ------------------------------------------------------------------ *)
(** * Helpers (re-bound to this export from the accepted classic certificates) *)

(** Base definitions (as in the accepted classic base library), provided here when this export's library lacks them. *)

(* ------------------------------------------------------------------ *)
(** * Generic covers and helpers *)

Lemma cdp_forall_cover (A B : Type) (Rel : A -> B -> SProp) (toB : A -> B) (toA : B -> A)
    (HB : forall a, Rel a (toB a)) (HA : forall b, Rel (toA b) b) (PR : A -> Prop) (PL : B -> SProp) :
  (forall a b, Rel a b -> PropSPropRel (PR a) (PL b)) -> PropSPropRel (forall a, PR a) (forall b, PL b).
Proof.
  intro H. apply prop_sprop_rel_intro.
  - intros HR b. exact (prop_to_sprop _ _ (H _ _ (HA b)) (HR _)).
  - intro HL. apply strictly_inhabits. intro a. exact (sprop_to_prop _ _ (H _ _ (HB a)) (HL _)).
Qed.

Lemma cdp_false_rel : PropSPropRel Logic.False I.False.
Proof.
  apply prop_sprop_rel_intro.
  - exact ct_coq_false_to_target.
  - exact ct_target_false_to_strict.
Qed.

Lemma cdp_mem (T : eqType) x s sL : ClListRel cid s sL ->
  PropSPropRel (x \in s) (I.Membership_mem T (I.List T) (I.List_instMembership T) sL x).
Proof. exact (cl_mem_rel_list T T cid cid (fun _ => Logic.eq_refl _) x s sL). Qed.

Lemma cdp_unmap_rel (T : Type) (l : I.List T) : ClListRel cid (cl_unmap cid l) l.
Proof. apply: coq_eq_to_imported_eq. exact (cl_map_unmap cid cid (fun _ => Logic.eq_refl _) l). Qed.

Lemma cdp_cl_map_inj (T : Type) (s1 s2 : seq T) : Logic.eq (cl_map cid s1) (cl_map cid s2) -> Logic.eq s1 s2.
Proof.
  intro E. rewrite -(cl_unmap_map cid cid (fun _ => Logic.eq_refl _) s1) -(cl_unmap_map cid cid (fun _ => Logic.eq_refl _) s2).
  by rewrite E.
Qed.

Lemma cdp_succ_rel nR nL : SubNatRel nR nL ->
  SubNatRel nR.+1 (I.HAdd_hAdd_inst7 Lean.Nat Lean.Nat Lean.Nat (I.instHAdd_inst1 Lean.Nat I.instAddNat) nL
                     (I.OfNat_ofNat_inst1 Lean.Nat 1 (I.instOfNatNat 1))).
Proof. intro Hn. exact (sub_imported_eq_congr Lean.Nat_succ _ _ Hn). Qed.

(* ------------------------------------------------------------------ *)
(** * Big concatenation over a half-open interval (as in the accepted arrival_sequence certificate) *)

Lemma cdp_forall_list (T : Type) (PR : seq T -> Prop) (PL : I.List T -> SProp) :
  (forall sR sL, ClListRel (B := T) cid sR sL -> PropSPropRel (PR sR) (PL sL)) -> PropSPropRel (forall s, PR s) (forall s, PL s).
Proof.
  exact (cdp_forall_cover _ _ (fun sR sL => ClListRel (B := T) cid sR sL) (cl_map cid) (cl_unmap cid)
           (fun s => @Lean.eq_refl _ _) (fun l => cdp_unmap_rel T l) PR PL).
Qed.

Definition CdpParRel (T : Type) (pR : T -> nat) (pL : T -> Lean.Nat) : SProp := forall x, SubNatRel (pR x) (pL x).

Lemma cdp_forall_par (T : Type) (PR : (T -> nat) -> Prop) (PL : (T -> Lean.Nat) -> SProp) :
  (forall pR pL, CdpParRel T pR pL -> PropSPropRel (PR pR) (PL pL)) -> PropSPropRel (forall p, PR p) (forall p, PL p).
Proof.
  exact (cdp_forall_cover _ _ (CdpParRel T) (fun pR j => sub_nat_to_imported (pR j)) (fun pL j => sub_nat_to_rocq (pL j))
           (fun pR j => sub_nat_rel_canonical (pR j)) (fun pL j => sub_nat_rel_surjective (pL j)) PR PL).
Qed.

Fixpoint cdp_natl (s : seq nat) : I.List_inst1 Lean.Nat :=
  match s with [::] => I.List_nil_inst1 _ | x :: s' => I.List_cons_inst1 _ (sub_nat_to_imported x) (cdp_natl s') end.

Definition cdp_one : Lean.Nat := I.OfNat_ofNat_inst1 Lean.Nat 1 (I.instOfNatNat 1).

Lemma cdp_iota_range : forall n s,
  Logic.eq (I.List_range' (sub_nat_to_imported s) (sub_nat_to_imported n) cdp_one) (cdp_natl (iota s n)).
Proof.
  elim => [|n IH] s; first reflexivity.
  change (Logic.eq (I.List_cons_inst1 _ (sub_nat_to_imported s)
      (I.List_range' (sub_nat_to_imported (S s)) (sub_nat_to_imported n) cdp_one))
    (I.List_cons_inst1 _ (sub_nat_to_imported s) (cdp_natl (iota (S s) n)))).
  by rewrite IH.
Qed.

Lemma cdp_cl_map_comp {A B C : Type} (f : A -> B) (g : B -> C) : forall s : seq A,
  Logic.eq (cl_map (fun x => g (f x)) s) (cl_map g (map f s)).
Proof. elim => [|x s IH] //=. by rewrite IH. Qed.

Lemma cdp_cl_map_ext {A B : Type} (f g : A -> B) (H : forall x, Logic.eq (f x) (g x)) : forall s : seq A,
  Logic.eq (cl_map f s) (cl_map g s).
Proof. elim => [|x s IH] //=. by rewrite H IH. Qed.

Lemma cdp_big_seq {A : Type} (F : nat -> seq A) : forall s : seq nat,
  Logic.eq (\big[cat/[::]]_(i <- s) F i) (flatten (map F s)).
Proof. elim => [|x s IH]; first by rewrite big_nil. by rewrite big_cons IH. Qed.

Definition CdpFamRel (A : Type) (fR : nat -> seq A) (fL : Lean.Nat -> I.List A) : SProp :=
  forall nR nL, SubNatRel nR nL -> ClListRel cid (fR nR) (fL nL).

(* ------------------------------------------------------------------ *)
(** * Arrival sequences and parameters *)

Section Rel.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).
Notation LArr := (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrival_sequence Job dJ).

Definition CdpArrRel (aR : ArrivalSequence.arrival_sequence Job) (aL : LArr) : SProp :=
  forall tR tL, SubNatRel tR tL -> ClListRel cid (aR tR) (aL tL).

Definition cdp_arr_to_target (aR : ArrivalSequence.arrival_sequence Job) : LArr :=
  fun tL => cl_map cid (aR (sub_nat_to_rocq tL)).

Definition cdp_arr_to_source (aL : LArr) : ArrivalSequence.arrival_sequence Job :=
  fun tR => cl_unmap cid (aL (sub_nat_to_imported tR)).

Lemma cdp_arr_canonical aR : CdpArrRel aR (cdp_arr_to_target aR).
Proof.
  intros tR tL Ht. have E := cl_nat_logic _ _ Ht. subst tL.
  apply: coq_eq_to_imported_eq. rewrite /cdp_arr_to_target sub_nat_rocq_roundtrip. reflexivity.
Qed.

Lemma cdp_arr_surjective aL : CdpArrRel (cdp_arr_to_source aL) aL.
Proof.
  intros tR tL Ht. have E := cl_nat_logic _ _ Ht. subst tL.
  apply: coq_eq_to_imported_eq. exact (cl_map_unmap cid cid (fun _ => Logic.eq_refl _) _).
Qed.

Lemma cdp_forall_arr (PR : ArrivalSequence.arrival_sequence Job -> Prop) (PL : LArr -> SProp) :
  (forall aR aL, CdpArrRel aR aL -> PropSPropRel (PR aR) (PL aL)) -> PropSPropRel (forall a, PR a) (forall a, PL a).
Proof. exact (cdp_forall_cover _ _ CdpArrRel cdp_arr_to_target cdp_arr_to_source cdp_arr_canonical cdp_arr_surjective PR PL). Qed.

End Rel.

(** The imported [ArrivalSequence] definitions this file's statements mention, related on related inputs. *)
Section ArrivalDefs.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).

Lemma cdp_arrives_in aR aL (Ha : CdpArrRel Job aR aL) j :
  PropSPropRel (ArrivalSequence.arrives_in aR j)
    (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrives_in Job dJ aL j).
Proof. apply: ct_exists_nat => tR tL Ht. exact (cdp_mem Job j _ _ (Ha tR tL Ht)). Qed.

End ArrivalDefs.

Section ArrivalDefs2.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).

Lemma cdp_has_arrived pR pL (Hp : CdpParRel Job pR pL) j tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (ArrivalSequence.has_arrived pR j tR)
    (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_has_arrived Job dJ pL j tL).
Proof. exact (ct_decide_le _ _ _ _ (Hp j) Ht). Qed.

End ArrivalDefs2.

Fixpoint cdp_snatl (s : seq nat) : I.List_inst1 Lean.Nat :=
  match s with [::] => I.List_nil_inst1 _ | x :: s' => I.List_cons_inst1 _ (sub_nat_to_imported x) (cdp_snatl s') end.

Lemma cdp_siota_range : forall n s,
  Logic.eq (I.List_range' (sub_nat_to_imported s) (sub_nat_to_imported n) (Lean.Nat_succ Lean.Nat_zero)) (cdp_snatl (iota s n)).
Proof.
  elim => [|n IH] s; first reflexivity.
  change (Logic.eq (I.List_cons_inst1 _ (sub_nat_to_imported s)
      (I.List_range' (sub_nat_to_imported (S s)) (sub_nat_to_imported n) (Lean.Nat_succ Lean.Nat_zero)))
    (I.List_cons_inst1 _ (sub_nat_to_imported s) (cdp_snatl (iota (S s) n)))).
  by rewrite IH.
Qed.

Lemma cdp_foldr_add (f : Lean.Nat -> Lean.Nat) (g : nat -> nat) (Hf : forall k, Logic.eq (f (sub_nat_to_imported k)) (sub_nat_to_imported (g k))) :
  forall s, Logic.eq (I.List_foldr_inst3 Lean.Nat Lean.Nat Lean.Nat_add Lean.Nat_zero (I.List_map_inst3 Lean.Nat Lean.Nat f (cdp_snatl s)))
                     (sub_nat_to_imported (foldr addn 0 (map g s))).
Proof.
  elim => [|k s IH] //=.
  change (Logic.eq (Lean.Nat_add (f (sub_nat_to_imported k))
            (I.List_foldr_inst3 Lean.Nat Lean.Nat Lean.Nat_add Lean.Nat_zero (I.List_map_inst3 Lean.Nat Lean.Nat f (cdp_snatl s))))
         (sub_nat_to_imported (g k + foldr addn 0 (map g s)))).
  rewrite IH Hf. exact (imported_eq_to_coq_eq _ _ (sub_add_canonical _ _)).
Qed.

Lemma cdp_big_fold (xs : seq nat) (F : nat -> nat) : Logic.eq (\sum_(i <- xs) F i) (foldr addn 0 (map F xs)).
Proof. elim: xs => [|x xs IH]; first by rewrite big_nil. by rewrite big_cons IH. Qed.

Definition CdpFunRel (FR : nat -> nat) (FL : Lean.Nat -> Lean.Nat) : SProp :=
  forall kR kL, SubNatRel kR kL -> SubNatRel (FR kR) (FL kL).

Lemma cdp_fun_canonical FR FL (HF : CdpFunRel FR FL) k : Logic.eq (FL (sub_nat_to_imported k)) (sub_nat_to_imported (FR k)).
Proof. exact (cl_nat_logic _ _ (HF _ _ (sub_nat_rel_canonical k))). Qed.

Lemma cdp_nat_sub_canonical (a b : nat) :
  Logic.eq (I.Nat_sub (sub_nat_to_imported a) (sub_nat_to_imported b)) (sub_nat_to_imported (a - b)).
Proof.
  elim: b => [|b IH]; first by rewrite subn0.
  change (Logic.eq (I.Nat_pred (I.Nat_sub (sub_nat_to_imported a) (sub_nat_to_imported b))) (sub_nat_to_imported (a - b.+1))).
  rewrite IH subnS. case: (a - b) => [|k]; reflexivity.
Qed.

Lemma cdp_ico mR mL nR nL FR FL (Hm : SubNatRel mR mL) (Hn : SubNatRel nR nL) (HF : CdpFunRel FR FL) :
  SubNatRel (\sum_(mR <= i < nR) FR i)
    (I.List_foldr_inst3 Lean.Nat Lean.Nat Lean.Nat_add Lean.Nat_zero
       (I.List_map_inst3 Lean.Nat Lean.Nat FL (I.List_range' mL (I.Nat_sub nL mL) (Lean.Nat_succ Lean.Nat_zero)))).
Proof.
  rewrite (cl_nat_logic _ _ Hm) (cl_nat_logic _ _ Hn).
  have -> : Logic.eq (I.Nat_sub (sub_nat_to_imported nR) (sub_nat_to_imported mR)) (sub_nat_to_imported (nR - mR))
    := cdp_nat_sub_canonical nR mR.
  rewrite cdp_siota_range.
  apply: coq_eq_to_imported_eq. apply: Logic.eq_sym. rewrite (cdp_foldr_add FL FR (cdp_fun_canonical FR FL HF)).
  by rewrite cdp_big_fold.
Qed.

(* ------------------------------------------------------------------ *)
(** * Options and uniprocessor schedules *)

(** Transport along the target equality (definitional UIP), as in the accepted global schedule certificate. *)
Definition cdp_tr {A : Type} {x y : A} (E : Lean.eq x y) (P : A -> Type) (h : P x) : P y :=
  match E in Lean.eq _ z return P z with Lean.eq_refl => h end.

Definition cdp_trs {A : Type} {x y : A} (E : Lean.eq x y) (P : A -> SProp) (h : P x) : P y :=
  match E in Lean.eq _ z return P z with Lean.eq_refl => h end.

Lemma cdp_opt_inj (A : Type) (o1 o2 : option A) : Logic.eq (cl_opt o1) (cl_opt o2) -> Logic.eq o1 o2.
Proof. intro E. by rewrite -(cl_unopt_opt o1) -(cl_unopt_opt o2) E. Qed.

Lemma cdp_opt_eqb_rel (A : eqType) (o1 o2 : option A) :
  PropSPropRel (is_true (o1 == o2)) (Lean.eq (cl_opt o1) (cl_opt o2)).
Proof.
  apply prop_sprop_rel_intro.
  - move=> /eqP E. rewrite E. exact (@Lean.eq_refl _ _).
  - intro E. apply strictly_inhabits. apply/eqP. exact (cdp_opt_inj A o1 o2 (imported_eq_to_coq_eq _ _ E)).
Qed.

Section Sched.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).
Notation LSched := (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job dJ).

Definition CdpSchedRel (sR : UniprocessorSchedule.schedule Job) (sL : LSched) : SProp :=
  forall tR tL, SubNatRel tR tL -> Lean.eq (cl_opt (sR tR)) (sL tL).

Definition cdp_sched_to_target (sR : UniprocessorSchedule.schedule Job) : LSched := fun tL => cl_opt (sR (sub_nat_to_rocq tL)).
Definition cdp_sched_to_source (sL : LSched) : UniprocessorSchedule.schedule Job := fun tR => cl_unopt (sL (sub_nat_to_imported tR)).

Lemma cdp_sched_canonical sR : CdpSchedRel sR (cdp_sched_to_target sR).
Proof. intros tR tL Ht. apply: coq_eq_to_imported_eq. by rewrite /cdp_sched_to_target (cl_nat_input _ _ Ht). Qed.

Lemma cdp_sched_surjective sL : CdpSchedRel (cdp_sched_to_source sL) sL.
Proof.
  intros tR tL Ht. apply: coq_eq_to_imported_eq. rewrite /cdp_sched_to_source cl_opt_unopt.
  by rewrite (cl_nat_logic _ _ Ht).
Qed.

Lemma cdp_forall_sched (PR : UniprocessorSchedule.schedule Job -> Prop) (PL : LSched -> SProp) :
  (forall sR sL, CdpSchedRel sR sL -> PropSPropRel (PR sR) (PL sL)) -> PropSPropRel (forall s, PR s) (forall s, PL s).
Proof. exact (cdp_forall_cover _ _ CdpSchedRel cdp_sched_to_target cdp_sched_to_source cdp_sched_canonical cdp_sched_surjective PR PL). Qed.

End Sched.

(* ------------------------------------------------------------------ *)
(** * Definitions *)

Lemma cdp_US_schedule (Job : eqType) :
  And (forall sR : UniprocessorSchedule.schedule Job, CdpSchedRel Job sR (cdp_sched_to_target Job sR))
      (forall sL : I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job (ct_decidable_eq Job), CdpSchedRel Job (cdp_sched_to_source Job sL) sL).
Proof. exact (And_intro _ _ (cdp_sched_canonical Job) (cdp_sched_surjective Job)). Qed.

Section USchedDefs.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).
Variables (sR : UniprocessorSchedule.schedule Job) (sL : I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job dJ).
Hypothesis Hs : CdpSchedRel Job sR sL.

Lemma cdp_US_scheduled_at j tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (UniprocessorSchedule.scheduled_at sR j tR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_scheduled_at Job dJ sL j tL).
Proof.
  apply: ct_decide_bool.
  exact (cdp_tr (Hs tR tL Ht) (fun z => PropSPropRel (sR tR == Some j) (Lean.eq z (cl_opt (Some j))))
           (cdp_opt_eqb_rel Job (sR tR) (Some j))).
Qed.

Lemma cdp_US_service_at j tR tL (Ht : SubNatRel tR tL) :
  SubNatRel (UniprocessorSchedule.service_at sR j tR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_service_at Job dJ sL j tL).
Proof. exact (ct_bool_to_nat _ _ (cdp_US_scheduled_at j tR tL Ht)). Qed.

Lemma cdp_service_at_fun j : CdpFunRel (fun t => UniprocessorSchedule.service_at sR j t) (fun t => I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_service_at Job dJ sL j t).
Proof. intros kR kL Hk. exact (cdp_US_service_at j kR kL Hk). Qed.

Lemma cdp_US_service_during j t1R t1L (H1 : SubNatRel t1R t1L) t2R t2L (H2 : SubNatRel t2R t2L) :
  SubNatRel (UniprocessorSchedule.service_during sR j t1R t2R) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_service_during Job dJ sL j t1L t2L).
Proof. exact (cdp_ico _ _ _ _ _ _ H1 H2 (cdp_service_at_fun j)). Qed.

Lemma cdp_US_service j tR tL (Ht : SubNatRel tR tL) :
  SubNatRel (UniprocessorSchedule.service sR j tR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_service Job dJ sL j tL).
Proof. exact (cdp_US_service_during j 0 _ (sub_nat_rel_canonical 0) tR tL Ht). Qed.

Lemma cdp_US_completed_by cR cL (Hc : CdpParRel Job cR cL) j tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (UniprocessorSchedule.completed_by cR sR j tR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_completed_by Job dJ cL sL j tL).
Proof. exact (ct_decide_le _ _ _ _ (Hc j) (cdp_US_service j tR tL Ht)). Qed.

Lemma cdp_US_pending aR aL (Ha : CdpParRel Job aR aL) cR cL (Hc : CdpParRel Job cR cL) j tR tL
    (Ht : SubNatRel tR tL) :
  CtBoolRel (UniprocessorSchedule.pending aR cR sR j tR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_pending Job dJ aL cL sL j tL).
Proof.
  exact (ct_bool_and _ _ _ _ (cdp_has_arrived Job aR aL Ha j tR tL Ht)
           (ct_bool_not _ _ (cdp_US_completed_by cR cL Hc j tR tL Ht))).
Qed.

Lemma cdp_US_backlogged aR aL (Ha : CdpParRel Job aR aL) cR cL (Hc : CdpParRel Job cR cL) j
    tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (UniprocessorSchedule.backlogged aR cR sR j tR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_backlogged Job dJ aL cL sL j tL).
Proof.
  exact (ct_bool_and _ _ _ _ (cdp_US_pending aR aL Ha cR cL Hc j tR tL Ht)
           (ct_bool_not _ _ (cdp_US_scheduled_at j tR tL Ht))).
Qed.

Lemma cdp_US_jobs_come_from_arrival_sequence arrR arrL (Harr : CdpArrRel Job arrR arrL) :
  PropSPropRel (UniprocessorSchedule.jobs_come_from_arrival_sequence sR arrR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_jobs_come_from_arrival_sequence Job dJ sL arrL).
Proof.
  apply: ct_forall_identity => j. apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (ct_bool_truth _ _ (cdp_US_scheduled_at j tR tL Ht)).
  exact (cdp_arrives_in Job arrR arrL Harr j).
Qed.

End USchedDefs.

Section UplatDefs.
Variables (Task Job : eqType).
Notation dT := (ct_decidable_eq Task).
Notation dJ := (ct_decidable_eq Job).
Variables (sR : UniprocessorSchedule.schedule Job) (sL : I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job dJ).
Hypothesis Hs : CdpSchedRel Job sR sL.

Lemma cdp_UP_work_conserving aR aL (Ha : CdpParRel Job aR aL) cR cL (Hc : CdpParRel Job cR cL)
    arrR arrL (Harr : CdpArrRel Job arrR arrL) :
  PropSPropRel (Platform.work_conserving aR cR arrR sR) (I.Prosa_Classic_Model_Schedule_Uni_Basic_Platform_Platform_work_conserving Job dJ aL cL arrL sL).
Proof.
  apply: ct_forall_identity => j. apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (cdp_arrives_in Job arrR arrL Harr j).
  apply: ct_imp; first exact (ct_bool_truth _ _ (cdp_US_backlogged Job sR sL Hs aR aL Ha cR cL Hc j tR tL Ht)).
  apply: ct_exists_identity => j_other.
  exact (ct_bool_truth _ _ (cdp_US_scheduled_at Job sR sL Hs j_other tR tL Ht)).
Qed.

End UplatDefs.

(** Priority relations (as in the accepted classic priority certificate). *)
Definition CdpRelRel (T : Type) (rR : T -> T -> bool) (rL : T -> T -> I.Bool) : SProp :=
  forall a b, CtBoolRel (rR a b) (rL a b).

Lemma cdp_rel_canonical (T : Type) (rR : T -> T -> bool) : CdpRelRel T rR (fun a b => ct_b2l (rR a b)).
Proof. intros a b. exact (ct_bool_canonical _). Qed.

Lemma cdp_rel_surjective (T : Type) (rL : T -> T -> I.Bool) : CdpRelRel T (fun a b => ct_l2b (rL a b)) rL.
Proof. intros a b. exact (ct_bool_surjective _). Qed.

Lemma cdp_forall_rel (T : Type) (PR : (T -> T -> bool) -> Prop) (PL : (T -> T -> I.Bool) -> SProp) :
  (forall rR rL, CdpRelRel T rR rL -> PropSPropRel (PR rR) (PL rL)) -> PropSPropRel (forall r, PR r) (forall r, PL r).
Proof.
  exact (cdp_forall_cover _ _ (CdpRelRel T) (fun rR a b => ct_b2l (rR a b)) (fun rL a b => ct_l2b (rL a b))
           (cdp_rel_canonical T) (cdp_rel_surjective T) PR PL).
Qed.

Definition CdpJldpRel (T : Type) (rR : nat -> T -> T -> bool) (rL : Lean.Nat -> T -> T -> I.Bool) : SProp :=
  forall tR tL, SubNatRel tR tL -> CdpRelRel T (rR tR) (rL tL).

Lemma cdp_jldp_canonical (T : Type) (rR : nat -> T -> T -> bool) :
  CdpJldpRel T rR (fun tL a b => ct_b2l (rR (sub_nat_to_rocq tL) a b)).
Proof.
  intros tR tL Ht a b. have E := cl_nat_logic _ _ Ht. subst tL. rewrite sub_nat_rocq_roundtrip.
  exact (ct_bool_canonical _).
Qed.

Lemma cdp_jldp_surjective (T : Type) (rL : Lean.Nat -> T -> T -> I.Bool) :
  CdpJldpRel T (fun tR a b => ct_l2b (rL (sub_nat_to_imported tR) a b)) rL.
Proof. intros tR tL Ht a b. have E := cl_nat_logic _ _ Ht. subst tL. exact (ct_bool_surjective _). Qed.

(* ------------------------------------------------------------------ *)
(** * Arrival sequences *)

Lemma cdp_forall_jldp (T : Type) (PR : (nat -> T -> T -> bool) -> Prop) (PL : (Lean.Nat -> T -> T -> I.Bool) -> SProp) :
  (forall rR rL, CdpJldpRel T rR rL -> PropSPropRel (PR rR) (PL rL)) -> PropSPropRel (forall r, PR r) (forall r, PL r).
Proof.
  exact (cdp_forall_cover _ _ (CdpJldpRel T) (fun rR tL a b => ct_b2l (rR (sub_nat_to_rocq tL) a b))
           (fun rL tR a b => ct_l2b (rL (sub_nat_to_imported tR) a b)) (cdp_jldp_canonical T) (cdp_jldp_surjective T) PR PL).
Qed.


(* ------------------------------------------------------------------ *)
(** * Preemption models *)

Section PmRel.
Variable Job : eqType.
Definition CdpPmRel (pR : Job -> nat -> bool) (pL : Job -> Lean.Nat -> I.Bool) : SProp :=
  forall j tR tL, SubNatRel tR tL -> CtBoolRel (pR j tR) (pL j tL).

Lemma cdp_pm_canonical pR : CdpPmRel pR (fun j tL => ct_b2l (pR j (sub_nat_to_rocq tL))).
Proof. intros j tR tL Ht. have E := cl_nat_logic _ _ Ht. subst tL. rewrite sub_nat_rocq_roundtrip. exact (ct_bool_canonical _). Qed.

Lemma cdp_pm_surjective pL : CdpPmRel (fun j tR => ct_l2b (pL j (sub_nat_to_imported tR))) pL.
Proof. intros j tR tL Ht. have E := cl_nat_logic _ _ Ht. subst tL. exact (ct_bool_surjective _). Qed.

Lemma cdp_forall_pm (PR : (Job -> nat -> bool) -> Prop) (PL : (Job -> Lean.Nat -> I.Bool) -> SProp) :
  (forall pR pL, CdpPmRel pR pL -> PropSPropRel (PR pR) (PL pL)) -> PropSPropRel (forall p, PR p) (forall p, PL p).
Proof. exact (cdp_forall_cover _ _ CdpPmRel _ _ cdp_pm_canonical cdp_pm_surjective PR PL). Qed.
End PmRel.

(* ------------------------------------------------------------------ *)
(** * Definitions *)

Section Defs.
Variables (Task Job : eqType).
Notation dT := (ct_decidable_eq Task).
Notation dJ := (ct_decidable_eq Job).
Variables (sR : UniprocessorSchedule.schedule Job) (sL : I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job dJ).
Hypothesis Hs : CdpSchedRel Job sR sL.
Variables (pR : Job -> nat -> bool) (pL : Job -> Lean.Nat -> I.Bool).
Hypothesis Hp : CdpPmRel Job pR pL.

Notation SA := (cdp_US_scheduled_at Job sR sL Hs).
Notation SV := (cdp_US_service Job sR sL Hs).

Theorem LimitedPreemptionPlatform_preemption_time_correspondence tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (LimitedPreemptionPlatform.preemption_time sR pR tR) (I.Prosa_Classic_Model_Schedule_Uni_Limited_Platform_Definitions_LimitedPreemptionPlatform_preemption_time Job dJ sL pL tL).
Proof.
  refine (cdp_trs (Hs tR tL Ht)
            (fun z => CtBoolRel (LimitedPreemptionPlatform.preemption_time sR pR tR)
                        (match z with
                         | I.Option_some j => pL j (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_service Job dJ sL j tL)
                         | I.Option_none => I.Bool_true end)) _).
  rewrite /LimitedPreemptionPlatform.preemption_time. destruct (sR tR) as [x|].
  - exact (Hp x _ _ (SV x tR tL Ht)).
  - exact (ct_bool_canonical true).
Qed.

Theorem LimitedPreemptionPlatform_not_preemptive_implies_scheduled_correspondence j :
  PropSPropRel (LimitedPreemptionPlatform.not_preemptive_implies_scheduled sR pR j) (I.Prosa_Classic_Model_Schedule_Uni_Limited_Platform_Definitions_LimitedPreemptionPlatform_not_preemptive_implies_scheduled Job dJ sL pL j).
Proof.
  apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (ct_bool_truth _ _ (ct_bool_not _ _ (Hp j _ _ (SV j tR tL Ht)))).
  exact (ct_bool_truth _ _ (SA j tR tL Ht)).
Qed.

Theorem LimitedPreemptionPlatform_execution_starts_with_preemption_point_correspondence j :
  PropSPropRel (LimitedPreemptionPlatform.execution_starts_with_preemption_point sR pR j) (I.Prosa_Classic_Model_Schedule_Uni_Limited_Platform_Definitions_LimitedPreemptionPlatform_execution_starts_with_preemption_point Job dJ sL pL j).
Proof.
  apply: ct_forall_nat => tR tL Ht.
  have Ht1 := cdp_succ_rel _ _ Ht.
  apply: ct_imp; first exact (ct_bool_truth _ _ (ct_bool_not _ _ (SA j tR tL Ht))).
  apply: ct_imp; first exact (ct_bool_truth _ _ (SA j _ _ Ht1)).
  exact (ct_bool_truth _ _ (Hp j _ _ (SV j _ _ Ht1))).
Qed.

Theorem LimitedPreemptionPlatform_correct_preemption_model_correspondence arrR arrL (Harr : CdpArrRel Job arrR arrL) :
  PropSPropRel (LimitedPreemptionPlatform.correct_preemption_model arrR sR pR) (I.Prosa_Classic_Model_Schedule_Uni_Limited_Platform_Definitions_LimitedPreemptionPlatform_correct_preemption_model Job dJ arrL sL pL).
Proof.
  apply: ct_forall_identity => j.
  apply: ct_imp; first exact (cdp_arrives_in Job arrR arrL Harr j).
  apply: ct_and; first exact (LimitedPreemptionPlatform_not_preemptive_implies_scheduled_correspondence j).
  exact (LimitedPreemptionPlatform_execution_starts_with_preemption_point_correspondence j).
Qed.
End Defs.

Section Defs2.
Variables (Task Job : eqType).
Notation dT := (ct_decidable_eq Task).
Notation dJ := (ct_decidable_eq Job).
Variables (pR : Job -> nat -> bool) (pL : Job -> Lean.Nat -> I.Bool).
Hypothesis Hp : CdpPmRel Job pR pL.
Variables (cR : Job -> nat) (cL : Job -> Lean.Nat) (mR : Job -> nat) (mL : Job -> Lean.Nat) (tmR : Task -> nat) (tmL : Task -> Lean.Nat).
Hypotheses (Hc : CdpParRel Job cR cL) (Hm : CdpParRel Job mR mL) (Htm : CdpParRel Task tmR tmL).

Theorem LimitedPreemptionPlatform_job_cannot_become_nonpreemptive_before_execution_correspondence j :
  PropSPropRel (LimitedPreemptionPlatform.job_cannot_become_nonpreemptive_before_execution pR j)
    (I.Prosa_Classic_Model_Schedule_Uni_Limited_Platform_Definitions_LimitedPreemptionPlatform_job_cannot_become_nonpreemptive_before_execution Job dJ pL j).
Proof. exact (ct_bool_truth _ _ (Hp j _ _ (sub_nat_rel_canonical 0))). Qed.

Theorem LimitedPreemptionPlatform_job_cannot_be_nonpreemptive_after_completion_correspondence j :
  PropSPropRel (LimitedPreemptionPlatform.job_cannot_be_nonpreemptive_after_completion cR pR j)
    (I.Prosa_Classic_Model_Schedule_Uni_Limited_Platform_Definitions_LimitedPreemptionPlatform_job_cannot_be_nonpreemptive_after_completion Job dJ cL pL j).
Proof. exact (ct_bool_truth _ _ (Hp j _ _ (Hc j))). Qed.

Theorem LimitedPreemptionPlatform_job_max_nonpreemptive_segment_le_task_max_nonpreemptive_segment_correspondence (job_task : Job -> Task)
    arrR arrL (Harr : CdpArrRel Job arrR arrL) j :
  PropSPropRel (LimitedPreemptionPlatform.job_max_nonpreemptive_segment_le_task_max_nonpreemptive_segment job_task arrR mR tmR j)
    (I.Prosa_Classic_Model_Schedule_Uni_Limited_Platform_Definitions_LimitedPreemptionPlatform_job_max_nonpreemptive_segment_le_task_max_nonpreemptive_segment Task dT Job dJ job_task arrL mL tmL j).
Proof.
  apply: ct_imp; first exact (cdp_arrives_in Job arrR arrL Harr j).
  exact (sub_nat_le_correspondence _ _ _ _ (Hm j) (Htm (job_task j))).
Qed.

Theorem LimitedPreemptionPlatform_nonpreemptive_regions_have_bounded_length_correspondence j :
  PropSPropRel (LimitedPreemptionPlatform.nonpreemptive_regions_have_bounded_length cR pR mR j)
    (I.Prosa_Classic_Model_Schedule_Uni_Limited_Platform_Definitions_LimitedPreemptionPlatform_nonpreemptive_regions_have_bounded_length Job dJ cL pL mL j).
Proof.
  apply: ct_forall_nat => gR gL Hg.
  apply: ct_imp; first exact (ct_bool_truth _ _ (ct_bool_and _ _ _ _ (ct_decide_le _ _ _ _ (sub_nat_rel_canonical 0) Hg) (ct_decide_le _ _ _ _ Hg (Hc j)))).
  apply: ct_exists_nat => xR xL Hx.
  apply: ct_and.
  - exact (ct_bool_truth _ _ (ct_bool_and _ _ _ _ (ct_decide_le _ _ _ _ Hg Hx)
             (ct_decide_le _ _ _ _ Hx (sub_add_correspondence _ _ _ _ Hg (ct_sub_rel _ _ _ _ (Hm j) (sub_nat_rel_canonical 1)))))).
  - exact (ct_bool_truth _ _ (Hp j _ _ Hx)).
Qed.

Theorem LimitedPreemptionPlatform_model_with_bounded_nonpreemptive_segments_correspondence (job_task : Job -> Task)
    arrR arrL (Harr : CdpArrRel Job arrR arrL) :
  PropSPropRel (LimitedPreemptionPlatform.model_with_bounded_nonpreemptive_segments cR job_task arrR pR mR tmR)
    (I.Prosa_Classic_Model_Schedule_Uni_Limited_Platform_Definitions_LimitedPreemptionPlatform_model_with_bounded_nonpreemptive_segments Task dT Job dJ cL job_task arrL pL mL tmL).
Proof.
  apply: ct_forall_identity => j.
  apply: ct_imp; first exact (cdp_arrives_in Job arrR arrL Harr j).
  apply: ct_and; first exact (LimitedPreemptionPlatform_job_cannot_become_nonpreemptive_before_execution_correspondence j).
  apply: ct_and; first exact (LimitedPreemptionPlatform_job_cannot_be_nonpreemptive_after_completion_correspondence j).
  apply: ct_and; first exact (LimitedPreemptionPlatform_job_max_nonpreemptive_segment_le_task_max_nonpreemptive_segment_correspondence job_task arrR arrL Harr j).
  exact (LimitedPreemptionPlatform_nonpreemptive_regions_have_bounded_length_correspondence j).
Qed.
End Defs2.

Theorem LimitedPreemptionPlatform_work_conserving_correspondence (Job : eqType) sR sL (Hs : CdpSchedRel Job sR sL) cR cL (Hc : CdpParRel Job cR cL)
    c0R c0L (Hc0 : CdpParRel Job c0R c0L) arrR arrL (Harr : CdpArrRel Job arrR arrL) :
  PropSPropRel (LimitedPreemptionPlatform.work_conserving cR c0R arrR sR) (I.Prosa_Classic_Model_Schedule_Uni_Limited_Platform_Definitions_LimitedPreemptionPlatform_work_conserving Job (ct_decidable_eq Job) cL c0L arrL sL).
Proof. exact (cdp_UP_work_conserving Job sR sL Hs cR cL Hc c0R c0L Hc0 arrR arrL Harr). Qed.

Section Resp.
Variables (Task Job : eqType).
Notation dT := (ct_decidable_eq Task).
Notation dJ := (ct_decidable_eq Job).
Variables (sR : UniprocessorSchedule.schedule Job) (sL : I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job dJ).
Hypothesis Hs : CdpSchedRel Job sR sL.
Variables (aR : Job -> nat) (aL : Job -> Lean.Nat) (cR : Job -> nat) (cL : Job -> Lean.Nat).
Hypotheses (Ha : CdpParRel Job aR aL) (Hc : CdpParRel Job cR cL).
Variables (arrR : ArrivalSequence.arrival_sequence Job)
  (arrL : I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrival_sequence Job dJ).
Hypothesis Harr : CdpArrRel Job arrR arrL.
Variables (pR : Job -> nat -> bool) (pL : Job -> Lean.Nat -> I.Bool).
Hypothesis Hp : CdpPmRel Job pR pL.

Theorem LimitedPreemptionPlatform_respects_FP_policy_at_preemption_point_correspondence (job_task : Job -> Task) hR hL (Hh : CdpRelRel Task hR hL) :
  PropSPropRel (LimitedPreemptionPlatform.respects_FP_policy_at_preemption_point aR cR job_task arrR sR pR hR)
    (I.Prosa_Classic_Model_Schedule_Uni_Limited_Platform_Definitions_LimitedPreemptionPlatform_respects_FP_policy_at_preemption_point Task dT Job dJ aL cL job_task arrL sL pL hL).
Proof.
  apply: ct_forall_identity => j. apply: ct_forall_identity => j_hp. apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (ct_bool_truth _ _ (LimitedPreemptionPlatform_preemption_time_correspondence Job sR sL Hs pR pL Hp tR tL Ht)).
  apply: ct_imp; first exact (cdp_arrives_in Job arrR arrL Harr j).
  apply: ct_imp; first exact (ct_bool_truth _ _ (cdp_US_backlogged Job sR sL Hs aR aL Ha cR cL Hc j tR tL Ht)).
  apply: ct_imp; first exact (ct_bool_truth _ _ (cdp_US_scheduled_at Job sR sL Hs j_hp tR tL Ht)).
  exact (ct_bool_truth _ _ (Hh (job_task j_hp) (job_task j))).
Qed.

Theorem LimitedPreemptionPlatform_respects_JLFP_policy_at_preemption_point_correspondence hR hL (Hh : CdpRelRel Job hR hL) :
  PropSPropRel (LimitedPreemptionPlatform.respects_JLFP_policy_at_preemption_point aR cR arrR sR pR hR)
    (I.Prosa_Classic_Model_Schedule_Uni_Limited_Platform_Definitions_LimitedPreemptionPlatform_respects_JLFP_policy_at_preemption_point Job dJ aL cL arrL sL pL hL).
Proof.
  apply: ct_forall_identity => j. apply: ct_forall_identity => j_hp. apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (ct_bool_truth _ _ (LimitedPreemptionPlatform_preemption_time_correspondence Job sR sL Hs pR pL Hp tR tL Ht)).
  apply: ct_imp; first exact (cdp_arrives_in Job arrR arrL Harr j).
  apply: ct_imp; first exact (ct_bool_truth _ _ (cdp_US_backlogged Job sR sL Hs aR aL Ha cR cL Hc j tR tL Ht)).
  apply: ct_imp; first exact (ct_bool_truth _ _ (cdp_US_scheduled_at Job sR sL Hs j_hp tR tL Ht)).
  exact (ct_bool_truth _ _ (Hh j_hp j)).
Qed.
End Resp.

(* ------------------------------------------------------------------ *)
(** * Statements *)

Definition src_zero_is_pt (Task Job : eqType) : Prop := ltac:(type_of_term (@LimitedPreemptionPlatform.zero_is_pt Task Job)).
Definition tgt_zero_is_pt (Task Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Model_Schedule_Uni_Limited_Platform_Definitions_LimitedPreemptionPlatform_zero_is_pt Task (ct_decidable_eq Task) Job (ct_decidable_eq Job))).

Theorem LimitedPreemptionPlatform_zero_is_pt_correspondence (Task Job : eqType) : PropSPropRel (src_zero_is_pt Task Job) (tgt_zero_is_pt Task Job).
Proof.
  unfold src_zero_is_pt, tgt_zero_is_pt.
  apply: cdp_forall_par => cR cL Hc. apply: ct_forall_identity => job_task. apply: cdp_forall_arr => arrR arrL Harr.
  apply: cdp_forall_sched => sR sL Hs. apply: cdp_forall_pm => pR pL Hp.
  apply: cdp_forall_par => mR mL Hm. apply: cdp_forall_par => tmR tmL Htm.
  apply: ct_imp; first exact (LimitedPreemptionPlatform_model_with_bounded_nonpreemptive_segments_correspondence Task Job pR pL Hp cR cL mR mL tmR tmL Hc Hm Htm job_task arrR arrL Harr).
  apply: ct_imp; first exact (cdp_US_jobs_come_from_arrival_sequence Job sR sL Hs arrR arrL Harr).
  exact (ct_bool_truth _ _ (LimitedPreemptionPlatform_preemption_time_correspondence Job sR sL Hs pR pL Hp _ _ (sub_nat_rel_canonical 0))).
Qed.

Definition src_first_moment_is_pt (Job : eqType) : Prop := ltac:(type_of_term (@LimitedPreemptionPlatform.first_moment_is_pt Job)).
Definition tgt_first_moment_is_pt (Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Model_Schedule_Uni_Limited_Platform_Definitions_LimitedPreemptionPlatform_first_moment_is_pt Job (ct_decidable_eq Job))).

Theorem LimitedPreemptionPlatform_first_moment_is_pt_correspondence (Job : eqType) : PropSPropRel (src_first_moment_is_pt Job) (tgt_first_moment_is_pt Job).
Proof.
  unfold src_first_moment_is_pt, tgt_first_moment_is_pt.
  apply: cdp_forall_arr => arrR arrL Harr. apply: cdp_forall_sched => sR sL Hs. apply: cdp_forall_pm => pR pL Hp.
  apply: ct_imp; first exact (LimitedPreemptionPlatform_correct_preemption_model_correspondence Job sR sL Hs pR pL Hp arrR arrL Harr).
  apply: ct_forall_identity => j. apply: ct_forall_nat => tR tL Ht.
  have Ht1 := cdp_succ_rel _ _ Ht.
  apply: ct_imp; first exact (cdp_arrives_in Job arrR arrL Harr j).
  apply: ct_imp; first exact (ct_bool_truth _ _ (ct_bool_not _ _ (cdp_US_scheduled_at Job sR sL Hs j tR tL Ht))).
  apply: ct_imp; first exact (ct_bool_truth _ _ (cdp_US_scheduled_at Job sR sL Hs j _ _ Ht1)).
  exact (ct_bool_truth _ _ (LimitedPreemptionPlatform_preemption_time_correspondence Job sR sL Hs pR pL Hp _ _ Ht1)).
Qed.
