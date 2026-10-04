From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq fintype bigop.
From prosa Require Import classic.model.time classic.model.arrival.basic.arrival_sequence classic.model.priority classic.model.schedule.uni.schedule classic.model.schedule.uni.basic.platform classic.model.schedule.uni.nonpreemptive.platform.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedClassicUniNonpreemptivePlatform.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence ClassicUniNonpreemptivePlatformBase ClassicUniNonpreemptivePlatformList.

Module I := ImportedClassicUniNonpreemptivePlatform.
Local Open Scope nat_scope.

(** Certificates for [classic/model/schedule/uni/nonpreemptive/platform.v] (ProsaBuddy classic, commit f692cb7).

    Inputs: the job and task types are [eqType]s, identified, with the Lean [DecidableEq] instances given by the
    eqTypes' decision procedures ([ct_decidable_eq]); [job_task] identified; times by [SubNatRel]; job parameters
    pointwise through [SubNatRel]; uniprocessor schedules pointwise through the option map; arrival sequences pointwise
    on related times; FP/JLFP policies pointwise on Booleans; all with two-way totals.  The imported uniprocessor
    schedule and platform definitions are related as in the accepted classic certificates (re-bound below, through the
    kernel-guarded body projections of [ClassicUniNonpreemptivePlatformInterface]).

    Statements: the source side is the exact elaborated type of the pinned lemma (via [type of]; the source proof
    is not used). *)

Ltac type_of_term t := let T := type of t in exact T.
Notation cid := (fun z => z).

(* ------------------------------------------------------------------ *)
(** * Helpers (re-bound to this export from the accepted classic certificates) *)

(** Base definitions (as in the accepted classic base library), provided here when this export's library lacks them. *)

(* ------------------------------------------------------------------ *)
(** * Generic covers and helpers *)

Lemma cnpl_forall_cover (A B : Type) (Rel : A -> B -> SProp) (toB : A -> B) (toA : B -> A)
    (HB : forall a, Rel a (toB a)) (HA : forall b, Rel (toA b) b) (PR : A -> Prop) (PL : B -> SProp) :
  (forall a b, Rel a b -> PropSPropRel (PR a) (PL b)) -> PropSPropRel (forall a, PR a) (forall b, PL b).
Proof.
  intro H. apply prop_sprop_rel_intro.
  - intros HR b. exact (prop_to_sprop _ _ (H _ _ (HA b)) (HR _)).
  - intro HL. apply strictly_inhabits. intro a. exact (sprop_to_prop _ _ (H _ _ (HB a)) (HL _)).
Qed.

Lemma cnpl_false_rel : PropSPropRel Logic.False I.False.
Proof.
  apply prop_sprop_rel_intro.
  - exact ct_coq_false_to_target.
  - exact ct_target_false_to_strict.
Qed.

Lemma cnpl_mem (T : eqType) x s sL : ClListRel cid s sL ->
  PropSPropRel (x \in s) (I.Membership_mem T (I.List T) (I.List_instMembership T) sL x).
Proof. exact (cl_mem_rel_list T T cid cid (fun _ => Logic.eq_refl _) x s sL). Qed.

Lemma cnpl_unmap_rel (T : Type) (l : I.List T) : ClListRel cid (cl_unmap cid l) l.
Proof. apply: coq_eq_to_imported_eq. exact (cl_map_unmap cid cid (fun _ => Logic.eq_refl _) l). Qed.

Lemma cnpl_cl_map_inj (T : Type) (s1 s2 : seq T) : Logic.eq (cl_map cid s1) (cl_map cid s2) -> Logic.eq s1 s2.
Proof.
  intro E. rewrite -(cl_unmap_map cid cid (fun _ => Logic.eq_refl _) s1) -(cl_unmap_map cid cid (fun _ => Logic.eq_refl _) s2).
  by rewrite E.
Qed.

Lemma cnpl_succ_rel nR nL : SubNatRel nR nL ->
  SubNatRel nR.+1 (I.HAdd_hAdd_inst7 Lean.Nat Lean.Nat Lean.Nat (I.instHAdd_inst1 Lean.Nat I.instAddNat) nL
                     (I.OfNat_ofNat_inst1 Lean.Nat 1 (I.instOfNatNat 1))).
Proof. intro Hn. exact (sub_imported_eq_congr Lean.Nat_succ _ _ Hn). Qed.

(* ------------------------------------------------------------------ *)
(** * Big concatenation over a half-open interval (as in the accepted arrival_sequence certificate) *)

Definition CnplParRel (T : Type) (pR : T -> nat) (pL : T -> Lean.Nat) : SProp := forall x, SubNatRel (pR x) (pL x).

Lemma cnpl_forall_par (T : Type) (PR : (T -> nat) -> Prop) (PL : (T -> Lean.Nat) -> SProp) :
  (forall pR pL, CnplParRel T pR pL -> PropSPropRel (PR pR) (PL pL)) -> PropSPropRel (forall p, PR p) (forall p, PL p).
Proof.
  exact (cnpl_forall_cover _ _ (CnplParRel T) (fun pR j => sub_nat_to_imported (pR j)) (fun pL j => sub_nat_to_rocq (pL j))
           (fun pR j => sub_nat_rel_canonical (pR j)) (fun pL j => sub_nat_rel_surjective (pL j)) PR PL).
Qed.

Fixpoint cnpl_natl (s : seq nat) : I.List_inst1 Lean.Nat :=
  match s with [::] => I.List_nil_inst1 _ | x :: s' => I.List_cons_inst1 _ (sub_nat_to_imported x) (cnpl_natl s') end.

Definition cnpl_one : Lean.Nat := I.OfNat_ofNat_inst1 Lean.Nat 1 (I.instOfNatNat 1).

Lemma cnpl_iota_range : forall n s,
  Logic.eq (I.List_range' (sub_nat_to_imported s) (sub_nat_to_imported n) cnpl_one) (cnpl_natl (iota s n)).
Proof.
  elim => [|n IH] s; first reflexivity.
  change (Logic.eq (I.List_cons_inst1 _ (sub_nat_to_imported s)
      (I.List_range' (sub_nat_to_imported (S s)) (sub_nat_to_imported n) cnpl_one))
    (I.List_cons_inst1 _ (sub_nat_to_imported s) (cnpl_natl (iota (S s) n)))).
  by rewrite IH.
Qed.

Lemma cnpl_cl_map_comp {A B C : Type} (f : A -> B) (g : B -> C) : forall s : seq A,
  Logic.eq (cl_map (fun x => g (f x)) s) (cl_map g (map f s)).
Proof. elim => [|x s IH] //=. by rewrite IH. Qed.

Lemma cnpl_cl_map_ext {A B : Type} (f g : A -> B) (H : forall x, Logic.eq (f x) (g x)) : forall s : seq A,
  Logic.eq (cl_map f s) (cl_map g s).
Proof. elim => [|x s IH] //=. by rewrite H IH. Qed.

Lemma cnpl_big_seq {A : Type} (F : nat -> seq A) : forall s : seq nat,
  Logic.eq (\big[cat/[::]]_(i <- s) F i) (flatten (map F s)).
Proof. elim => [|x s IH]; first by rewrite big_nil. by rewrite big_cons IH. Qed.

Definition CnplFamRel (A : Type) (fR : nat -> seq A) (fL : Lean.Nat -> I.List A) : SProp :=
  forall nR nL, SubNatRel nR nL -> ClListRel cid (fR nR) (fL nL).

(* ------------------------------------------------------------------ *)
(** * Arrival sequences and parameters *)

Section Rel.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).
Notation LArr := (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrival_sequence Job dJ).

Definition CnplArrRel (aR : ArrivalSequence.arrival_sequence Job) (aL : LArr) : SProp :=
  forall tR tL, SubNatRel tR tL -> ClListRel cid (aR tR) (aL tL).

Definition cnpl_arr_to_target (aR : ArrivalSequence.arrival_sequence Job) : LArr :=
  fun tL => cl_map cid (aR (sub_nat_to_rocq tL)).

Definition cnpl_arr_to_source (aL : LArr) : ArrivalSequence.arrival_sequence Job :=
  fun tR => cl_unmap cid (aL (sub_nat_to_imported tR)).

Lemma cnpl_arr_canonical aR : CnplArrRel aR (cnpl_arr_to_target aR).
Proof.
  intros tR tL Ht. have E := cl_nat_logic _ _ Ht. subst tL.
  apply: coq_eq_to_imported_eq. rewrite /cnpl_arr_to_target sub_nat_rocq_roundtrip. reflexivity.
Qed.

Lemma cnpl_arr_surjective aL : CnplArrRel (cnpl_arr_to_source aL) aL.
Proof.
  intros tR tL Ht. have E := cl_nat_logic _ _ Ht. subst tL.
  apply: coq_eq_to_imported_eq. exact (cl_map_unmap cid cid (fun _ => Logic.eq_refl _) _).
Qed.

Lemma cnpl_forall_arr (PR : ArrivalSequence.arrival_sequence Job -> Prop) (PL : LArr -> SProp) :
  (forall aR aL, CnplArrRel aR aL -> PropSPropRel (PR aR) (PL aL)) -> PropSPropRel (forall a, PR a) (forall a, PL a).
Proof. exact (cnpl_forall_cover _ _ CnplArrRel cnpl_arr_to_target cnpl_arr_to_source cnpl_arr_canonical cnpl_arr_surjective PR PL). Qed.

End Rel.

(** The imported [ArrivalSequence] definitions this file's statements mention, related on related inputs. *)
Section ArrivalDefs.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).

Lemma cnpl_arrives_in aR aL (Ha : CnplArrRel Job aR aL) j :
  PropSPropRel (ArrivalSequence.arrives_in aR j)
    (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrives_in Job dJ aL j).
Proof. apply: ct_exists_nat => tR tL Ht. exact (cnpl_mem Job j _ _ (Ha tR tL Ht)). Qed.

End ArrivalDefs.

Section ArrivalDefs2.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).

Lemma cnpl_has_arrived pR pL (Hp : CnplParRel Job pR pL) j tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (ArrivalSequence.has_arrived pR j tR)
    (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_has_arrived Job dJ pL j tL).
Proof. exact (ct_decide_le _ _ _ _ (Hp j) Ht). Qed.

End ArrivalDefs2.

Fixpoint cnpl_snatl (s : seq nat) : I.List_inst1 Lean.Nat :=
  match s with [::] => I.List_nil_inst1 _ | x :: s' => I.List_cons_inst1 _ (sub_nat_to_imported x) (cnpl_snatl s') end.

Lemma cnpl_siota_range : forall n s,
  Logic.eq (I.List_range' (sub_nat_to_imported s) (sub_nat_to_imported n) (Lean.Nat_succ Lean.Nat_zero)) (cnpl_snatl (iota s n)).
Proof.
  elim => [|n IH] s; first reflexivity.
  change (Logic.eq (I.List_cons_inst1 _ (sub_nat_to_imported s)
      (I.List_range' (sub_nat_to_imported (S s)) (sub_nat_to_imported n) (Lean.Nat_succ Lean.Nat_zero)))
    (I.List_cons_inst1 _ (sub_nat_to_imported s) (cnpl_snatl (iota (S s) n)))).
  by rewrite IH.
Qed.

Lemma cnpl_foldr_add (f : Lean.Nat -> Lean.Nat) (g : nat -> nat) (Hf : forall k, Logic.eq (f (sub_nat_to_imported k)) (sub_nat_to_imported (g k))) :
  forall s, Logic.eq (I.List_foldr_inst3 Lean.Nat Lean.Nat Lean.Nat_add Lean.Nat_zero (I.List_map_inst3 Lean.Nat Lean.Nat f (cnpl_snatl s)))
                     (sub_nat_to_imported (foldr addn 0 (map g s))).
Proof.
  elim => [|k s IH] //=.
  change (Logic.eq (Lean.Nat_add (f (sub_nat_to_imported k))
            (I.List_foldr_inst3 Lean.Nat Lean.Nat Lean.Nat_add Lean.Nat_zero (I.List_map_inst3 Lean.Nat Lean.Nat f (cnpl_snatl s))))
         (sub_nat_to_imported (g k + foldr addn 0 (map g s)))).
  rewrite IH Hf. exact (imported_eq_to_coq_eq _ _ (sub_add_canonical _ _)).
Qed.

Lemma cnpl_big_fold (xs : seq nat) (F : nat -> nat) : Logic.eq (\sum_(i <- xs) F i) (foldr addn 0 (map F xs)).
Proof. elim: xs => [|x xs IH]; first by rewrite big_nil. by rewrite big_cons IH. Qed.

Definition CnplFunRel (FR : nat -> nat) (FL : Lean.Nat -> Lean.Nat) : SProp :=
  forall kR kL, SubNatRel kR kL -> SubNatRel (FR kR) (FL kL).

Lemma cnpl_fun_canonical FR FL (HF : CnplFunRel FR FL) k : Logic.eq (FL (sub_nat_to_imported k)) (sub_nat_to_imported (FR k)).
Proof. exact (cl_nat_logic _ _ (HF _ _ (sub_nat_rel_canonical k))). Qed.

Lemma cnpl_nat_sub_canonical (a b : nat) :
  Logic.eq (I.Nat_sub (sub_nat_to_imported a) (sub_nat_to_imported b)) (sub_nat_to_imported (a - b)).
Proof.
  elim: b => [|b IH]; first by rewrite subn0.
  change (Logic.eq (I.Nat_pred (I.Nat_sub (sub_nat_to_imported a) (sub_nat_to_imported b))) (sub_nat_to_imported (a - b.+1))).
  rewrite IH subnS. case: (a - b) => [|k]; reflexivity.
Qed.

Lemma cnpl_ico mR mL nR nL FR FL (Hm : SubNatRel mR mL) (Hn : SubNatRel nR nL) (HF : CnplFunRel FR FL) :
  SubNatRel (\sum_(mR <= i < nR) FR i)
    (I.List_foldr_inst3 Lean.Nat Lean.Nat Lean.Nat_add Lean.Nat_zero
       (I.List_map_inst3 Lean.Nat Lean.Nat FL (I.List_range' mL (I.Nat_sub nL mL) (Lean.Nat_succ Lean.Nat_zero)))).
Proof.
  rewrite (cl_nat_logic _ _ Hm) (cl_nat_logic _ _ Hn).
  have -> : Logic.eq (I.Nat_sub (sub_nat_to_imported nR) (sub_nat_to_imported mR)) (sub_nat_to_imported (nR - mR))
    := cnpl_nat_sub_canonical nR mR.
  rewrite cnpl_siota_range.
  apply: coq_eq_to_imported_eq. apply: Logic.eq_sym. rewrite (cnpl_foldr_add FL FR (cnpl_fun_canonical FR FL HF)).
  by rewrite cnpl_big_fold.
Qed.

(* ------------------------------------------------------------------ *)
(** * Options and uniprocessor schedules *)

(** Transport along the target equality (definitional UIP), as in the accepted global schedule certificate. *)
Definition cnpl_tr {A : Type} {x y : A} (E : Lean.eq x y) (P : A -> Type) (h : P x) : P y :=
  match E in Lean.eq _ z return P z with Lean.eq_refl => h end.

Definition cnpl_trs {A : Type} {x y : A} (E : Lean.eq x y) (P : A -> SProp) (h : P x) : P y :=
  match E in Lean.eq _ z return P z with Lean.eq_refl => h end.

Lemma cnpl_opt_inj (A : Type) (o1 o2 : option A) : Logic.eq (cl_opt o1) (cl_opt o2) -> Logic.eq o1 o2.
Proof. intro E. by rewrite -(cl_unopt_opt o1) -(cl_unopt_opt o2) E. Qed.

Lemma cnpl_opt_eqb_rel (A : eqType) (o1 o2 : option A) :
  PropSPropRel (is_true (o1 == o2)) (Lean.eq (cl_opt o1) (cl_opt o2)).
Proof.
  apply prop_sprop_rel_intro.
  - move=> /eqP E. rewrite E. exact (@Lean.eq_refl _ _).
  - intro E. apply strictly_inhabits. apply/eqP. exact (cnpl_opt_inj A o1 o2 (imported_eq_to_coq_eq _ _ E)).
Qed.

Section Sched.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).
Notation LSched := (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job dJ).

Definition CnplSchedRel (sR : UniprocessorSchedule.schedule Job) (sL : LSched) : SProp :=
  forall tR tL, SubNatRel tR tL -> Lean.eq (cl_opt (sR tR)) (sL tL).

Definition cnpl_sched_to_target (sR : UniprocessorSchedule.schedule Job) : LSched := fun tL => cl_opt (sR (sub_nat_to_rocq tL)).
Definition cnpl_sched_to_source (sL : LSched) : UniprocessorSchedule.schedule Job := fun tR => cl_unopt (sL (sub_nat_to_imported tR)).

Lemma cnpl_sched_canonical sR : CnplSchedRel sR (cnpl_sched_to_target sR).
Proof. intros tR tL Ht. apply: coq_eq_to_imported_eq. by rewrite /cnpl_sched_to_target (cl_nat_input _ _ Ht). Qed.

Lemma cnpl_sched_surjective sL : CnplSchedRel (cnpl_sched_to_source sL) sL.
Proof.
  intros tR tL Ht. apply: coq_eq_to_imported_eq. rewrite /cnpl_sched_to_source cl_opt_unopt.
  by rewrite (cl_nat_logic _ _ Ht).
Qed.

Lemma cnpl_forall_sched (PR : UniprocessorSchedule.schedule Job -> Prop) (PL : LSched -> SProp) :
  (forall sR sL, CnplSchedRel sR sL -> PropSPropRel (PR sR) (PL sL)) -> PropSPropRel (forall s, PR s) (forall s, PL s).
Proof. exact (cnpl_forall_cover _ _ CnplSchedRel cnpl_sched_to_target cnpl_sched_to_source cnpl_sched_canonical cnpl_sched_surjective PR PL). Qed.

End Sched.

(* ------------------------------------------------------------------ *)
(** * Definitions *)

Lemma cnpl_US_schedule (Job : eqType) :
  And (forall sR : UniprocessorSchedule.schedule Job, CnplSchedRel Job sR (cnpl_sched_to_target Job sR))
      (forall sL : I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job (ct_decidable_eq Job), CnplSchedRel Job (cnpl_sched_to_source Job sL) sL).
Proof. exact (And_intro _ _ (cnpl_sched_canonical Job) (cnpl_sched_surjective Job)). Qed.

Section USchedDefs.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).
Variables (sR : UniprocessorSchedule.schedule Job) (sL : I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job dJ).
Hypothesis Hs : CnplSchedRel Job sR sL.

Lemma cnpl_US_scheduled_at j tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (UniprocessorSchedule.scheduled_at sR j tR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_scheduled_at Job dJ sL j tL).
Proof.
  apply: ct_decide_bool.
  exact (cnpl_tr (Hs tR tL Ht) (fun z => PropSPropRel (sR tR == Some j) (Lean.eq z (cl_opt (Some j))))
           (cnpl_opt_eqb_rel Job (sR tR) (Some j))).
Qed.

Lemma cnpl_US_service_at j tR tL (Ht : SubNatRel tR tL) :
  SubNatRel (UniprocessorSchedule.service_at sR j tR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_service_at Job dJ sL j tL).
Proof. exact (ct_bool_to_nat _ _ (cnpl_US_scheduled_at j tR tL Ht)). Qed.

Lemma cnpl_service_at_fun j : CnplFunRel (fun t => UniprocessorSchedule.service_at sR j t) (fun t => I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_service_at Job dJ sL j t).
Proof. intros kR kL Hk. exact (cnpl_US_service_at j kR kL Hk). Qed.

Lemma cnpl_US_service_during j t1R t1L (H1 : SubNatRel t1R t1L) t2R t2L (H2 : SubNatRel t2R t2L) :
  SubNatRel (UniprocessorSchedule.service_during sR j t1R t2R) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_service_during Job dJ sL j t1L t2L).
Proof. exact (cnpl_ico _ _ _ _ _ _ H1 H2 (cnpl_service_at_fun j)). Qed.

Lemma cnpl_US_service j tR tL (Ht : SubNatRel tR tL) :
  SubNatRel (UniprocessorSchedule.service sR j tR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_service Job dJ sL j tL).
Proof. exact (cnpl_US_service_during j 0 _ (sub_nat_rel_canonical 0) tR tL Ht). Qed.

Lemma cnpl_US_completed_by cR cL (Hc : CnplParRel Job cR cL) j tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (UniprocessorSchedule.completed_by cR sR j tR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_completed_by Job dJ cL sL j tL).
Proof. exact (ct_decide_le _ _ _ _ (Hc j) (cnpl_US_service j tR tL Ht)). Qed.

Lemma cnpl_US_pending aR aL (Ha : CnplParRel Job aR aL) cR cL (Hc : CnplParRel Job cR cL) j tR tL
    (Ht : SubNatRel tR tL) :
  CtBoolRel (UniprocessorSchedule.pending aR cR sR j tR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_pending Job dJ aL cL sL j tL).
Proof.
  exact (ct_bool_and _ _ _ _ (cnpl_has_arrived Job aR aL Ha j tR tL Ht)
           (ct_bool_not _ _ (cnpl_US_completed_by cR cL Hc j tR tL Ht))).
Qed.

Lemma cnpl_US_backlogged aR aL (Ha : CnplParRel Job aR aL) cR cL (Hc : CnplParRel Job cR cL) j
    tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (UniprocessorSchedule.backlogged aR cR sR j tR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_backlogged Job dJ aL cL sL j tL).
Proof.
  exact (ct_bool_and _ _ _ _ (cnpl_US_pending aR aL Ha cR cL Hc j tR tL Ht)
           (ct_bool_not _ _ (cnpl_US_scheduled_at j tR tL Ht))).
Qed.

End USchedDefs.

Section UplatDefs.
Variables (Task Job : eqType).
Notation dT := (ct_decidable_eq Task).
Notation dJ := (ct_decidable_eq Job).
Variables (sR : UniprocessorSchedule.schedule Job) (sL : I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job dJ).
Hypothesis Hs : CnplSchedRel Job sR sL.

Lemma cnpl_UP_work_conserving aR aL (Ha : CnplParRel Job aR aL) cR cL (Hc : CnplParRel Job cR cL)
    arrR arrL (Harr : CnplArrRel Job arrR arrL) :
  PropSPropRel (Platform.work_conserving aR cR arrR sR) (I.Prosa_Classic_Model_Schedule_Uni_Basic_Platform_Platform_work_conserving Job dJ aL cL arrL sL).
Proof.
  apply: ct_forall_identity => j. apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (cnpl_arrives_in Job arrR arrL Harr j).
  apply: ct_imp; first exact (ct_bool_truth _ _ (cnpl_US_backlogged Job sR sL Hs aR aL Ha cR cL Hc j tR tL Ht)).
  apply: ct_exists_identity => j_other.
  exact (ct_bool_truth _ _ (cnpl_US_scheduled_at Job sR sL Hs j_other tR tL Ht)).
Qed.

End UplatDefs.

(** Priority relations (as in the accepted classic priority certificate). *)
Definition CnplRelRel (T : Type) (rR : T -> T -> bool) (rL : T -> T -> I.Bool) : SProp :=
  forall a b, CtBoolRel (rR a b) (rL a b).

Lemma cnpl_rel_canonical (T : Type) (rR : T -> T -> bool) : CnplRelRel T rR (fun a b => ct_b2l (rR a b)).
Proof. intros a b. exact (ct_bool_canonical _). Qed.

Lemma cnpl_rel_surjective (T : Type) (rL : T -> T -> I.Bool) : CnplRelRel T (fun a b => ct_l2b (rL a b)) rL.
Proof. intros a b. exact (ct_bool_surjective _). Qed.

Lemma cnpl_forall_rel (T : Type) (PR : (T -> T -> bool) -> Prop) (PL : (T -> T -> I.Bool) -> SProp) :
  (forall rR rL, CnplRelRel T rR rL -> PropSPropRel (PR rR) (PL rL)) -> PropSPropRel (forall r, PR r) (forall r, PL r).
Proof.
  exact (cnpl_forall_cover _ _ (CnplRelRel T) (fun rR a b => ct_b2l (rR a b)) (fun rL a b => ct_l2b (rL a b))
           (cnpl_rel_canonical T) (cnpl_rel_surjective T) PR PL).
Qed.

Definition CnplJldpRel (T : Type) (rR : nat -> T -> T -> bool) (rL : Lean.Nat -> T -> T -> I.Bool) : SProp :=
  forall tR tL, SubNatRel tR tL -> CnplRelRel T (rR tR) (rL tL).

Lemma cnpl_jldp_canonical (T : Type) (rR : nat -> T -> T -> bool) :
  CnplJldpRel T rR (fun tL a b => ct_b2l (rR (sub_nat_to_rocq tL) a b)).
Proof.
  intros tR tL Ht a b. have E := cl_nat_logic _ _ Ht. subst tL. rewrite sub_nat_rocq_roundtrip.
  exact (ct_bool_canonical _).
Qed.

Lemma cnpl_jldp_surjective (T : Type) (rL : Lean.Nat -> T -> T -> I.Bool) :
  CnplJldpRel T (fun tR a b => ct_l2b (rL (sub_nat_to_imported tR) a b)) rL.
Proof. intros tR tL Ht a b. have E := cl_nat_logic _ _ Ht. subst tL. exact (ct_bool_surjective _). Qed.

(* ------------------------------------------------------------------ *)
(** * Arrival sequences *)

Lemma cnpl_forall_jldp (T : Type) (PR : (nat -> T -> T -> bool) -> Prop) (PL : (Lean.Nat -> T -> T -> I.Bool) -> SProp) :
  (forall rR rL, CnplJldpRel T rR rL -> PropSPropRel (PR rR) (PL rL)) -> PropSPropRel (forall r, PR r) (forall r, PL r).
Proof.
  exact (cnpl_forall_cover _ _ (CnplJldpRel T) (fun rR tL a b => ct_b2l (rR (sub_nat_to_rocq tL) a b))
           (fun rL tR a b => ct_l2b (rL (sub_nat_to_imported tR) a b)) (cnpl_jldp_canonical T) (cnpl_jldp_surjective T) PR PL).
Qed.

Lemma cnpl_iff (P Q : Prop) (PL QL : SProp) :
  PropSPropRel P PL -> PropSPropRel Q QL -> PropSPropRel (P <-> Q) (I.Iff PL QL).
Proof.
  intros HP HQ. apply prop_sprop_rel_intro.
  - intros [f g]. apply I.Iff_intro.
    + intro p. exact (prop_to_sprop _ _ HQ (f (sprop_to_prop _ _ HP p))).
    + intro q. exact (prop_to_sprop _ _ HP (g (sprop_to_prop _ _ HQ q))).
  - intros [f g]. apply strictly_inhabits. split.
    + intro p. exact (sprop_to_prop _ _ HQ (f (prop_to_sprop _ _ HP p))).
    + intro q. exact (sprop_to_prop _ _ HP (g (prop_to_sprop _ _ HQ q))).
Qed.


(* ------------------------------------------------------------------ *)
(** * Definitions *)

Lemma cnpl_opt_eq_rel (A : Type) (o1 o2 : option A) :
  PropSPropRel (Logic.eq o1 o2) (Lean.eq (cl_opt o1) (cl_opt o2)).
Proof.
  apply prop_sprop_rel_intro.
  - intro E. rewrite E. exact (@Lean.eq_refl _ _).
  - intro E. apply strictly_inhabits. exact (cnpl_opt_inj A o1 o2 (imported_eq_to_coq_eq _ _ E)).
Qed.

Section Defs.
Variables (Task Job : eqType).
Notation dT := (ct_decidable_eq Task).
Notation dJ := (ct_decidable_eq Job).
Variables (sR : UniprocessorSchedule.schedule Job) (sL : I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job dJ).
Hypothesis Hs : CnplSchedRel Job sR sL.
Variables (cR : Job -> nat) (cL : Job -> Lean.Nat).
Hypothesis Hc : CnplParRel Job cR cL.

Notation SA := (cnpl_US_scheduled_at Job sR sL Hs).
Notation CB := (cnpl_US_completed_by Job sR sL Hs cR cL Hc).

Theorem NonpreemptivePlatform_is_preemption_point'_correspondence tR tL (Ht : SubNatRel tR tL) :
  PropSPropRel (NonpreemptivePlatform.is_preemption_point' cR sR tR) (I.Prosa_Classic_Model_Schedule_Uni_Nonpreemptive_Platform_NonpreemptivePlatform_is_preemption_point' Job dJ cL sL tL).
Proof.
  have Hp := ct_sub_rel _ _ _ _ Ht (sub_nat_rel_canonical 1).
  apply: ct_or; first exact (sub_nat_eq_correspondence _ _ _ _ Ht (sub_nat_rel_canonical 0)).
  apply: ct_or.
  - exact (cnpl_tr (Hs _ _ Hp) (fun z => PropSPropRel (sR (tR - 1) = None) (Lean.eq z (cl_opt None)))
             (cnpl_opt_eq_rel Job (sR (tR - 1)) None)).
  - apply: ct_exists_identity => j.
    apply: ct_and; first exact (ct_bool_truth _ _ (SA j _ _ Hp)).
    exact (ct_bool_truth _ _ (CB j tR tL Ht)).
Qed.

Theorem NonpreemptivePlatform_is_preemption_point_correspondence tR tL (Ht : SubNatRel tR tL) :
  PropSPropRel (NonpreemptivePlatform.is_preemption_point cR sR tR) (I.Prosa_Classic_Model_Schedule_Uni_Nonpreemptive_Platform_NonpreemptivePlatform_is_preemption_point Job dJ cL sL tL).
Proof.
  have Hp := ct_sub_rel _ _ _ _ Ht (sub_nat_rel_canonical 1).
  apply: ct_or; first exact (sub_nat_eq_correspondence _ _ _ _ Ht (sub_nat_rel_canonical 0)).
  apply: ct_forall_identity => j.
  apply: ct_imp; first exact (ct_bool_truth _ _ (SA j _ _ Hp)).
  exact (ct_bool_truth _ _ (CB j tR tL Ht)).
Qed.

Theorem NonpreemptivePlatform_work_conserving_correspondence c0R c0L (Hc0 : CnplParRel Job c0R c0L) arrR arrL (Harr : CnplArrRel Job arrR arrL) :
  PropSPropRel (NonpreemptivePlatform.work_conserving cR c0R arrR sR) (I.Prosa_Classic_Model_Schedule_Uni_Nonpreemptive_Platform_NonpreemptivePlatform_work_conserving Job dJ cL c0L arrL sL).
Proof. exact (cnpl_UP_work_conserving Job sR sL Hs cR cL Hc c0R c0L Hc0 arrR arrL Harr). Qed.

Section Resp.
Variables (aR : Job -> nat) (aL : Job -> Lean.Nat).
Hypothesis Ha : CnplParRel Job aR aL.
Variables (arrR : ArrivalSequence.arrival_sequence Job)
  (arrL : I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrival_sequence Job dJ).
Hypothesis Harr : CnplArrRel Job arrR arrL.

Theorem NonpreemptivePlatform_respects_FP_policy_at_preemption_point_correspondence (job_task : Job -> Task) hR hL (Hh : CnplRelRel Task hR hL) :
  PropSPropRel (NonpreemptivePlatform.respects_FP_policy_at_preemption_point aR cR job_task arrR sR hR)
    (I.Prosa_Classic_Model_Schedule_Uni_Nonpreemptive_Platform_NonpreemptivePlatform_respects_FP_policy_at_preemption_point Task dT Job dJ aL cL job_task arrL sL hL).
Proof.
  apply: ct_forall_identity => j. apply: ct_forall_identity => j_hp. apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (cnpl_arrives_in Job arrR arrL Harr j).
  apply: ct_imp; first exact (ct_bool_truth _ _ (cnpl_US_backlogged Job sR sL Hs aR aL Ha cR cL Hc j tR tL Ht)).
  apply: ct_imp; first exact (ct_bool_truth _ _ (SA j_hp tR tL Ht)).
  apply: ct_imp; first exact (NonpreemptivePlatform_is_preemption_point_correspondence tR tL Ht).
  exact (ct_bool_truth _ _ (Hh (job_task j_hp) (job_task j))).
Qed.

Theorem NonpreemptivePlatform_respects_JLFP_policy_at_preemption_point_correspondence hR hL (Hh : CnplRelRel Job hR hL) :
  PropSPropRel (NonpreemptivePlatform.respects_JLFP_policy_at_preemption_point aR cR arrR sR hR)
    (I.Prosa_Classic_Model_Schedule_Uni_Nonpreemptive_Platform_NonpreemptivePlatform_respects_JLFP_policy_at_preemption_point Job dJ aL cL arrL sL hL).
Proof.
  apply: ct_forall_identity => j. apply: ct_forall_identity => j_hp. apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (cnpl_arrives_in Job arrR arrL Harr j).
  apply: ct_imp; first exact (ct_bool_truth _ _ (cnpl_US_backlogged Job sR sL Hs aR aL Ha cR cL Hc j tR tL Ht)).
  apply: ct_imp; first exact (ct_bool_truth _ _ (SA j_hp tR tL Ht)).
  apply: ct_imp; first exact (NonpreemptivePlatform_is_preemption_point_correspondence tR tL Ht).
  exact (ct_bool_truth _ _ (Hh j_hp j)).
Qed.
End Resp.
End Defs.

(* ------------------------------------------------------------------ *)
(** * Statements *)

Definition src_defitions_of_preemption_point_are_equal (Job : eqType) : Prop :=
  ltac:(type_of_term (@NonpreemptivePlatform.defitions_of_preemption_point_are_equal Job)).
Definition tgt_defitions_of_preemption_point_are_equal (Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Model_Schedule_Uni_Nonpreemptive_Platform_NonpreemptivePlatform_defitions_of_preemption_point_are_equal Job (ct_decidable_eq Job))).

Theorem NonpreemptivePlatform_defitions_of_preemption_point_are_equal_correspondence (Job : eqType) :
  PropSPropRel (src_defitions_of_preemption_point_are_equal Job) (tgt_defitions_of_preemption_point_are_equal Job).
Proof.
  unfold src_defitions_of_preemption_point_are_equal, tgt_defitions_of_preemption_point_are_equal.
  apply: cnpl_forall_par => cR cL Hc. apply: cnpl_forall_sched => sR sL Hs. apply: ct_forall_nat => tR tL Ht.
  exact (cnpl_iff _ _ _ _ (NonpreemptivePlatform_is_preemption_point_correspondence Job sR sL Hs cR cL Hc tR tL Ht)
           (NonpreemptivePlatform_is_preemption_point'_correspondence Job sR sL Hs cR cL Hc tR tL Ht)).
Qed.
