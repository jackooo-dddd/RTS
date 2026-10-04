From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq fintype bigop.
From prosa Require Import classic.model.time classic.model.schedule.uni.schedule classic.model.schedule.uni.nonpreemptive.schedule.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedClassicUniNonpreemptiveSchedule.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence ClassicUniNonpreemptiveScheduleBase ClassicUniNonpreemptiveScheduleList.

Module I := ImportedClassicUniNonpreemptiveSchedule.
Local Open Scope nat_scope.

(** Certificates for [classic/model/schedule/uni/nonpreemptive/schedule.v] (ProsaBuddy classic, commit f692cb7).

    Inputs: the job type is an [eqType], identified, with the Lean [DecidableEq] instance given by the eqType's decision
    procedure ([ct_decidable_eq]); times by [SubNatRel]; job costs pointwise through [SubNatRel]; uniprocessor
    schedules pointwise through the option map; all with two-way totals.  The imported uniprocessor schedule
    definitions are related as in the accepted classic uniprocessor schedule certificate (re-bound below, through the
    kernel-guarded body projections of [ClassicUniNonpreemptiveScheduleInterface]).

    Statements: the source side is the exact elaborated type of the pinned lemma (via [type of]; the source proof
    is not used). *)

Ltac type_of_term t := let T := type of t in exact T.
Notation cid := (fun z => z).

(* ------------------------------------------------------------------ *)
(** * Helpers (re-bound to this export from the accepted classic certificates) *)

(** Base definitions (as in the accepted classic base library), provided here when this export's library lacks them. *)

(* ------------------------------------------------------------------ *)
(** * Generic covers and helpers *)

Lemma cnp_forall_cover (A B : Type) (Rel : A -> B -> SProp) (toB : A -> B) (toA : B -> A)
    (HB : forall a, Rel a (toB a)) (HA : forall b, Rel (toA b) b) (PR : A -> Prop) (PL : B -> SProp) :
  (forall a b, Rel a b -> PropSPropRel (PR a) (PL b)) -> PropSPropRel (forall a, PR a) (forall b, PL b).
Proof.
  intro H. apply prop_sprop_rel_intro.
  - intros HR b. exact (prop_to_sprop _ _ (H _ _ (HA b)) (HR _)).
  - intro HL. apply strictly_inhabits. intro a. exact (sprop_to_prop _ _ (H _ _ (HB a)) (HL _)).
Qed.

Lemma cnp_false_rel : PropSPropRel Logic.False I.False.
Proof.
  apply prop_sprop_rel_intro.
  - exact ct_coq_false_to_target.
  - exact ct_target_false_to_strict.
Qed.

Lemma cnp_unmap_rel (T : Type) (l : I.List T) : ClListRel cid (cl_unmap cid l) l.
Proof. apply: coq_eq_to_imported_eq. exact (cl_map_unmap cid cid (fun _ => Logic.eq_refl _) l). Qed.

Lemma cnp_cl_map_inj (T : Type) (s1 s2 : seq T) : Logic.eq (cl_map cid s1) (cl_map cid s2) -> Logic.eq s1 s2.
Proof.
  intro E. rewrite -(cl_unmap_map cid cid (fun _ => Logic.eq_refl _) s1) -(cl_unmap_map cid cid (fun _ => Logic.eq_refl _) s2).
  by rewrite E.
Qed.

Lemma cnp_succ_rel nR nL : SubNatRel nR nL ->
  SubNatRel nR.+1 (I.HAdd_hAdd_inst7 Lean.Nat Lean.Nat Lean.Nat (I.instHAdd_inst1 Lean.Nat I.instAddNat) nL
                     (I.OfNat_ofNat_inst1 Lean.Nat 1 (I.instOfNatNat 1))).
Proof. intro Hn. exact (sub_imported_eq_congr Lean.Nat_succ _ _ Hn). Qed.

(* ------------------------------------------------------------------ *)
(** * Big concatenation over a half-open interval (as in the accepted arrival_sequence certificate) *)

Definition CnpParRel (T : Type) (pR : T -> nat) (pL : T -> Lean.Nat) : SProp := forall x, SubNatRel (pR x) (pL x).

Lemma cnp_forall_par (T : Type) (PR : (T -> nat) -> Prop) (PL : (T -> Lean.Nat) -> SProp) :
  (forall pR pL, CnpParRel T pR pL -> PropSPropRel (PR pR) (PL pL)) -> PropSPropRel (forall p, PR p) (forall p, PL p).
Proof.
  exact (cnp_forall_cover _ _ (CnpParRel T) (fun pR j => sub_nat_to_imported (pR j)) (fun pL j => sub_nat_to_rocq (pL j))
           (fun pR j => sub_nat_rel_canonical (pR j)) (fun pL j => sub_nat_rel_surjective (pL j)) PR PL).
Qed.

Fixpoint cnp_natl (s : seq nat) : I.List_inst1 Lean.Nat :=
  match s with [::] => I.List_nil_inst1 _ | x :: s' => I.List_cons_inst1 _ (sub_nat_to_imported x) (cnp_natl s') end.

Definition cnp_one : Lean.Nat := I.OfNat_ofNat_inst1 Lean.Nat 1 (I.instOfNatNat 1).

Lemma cnp_iota_range : forall n s,
  Logic.eq (I.List_range' (sub_nat_to_imported s) (sub_nat_to_imported n) cnp_one) (cnp_natl (iota s n)).
Proof.
  elim => [|n IH] s; first reflexivity.
  change (Logic.eq (I.List_cons_inst1 _ (sub_nat_to_imported s)
      (I.List_range' (sub_nat_to_imported (S s)) (sub_nat_to_imported n) cnp_one))
    (I.List_cons_inst1 _ (sub_nat_to_imported s) (cnp_natl (iota (S s) n)))).
  by rewrite IH.
Qed.

Lemma cnp_cl_map_comp {A B C : Type} (f : A -> B) (g : B -> C) : forall s : seq A,
  Logic.eq (cl_map (fun x => g (f x)) s) (cl_map g (map f s)).
Proof. elim => [|x s IH] //=. by rewrite IH. Qed.

Lemma cnp_cl_map_ext {A B : Type} (f g : A -> B) (H : forall x, Logic.eq (f x) (g x)) : forall s : seq A,
  Logic.eq (cl_map f s) (cl_map g s).
Proof. elim => [|x s IH] //=. by rewrite H IH. Qed.

Lemma cnp_big_seq {A : Type} (F : nat -> seq A) : forall s : seq nat,
  Logic.eq (\big[cat/[::]]_(i <- s) F i) (flatten (map F s)).
Proof. elim => [|x s IH]; first by rewrite big_nil. by rewrite big_cons IH. Qed.

Definition CnpFamRel (A : Type) (fR : nat -> seq A) (fL : Lean.Nat -> I.List A) : SProp :=
  forall nR nL, SubNatRel nR nL -> ClListRel cid (fR nR) (fL nL).

(* ------------------------------------------------------------------ *)
(** * Arrival sequences and parameters *)

(** The imported [ArrivalSequence] definitions this file's statements mention, related on related inputs. *)
Section ArrivalDefs.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).

End ArrivalDefs.

Section ArrivalDefs2.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).

End ArrivalDefs2.

Fixpoint cnp_snatl (s : seq nat) : I.List_inst1 Lean.Nat :=
  match s with [::] => I.List_nil_inst1 _ | x :: s' => I.List_cons_inst1 _ (sub_nat_to_imported x) (cnp_snatl s') end.

Lemma cnp_siota_range : forall n s,
  Logic.eq (I.List_range' (sub_nat_to_imported s) (sub_nat_to_imported n) (Lean.Nat_succ Lean.Nat_zero)) (cnp_snatl (iota s n)).
Proof.
  elim => [|n IH] s; first reflexivity.
  change (Logic.eq (I.List_cons_inst1 _ (sub_nat_to_imported s)
      (I.List_range' (sub_nat_to_imported (S s)) (sub_nat_to_imported n) (Lean.Nat_succ Lean.Nat_zero)))
    (I.List_cons_inst1 _ (sub_nat_to_imported s) (cnp_snatl (iota (S s) n)))).
  by rewrite IH.
Qed.

Lemma cnp_foldr_add (f : Lean.Nat -> Lean.Nat) (g : nat -> nat) (Hf : forall k, Logic.eq (f (sub_nat_to_imported k)) (sub_nat_to_imported (g k))) :
  forall s, Logic.eq (I.List_foldr_inst3 Lean.Nat Lean.Nat Lean.Nat_add Lean.Nat_zero (I.List_map_inst3 Lean.Nat Lean.Nat f (cnp_snatl s)))
                     (sub_nat_to_imported (foldr addn 0 (map g s))).
Proof.
  elim => [|k s IH] //=.
  change (Logic.eq (Lean.Nat_add (f (sub_nat_to_imported k))
            (I.List_foldr_inst3 Lean.Nat Lean.Nat Lean.Nat_add Lean.Nat_zero (I.List_map_inst3 Lean.Nat Lean.Nat f (cnp_snatl s))))
         (sub_nat_to_imported (g k + foldr addn 0 (map g s)))).
  rewrite IH Hf. exact (imported_eq_to_coq_eq _ _ (sub_add_canonical _ _)).
Qed.

Lemma cnp_big_fold (xs : seq nat) (F : nat -> nat) : Logic.eq (\sum_(i <- xs) F i) (foldr addn 0 (map F xs)).
Proof. elim: xs => [|x xs IH]; first by rewrite big_nil. by rewrite big_cons IH. Qed.

Definition CnpFunRel (FR : nat -> nat) (FL : Lean.Nat -> Lean.Nat) : SProp :=
  forall kR kL, SubNatRel kR kL -> SubNatRel (FR kR) (FL kL).

Lemma cnp_fun_canonical FR FL (HF : CnpFunRel FR FL) k : Logic.eq (FL (sub_nat_to_imported k)) (sub_nat_to_imported (FR k)).
Proof. exact (cl_nat_logic _ _ (HF _ _ (sub_nat_rel_canonical k))). Qed.

Lemma cnp_nat_sub_canonical (a b : nat) :
  Logic.eq (I.Nat_sub (sub_nat_to_imported a) (sub_nat_to_imported b)) (sub_nat_to_imported (a - b)).
Proof.
  elim: b => [|b IH]; first by rewrite subn0.
  change (Logic.eq (I.Nat_pred (I.Nat_sub (sub_nat_to_imported a) (sub_nat_to_imported b))) (sub_nat_to_imported (a - b.+1))).
  rewrite IH subnS. case: (a - b) => [|k]; reflexivity.
Qed.

Lemma cnp_ico mR mL nR nL FR FL (Hm : SubNatRel mR mL) (Hn : SubNatRel nR nL) (HF : CnpFunRel FR FL) :
  SubNatRel (\sum_(mR <= i < nR) FR i)
    (I.List_foldr_inst3 Lean.Nat Lean.Nat Lean.Nat_add Lean.Nat_zero
       (I.List_map_inst3 Lean.Nat Lean.Nat FL (I.List_range' mL (I.Nat_sub nL mL) (Lean.Nat_succ Lean.Nat_zero)))).
Proof.
  rewrite (cl_nat_logic _ _ Hm) (cl_nat_logic _ _ Hn).
  have -> : Logic.eq (I.Nat_sub (sub_nat_to_imported nR) (sub_nat_to_imported mR)) (sub_nat_to_imported (nR - mR))
    := cnp_nat_sub_canonical nR mR.
  rewrite cnp_siota_range.
  apply: coq_eq_to_imported_eq. apply: Logic.eq_sym. rewrite (cnp_foldr_add FL FR (cnp_fun_canonical FR FL HF)).
  by rewrite cnp_big_fold.
Qed.

(* ------------------------------------------------------------------ *)
(** * Options and uniprocessor schedules *)

(** Transport along the target equality (definitional UIP), as in the accepted global schedule certificate. *)
Definition cnp_tr {A : Type} {x y : A} (E : Lean.eq x y) (P : A -> Type) (h : P x) : P y :=
  match E in Lean.eq _ z return P z with Lean.eq_refl => h end.

Definition cnp_trs {A : Type} {x y : A} (E : Lean.eq x y) (P : A -> SProp) (h : P x) : P y :=
  match E in Lean.eq _ z return P z with Lean.eq_refl => h end.

Lemma cnp_opt_inj (A : Type) (o1 o2 : option A) : Logic.eq (cl_opt o1) (cl_opt o2) -> Logic.eq o1 o2.
Proof. intro E. by rewrite -(cl_unopt_opt o1) -(cl_unopt_opt o2) E. Qed.

Lemma cnp_opt_eqb_rel (A : eqType) (o1 o2 : option A) :
  PropSPropRel (is_true (o1 == o2)) (Lean.eq (cl_opt o1) (cl_opt o2)).
Proof.
  apply prop_sprop_rel_intro.
  - move=> /eqP E. rewrite E. exact (@Lean.eq_refl _ _).
  - intro E. apply strictly_inhabits. apply/eqP. exact (cnp_opt_inj A o1 o2 (imported_eq_to_coq_eq _ _ E)).
Qed.

Section Sched.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).
Notation LSched := (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job dJ).

Definition CnpSchedRel (sR : UniprocessorSchedule.schedule Job) (sL : LSched) : SProp :=
  forall tR tL, SubNatRel tR tL -> Lean.eq (cl_opt (sR tR)) (sL tL).

Definition cnp_sched_to_target (sR : UniprocessorSchedule.schedule Job) : LSched := fun tL => cl_opt (sR (sub_nat_to_rocq tL)).
Definition cnp_sched_to_source (sL : LSched) : UniprocessorSchedule.schedule Job := fun tR => cl_unopt (sL (sub_nat_to_imported tR)).

Lemma cnp_sched_canonical sR : CnpSchedRel sR (cnp_sched_to_target sR).
Proof. intros tR tL Ht. apply: coq_eq_to_imported_eq. by rewrite /cnp_sched_to_target (cl_nat_input _ _ Ht). Qed.

Lemma cnp_sched_surjective sL : CnpSchedRel (cnp_sched_to_source sL) sL.
Proof.
  intros tR tL Ht. apply: coq_eq_to_imported_eq. rewrite /cnp_sched_to_source cl_opt_unopt.
  by rewrite (cl_nat_logic _ _ Ht).
Qed.

Lemma cnp_forall_sched (PR : UniprocessorSchedule.schedule Job -> Prop) (PL : LSched -> SProp) :
  (forall sR sL, CnpSchedRel sR sL -> PropSPropRel (PR sR) (PL sL)) -> PropSPropRel (forall s, PR s) (forall s, PL s).
Proof. exact (cnp_forall_cover _ _ CnpSchedRel cnp_sched_to_target cnp_sched_to_source cnp_sched_canonical cnp_sched_surjective PR PL). Qed.

End Sched.

(* ------------------------------------------------------------------ *)
(** * Definitions *)

Lemma cnp_US_schedule (Job : eqType) :
  And (forall sR : UniprocessorSchedule.schedule Job, CnpSchedRel Job sR (cnp_sched_to_target Job sR))
      (forall sL : I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job (ct_decidable_eq Job), CnpSchedRel Job (cnp_sched_to_source Job sL) sL).
Proof. exact (And_intro _ _ (cnp_sched_canonical Job) (cnp_sched_surjective Job)). Qed.

Section USchedDefs.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).
Variables (sR : UniprocessorSchedule.schedule Job) (sL : I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job dJ).
Hypothesis Hs : CnpSchedRel Job sR sL.

Lemma cnp_US_scheduled_at j tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (UniprocessorSchedule.scheduled_at sR j tR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_scheduled_at Job dJ sL j tL).
Proof.
  apply: ct_decide_bool.
  exact (cnp_tr (Hs tR tL Ht) (fun z => PropSPropRel (sR tR == Some j) (Lean.eq z (cl_opt (Some j))))
           (cnp_opt_eqb_rel Job (sR tR) (Some j))).
Qed.

Lemma cnp_US_service_at j tR tL (Ht : SubNatRel tR tL) :
  SubNatRel (UniprocessorSchedule.service_at sR j tR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_service_at Job dJ sL j tL).
Proof. exact (ct_bool_to_nat _ _ (cnp_US_scheduled_at j tR tL Ht)). Qed.

Lemma cnp_service_at_fun j : CnpFunRel (fun t => UniprocessorSchedule.service_at sR j t) (fun t => I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_service_at Job dJ sL j t).
Proof. intros kR kL Hk. exact (cnp_US_service_at j kR kL Hk). Qed.

Lemma cnp_US_service_during j t1R t1L (H1 : SubNatRel t1R t1L) t2R t2L (H2 : SubNatRel t2R t2L) :
  SubNatRel (UniprocessorSchedule.service_during sR j t1R t2R) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_service_during Job dJ sL j t1L t2L).
Proof. exact (cnp_ico _ _ _ _ _ _ H1 H2 (cnp_service_at_fun j)). Qed.

Lemma cnp_US_service j tR tL (Ht : SubNatRel tR tL) :
  SubNatRel (UniprocessorSchedule.service sR j tR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_service Job dJ sL j tL).
Proof. exact (cnp_US_service_during j 0 _ (sub_nat_rel_canonical 0) tR tL Ht). Qed.

Lemma cnp_US_completed_by cR cL (Hc : CnpParRel Job cR cL) j tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (UniprocessorSchedule.completed_by cR sR j tR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_completed_by Job dJ cL sL j tL).
Proof. exact (ct_decide_le _ _ _ _ (Hc j) (cnp_US_service j tR tL Ht)). Qed.

Lemma cnp_US_completed_jobs_dont_execute cR cL (Hc : CnpParRel Job cR cL) :
  PropSPropRel (UniprocessorSchedule.completed_jobs_dont_execute cR sR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_completed_jobs_dont_execute Job dJ cL sL).
Proof.
  apply: ct_forall_identity => j. apply: ct_forall_nat => tR tL Ht.
  exact (sub_nat_le_correspondence _ _ _ _ (cnp_US_service j tR tL Ht) (Hc j)).
Qed.

Lemma cnp_US_remaining_cost cR cL (Hc : CnpParRel Job cR cL) j tR tL (Ht : SubNatRel tR tL) :
  SubNatRel (UniprocessorSchedule.remaining_cost cR sR j tR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_remaining_cost Job dJ cL sL j tL).
Proof. exact (ct_sub_rel _ _ _ _ (Hc j) (cnp_US_service j tR tL Ht)). Qed.

End USchedDefs.


(* ------------------------------------------------------------------ *)
(** * Definitions *)

Theorem NonpreemptiveSchedule_is_nonpreemptive_schedule_correspondence (Job : eqType) sR sL (Hs : CnpSchedRel Job sR sL)
    cR cL (Hc : CnpParRel Job cR cL) :
  PropSPropRel (NonpreemptiveSchedule.is_nonpreemptive_schedule cR sR) (I.Prosa_Classic_Model_Schedule_Uni_Nonpreemptive_Schedule_NonpreemptiveSchedule_is_nonpreemptive_schedule Job (ct_decidable_eq Job) cL sL).
Proof.
  apply: ct_forall_identity => j. apply: ct_forall_nat => tR tL Ht. apply: ct_forall_nat => t'R t'L Ht'.
  apply: ct_imp; first exact (sub_nat_le_correspondence _ _ _ _ Ht Ht').
  apply: ct_imp; first exact (ct_bool_truth _ _ (cnp_US_scheduled_at Job sR sL Hs j tR tL Ht)).
  apply: ct_imp; first exact (ct_bool_truth _ _ (ct_bool_not _ _ (cnp_US_completed_by Job sR sL Hs cR cL Hc j t'R t'L Ht'))).
  exact (ct_bool_truth _ _ (cnp_US_scheduled_at Job sR sL Hs j t'R t'L Ht')).
Qed.

(* ------------------------------------------------------------------ *)
(** * Statements *)

Definition src_subh3 : Prop := ltac:(type_of_term @NonpreemptiveSchedule.subh3).
Definition tgt_subh3 : SProp := ltac:(type_of_term I.Prosa_Classic_Model_Schedule_Uni_Nonpreemptive_Schedule_NonpreemptiveSchedule_subh3).

Theorem NonpreemptiveSchedule_subh3_correspondence : PropSPropRel src_subh3 tgt_subh3.
Proof.
  unfold src_subh3, tgt_subh3.
  apply: ct_forall_nat => mR mL Hm. apply: ct_forall_nat => nR nL Hn. apply: ct_forall_nat => pR pL Hp.
  apply: ct_imp; first exact (sub_nat_le_correspondence _ _ _ _ (sub_add_correspondence _ _ _ _ Hm Hp) Hn).
  exact (sub_nat_le_correspondence _ _ _ _ Hm (ct_sub_rel _ _ _ _ Hn Hp)).
Qed.

Definition src_continuity_of_nonpreemptive_scheduling (Job : eqType) : Prop :=
  ltac:(type_of_term (@NonpreemptiveSchedule.continuity_of_nonpreemptive_scheduling Job)).
Definition tgt_continuity_of_nonpreemptive_scheduling (Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Model_Schedule_Uni_Nonpreemptive_Schedule_NonpreemptiveSchedule_continuity_of_nonpreemptive_scheduling Job (ct_decidable_eq Job))).

Theorem NonpreemptiveSchedule_continuity_of_nonpreemptive_scheduling_correspondence (Job : eqType) :
  PropSPropRel (src_continuity_of_nonpreemptive_scheduling Job) (tgt_continuity_of_nonpreemptive_scheduling Job).
Proof.
  unfold src_continuity_of_nonpreemptive_scheduling, tgt_continuity_of_nonpreemptive_scheduling.
  apply: cnp_forall_par => cR cL Hc. apply: cnp_forall_sched => sR sL Hs.
  apply: ct_imp; first exact (NonpreemptiveSchedule_is_nonpreemptive_schedule_correspondence Job sR sL Hs cR cL Hc).
  apply: ct_forall_identity => j.
  apply: ct_imp; first exact (cnp_US_completed_jobs_dont_execute Job sR sL Hs cR cL Hc).
  apply: ct_forall_nat => tR tL Ht. apply: ct_forall_nat => t1R t1L H1. apply: ct_forall_nat => t2R t2L H2.
  apply: ct_imp; first exact (ct_bool_truth _ _ (ct_bool_and _ _ _ _ (ct_decide_le _ _ _ _ H1 Ht) (ct_decide_le _ _ _ _ Ht H2))).
  apply: ct_imp; first exact (ct_bool_truth _ _ (cnp_US_scheduled_at Job sR sL Hs j t1R t1L H1)).
  apply: ct_imp; first exact (ct_bool_truth _ _ (cnp_US_scheduled_at Job sR sL Hs j t2R t2L H2)).
  exact (ct_bool_truth _ _ (cnp_US_scheduled_at Job sR sL Hs j tR tL Ht)).
Qed.
Definition src_in_nonpreemption_schedule_preemption_implies_completeness (Job : eqType) : Prop :=
  ltac:(type_of_term (@NonpreemptiveSchedule.in_nonpreemption_schedule_preemption_implies_completeness Job)).
Definition tgt_in_nonpreemption_schedule_preemption_implies_completeness (Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Model_Schedule_Uni_Nonpreemptive_Schedule_NonpreemptiveSchedule_in_nonpreemption_schedule_preemption_implies_completeness Job (ct_decidable_eq Job))).

Theorem NonpreemptiveSchedule_in_nonpreemption_schedule_preemption_implies_completeness_correspondence (Job : eqType) :
  PropSPropRel (src_in_nonpreemption_schedule_preemption_implies_completeness Job) (tgt_in_nonpreemption_schedule_preemption_implies_completeness Job).
Proof.
  unfold src_in_nonpreemption_schedule_preemption_implies_completeness, tgt_in_nonpreemption_schedule_preemption_implies_completeness.
  apply: cnp_forall_par => cR cL Hc. apply: cnp_forall_sched => sR sL Hs.
  apply: ct_imp; first exact (NonpreemptiveSchedule_is_nonpreemptive_schedule_correspondence Job sR sL Hs cR cL Hc).
  apply: ct_forall_identity => j.
  apply: ct_forall_nat => tR tL Ht. apply: ct_forall_nat => t'R t'L Ht'.
  apply: ct_imp; first exact (sub_nat_le_correspondence _ _ _ _ Ht Ht').
  apply: ct_imp; first exact (ct_bool_truth _ _ (cnp_US_scheduled_at Job sR sL Hs j tR tL Ht)).
  apply: ct_imp; first exact (ct_bool_truth _ _ (ct_bool_not _ _ (cnp_US_scheduled_at Job sR sL Hs j t'R t'L Ht'))).
  exact (ct_bool_truth _ _ (cnp_US_completed_by Job sR sL Hs cR cL Hc j t'R t'L Ht')).
Qed.
Definition src_job_completes_after_remaining_cost (Job : eqType) : Prop :=
  ltac:(type_of_term (@NonpreemptiveSchedule.job_completes_after_remaining_cost Job)).
Definition tgt_job_completes_after_remaining_cost (Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Model_Schedule_Uni_Nonpreemptive_Schedule_NonpreemptiveSchedule_job_completes_after_remaining_cost Job (ct_decidable_eq Job))).

Theorem NonpreemptiveSchedule_job_completes_after_remaining_cost_correspondence (Job : eqType) :
  PropSPropRel (src_job_completes_after_remaining_cost Job) (tgt_job_completes_after_remaining_cost Job).
Proof.
  unfold src_job_completes_after_remaining_cost, tgt_job_completes_after_remaining_cost.
  apply: cnp_forall_par => cR cL Hc. apply: cnp_forall_sched => sR sL Hs.
  apply: ct_imp; first exact (NonpreemptiveSchedule_is_nonpreemptive_schedule_correspondence Job sR sL Hs cR cL Hc).
  apply: ct_imp; first exact (cnp_US_completed_jobs_dont_execute Job sR sL Hs cR cL Hc).
  apply: ct_forall_identity => j. apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (ct_bool_truth _ _ (cnp_US_scheduled_at Job sR sL Hs j tR tL Ht)).
  exact (ct_bool_truth _ _ (cnp_US_completed_by Job sR sL Hs cR cL Hc j _ _ (sub_add_correspondence _ _ _ _ Ht (cnp_US_remaining_cost Job sR sL Hs cR cL Hc j tR tL Ht)))).
Qed.
Definition src_j_is_scheduled_at_t_minus_service (Job : eqType) : Prop :=
  ltac:(type_of_term (@NonpreemptiveSchedule.j_is_scheduled_at_t_minus_service Job)).
Definition tgt_j_is_scheduled_at_t_minus_service (Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Model_Schedule_Uni_Nonpreemptive_Schedule_NonpreemptiveSchedule_j_is_scheduled_at_t_minus_service Job (ct_decidable_eq Job))).

Theorem NonpreemptiveSchedule_j_is_scheduled_at_t_minus_service_correspondence (Job : eqType) :
  PropSPropRel (src_j_is_scheduled_at_t_minus_service Job) (tgt_j_is_scheduled_at_t_minus_service Job).
Proof.
  unfold src_j_is_scheduled_at_t_minus_service, tgt_j_is_scheduled_at_t_minus_service.
  apply: cnp_forall_par => cR cL Hc. apply: cnp_forall_sched => sR sL Hs.
  apply: ct_imp; first exact (NonpreemptiveSchedule_is_nonpreemptive_schedule_correspondence Job sR sL Hs cR cL Hc).
  apply: ct_imp; first exact (cnp_US_completed_jobs_dont_execute Job sR sL Hs cR cL Hc).
  apply: ct_forall_identity => j. apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (ct_bool_truth _ _ (cnp_US_scheduled_at Job sR sL Hs j tR tL Ht)).
  have Hts := ct_sub_rel _ _ _ _ Ht (cnp_US_service Job sR sL Hs j tR tL Ht).
  have Htr := sub_add_correspondence _ _ _ _ Ht (cnp_US_remaining_cost Job sR sL Hs cR cL Hc j tR tL Ht).
  exact (ct_bool_truth _ _ (cnp_US_scheduled_at Job sR sL Hs j _ _ Hts)).
Qed.
Definition src_j_is_not_scheduled_at_t_minus_service_minus_one (Job : eqType) : Prop :=
  ltac:(type_of_term (@NonpreemptiveSchedule.j_is_not_scheduled_at_t_minus_service_minus_one Job)).
Definition tgt_j_is_not_scheduled_at_t_minus_service_minus_one (Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Model_Schedule_Uni_Nonpreemptive_Schedule_NonpreemptiveSchedule_j_is_not_scheduled_at_t_minus_service_minus_one Job (ct_decidable_eq Job))).

Theorem NonpreemptiveSchedule_j_is_not_scheduled_at_t_minus_service_minus_one_correspondence (Job : eqType) :
  PropSPropRel (src_j_is_not_scheduled_at_t_minus_service_minus_one Job) (tgt_j_is_not_scheduled_at_t_minus_service_minus_one Job).
Proof.
  unfold src_j_is_not_scheduled_at_t_minus_service_minus_one, tgt_j_is_not_scheduled_at_t_minus_service_minus_one.
  apply: cnp_forall_par => cR cL Hc. apply: cnp_forall_sched => sR sL Hs.
  apply: ct_imp; first exact (NonpreemptiveSchedule_is_nonpreemptive_schedule_correspondence Job sR sL Hs cR cL Hc).
  apply: ct_imp; first exact (cnp_US_completed_jobs_dont_execute Job sR sL Hs cR cL Hc).
  apply: ct_forall_identity => j. apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (ct_bool_truth _ _ (cnp_US_scheduled_at Job sR sL Hs j tR tL Ht)).
  have Hts := ct_sub_rel _ _ _ _ Ht (cnp_US_service Job sR sL Hs j tR tL Ht).
  have Htr := sub_add_correspondence _ _ _ _ Ht (cnp_US_remaining_cost Job sR sL Hs cR cL Hc j tR tL Ht).
  apply: ct_imp; first exact (sub_nat_lt_correspondence _ _ _ _ (sub_nat_rel_canonical 0) Hts).
  exact (ct_bool_truth _ _ (ct_bool_not _ _ (cnp_US_scheduled_at Job sR sL Hs j _ _ (ct_sub_rel _ _ _ _ Hts (sub_nat_rel_canonical 1))))).
Qed.
Definition src_j_is_not_scheduled_earlier_t_minus_service (Job : eqType) : Prop :=
  ltac:(type_of_term (@NonpreemptiveSchedule.j_is_not_scheduled_earlier_t_minus_service Job)).
Definition tgt_j_is_not_scheduled_earlier_t_minus_service (Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Model_Schedule_Uni_Nonpreemptive_Schedule_NonpreemptiveSchedule_j_is_not_scheduled_earlier_t_minus_service Job (ct_decidable_eq Job))).

Theorem NonpreemptiveSchedule_j_is_not_scheduled_earlier_t_minus_service_correspondence (Job : eqType) :
  PropSPropRel (src_j_is_not_scheduled_earlier_t_minus_service Job) (tgt_j_is_not_scheduled_earlier_t_minus_service Job).
Proof.
  unfold src_j_is_not_scheduled_earlier_t_minus_service, tgt_j_is_not_scheduled_earlier_t_minus_service.
  apply: cnp_forall_par => cR cL Hc. apply: cnp_forall_sched => sR sL Hs.
  apply: ct_imp; first exact (NonpreemptiveSchedule_is_nonpreemptive_schedule_correspondence Job sR sL Hs cR cL Hc).
  apply: ct_imp; first exact (cnp_US_completed_jobs_dont_execute Job sR sL Hs cR cL Hc).
  apply: ct_forall_identity => j. apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (ct_bool_truth _ _ (cnp_US_scheduled_at Job sR sL Hs j tR tL Ht)).
  have Hts := ct_sub_rel _ _ _ _ Ht (cnp_US_service Job sR sL Hs j tR tL Ht).
  have Htr := sub_add_correspondence _ _ _ _ Ht (cnp_US_remaining_cost Job sR sL Hs cR cL Hc j tR tL Ht).
  apply: ct_forall_nat => t'R t'L Ht'.
  apply: ct_imp; first exact (sub_nat_lt_correspondence _ _ _ _ Ht' Hts).
  exact (ct_bool_truth _ _ (ct_bool_not _ _ (cnp_US_scheduled_at Job sR sL Hs j _ _ Ht'))).
Qed.
Definition src_j_is_scheduled_at_t_plus_remaining_cost_minus_one (Job : eqType) : Prop :=
  ltac:(type_of_term (@NonpreemptiveSchedule.j_is_scheduled_at_t_plus_remaining_cost_minus_one Job)).
Definition tgt_j_is_scheduled_at_t_plus_remaining_cost_minus_one (Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Model_Schedule_Uni_Nonpreemptive_Schedule_NonpreemptiveSchedule_j_is_scheduled_at_t_plus_remaining_cost_minus_one Job (ct_decidable_eq Job))).

Theorem NonpreemptiveSchedule_j_is_scheduled_at_t_plus_remaining_cost_minus_one_correspondence (Job : eqType) :
  PropSPropRel (src_j_is_scheduled_at_t_plus_remaining_cost_minus_one Job) (tgt_j_is_scheduled_at_t_plus_remaining_cost_minus_one Job).
Proof.
  unfold src_j_is_scheduled_at_t_plus_remaining_cost_minus_one, tgt_j_is_scheduled_at_t_plus_remaining_cost_minus_one.
  apply: cnp_forall_par => cR cL Hc. apply: cnp_forall_sched => sR sL Hs.
  apply: ct_imp; first exact (NonpreemptiveSchedule_is_nonpreemptive_schedule_correspondence Job sR sL Hs cR cL Hc).
  apply: ct_imp; first exact (cnp_US_completed_jobs_dont_execute Job sR sL Hs cR cL Hc).
  apply: ct_forall_identity => j. apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (ct_bool_truth _ _ (cnp_US_scheduled_at Job sR sL Hs j tR tL Ht)).
  have Hts := ct_sub_rel _ _ _ _ Ht (cnp_US_service Job sR sL Hs j tR tL Ht).
  have Htr := sub_add_correspondence _ _ _ _ Ht (cnp_US_remaining_cost Job sR sL Hs cR cL Hc j tR tL Ht).
  exact (ct_bool_truth _ _ (cnp_US_scheduled_at Job sR sL Hs j _ _ (ct_sub_rel _ _ _ _ Htr (sub_nat_rel_canonical 1)))).
Qed.
Definition src_j_is_not_scheduled_after_t_plus_remaining_cost_minus_one (Job : eqType) : Prop :=
  ltac:(type_of_term (@NonpreemptiveSchedule.j_is_not_scheduled_after_t_plus_remaining_cost_minus_one Job)).
Definition tgt_j_is_not_scheduled_after_t_plus_remaining_cost_minus_one (Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Model_Schedule_Uni_Nonpreemptive_Schedule_NonpreemptiveSchedule_j_is_not_scheduled_after_t_plus_remaining_cost_minus_one Job (ct_decidable_eq Job))).

Theorem NonpreemptiveSchedule_j_is_not_scheduled_after_t_plus_remaining_cost_minus_one_correspondence (Job : eqType) :
  PropSPropRel (src_j_is_not_scheduled_after_t_plus_remaining_cost_minus_one Job) (tgt_j_is_not_scheduled_after_t_plus_remaining_cost_minus_one Job).
Proof.
  unfold src_j_is_not_scheduled_after_t_plus_remaining_cost_minus_one, tgt_j_is_not_scheduled_after_t_plus_remaining_cost_minus_one.
  apply: cnp_forall_par => cR cL Hc. apply: cnp_forall_sched => sR sL Hs.
  apply: ct_imp; first exact (NonpreemptiveSchedule_is_nonpreemptive_schedule_correspondence Job sR sL Hs cR cL Hc).
  apply: ct_imp; first exact (cnp_US_completed_jobs_dont_execute Job sR sL Hs cR cL Hc).
  apply: ct_forall_identity => j. apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (ct_bool_truth _ _ (cnp_US_scheduled_at Job sR sL Hs j tR tL Ht)).
  have Hts := ct_sub_rel _ _ _ _ Ht (cnp_US_service Job sR sL Hs j tR tL Ht).
  have Htr := sub_add_correspondence _ _ _ _ Ht (cnp_US_remaining_cost Job sR sL Hs cR cL Hc j tR tL Ht).
  apply: ct_forall_nat => t'R t'L Ht'.
  apply: ct_imp; first exact (sub_nat_le_correspondence _ _ _ _ Htr Ht').
  exact (ct_bool_truth _ _ (ct_bool_not _ _ (cnp_US_scheduled_at Job sR sL Hs j _ _ Ht'))).
Qed.
Definition src_nonpreemptive_executing_interval (Job : eqType) : Prop :=
  ltac:(type_of_term (@NonpreemptiveSchedule.nonpreemptive_executing_interval Job)).
Definition tgt_nonpreemptive_executing_interval (Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Model_Schedule_Uni_Nonpreemptive_Schedule_NonpreemptiveSchedule_nonpreemptive_executing_interval Job (ct_decidable_eq Job))).

Theorem NonpreemptiveSchedule_nonpreemptive_executing_interval_correspondence (Job : eqType) :
  PropSPropRel (src_nonpreemptive_executing_interval Job) (tgt_nonpreemptive_executing_interval Job).
Proof.
  unfold src_nonpreemptive_executing_interval, tgt_nonpreemptive_executing_interval.
  apply: cnp_forall_par => cR cL Hc. apply: cnp_forall_sched => sR sL Hs.
  apply: ct_imp; first exact (NonpreemptiveSchedule_is_nonpreemptive_schedule_correspondence Job sR sL Hs cR cL Hc).
  apply: ct_imp; first exact (cnp_US_completed_jobs_dont_execute Job sR sL Hs cR cL Hc).
  apply: ct_forall_identity => j. apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (ct_bool_truth _ _ (cnp_US_scheduled_at Job sR sL Hs j tR tL Ht)).
  have Hts := ct_sub_rel _ _ _ _ Ht (cnp_US_service Job sR sL Hs j tR tL Ht).
  have Htr := sub_add_correspondence _ _ _ _ Ht (cnp_US_remaining_cost Job sR sL Hs cR cL Hc j tR tL Ht).
  apply: ct_forall_nat => t'R t'L Ht'.
  apply: ct_imp; first exact (ct_bool_truth _ _ (ct_bool_and _ _ _ _ (ct_decide_le _ _ _ _ Hts Ht') (ct_decide_lt _ _ _ _ Ht' Htr))).
  exact (ct_bool_truth _ _ (cnp_US_scheduled_at Job sR sL Hs j _ _ Ht')).
Qed.
