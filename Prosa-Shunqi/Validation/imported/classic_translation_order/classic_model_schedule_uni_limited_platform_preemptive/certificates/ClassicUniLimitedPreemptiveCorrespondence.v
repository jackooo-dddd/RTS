From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq fintype bigop.
From prosa Require Import util.epsilon classic.model.time classic.model.arrival.basic.arrival_sequence classic.model.arrival.basic.job classic.model.priority classic.model.schedule.uni.schedule classic.model.schedule.uni.basic.platform classic.model.schedule.uni.nonpreemptive.schedule classic.model.schedule.uni.limited.platform.definitions classic.model.schedule.uni.limited.platform.preemptive.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedClassicUniLimitedPreemptive.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence ClassicUniLimitedPreemptiveBase ClassicUniLimitedPreemptiveList.

Module I := ImportedClassicUniLimitedPreemptive.
Local Open Scope nat_scope.

(** Certificates for [classic/model/schedule/uni/limited/platform/preemptive.v] (ProsaBuddy classic, commit f692cb7).

    Inputs: the job and task types are [eqType]s, identified, with the Lean [DecidableEq] instances given by the
    eqTypes' decision procedures ([ct_decidable_eq]); [job_task] identified; times by [SubNatRel]; job/task parameters
    pointwise through [SubNatRel]; uniprocessor schedules pointwise through the option map; arrival sequences pointwise
    on related times; all with two-way totals.  The imported schedule, job and limited-preemption platform definitions
    are related as in the accepted classic certificates (re-bound below).

    Statements: the source side is the exact elaborated type of the pinned lemma (via [type of]; the source proof
    is not used).  Where the binder lists put task parameters before the job type, the job type is fixed as an
    [eqType] with its canonical Lean instance and the task parameters stay universally quantified on both sides. *)

Ltac type_of_term t := let T := type of t in exact T.
Notation cid := (fun z => z).

(* ------------------------------------------------------------------ *)
(** * Helpers (re-bound to this export from the accepted classic certificates) *)

(** Base definitions (as in the accepted classic base library), provided here when this export's library lacks them. *)

(* ------------------------------------------------------------------ *)
(** * Generic covers and helpers *)

Lemma cpm_forall_cover (A B : Type) (Rel : A -> B -> SProp) (toB : A -> B) (toA : B -> A)
    (HB : forall a, Rel a (toB a)) (HA : forall b, Rel (toA b) b) (PR : A -> Prop) (PL : B -> SProp) :
  (forall a b, Rel a b -> PropSPropRel (PR a) (PL b)) -> PropSPropRel (forall a, PR a) (forall b, PL b).
Proof.
  intro H. apply prop_sprop_rel_intro.
  - intros HR b. exact (prop_to_sprop _ _ (H _ _ (HA b)) (HR _)).
  - intro HL. apply strictly_inhabits. intro a. exact (sprop_to_prop _ _ (H _ _ (HB a)) (HL _)).
Qed.

Lemma cpm_false_rel : PropSPropRel Logic.False I.False.
Proof.
  apply prop_sprop_rel_intro.
  - exact ct_coq_false_to_target.
  - exact ct_target_false_to_strict.
Qed.

Lemma cpm_mem (T : eqType) x s sL : ClListRel cid s sL ->
  PropSPropRel (x \in s) (I.Membership_mem T (I.List T) (I.List_instMembership T) sL x).
Proof. exact (cl_mem_rel_list T T cid cid (fun _ => Logic.eq_refl _) x s sL). Qed.

Lemma cpm_unmap_rel (T : Type) (l : I.List T) : ClListRel cid (cl_unmap cid l) l.
Proof. apply: coq_eq_to_imported_eq. exact (cl_map_unmap cid cid (fun _ => Logic.eq_refl _) l). Qed.

Lemma cpm_cl_map_inj (T : Type) (s1 s2 : seq T) : Logic.eq (cl_map cid s1) (cl_map cid s2) -> Logic.eq s1 s2.
Proof.
  intro E. rewrite -(cl_unmap_map cid cid (fun _ => Logic.eq_refl _) s1) -(cl_unmap_map cid cid (fun _ => Logic.eq_refl _) s2).
  by rewrite E.
Qed.

Lemma cpm_succ_rel nR nL : SubNatRel nR nL ->
  SubNatRel nR.+1 (I.HAdd_hAdd_inst7 Lean.Nat Lean.Nat Lean.Nat (I.instHAdd_inst1 Lean.Nat I.instAddNat) nL
                     (I.OfNat_ofNat_inst1 Lean.Nat 1 (I.instOfNatNat 1))).
Proof. intro Hn. exact (sub_imported_eq_congr Lean.Nat_succ _ _ Hn). Qed.

(* ------------------------------------------------------------------ *)
(** * Big concatenation over a half-open interval (as in the accepted arrival_sequence certificate) *)

Lemma cpm_forall_list (T : Type) (PR : seq T -> Prop) (PL : I.List T -> SProp) :
  (forall sR sL, ClListRel (B := T) cid sR sL -> PropSPropRel (PR sR) (PL sL)) -> PropSPropRel (forall s, PR s) (forall s, PL s).
Proof.
  exact (cpm_forall_cover _ _ (fun sR sL => ClListRel (B := T) cid sR sL) (cl_map cid) (cl_unmap cid)
           (fun s => @Lean.eq_refl _ _) (fun l => cpm_unmap_rel T l) PR PL).
Qed.

Definition CpmParRel (T : Type) (pR : T -> nat) (pL : T -> Lean.Nat) : SProp := forall x, SubNatRel (pR x) (pL x).

Lemma cpm_forall_par (T : Type) (PR : (T -> nat) -> Prop) (PL : (T -> Lean.Nat) -> SProp) :
  (forall pR pL, CpmParRel T pR pL -> PropSPropRel (PR pR) (PL pL)) -> PropSPropRel (forall p, PR p) (forall p, PL p).
Proof.
  exact (cpm_forall_cover _ _ (CpmParRel T) (fun pR j => sub_nat_to_imported (pR j)) (fun pL j => sub_nat_to_rocq (pL j))
           (fun pR j => sub_nat_rel_canonical (pR j)) (fun pL j => sub_nat_rel_surjective (pL j)) PR PL).
Qed.

Fixpoint cpm_natl (s : seq nat) : I.List_inst1 Lean.Nat :=
  match s with [::] => I.List_nil_inst1 _ | x :: s' => I.List_cons_inst1 _ (sub_nat_to_imported x) (cpm_natl s') end.

Definition cpm_one : Lean.Nat := I.OfNat_ofNat_inst1 Lean.Nat 1 (I.instOfNatNat 1).

Lemma cpm_iota_range : forall n s,
  Logic.eq (I.List_range' (sub_nat_to_imported s) (sub_nat_to_imported n) cpm_one) (cpm_natl (iota s n)).
Proof.
  elim => [|n IH] s; first reflexivity.
  change (Logic.eq (I.List_cons_inst1 _ (sub_nat_to_imported s)
      (I.List_range' (sub_nat_to_imported (S s)) (sub_nat_to_imported n) cpm_one))
    (I.List_cons_inst1 _ (sub_nat_to_imported s) (cpm_natl (iota (S s) n)))).
  by rewrite IH.
Qed.

Lemma cpm_cl_map_comp {A B C : Type} (f : A -> B) (g : B -> C) : forall s : seq A,
  Logic.eq (cl_map (fun x => g (f x)) s) (cl_map g (map f s)).
Proof. elim => [|x s IH] //=. by rewrite IH. Qed.

Lemma cpm_cl_map_ext {A B : Type} (f g : A -> B) (H : forall x, Logic.eq (f x) (g x)) : forall s : seq A,
  Logic.eq (cl_map f s) (cl_map g s).
Proof. elim => [|x s IH] //=. by rewrite H IH. Qed.

Lemma cpm_big_seq {A : Type} (F : nat -> seq A) : forall s : seq nat,
  Logic.eq (\big[cat/[::]]_(i <- s) F i) (flatten (map F s)).
Proof. elim => [|x s IH]; first by rewrite big_nil. by rewrite big_cons IH. Qed.

Definition CpmFamRel (A : Type) (fR : nat -> seq A) (fL : Lean.Nat -> I.List A) : SProp :=
  forall nR nL, SubNatRel nR nL -> ClListRel cid (fR nR) (fL nL).

(* ------------------------------------------------------------------ *)
(** * Arrival sequences and parameters *)

Section Rel.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).
Notation LArr := (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrival_sequence Job dJ).

Definition CpmArrRel (aR : ArrivalSequence.arrival_sequence Job) (aL : LArr) : SProp :=
  forall tR tL, SubNatRel tR tL -> ClListRel cid (aR tR) (aL tL).

Definition cpm_arr_to_target (aR : ArrivalSequence.arrival_sequence Job) : LArr :=
  fun tL => cl_map cid (aR (sub_nat_to_rocq tL)).

Definition cpm_arr_to_source (aL : LArr) : ArrivalSequence.arrival_sequence Job :=
  fun tR => cl_unmap cid (aL (sub_nat_to_imported tR)).

Lemma cpm_arr_canonical aR : CpmArrRel aR (cpm_arr_to_target aR).
Proof.
  intros tR tL Ht. have E := cl_nat_logic _ _ Ht. subst tL.
  apply: coq_eq_to_imported_eq. rewrite /cpm_arr_to_target sub_nat_rocq_roundtrip. reflexivity.
Qed.

Lemma cpm_arr_surjective aL : CpmArrRel (cpm_arr_to_source aL) aL.
Proof.
  intros tR tL Ht. have E := cl_nat_logic _ _ Ht. subst tL.
  apply: coq_eq_to_imported_eq. exact (cl_map_unmap cid cid (fun _ => Logic.eq_refl _) _).
Qed.

Lemma cpm_forall_arr (PR : ArrivalSequence.arrival_sequence Job -> Prop) (PL : LArr -> SProp) :
  (forall aR aL, CpmArrRel aR aL -> PropSPropRel (PR aR) (PL aL)) -> PropSPropRel (forall a, PR a) (forall a, PL a).
Proof. exact (cpm_forall_cover _ _ CpmArrRel cpm_arr_to_target cpm_arr_to_source cpm_arr_canonical cpm_arr_surjective PR PL). Qed.

End Rel.

(** The imported [ArrivalSequence] definitions this file's statements mention, related on related inputs. *)
Section ArrivalDefs.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).

Lemma cpm_arrives_in aR aL (Ha : CpmArrRel Job aR aL) j :
  PropSPropRel (ArrivalSequence.arrives_in aR j)
    (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrives_in Job dJ aL j).
Proof. apply: ct_exists_nat => tR tL Ht. exact (cpm_mem Job j _ _ (Ha tR tL Ht)). Qed.

End ArrivalDefs.

Section ArrivalDefs2.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).

End ArrivalDefs2.

Fixpoint cpm_snatl (s : seq nat) : I.List_inst1 Lean.Nat :=
  match s with [::] => I.List_nil_inst1 _ | x :: s' => I.List_cons_inst1 _ (sub_nat_to_imported x) (cpm_snatl s') end.

Lemma cpm_siota_range : forall n s,
  Logic.eq (I.List_range' (sub_nat_to_imported s) (sub_nat_to_imported n) (Lean.Nat_succ Lean.Nat_zero)) (cpm_snatl (iota s n)).
Proof.
  elim => [|n IH] s; first reflexivity.
  change (Logic.eq (I.List_cons_inst1 _ (sub_nat_to_imported s)
      (I.List_range' (sub_nat_to_imported (S s)) (sub_nat_to_imported n) (Lean.Nat_succ Lean.Nat_zero)))
    (I.List_cons_inst1 _ (sub_nat_to_imported s) (cpm_snatl (iota (S s) n)))).
  by rewrite IH.
Qed.

Lemma cpm_foldr_add (f : Lean.Nat -> Lean.Nat) (g : nat -> nat) (Hf : forall k, Logic.eq (f (sub_nat_to_imported k)) (sub_nat_to_imported (g k))) :
  forall s, Logic.eq (I.List_foldr_inst3 Lean.Nat Lean.Nat Lean.Nat_add Lean.Nat_zero (I.List_map_inst3 Lean.Nat Lean.Nat f (cpm_snatl s)))
                     (sub_nat_to_imported (foldr addn 0 (map g s))).
Proof.
  elim => [|k s IH] //=.
  change (Logic.eq (Lean.Nat_add (f (sub_nat_to_imported k))
            (I.List_foldr_inst3 Lean.Nat Lean.Nat Lean.Nat_add Lean.Nat_zero (I.List_map_inst3 Lean.Nat Lean.Nat f (cpm_snatl s))))
         (sub_nat_to_imported (g k + foldr addn 0 (map g s)))).
  rewrite IH Hf. exact (imported_eq_to_coq_eq _ _ (sub_add_canonical _ _)).
Qed.

Lemma cpm_big_fold (xs : seq nat) (F : nat -> nat) : Logic.eq (\sum_(i <- xs) F i) (foldr addn 0 (map F xs)).
Proof. elim: xs => [|x xs IH]; first by rewrite big_nil. by rewrite big_cons IH. Qed.

Definition CpmFunRel (FR : nat -> nat) (FL : Lean.Nat -> Lean.Nat) : SProp :=
  forall kR kL, SubNatRel kR kL -> SubNatRel (FR kR) (FL kL).

Lemma cpm_fun_canonical FR FL (HF : CpmFunRel FR FL) k : Logic.eq (FL (sub_nat_to_imported k)) (sub_nat_to_imported (FR k)).
Proof. exact (cl_nat_logic _ _ (HF _ _ (sub_nat_rel_canonical k))). Qed.

Lemma cpm_nat_sub_canonical (a b : nat) :
  Logic.eq (I.Nat_sub (sub_nat_to_imported a) (sub_nat_to_imported b)) (sub_nat_to_imported (a - b)).
Proof.
  elim: b => [|b IH]; first by rewrite subn0.
  change (Logic.eq (I.Nat_pred (I.Nat_sub (sub_nat_to_imported a) (sub_nat_to_imported b))) (sub_nat_to_imported (a - b.+1))).
  rewrite IH subnS. case: (a - b) => [|k]; reflexivity.
Qed.

Lemma cpm_ico mR mL nR nL FR FL (Hm : SubNatRel mR mL) (Hn : SubNatRel nR nL) (HF : CpmFunRel FR FL) :
  SubNatRel (\sum_(mR <= i < nR) FR i)
    (I.List_foldr_inst3 Lean.Nat Lean.Nat Lean.Nat_add Lean.Nat_zero
       (I.List_map_inst3 Lean.Nat Lean.Nat FL (I.List_range' mL (I.Nat_sub nL mL) (Lean.Nat_succ Lean.Nat_zero)))).
Proof.
  rewrite (cl_nat_logic _ _ Hm) (cl_nat_logic _ _ Hn).
  have -> : Logic.eq (I.Nat_sub (sub_nat_to_imported nR) (sub_nat_to_imported mR)) (sub_nat_to_imported (nR - mR))
    := cpm_nat_sub_canonical nR mR.
  rewrite cpm_siota_range.
  apply: coq_eq_to_imported_eq. apply: Logic.eq_sym. rewrite (cpm_foldr_add FL FR (cpm_fun_canonical FR FL HF)).
  by rewrite cpm_big_fold.
Qed.

(* ------------------------------------------------------------------ *)
(** * Options and uniprocessor schedules *)

(** Transport along the target equality (definitional UIP), as in the accepted global schedule certificate. *)
Definition cpm_tr {A : Type} {x y : A} (E : Lean.eq x y) (P : A -> Type) (h : P x) : P y :=
  match E in Lean.eq _ z return P z with Lean.eq_refl => h end.

Definition cpm_trs {A : Type} {x y : A} (E : Lean.eq x y) (P : A -> SProp) (h : P x) : P y :=
  match E in Lean.eq _ z return P z with Lean.eq_refl => h end.

Lemma cpm_opt_inj (A : Type) (o1 o2 : option A) : Logic.eq (cl_opt o1) (cl_opt o2) -> Logic.eq o1 o2.
Proof. intro E. by rewrite -(cl_unopt_opt o1) -(cl_unopt_opt o2) E. Qed.

Lemma cpm_opt_eqb_rel (A : eqType) (o1 o2 : option A) :
  PropSPropRel (is_true (o1 == o2)) (Lean.eq (cl_opt o1) (cl_opt o2)).
Proof.
  apply prop_sprop_rel_intro.
  - move=> /eqP E. rewrite E. exact (@Lean.eq_refl _ _).
  - intro E. apply strictly_inhabits. apply/eqP. exact (cpm_opt_inj A o1 o2 (imported_eq_to_coq_eq _ _ E)).
Qed.

Section Sched.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).
Notation LSched := (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job dJ).

Definition CpmSchedRel (sR : UniprocessorSchedule.schedule Job) (sL : LSched) : SProp :=
  forall tR tL, SubNatRel tR tL -> Lean.eq (cl_opt (sR tR)) (sL tL).

Definition cpm_sched_to_target (sR : UniprocessorSchedule.schedule Job) : LSched := fun tL => cl_opt (sR (sub_nat_to_rocq tL)).
Definition cpm_sched_to_source (sL : LSched) : UniprocessorSchedule.schedule Job := fun tR => cl_unopt (sL (sub_nat_to_imported tR)).

Lemma cpm_sched_canonical sR : CpmSchedRel sR (cpm_sched_to_target sR).
Proof. intros tR tL Ht. apply: coq_eq_to_imported_eq. by rewrite /cpm_sched_to_target (cl_nat_input _ _ Ht). Qed.

Lemma cpm_sched_surjective sL : CpmSchedRel (cpm_sched_to_source sL) sL.
Proof.
  intros tR tL Ht. apply: coq_eq_to_imported_eq. rewrite /cpm_sched_to_source cl_opt_unopt.
  by rewrite (cl_nat_logic _ _ Ht).
Qed.

Lemma cpm_forall_sched (PR : UniprocessorSchedule.schedule Job -> Prop) (PL : LSched -> SProp) :
  (forall sR sL, CpmSchedRel sR sL -> PropSPropRel (PR sR) (PL sL)) -> PropSPropRel (forall s, PR s) (forall s, PL s).
Proof. exact (cpm_forall_cover _ _ CpmSchedRel cpm_sched_to_target cpm_sched_to_source cpm_sched_canonical cpm_sched_surjective PR PL). Qed.

End Sched.

(* ------------------------------------------------------------------ *)
(** * Definitions *)

Lemma cpm_US_schedule (Job : eqType) :
  And (forall sR : UniprocessorSchedule.schedule Job, CpmSchedRel Job sR (cpm_sched_to_target Job sR))
      (forall sL : I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job (ct_decidable_eq Job), CpmSchedRel Job (cpm_sched_to_source Job sL) sL).
Proof. exact (And_intro _ _ (cpm_sched_canonical Job) (cpm_sched_surjective Job)). Qed.

Section USchedDefs.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).
Variables (sR : UniprocessorSchedule.schedule Job) (sL : I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job dJ).
Hypothesis Hs : CpmSchedRel Job sR sL.

Lemma cpm_US_scheduled_at j tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (UniprocessorSchedule.scheduled_at sR j tR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_scheduled_at Job dJ sL j tL).
Proof.
  apply: ct_decide_bool.
  exact (cpm_tr (Hs tR tL Ht) (fun z => PropSPropRel (sR tR == Some j) (Lean.eq z (cl_opt (Some j))))
           (cpm_opt_eqb_rel Job (sR tR) (Some j))).
Qed.

Lemma cpm_US_service_at j tR tL (Ht : SubNatRel tR tL) :
  SubNatRel (UniprocessorSchedule.service_at sR j tR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_service_at Job dJ sL j tL).
Proof. exact (ct_bool_to_nat _ _ (cpm_US_scheduled_at j tR tL Ht)). Qed.

Lemma cpm_service_at_fun j : CpmFunRel (fun t => UniprocessorSchedule.service_at sR j t) (fun t => I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_service_at Job dJ sL j t).
Proof. intros kR kL Hk. exact (cpm_US_service_at j kR kL Hk). Qed.

Lemma cpm_US_service_during j t1R t1L (H1 : SubNatRel t1R t1L) t2R t2L (H2 : SubNatRel t2R t2L) :
  SubNatRel (UniprocessorSchedule.service_during sR j t1R t2R) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_service_during Job dJ sL j t1L t2L).
Proof. exact (cpm_ico _ _ _ _ _ _ H1 H2 (cpm_service_at_fun j)). Qed.

Lemma cpm_US_service j tR tL (Ht : SubNatRel tR tL) :
  SubNatRel (UniprocessorSchedule.service sR j tR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_service Job dJ sL j tL).
Proof. exact (cpm_US_service_during j 0 _ (sub_nat_rel_canonical 0) tR tL Ht). Qed.

End USchedDefs.

(** The imported [Job] definitions (as in the accepted classic job certificate). *)
Section JobDefs.
Notation c0 := (sub_nat_rel_canonical 0).
Variables (Task Job : eqType).
Notation dT := (ct_decidable_eq Task).
Notation dJ := (ct_decidable_eq Job).

End JobDefs.

(** * Preemption models *)

Section LpdefsPmRel.
Variable Job : eqType.
Definition CpmPmRel (pR : Job -> nat -> bool) (pL : Job -> Lean.Nat -> I.Bool) : SProp :=
  forall j tR tL, SubNatRel tR tL -> CtBoolRel (pR j tR) (pL j tL).

Lemma cpm_pm_canonical pR : CpmPmRel pR (fun j tL => ct_b2l (pR j (sub_nat_to_rocq tL))).
Proof. intros j tR tL Ht. have E := cl_nat_logic _ _ Ht. subst tL. rewrite sub_nat_rocq_roundtrip. exact (ct_bool_canonical _). Qed.

Lemma cpm_pm_surjective pL : CpmPmRel (fun j tR => ct_l2b (pL j (sub_nat_to_imported tR))) pL.
Proof. intros j tR tL Ht. have E := cl_nat_logic _ _ Ht. subst tL. exact (ct_bool_surjective _). Qed.

Lemma cpm_forall_pm (PR : (Job -> nat -> bool) -> Prop) (PL : (Job -> Lean.Nat -> I.Bool) -> SProp) :
  (forall pR pL, CpmPmRel pR pL -> PropSPropRel (PR pR) (PL pL)) -> PropSPropRel (forall p, PR p) (forall p, PL p).
Proof. exact (cpm_forall_cover _ _ CpmPmRel _ _ cpm_pm_canonical cpm_pm_surjective PR PL). Qed.

End LpdefsPmRel.

(* ------------------------------------------------------------------ *)
(** * Definitions *)

Section LpdefsDefs.
Variables (Task Job : eqType).
Notation dT := (ct_decidable_eq Task).
Notation dJ := (ct_decidable_eq Job).
Variables (sR : UniprocessorSchedule.schedule Job) (sL : I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job dJ).
Hypothesis Hs : CpmSchedRel Job sR sL.
Variables (pR : Job -> nat -> bool) (pL : Job -> Lean.Nat -> I.Bool).
Hypothesis Hp : CpmPmRel Job pR pL.

Notation SA := (cpm_US_scheduled_at Job sR sL Hs).
Notation SV := (cpm_US_service Job sR sL Hs).

Lemma cpm_LP_not_preemptive_implies_scheduled j :
  PropSPropRel (LimitedPreemptionPlatform.not_preemptive_implies_scheduled sR pR j) (I.Prosa_Classic_Model_Schedule_Uni_Limited_Platform_Definitions_LimitedPreemptionPlatform_not_preemptive_implies_scheduled Job dJ sL pL j).
Proof.
  apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (ct_bool_truth _ _ (ct_bool_not _ _ (Hp j _ _ (SV j tR tL Ht)))).
  exact (ct_bool_truth _ _ (SA j tR tL Ht)).
Qed.

Lemma cpm_LP_execution_starts_with_preemption_point j :
  PropSPropRel (LimitedPreemptionPlatform.execution_starts_with_preemption_point sR pR j) (I.Prosa_Classic_Model_Schedule_Uni_Limited_Platform_Definitions_LimitedPreemptionPlatform_execution_starts_with_preemption_point Job dJ sL pL j).
Proof.
  apply: ct_forall_nat => tR tL Ht.
  have Ht1 := cpm_succ_rel _ _ Ht.
  apply: ct_imp; first exact (ct_bool_truth _ _ (ct_bool_not _ _ (SA j tR tL Ht))).
  apply: ct_imp; first exact (ct_bool_truth _ _ (SA j _ _ Ht1)).
  exact (ct_bool_truth _ _ (Hp j _ _ (SV j _ _ Ht1))).
Qed.

Lemma cpm_LP_correct_preemption_model arrR arrL (Harr : CpmArrRel Job arrR arrL) :
  PropSPropRel (LimitedPreemptionPlatform.correct_preemption_model arrR sR pR) (I.Prosa_Classic_Model_Schedule_Uni_Limited_Platform_Definitions_LimitedPreemptionPlatform_correct_preemption_model Job dJ arrL sL pL).
Proof.
  apply: ct_forall_identity => j.
  apply: ct_imp; first exact (cpm_arrives_in Job arrR arrL Harr j).
  apply: ct_and; first exact (cpm_LP_not_preemptive_implies_scheduled j).
  exact (cpm_LP_execution_starts_with_preemption_point j).
Qed.

End LpdefsDefs.

Section LpdefsDefs2.
Variables (Task Job : eqType).
Notation dT := (ct_decidable_eq Task).
Notation dJ := (ct_decidable_eq Job).
Variables (pR : Job -> nat -> bool) (pL : Job -> Lean.Nat -> I.Bool).
Hypothesis Hp : CpmPmRel Job pR pL.
Variables (cR : Job -> nat) (cL : Job -> Lean.Nat) (mR : Job -> nat) (mL : Job -> Lean.Nat) (tmR : Task -> nat) (tmL : Task -> Lean.Nat).
Hypotheses (Hc : CpmParRel Job cR cL) (Hm : CpmParRel Job mR mL) (Htm : CpmParRel Task tmR tmL).

Lemma cpm_LP_job_cannot_become_nonpreemptive_before_execution j :
  PropSPropRel (LimitedPreemptionPlatform.job_cannot_become_nonpreemptive_before_execution pR j)
    (I.Prosa_Classic_Model_Schedule_Uni_Limited_Platform_Definitions_LimitedPreemptionPlatform_job_cannot_become_nonpreemptive_before_execution Job dJ pL j).
Proof. exact (ct_bool_truth _ _ (Hp j _ _ (sub_nat_rel_canonical 0))). Qed.

Lemma cpm_LP_job_cannot_be_nonpreemptive_after_completion j :
  PropSPropRel (LimitedPreemptionPlatform.job_cannot_be_nonpreemptive_after_completion cR pR j)
    (I.Prosa_Classic_Model_Schedule_Uni_Limited_Platform_Definitions_LimitedPreemptionPlatform_job_cannot_be_nonpreemptive_after_completion Job dJ cL pL j).
Proof. exact (ct_bool_truth _ _ (Hp j _ _ (Hc j))). Qed.

Lemma cpm_LP_job_max_nonpreemptive_segment_le_task_max_nonpreemptive_segment (job_task : Job -> Task)
    arrR arrL (Harr : CpmArrRel Job arrR arrL) j :
  PropSPropRel (LimitedPreemptionPlatform.job_max_nonpreemptive_segment_le_task_max_nonpreemptive_segment job_task arrR mR tmR j)
    (I.Prosa_Classic_Model_Schedule_Uni_Limited_Platform_Definitions_LimitedPreemptionPlatform_job_max_nonpreemptive_segment_le_task_max_nonpreemptive_segment Task dT Job dJ job_task arrL mL tmL j).
Proof.
  apply: ct_imp; first exact (cpm_arrives_in Job arrR arrL Harr j).
  exact (sub_nat_le_correspondence _ _ _ _ (Hm j) (Htm (job_task j))).
Qed.

Lemma cpm_LP_nonpreemptive_regions_have_bounded_length j :
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

Lemma cpm_LP_model_with_bounded_nonpreemptive_segments (job_task : Job -> Task)
    arrR arrL (Harr : CpmArrRel Job arrR arrL) :
  PropSPropRel (LimitedPreemptionPlatform.model_with_bounded_nonpreemptive_segments cR job_task arrR pR mR tmR)
    (I.Prosa_Classic_Model_Schedule_Uni_Limited_Platform_Definitions_LimitedPreemptionPlatform_model_with_bounded_nonpreemptive_segments Task dT Job dJ cL job_task arrL pL mL tmL).
Proof.
  apply: ct_forall_identity => j.
  apply: ct_imp; first exact (cpm_arrives_in Job arrR arrL Harr j).
  apply: ct_and; first exact (cpm_LP_job_cannot_become_nonpreemptive_before_execution j).
  apply: ct_and; first exact (cpm_LP_job_cannot_be_nonpreemptive_after_completion j).
  apply: ct_and; first exact (cpm_LP_job_max_nonpreemptive_segment_le_task_max_nonpreemptive_segment job_task arrR arrL Harr j).
  exact (cpm_LP_nonpreemptive_regions_have_bounded_length j).
Qed.

End LpdefsDefs2.



(* ------------------------------------------------------------------ *)
(** * Definitions *)

Theorem FullyPreemptivePlatform_can_be_preempted_for_fully_preemptive_model_correspondence (Job : eqType) :
  CpmPmRel Job (FullyPreemptivePlatform.can_be_preempted_for_fully_preemptive_model (Job := Job))
    (I.Prosa_Classic_Model_Schedule_Uni_Limited_Platform_Preemptive_FullyPreemptivePlatform_can_be_preempted_for_fully_preemptive_model Job (ct_decidable_eq Job)).
Proof. intros j tR tL Ht. exact (ct_bool_canonical true). Qed.

(* ------------------------------------------------------------------ *)
(** * Statements *)

Notation CBP := FullyPreemptivePlatform_can_be_preempted_for_fully_preemptive_model_correspondence.

Definition src_fully_preemptive_model_is_correct (Job : eqType) : Prop :=
   ltac:(type_of_term (@FullyPreemptivePlatform.fully_preemptive_model_is_correct Job)).
Definition tgt_fully_preemptive_model_is_correct (Job : eqType) : SProp :=
   ltac:(type_of_term (I.Prosa_Classic_Model_Schedule_Uni_Limited_Platform_Preemptive_FullyPreemptivePlatform_fully_preemptive_model_is_correct Job (ct_decidable_eq Job))).

Theorem FullyPreemptivePlatform_fully_preemptive_model_is_correct_correspondence (Job : eqType) :
  PropSPropRel (src_fully_preemptive_model_is_correct Job) (tgt_fully_preemptive_model_is_correct Job).
Proof.
  unfold src_fully_preemptive_model_is_correct, tgt_fully_preemptive_model_is_correct.
  apply: cpm_forall_arr => arrR arrL Harr. apply: cpm_forall_sched => sR sL Hs.
  exact (cpm_LP_correct_preemption_model Job sR sL Hs _ _ (CBP Job) arrR arrL Harr).
Qed.
Definition src_fully_preemptive_model_is_model_with_bounded_nonpreemptive_regions (Task Job : eqType) : Prop :=
   ltac:(type_of_term (@FullyPreemptivePlatform.fully_preemptive_model_is_model_with_bounded_nonpreemptive_regions Task Job)).
Definition tgt_fully_preemptive_model_is_model_with_bounded_nonpreemptive_regions (Task Job : eqType) : SProp :=
   ltac:(type_of_term (I.Prosa_Classic_Model_Schedule_Uni_Limited_Platform_Preemptive_FullyPreemptivePlatform_fully_preemptive_model_is_model_with_bounded_nonpreemptive_regions Task (ct_decidable_eq Task) Job (ct_decidable_eq Job))).

Theorem FullyPreemptivePlatform_fully_preemptive_model_is_model_with_bounded_nonpreemptive_regions_correspondence (Task Job : eqType) :
  PropSPropRel (src_fully_preemptive_model_is_model_with_bounded_nonpreemptive_regions Task Job) (tgt_fully_preemptive_model_is_model_with_bounded_nonpreemptive_regions Task Job).
Proof.
  unfold src_fully_preemptive_model_is_model_with_bounded_nonpreemptive_regions, tgt_fully_preemptive_model_is_model_with_bounded_nonpreemptive_regions.
  apply: cpm_forall_par => cR cL Hc. apply: ct_forall_identity => job_task. apply: cpm_forall_arr => arrR arrL Harr.
  exact (cpm_LP_model_with_bounded_nonpreemptive_segments Task Job _ _ (CBP Job) cR cL (fun _ => 1) _ (fun _ => 1) _ Hc
           (fun _ => sub_nat_rel_canonical 1) (fun _ => sub_nat_rel_canonical 1) job_task arrR arrL Harr).
Qed.
