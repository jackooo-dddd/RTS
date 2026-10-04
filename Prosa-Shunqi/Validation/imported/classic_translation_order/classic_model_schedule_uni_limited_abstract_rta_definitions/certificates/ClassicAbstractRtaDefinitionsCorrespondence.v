From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq fintype bigop.
From prosa Require Import classic.model.time classic.model.arrival.basic.arrival_sequence classic.model.schedule.uni.schedule classic.model.schedule.uni.limited.abstract_RTA.definitions.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedClassicAbstractRtaDefinitions.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence ClassicAbstractRtaDefinitionsBase ClassicAbstractRtaDefinitionsList.

Module I := ImportedClassicAbstractRtaDefinitions.
Local Open Scope nat_scope.

(** Certificates for [classic/model/schedule/uni/limited/abstract_RTA/definitions.v] (ProsaBuddy classic, commit f692cb7).

    Inputs: the job and task types are [eqType]s, identified, with the Lean [DecidableEq] instances given by the
    eqTypes' decision procedures ([ct_decidable_eq]); [job_task] identified; times by [SubNatRel]; job parameters
    pointwise through [SubNatRel]; uniprocessor schedules pointwise through the option map; arrival sequences pointwise
    on related times; interference predicates [Job -> time -> bool] and interfering workloads [Job -> time -> time]
    pointwise on related times; interference bound functions pointwise on related arguments; all with two-way totals.

    Computation: the half-open sums of [cumul_interference] / [cumul_interfering_workload] (and of the imported
    [service_during]) against their kernel-guarded body projections in [ClassicAbstractRtaDefinitionsInterface],
    related by [car_ico] as in the accepted classic sum / schedule certificates.

    Statements: the source side is the exact elaborated type of the pinned lemma (via [type of]; the source proof
    is not used). *)

Ltac type_of_term t := let T := type of t in exact T.
Notation cid := (fun z => z).

(* ------------------------------------------------------------------ *)
(** * Helpers (re-bound to this export from the accepted classic certificates) *)

(** Base definitions (as in the accepted classic base library), provided here when this export's library lacks them. *)

(* ------------------------------------------------------------------ *)
(** * Generic covers and helpers *)

Lemma car_forall_cover (A B : Type) (Rel : A -> B -> SProp) (toB : A -> B) (toA : B -> A)
    (HB : forall a, Rel a (toB a)) (HA : forall b, Rel (toA b) b) (PR : A -> Prop) (PL : B -> SProp) :
  (forall a b, Rel a b -> PropSPropRel (PR a) (PL b)) -> PropSPropRel (forall a, PR a) (forall b, PL b).
Proof.
  intro H. apply prop_sprop_rel_intro.
  - intros HR b. exact (prop_to_sprop _ _ (H _ _ (HA b)) (HR _)).
  - intro HL. apply strictly_inhabits. intro a. exact (sprop_to_prop _ _ (H _ _ (HB a)) (HL _)).
Qed.

Lemma car_false_rel : PropSPropRel Logic.False I.False.
Proof.
  apply prop_sprop_rel_intro.
  - exact ct_coq_false_to_target.
  - exact ct_target_false_to_strict.
Qed.

Lemma car_mem (T : eqType) x s sL : ClListRel cid s sL ->
  PropSPropRel (x \in s) (I.Membership_mem T (I.List T) (I.List_instMembership T) sL x).
Proof. exact (cl_mem_rel_list T T cid cid (fun _ => Logic.eq_refl _) x s sL). Qed.

Lemma car_unmap_rel (T : Type) (l : I.List T) : ClListRel cid (cl_unmap cid l) l.
Proof. apply: coq_eq_to_imported_eq. exact (cl_map_unmap cid cid (fun _ => Logic.eq_refl _) l). Qed.

Lemma car_cl_map_inj (T : Type) (s1 s2 : seq T) : Logic.eq (cl_map cid s1) (cl_map cid s2) -> Logic.eq s1 s2.
Proof.
  intro E. rewrite -(cl_unmap_map cid cid (fun _ => Logic.eq_refl _) s1) -(cl_unmap_map cid cid (fun _ => Logic.eq_refl _) s2).
  by rewrite E.
Qed.

Lemma car_succ_rel nR nL : SubNatRel nR nL ->
  SubNatRel nR.+1 (I.HAdd_hAdd_inst7 Lean.Nat Lean.Nat Lean.Nat (I.instHAdd_inst1 Lean.Nat I.instAddNat) nL
                     (I.OfNat_ofNat_inst1 Lean.Nat 1 (I.instOfNatNat 1))).
Proof. intro Hn. exact (sub_imported_eq_congr Lean.Nat_succ _ _ Hn). Qed.

(* ------------------------------------------------------------------ *)
(** * Big concatenation over a half-open interval (as in the accepted arrival_sequence certificate) *)

Definition CarParRel (T : Type) (pR : T -> nat) (pL : T -> Lean.Nat) : SProp := forall x, SubNatRel (pR x) (pL x).

Lemma car_forall_par (T : Type) (PR : (T -> nat) -> Prop) (PL : (T -> Lean.Nat) -> SProp) :
  (forall pR pL, CarParRel T pR pL -> PropSPropRel (PR pR) (PL pL)) -> PropSPropRel (forall p, PR p) (forall p, PL p).
Proof.
  exact (car_forall_cover _ _ (CarParRel T) (fun pR j => sub_nat_to_imported (pR j)) (fun pL j => sub_nat_to_rocq (pL j))
           (fun pR j => sub_nat_rel_canonical (pR j)) (fun pL j => sub_nat_rel_surjective (pL j)) PR PL).
Qed.

Fixpoint car_natl (s : seq nat) : I.List_inst1 Lean.Nat :=
  match s with [::] => I.List_nil_inst1 _ | x :: s' => I.List_cons_inst1 _ (sub_nat_to_imported x) (car_natl s') end.

Definition car_one : Lean.Nat := I.OfNat_ofNat_inst1 Lean.Nat 1 (I.instOfNatNat 1).

Lemma car_iota_range : forall n s,
  Logic.eq (I.List_range' (sub_nat_to_imported s) (sub_nat_to_imported n) car_one) (car_natl (iota s n)).
Proof.
  elim => [|n IH] s; first reflexivity.
  change (Logic.eq (I.List_cons_inst1 _ (sub_nat_to_imported s)
      (I.List_range' (sub_nat_to_imported (S s)) (sub_nat_to_imported n) car_one))
    (I.List_cons_inst1 _ (sub_nat_to_imported s) (car_natl (iota (S s) n)))).
  by rewrite IH.
Qed.

Lemma car_cl_map_comp {A B C : Type} (f : A -> B) (g : B -> C) : forall s : seq A,
  Logic.eq (cl_map (fun x => g (f x)) s) (cl_map g (map f s)).
Proof. elim => [|x s IH] //=. by rewrite IH. Qed.

Lemma car_cl_map_ext {A B : Type} (f g : A -> B) (H : forall x, Logic.eq (f x) (g x)) : forall s : seq A,
  Logic.eq (cl_map f s) (cl_map g s).
Proof. elim => [|x s IH] //=. by rewrite H IH. Qed.

Lemma car_big_seq {A : Type} (F : nat -> seq A) : forall s : seq nat,
  Logic.eq (\big[cat/[::]]_(i <- s) F i) (flatten (map F s)).
Proof. elim => [|x s IH]; first by rewrite big_nil. by rewrite big_cons IH. Qed.

Definition CarFamRel (A : Type) (fR : nat -> seq A) (fL : Lean.Nat -> I.List A) : SProp :=
  forall nR nL, SubNatRel nR nL -> ClListRel cid (fR nR) (fL nL).

(* ------------------------------------------------------------------ *)
(** * Arrival sequences and parameters *)

Section Rel.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).
Notation LArr := (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrival_sequence Job dJ).

Definition CarArrRel (aR : ArrivalSequence.arrival_sequence Job) (aL : LArr) : SProp :=
  forall tR tL, SubNatRel tR tL -> ClListRel cid (aR tR) (aL tL).

Definition car_arr_to_target (aR : ArrivalSequence.arrival_sequence Job) : LArr :=
  fun tL => cl_map cid (aR (sub_nat_to_rocq tL)).

Definition car_arr_to_source (aL : LArr) : ArrivalSequence.arrival_sequence Job :=
  fun tR => cl_unmap cid (aL (sub_nat_to_imported tR)).

Lemma car_arr_canonical aR : CarArrRel aR (car_arr_to_target aR).
Proof.
  intros tR tL Ht. have E := cl_nat_logic _ _ Ht. subst tL.
  apply: coq_eq_to_imported_eq. rewrite /car_arr_to_target sub_nat_rocq_roundtrip. reflexivity.
Qed.

Lemma car_arr_surjective aL : CarArrRel (car_arr_to_source aL) aL.
Proof.
  intros tR tL Ht. have E := cl_nat_logic _ _ Ht. subst tL.
  apply: coq_eq_to_imported_eq. exact (cl_map_unmap cid cid (fun _ => Logic.eq_refl _) _).
Qed.

Lemma car_forall_arr (PR : ArrivalSequence.arrival_sequence Job -> Prop) (PL : LArr -> SProp) :
  (forall aR aL, CarArrRel aR aL -> PropSPropRel (PR aR) (PL aL)) -> PropSPropRel (forall a, PR a) (forall a, PL a).
Proof. exact (car_forall_cover _ _ CarArrRel car_arr_to_target car_arr_to_source car_arr_canonical car_arr_surjective PR PL). Qed.

End Rel.

(** The imported [ArrivalSequence] definitions this file's statements mention, related on related inputs. *)
Section ArrivalDefs.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).

Lemma car_arrives_in aR aL (Ha : CarArrRel Job aR aL) j :
  PropSPropRel (ArrivalSequence.arrives_in aR j)
    (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrives_in Job dJ aL j).
Proof. apply: ct_exists_nat => tR tL Ht. exact (car_mem Job j _ _ (Ha tR tL Ht)). Qed.

End ArrivalDefs.

Section ArrivalDefs2.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).

Lemma car_arrived_before pR pL (Hp : CarParRel Job pR pL) j tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (ArrivalSequence.arrived_before pR j tR)
    (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrived_before Job dJ pL j tL).
Proof. exact (ct_decide_lt _ _ _ _ (Hp j) Ht). Qed.

End ArrivalDefs2.

Fixpoint car_snatl (s : seq nat) : I.List_inst1 Lean.Nat :=
  match s with [::] => I.List_nil_inst1 _ | x :: s' => I.List_cons_inst1 _ (sub_nat_to_imported x) (car_snatl s') end.

Lemma car_siota_range : forall n s,
  Logic.eq (I.List_range' (sub_nat_to_imported s) (sub_nat_to_imported n) (Lean.Nat_succ Lean.Nat_zero)) (car_snatl (iota s n)).
Proof.
  elim => [|n IH] s; first reflexivity.
  change (Logic.eq (I.List_cons_inst1 _ (sub_nat_to_imported s)
      (I.List_range' (sub_nat_to_imported (S s)) (sub_nat_to_imported n) (Lean.Nat_succ Lean.Nat_zero)))
    (I.List_cons_inst1 _ (sub_nat_to_imported s) (car_snatl (iota (S s) n)))).
  by rewrite IH.
Qed.

Lemma car_foldr_add (f : Lean.Nat -> Lean.Nat) (g : nat -> nat) (Hf : forall k, Logic.eq (f (sub_nat_to_imported k)) (sub_nat_to_imported (g k))) :
  forall s, Logic.eq (I.List_foldr_inst3 Lean.Nat Lean.Nat Lean.Nat_add Lean.Nat_zero (I.List_map_inst3 Lean.Nat Lean.Nat f (car_snatl s)))
                     (sub_nat_to_imported (foldr addn 0 (map g s))).
Proof.
  elim => [|k s IH] //=.
  change (Logic.eq (Lean.Nat_add (f (sub_nat_to_imported k))
            (I.List_foldr_inst3 Lean.Nat Lean.Nat Lean.Nat_add Lean.Nat_zero (I.List_map_inst3 Lean.Nat Lean.Nat f (car_snatl s))))
         (sub_nat_to_imported (g k + foldr addn 0 (map g s)))).
  rewrite IH Hf. exact (imported_eq_to_coq_eq _ _ (sub_add_canonical _ _)).
Qed.

Lemma car_big_fold (xs : seq nat) (F : nat -> nat) : Logic.eq (\sum_(i <- xs) F i) (foldr addn 0 (map F xs)).
Proof. elim: xs => [|x xs IH]; first by rewrite big_nil. by rewrite big_cons IH. Qed.

Definition CarFunRel (FR : nat -> nat) (FL : Lean.Nat -> Lean.Nat) : SProp :=
  forall kR kL, SubNatRel kR kL -> SubNatRel (FR kR) (FL kL).

Lemma car_fun_canonical FR FL (HF : CarFunRel FR FL) k : Logic.eq (FL (sub_nat_to_imported k)) (sub_nat_to_imported (FR k)).
Proof. exact (cl_nat_logic _ _ (HF _ _ (sub_nat_rel_canonical k))). Qed.

Lemma car_nat_sub_canonical (a b : nat) :
  Logic.eq (I.Nat_sub (sub_nat_to_imported a) (sub_nat_to_imported b)) (sub_nat_to_imported (a - b)).
Proof.
  elim: b => [|b IH]; first by rewrite subn0.
  change (Logic.eq (I.Nat_pred (I.Nat_sub (sub_nat_to_imported a) (sub_nat_to_imported b))) (sub_nat_to_imported (a - b.+1))).
  rewrite IH subnS. case: (a - b) => [|k]; reflexivity.
Qed.

Lemma car_ico mR mL nR nL FR FL (Hm : SubNatRel mR mL) (Hn : SubNatRel nR nL) (HF : CarFunRel FR FL) :
  SubNatRel (\sum_(mR <= i < nR) FR i)
    (I.List_foldr_inst3 Lean.Nat Lean.Nat Lean.Nat_add Lean.Nat_zero
       (I.List_map_inst3 Lean.Nat Lean.Nat FL (I.List_range' mL (I.Nat_sub nL mL) (Lean.Nat_succ Lean.Nat_zero)))).
Proof.
  rewrite (cl_nat_logic _ _ Hm) (cl_nat_logic _ _ Hn).
  have -> : Logic.eq (I.Nat_sub (sub_nat_to_imported nR) (sub_nat_to_imported mR)) (sub_nat_to_imported (nR - mR))
    := car_nat_sub_canonical nR mR.
  rewrite car_siota_range.
  apply: coq_eq_to_imported_eq. apply: Logic.eq_sym. rewrite (car_foldr_add FL FR (car_fun_canonical FR FL HF)).
  by rewrite car_big_fold.
Qed.

(* ------------------------------------------------------------------ *)
(** * Options and uniprocessor schedules *)

(** Transport along the target equality (definitional UIP), as in the accepted global schedule certificate. *)
Definition car_tr {A : Type} {x y : A} (E : Lean.eq x y) (P : A -> Type) (h : P x) : P y :=
  match E in Lean.eq _ z return P z with Lean.eq_refl => h end.

Definition car_trs {A : Type} {x y : A} (E : Lean.eq x y) (P : A -> SProp) (h : P x) : P y :=
  match E in Lean.eq _ z return P z with Lean.eq_refl => h end.

Lemma car_opt_inj (A : Type) (o1 o2 : option A) : Logic.eq (cl_opt o1) (cl_opt o2) -> Logic.eq o1 o2.
Proof. intro E. by rewrite -(cl_unopt_opt o1) -(cl_unopt_opt o2) E. Qed.

Lemma car_opt_eqb_rel (A : eqType) (o1 o2 : option A) :
  PropSPropRel (is_true (o1 == o2)) (Lean.eq (cl_opt o1) (cl_opt o2)).
Proof.
  apply prop_sprop_rel_intro.
  - move=> /eqP E. rewrite E. exact (@Lean.eq_refl _ _).
  - intro E. apply strictly_inhabits. apply/eqP. exact (car_opt_inj A o1 o2 (imported_eq_to_coq_eq _ _ E)).
Qed.

Section Sched.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).
Notation LSched := (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job dJ).

Definition CarSchedRel (sR : UniprocessorSchedule.schedule Job) (sL : LSched) : SProp :=
  forall tR tL, SubNatRel tR tL -> Lean.eq (cl_opt (sR tR)) (sL tL).

Definition car_sched_to_target (sR : UniprocessorSchedule.schedule Job) : LSched := fun tL => cl_opt (sR (sub_nat_to_rocq tL)).
Definition car_sched_to_source (sL : LSched) : UniprocessorSchedule.schedule Job := fun tR => cl_unopt (sL (sub_nat_to_imported tR)).

Lemma car_sched_canonical sR : CarSchedRel sR (car_sched_to_target sR).
Proof. intros tR tL Ht. apply: coq_eq_to_imported_eq. by rewrite /car_sched_to_target (cl_nat_input _ _ Ht). Qed.

Lemma car_sched_surjective sL : CarSchedRel (car_sched_to_source sL) sL.
Proof.
  intros tR tL Ht. apply: coq_eq_to_imported_eq. rewrite /car_sched_to_source cl_opt_unopt.
  by rewrite (cl_nat_logic _ _ Ht).
Qed.

Lemma car_forall_sched (PR : UniprocessorSchedule.schedule Job -> Prop) (PL : LSched -> SProp) :
  (forall sR sL, CarSchedRel sR sL -> PropSPropRel (PR sR) (PL sL)) -> PropSPropRel (forall s, PR s) (forall s, PL s).
Proof. exact (car_forall_cover _ _ CarSchedRel car_sched_to_target car_sched_to_source car_sched_canonical car_sched_surjective PR PL). Qed.

End Sched.

(* ------------------------------------------------------------------ *)
(** * Definitions *)

Lemma car_US_schedule (Job : eqType) :
  And (forall sR : UniprocessorSchedule.schedule Job, CarSchedRel Job sR (car_sched_to_target Job sR))
      (forall sL : I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job (ct_decidable_eq Job), CarSchedRel Job (car_sched_to_source Job sL) sL).
Proof. exact (And_intro _ _ (car_sched_canonical Job) (car_sched_surjective Job)). Qed.

Section USchedDefs.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).
Variables (sR : UniprocessorSchedule.schedule Job) (sL : I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job dJ).
Hypothesis Hs : CarSchedRel Job sR sL.

Lemma car_US_scheduled_at j tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (UniprocessorSchedule.scheduled_at sR j tR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_scheduled_at Job dJ sL j tL).
Proof.
  apply: ct_decide_bool.
  exact (car_tr (Hs tR tL Ht) (fun z => PropSPropRel (sR tR == Some j) (Lean.eq z (cl_opt (Some j))))
           (car_opt_eqb_rel Job (sR tR) (Some j))).
Qed.

Lemma car_US_service_at j tR tL (Ht : SubNatRel tR tL) :
  SubNatRel (UniprocessorSchedule.service_at sR j tR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_service_at Job dJ sL j tL).
Proof. exact (ct_bool_to_nat _ _ (car_US_scheduled_at j tR tL Ht)). Qed.

Lemma car_service_at_fun j : CarFunRel (fun t => UniprocessorSchedule.service_at sR j t) (fun t => I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_service_at Job dJ sL j t).
Proof. intros kR kL Hk. exact (car_US_service_at j kR kL Hk). Qed.

Lemma car_US_service_during j t1R t1L (H1 : SubNatRel t1R t1L) t2R t2L (H2 : SubNatRel t2R t2L) :
  SubNatRel (UniprocessorSchedule.service_during sR j t1R t2R) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_service_during Job dJ sL j t1L t2L).
Proof. exact (car_ico _ _ _ _ _ _ H1 H2 (car_service_at_fun j)). Qed.

Lemma car_US_service j tR tL (Ht : SubNatRel tR tL) :
  SubNatRel (UniprocessorSchedule.service sR j tR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_service Job dJ sL j tL).
Proof. exact (car_US_service_during j 0 _ (sub_nat_rel_canonical 0) tR tL Ht). Qed.

Lemma car_US_completed_by cR cL (Hc : CarParRel Job cR cL) j tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (UniprocessorSchedule.completed_by cR sR j tR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_completed_by Job dJ cL sL j tL).
Proof. exact (ct_decide_le _ _ _ _ (Hc j) (car_US_service j tR tL Ht)). Qed.

Lemma car_US_pending_earlier_and_at aR aL (Ha : CarParRel Job aR aL) cR cL (Hc : CarParRel Job cR cL) j
    tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (UniprocessorSchedule.pending_earlier_and_at aR cR sR j tR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_pending_earlier_and_at Job dJ aL cL sL j tL).
Proof.
  exact (ct_bool_and _ _ _ _ (car_arrived_before Job aR aL Ha j tR tL Ht)
           (ct_bool_not _ _ (car_US_completed_by cR cL Hc j tR tL Ht))).
Qed.

End USchedDefs.

Lemma car_iff (P Q : Prop) (PL QL : SProp) :
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
(** * Interference predicates and interfering workloads *)

Section IRel.
Variable Job : eqType.

Definition CarIntRel (iR : Job -> nat -> bool) (iL : Job -> Lean.Nat -> I.Bool) : SProp :=
  forall j tR tL, SubNatRel tR tL -> CtBoolRel (iR j tR) (iL j tL).

Lemma car_int_canonical iR : CarIntRel iR (fun j tL => ct_b2l (iR j (sub_nat_to_rocq tL))).
Proof. intros j tR tL Ht. have E := cl_nat_logic _ _ Ht. subst tL. rewrite sub_nat_rocq_roundtrip. exact (ct_bool_canonical _). Qed.

Lemma car_int_surjective iL : CarIntRel (fun j tR => ct_l2b (iL j (sub_nat_to_imported tR))) iL.
Proof. intros j tR tL Ht. have E := cl_nat_logic _ _ Ht. subst tL. exact (ct_bool_surjective _). Qed.

Lemma car_forall_int (PR : (Job -> nat -> bool) -> Prop) (PL : (Job -> Lean.Nat -> I.Bool) -> SProp) :
  (forall iR iL, CarIntRel iR iL -> PropSPropRel (PR iR) (PL iL)) -> PropSPropRel (forall i, PR i) (forall i, PL i).
Proof. exact (car_forall_cover _ _ CarIntRel _ _ car_int_canonical car_int_surjective PR PL). Qed.

Definition CarWlRel (wR : Job -> nat -> nat) (wL : Job -> Lean.Nat -> Lean.Nat) : SProp :=
  forall j tR tL, SubNatRel tR tL -> SubNatRel (wR j tR) (wL j tL).

Lemma car_wl_canonical wR : CarWlRel wR (fun j tL => sub_nat_to_imported (wR j (sub_nat_to_rocq tL))).
Proof. intros j tR tL Ht. have E := cl_nat_logic _ _ Ht. subst tL. rewrite sub_nat_rocq_roundtrip. exact (sub_nat_rel_canonical _). Qed.

Lemma car_wl_surjective wL : CarWlRel (fun j tR => sub_nat_to_rocq (wL j (sub_nat_to_imported tR))) wL.
Proof. intros j tR tL Ht. have E := cl_nat_logic _ _ Ht. subst tL. exact (sub_nat_rel_surjective _). Qed.

Lemma car_forall_wl (PR : (Job -> nat -> nat) -> Prop) (PL : (Job -> Lean.Nat -> Lean.Nat) -> SProp) :
  (forall wR wL, CarWlRel wR wL -> PropSPropRel (PR wR) (PL wL)) -> PropSPropRel (forall w, PR w) (forall w, PL w).
Proof. exact (car_forall_cover _ _ CarWlRel _ _ car_wl_canonical car_wl_surjective PR PL). Qed.
End IRel.

(* ------------------------------------------------------------------ *)
(** * Definitions *)

Section Defs.
Variables (Task Job : eqType).
Notation dT := (ct_decidable_eq Task).
Notation dJ := (ct_decidable_eq Job).

Theorem AbstractRTADefinitions_cumul_interference_correspondence iR iL (Hi : CarIntRel Job iR iL) j t1R t1L (H1 : SubNatRel t1R t1L)
    t2R t2L (H2 : SubNatRel t2R t2L) :
  SubNatRel (AbstractRTADefinitions.cumul_interference iR j t1R t2R) (I.Prosa_Classic_Model_Schedule_Uni_Limited_AbstractRTA_Definitions_AbstractRTADefinitions_cumul_interference Job dJ iL j t1L t2L).
Proof. exact (car_ico _ _ _ _ _ _ H1 H2 (fun kR kL Hk => ct_bool_to_nat _ _ (Hi j kR kL Hk))). Qed.

Theorem AbstractRTADefinitions_cumul_interfering_workload_correspondence wR wL (Hw : CarWlRel Job wR wL) j t1R t1L (H1 : SubNatRel t1R t1L)
    t2R t2L (H2 : SubNatRel t2R t2L) :
  SubNatRel (AbstractRTADefinitions.cumul_interfering_workload wR j t1R t2R) (I.Prosa_Classic_Model_Schedule_Uni_Limited_AbstractRTA_Definitions_AbstractRTADefinitions_cumul_interfering_workload Job dJ wL j t1L t2L).
Proof. exact (car_ico _ _ _ _ _ _ H1 H2 (fun kR kL Hk => Hw j kR kL Hk)). Qed.

Notation CI := AbstractRTADefinitions_cumul_interference_correspondence.
Notation CW := AbstractRTADefinitions_cumul_interfering_workload_correspondence.

Section Sched.
Variables (sR : UniprocessorSchedule.schedule Job) (sL : I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job dJ).
Hypothesis Hs : CarSchedRel Job sR sL.
Variables (aR : Job -> nat) (aL : Job -> Lean.Nat) (cR : Job -> nat) (cL : Job -> Lean.Nat).
Hypotheses (Ha : CarParRel Job aR aL) (Hc : CarParRel Job cR cL).
Variables (iR : Job -> nat -> bool) (iL : Job -> Lean.Nat -> I.Bool) (wR : Job -> nat -> nat) (wL : Job -> Lean.Nat -> Lean.Nat).
Hypotheses (Hi : CarIntRel Job iR iL) (Hw : CarWlRel Job wR wL).

Theorem AbstractRTADefinitions_quiet_time_correspondence j tR tL (Ht : SubNatRel tR tL) :
  PropSPropRel (AbstractRTADefinitions.quiet_time aR cR sR iR wR j tR) (I.Prosa_Classic_Model_Schedule_Uni_Limited_AbstractRTA_Definitions_AbstractRTADefinitions_quiet_time Job dJ aL cL sL iL wL j tL).
Proof.
  apply: ct_and.
  - exact (sub_nat_eq_correspondence _ _ _ _ (CI iR iL Hi j 0 _ (sub_nat_rel_canonical 0) tR tL Ht)
             (CW wR wL Hw j 0 _ (sub_nat_rel_canonical 0) tR tL Ht)).
  - exact (ct_bool_truth _ _ (ct_bool_not _ _ (car_US_pending_earlier_and_at Job sR sL Hs aR aL Ha cR cL Hc j tR tL Ht))).
Qed.

Theorem AbstractRTADefinitions_busy_interval_prefix_correspondence j t1R t1L (H1 : SubNatRel t1R t1L) t2R t2L (H2 : SubNatRel t2R t2L) :
  PropSPropRel (AbstractRTADefinitions.busy_interval_prefix aR cR sR iR wR j t1R t2R) (I.Prosa_Classic_Model_Schedule_Uni_Limited_AbstractRTA_Definitions_AbstractRTADefinitions_busy_interval_prefix Job dJ aL cL sL iL wL j t1L t2L).
Proof.
  apply: ct_and; first exact (ct_bool_truth _ _ (ct_bool_and _ _ _ _ (ct_decide_le _ _ _ _ H1 (Ha j)) (ct_decide_lt _ _ _ _ (Ha j) H2))).
  apply: ct_and; first exact (AbstractRTADefinitions_quiet_time_correspondence j t1R t1L H1).
  apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (ct_bool_truth _ _ (ct_bool_and _ _ _ _ (ct_decide_lt _ _ _ _ H1 Ht) (ct_decide_lt _ _ _ _ Ht H2))).
  exact (ct_imp _ _ _ _ (AbstractRTADefinitions_quiet_time_correspondence j tR tL Ht) car_false_rel).
Qed.

Theorem AbstractRTADefinitions_busy_interval_correspondence j t1R t1L (H1 : SubNatRel t1R t1L) t2R t2L (H2 : SubNatRel t2R t2L) :
  PropSPropRel (AbstractRTADefinitions.busy_interval aR cR sR iR wR j t1R t2R) (I.Prosa_Classic_Model_Schedule_Uni_Limited_AbstractRTA_Definitions_AbstractRTADefinitions_busy_interval Job dJ aL cL sL iL wL j t1L t2L).
Proof.
  apply: ct_and; first exact (AbstractRTADefinitions_busy_interval_prefix_correspondence j t1R t1L H1 t2R t2L H2).
  exact (AbstractRTADefinitions_quiet_time_correspondence j t2R t2L H2).
Qed.

Notation BI := AbstractRTADefinitions_busy_interval_correspondence.

Theorem AbstractRTADefinitions_work_conserving_correspondence (job_task : Job -> Task) arrR arrL (Harr : CarArrRel Job arrR arrL) tsk :
  PropSPropRel (AbstractRTADefinitions.work_conserving aR cR job_task arrR sR tsk iR wR)
    (I.Prosa_Classic_Model_Schedule_Uni_Limited_AbstractRTA_Definitions_AbstractRTADefinitions_work_conserving Task dT Job dJ aL cL job_task arrL sL tsk iL wL).
Proof.
  apply: ct_forall_identity => j.
  apply: ct_forall_nat => t1R t1L H1. apply: ct_forall_nat => t2R t2L H2. apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (car_arrives_in Job arrR arrL Harr j).
  apply: ct_imp; first exact (ct_eq_rel Task (job_task j) tsk).
  apply: ct_imp; first exact (sub_nat_lt_correspondence _ _ _ _ (sub_nat_rel_canonical 0) (Hc j)).
  apply: ct_imp; first exact (BI j t1R t1L H1 t2R t2L H2).
  apply: ct_imp; first exact (ct_bool_truth _ _ (ct_bool_and _ _ _ _ (ct_decide_le _ _ _ _ H1 Ht) (ct_decide_lt _ _ _ _ Ht H2))).
  apply: car_iff.
  - exact (ct_imp _ _ _ _ (ct_bool_truth _ _ (Hi j tR tL Ht)) car_false_rel).
  - exact (ct_bool_truth _ _ (car_US_scheduled_at Job sR sL Hs j tR tL Ht)).
Qed.

Theorem AbstractRTADefinitions_busy_intervals_are_bounded_by_correspondence (job_task : Job -> Task) arrR arrL (Harr : CarArrRel Job arrR arrL)
    tsk LR LL (HL : SubNatRel LR LL) :
  PropSPropRel (AbstractRTADefinitions.busy_intervals_are_bounded_by aR cR job_task arrR sR tsk iR wR LR)
    (I.Prosa_Classic_Model_Schedule_Uni_Limited_AbstractRTA_Definitions_AbstractRTADefinitions_busy_intervals_are_bounded_by Task dT Job dJ aL cL job_task arrL sL tsk iL wL LL).
Proof.
  apply: ct_forall_identity => j.
  apply: ct_imp; first exact (car_arrives_in Job arrR arrL Harr j).
  apply: ct_imp; first exact (ct_eq_rel Task (job_task j) tsk).
  apply: ct_imp; first exact (sub_nat_lt_correspondence _ _ _ _ (sub_nat_rel_canonical 0) (Hc j)).
  apply: ct_exists_nat => t1R t1L H1. apply: ct_exists_nat => t2R t2L H2.
  apply: ct_and; first exact (ct_bool_truth _ _ (ct_bool_and _ _ _ _ (ct_decide_le _ _ _ _ H1 (Ha j)) (ct_decide_lt _ _ _ _ (Ha j) H2))).
  apply: ct_and; first exact (sub_nat_le_correspondence _ _ _ _ H2 (sub_add_correspondence _ _ _ _ H1 HL)).
  exact (BI j t1R t1L H1 t2R t2L H2).
Qed.

Theorem AbstractRTADefinitions_job_interference_is_bounded_by_correspondence (job_task : Job -> Task) arrR arrL (Harr : CarArrRel Job arrR arrL)
    tsk fR fL (Hf : forall tsk aR' aL', SubNatRel aR' aL' -> forall xR xL, SubNatRel xR xL -> SubNatRel (fR tsk aR' xR) (fL tsk aL' xL)) :
  PropSPropRel (AbstractRTADefinitions.job_interference_is_bounded_by aR cR job_task arrR sR tsk iR wR fR)
    (I.Prosa_Classic_Model_Schedule_Uni_Limited_AbstractRTA_Definitions_AbstractRTADefinitions_job_interference_is_bounded_by Task dT Job dJ aL cL job_task arrL sL tsk iL wL fL).
Proof.
  apply: ct_forall_nat => t1R t1L H1. apply: ct_forall_nat => t2R t2L H2. apply: ct_forall_nat => dR dL Hd.
  apply: ct_forall_identity => j.
  apply: ct_imp; first exact (BI j t1R t1L H1 t2R t2L H2).
  have H1d := sub_add_correspondence _ _ _ _ H1 Hd.
  apply: ct_imp; first exact (sub_nat_lt_correspondence _ _ _ _ H1d H2).
  apply: ct_imp; first exact (car_arrives_in Job arrR arrL Harr j).
  apply: ct_imp; first exact (ct_eq_rel Task (job_task j) tsk).
  apply: ct_imp; first exact (ct_bool_truth _ _ (ct_bool_not _ _ (car_US_completed_by Job sR sL Hs cR cL Hc j _ _ H1d))).
  cbv zeta.
  exact (sub_nat_le_correspondence _ _ _ _ (CI iR iL Hi j _ _ H1 _ _ H1d) (Hf tsk _ _ (ct_sub_rel _ _ _ _ (Ha j) H1) _ _ Hd)).
Qed.
End Sched.
End Defs.

(* ------------------------------------------------------------------ *)
(** * Statements *)

Definition src_busy_interval_is_unique (Job : eqType) : Prop :=
  ltac:(type_of_term (@AbstractRTADefinitions.busy_interval_is_unique Job)).
Definition tgt_busy_interval_is_unique (Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Model_Schedule_Uni_Limited_AbstractRTA_Definitions_AbstractRTADefinitions_busy_interval_is_unique Job (ct_decidable_eq Job))).

Theorem AbstractRTADefinitions_busy_interval_is_unique_correspondence (Job : eqType) :
  PropSPropRel (src_busy_interval_is_unique Job) (tgt_busy_interval_is_unique Job).
Proof.
  unfold src_busy_interval_is_unique, tgt_busy_interval_is_unique.
  apply: car_forall_par => aR aL Ha. apply: car_forall_par => cR cL Hc. apply: car_forall_sched => sR sL Hs.
  apply: car_forall_int => iR iL Hi. apply: car_forall_wl => wR wL Hw.
  apply: ct_forall_identity => j.
  apply: ct_forall_nat => t1R t1L H1. apply: ct_forall_nat => t2R t2L H2.
  apply: ct_forall_nat => t1'R t1'L H1'. apply: ct_forall_nat => t2'R t2'L H2'.
  apply: ct_imp; first exact (AbstractRTADefinitions_busy_interval_correspondence Job sR sL Hs aR aL cR cL Ha Hc iR iL wR wL Hi Hw j _ _ H1 _ _ H2).
  apply: ct_imp; first exact (AbstractRTADefinitions_busy_interval_correspondence Job sR sL Hs aR aL cR cL Ha Hc iR iL wR wL Hi Hw j _ _ H1' _ _ H2').
  apply: ct_and; first exact (sub_nat_eq_correspondence _ _ _ _ H1 H1').
  exact (sub_nat_eq_correspondence _ _ _ _ H2 H2').
Qed.
