From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq fintype bigop.
From prosa Require Import classic.model.time classic.model.arrival.basic.arrival_sequence classic.model.arrival.basic.job classic.model.schedule.uni.schedule classic.model.schedule.uni.response_time classic.model.schedule.uni.limited.schedule classic.model.schedule.uni.limited.abstract_RTA.definitions classic.model.schedule.uni.limited.abstract_RTA.reduction_of_search_space classic.model.schedule.uni.limited.abstract_RTA.abstract_rta.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedClassicAbstractRta.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence ClassicAbstractRtaBase ClassicAbstractRtaList.



Module I := ImportedClassicAbstractRta.
Local Open Scope nat_scope.

(** Certificates for [classic/model/schedule/uni/limited/abstract_RTA/abstract_rta.v] (ProsaBuddy classic, commit f692cb7).

    Inputs: the job and task types are [eqType]s, identified, with the Lean [DecidableEq] instances given by the eqTypes'
    decision procedures ([ct_decidable_eq]); [job_task] identified; times by [SubNatRel]; job and task parameters
    pointwise through [SubNatRel]; arrival sequences pointwise on related times; interference predicates and
    interfering workloads pointwise on related times; interference bound functions pointwise on related arguments;
    uniprocessor schedules pointwise through the option map; all with two-way totals.  The abstract-RTA definitions,
    the reduction of the search space and the limited-preemption lock-in-service notions as in the accepted classic
    certificates (re-bound below).

    Statements: the source side is the exact elaborated type of the pinned lemma (via [type of]; the source proof is not
    used).  Where the task cost precedes the job type in both binder lists, the job type is fixed as an [eqType] with
    its canonical Lean instance and the task cost stays universally quantified on both sides. *)

Ltac type_of_term t := let T := type of t in exact T.
Notation cid := (fun z => z).

(* ------------------------------------------------------------------ *)
(** * Helpers (re-bound to this export from the accepted classic certificates) *)

(** Base definitions (as in the accepted classic base library), provided here when this export's library lacks them. *)

(* ------------------------------------------------------------------ *)
(** * Generic covers and helpers *)

Lemma cab_forall_cover (A B : Type) (Rel : A -> B -> SProp) (toB : A -> B) (toA : B -> A)
    (HB : forall a, Rel a (toB a)) (HA : forall b, Rel (toA b) b) (PR : A -> Prop) (PL : B -> SProp) :
  (forall a b, Rel a b -> PropSPropRel (PR a) (PL b)) -> PropSPropRel (forall a, PR a) (forall b, PL b).
Proof.
  intro H. apply prop_sprop_rel_intro.
  - intros HR b. exact (prop_to_sprop _ _ (H _ _ (HA b)) (HR _)).
  - intro HL. apply strictly_inhabits. intro a. exact (sprop_to_prop _ _ (H _ _ (HB a)) (HL _)).
Qed.

Lemma cab_false_rel : PropSPropRel Logic.False I.False.
Proof.
  apply prop_sprop_rel_intro.
  - exact ct_coq_false_to_target.
  - exact ct_target_false_to_strict.
Qed.

Lemma cab_ne (T : Type) (x y : T) : PropSPropRel (x <> y) (I.Ne T x y).
Proof. exact (ct_imp _ _ _ _ (ct_eq_rel T x y) cab_false_rel). Qed.

Lemma cab_mem (T : eqType) x s sL : ClListRel cid s sL ->
  PropSPropRel (x \in s) (I.Membership_mem T (I.List T) (I.List_instMembership T) sL x).
Proof. exact (cl_mem_rel_list T T cid cid (fun _ => Logic.eq_refl _) x s sL). Qed.

Lemma cab_unmap_rel (T : Type) (l : I.List T) : ClListRel cid (cl_unmap cid l) l.
Proof. apply: coq_eq_to_imported_eq. exact (cl_map_unmap cid cid (fun _ => Logic.eq_refl _) l). Qed.

Lemma cab_cl_map_inj (T : Type) (s1 s2 : seq T) : Logic.eq (cl_map cid s1) (cl_map cid s2) -> Logic.eq s1 s2.
Proof.
  intro E. rewrite -(cl_unmap_map cid cid (fun _ => Logic.eq_refl _) s1) -(cl_unmap_map cid cid (fun _ => Logic.eq_refl _) s2).
  by rewrite E.
Qed.

Lemma cab_succ_rel nR nL : SubNatRel nR nL ->
  SubNatRel nR.+1 (I.HAdd_hAdd_inst7 Lean.Nat Lean.Nat Lean.Nat (I.instHAdd_inst1 Lean.Nat I.instAddNat) nL
                     (I.OfNat_ofNat_inst1 Lean.Nat 1 (I.instOfNatNat 1))).
Proof. intro Hn. exact (sub_imported_eq_congr Lean.Nat_succ _ _ Hn). Qed.

(* ------------------------------------------------------------------ *)
(** * Big concatenation over a half-open interval (as in the accepted arrival_sequence certificate) *)

Lemma cab_forall_list (T : Type) (PR : seq T -> Prop) (PL : I.List T -> SProp) :
  (forall sR sL, ClListRel (B := T) cid sR sL -> PropSPropRel (PR sR) (PL sL)) -> PropSPropRel (forall s, PR s) (forall s, PL s).
Proof.
  exact (cab_forall_cover _ _ (fun sR sL => ClListRel (B := T) cid sR sL) (cl_map cid) (cl_unmap cid)
           (fun s => @Lean.eq_refl _ _) (fun l => cab_unmap_rel T l) PR PL).
Qed.

Definition CabParRel (T : Type) (pR : T -> nat) (pL : T -> Lean.Nat) : SProp := forall x, SubNatRel (pR x) (pL x).

Lemma cab_forall_par (T : Type) (PR : (T -> nat) -> Prop) (PL : (T -> Lean.Nat) -> SProp) :
  (forall pR pL, CabParRel T pR pL -> PropSPropRel (PR pR) (PL pL)) -> PropSPropRel (forall p, PR p) (forall p, PL p).
Proof.
  exact (cab_forall_cover _ _ (CabParRel T) (fun pR j => sub_nat_to_imported (pR j)) (fun pL j => sub_nat_to_rocq (pL j))
           (fun pR j => sub_nat_rel_canonical (pR j)) (fun pL j => sub_nat_rel_surjective (pL j)) PR PL).
Qed.

Fixpoint cab_natl (s : seq nat) : I.List_inst1 Lean.Nat :=
  match s with [::] => I.List_nil_inst1 _ | x :: s' => I.List_cons_inst1 _ (sub_nat_to_imported x) (cab_natl s') end.

Definition cab_one : Lean.Nat := I.OfNat_ofNat_inst1 Lean.Nat 1 (I.instOfNatNat 1).

Lemma cab_iota_range : forall n s,
  Logic.eq (I.List_range' (sub_nat_to_imported s) (sub_nat_to_imported n) cab_one) (cab_natl (iota s n)).
Proof.
  elim => [|n IH] s; first reflexivity.
  change (Logic.eq (I.List_cons_inst1 _ (sub_nat_to_imported s)
      (I.List_range' (sub_nat_to_imported (S s)) (sub_nat_to_imported n) cab_one))
    (I.List_cons_inst1 _ (sub_nat_to_imported s) (cab_natl (iota (S s) n)))).
  by rewrite IH.
Qed.

Lemma cab_cl_map_comp {A B C : Type} (f : A -> B) (g : B -> C) : forall s : seq A,
  Logic.eq (cl_map (fun x => g (f x)) s) (cl_map g (map f s)).
Proof. elim => [|x s IH] //=. by rewrite IH. Qed.

Lemma cab_cl_map_ext {A B : Type} (f g : A -> B) (H : forall x, Logic.eq (f x) (g x)) : forall s : seq A,
  Logic.eq (cl_map f s) (cl_map g s).
Proof. elim => [|x s IH] //=. by rewrite H IH. Qed.

Lemma cab_big_seq {A : Type} (F : nat -> seq A) : forall s : seq nat,
  Logic.eq (\big[cat/[::]]_(i <- s) F i) (flatten (map F s)).
Proof. elim => [|x s IH]; first by rewrite big_nil. by rewrite big_cons IH. Qed.

Definition CabFamRel (A : Type) (fR : nat -> seq A) (fL : Lean.Nat -> I.List A) : SProp :=
  forall nR nL, SubNatRel nR nL -> ClListRel cid (fR nR) (fL nL).

(* ------------------------------------------------------------------ *)
(** * Arrival sequences and parameters *)

Section Rel.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).
Notation LArr := (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrival_sequence Job dJ).

Definition CabArrRel (aR : ArrivalSequence.arrival_sequence Job) (aL : LArr) : SProp :=
  forall tR tL, SubNatRel tR tL -> ClListRel cid (aR tR) (aL tL).

Definition cab_arr_to_target (aR : ArrivalSequence.arrival_sequence Job) : LArr :=
  fun tL => cl_map cid (aR (sub_nat_to_rocq tL)).

Definition cab_arr_to_source (aL : LArr) : ArrivalSequence.arrival_sequence Job :=
  fun tR => cl_unmap cid (aL (sub_nat_to_imported tR)).

Lemma cab_arr_canonical aR : CabArrRel aR (cab_arr_to_target aR).
Proof.
  intros tR tL Ht. have E := cl_nat_logic _ _ Ht. subst tL.
  apply: coq_eq_to_imported_eq. rewrite /cab_arr_to_target sub_nat_rocq_roundtrip. reflexivity.
Qed.

Lemma cab_arr_surjective aL : CabArrRel (cab_arr_to_source aL) aL.
Proof.
  intros tR tL Ht. have E := cl_nat_logic _ _ Ht. subst tL.
  apply: coq_eq_to_imported_eq. exact (cl_map_unmap cid cid (fun _ => Logic.eq_refl _) _).
Qed.

Lemma cab_forall_arr (PR : ArrivalSequence.arrival_sequence Job -> Prop) (PL : LArr -> SProp) :
  (forall aR aL, CabArrRel aR aL -> PropSPropRel (PR aR) (PL aL)) -> PropSPropRel (forall a, PR a) (forall a, PL a).
Proof. exact (cab_forall_cover _ _ CabArrRel cab_arr_to_target cab_arr_to_source cab_arr_canonical cab_arr_surjective PR PL). Qed.

End Rel.

(** The imported [ArrivalSequence] definitions this file's statements mention, related on related inputs. *)
Section ArrivalDefs.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).

Lemma cab_arrives_in aR aL (Ha : CabArrRel Job aR aL) j :
  PropSPropRel (ArrivalSequence.arrives_in aR j)
    (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrives_in Job dJ aL j).
Proof. apply: ct_exists_nat => tR tL Ht. exact (cab_mem Job j _ _ (Ha tR tL Ht)). Qed.

End ArrivalDefs.

Section ArrivalDefs2.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).

Lemma cab_has_arrived pR pL (Hp : CabParRel Job pR pL) j tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (ArrivalSequence.has_arrived pR j tR)
    (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_has_arrived Job dJ pL j tL).
Proof. exact (ct_decide_le _ _ _ _ (Hp j) Ht). Qed.

Lemma cab_arrived_before pR pL (Hp : CabParRel Job pR pL) j tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (ArrivalSequence.arrived_before pR j tR)
    (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrived_before Job dJ pL j tL).
Proof. exact (ct_decide_lt _ _ _ _ (Hp j) Ht). Qed.

End ArrivalDefs2.

Fixpoint cab_snatl (s : seq nat) : I.List_inst1 Lean.Nat :=
  match s with [::] => I.List_nil_inst1 _ | x :: s' => I.List_cons_inst1 _ (sub_nat_to_imported x) (cab_snatl s') end.

Lemma cab_siota_range : forall n s,
  Logic.eq (I.List_range' (sub_nat_to_imported s) (sub_nat_to_imported n) (Lean.Nat_succ Lean.Nat_zero)) (cab_snatl (iota s n)).
Proof.
  elim => [|n IH] s; first reflexivity.
  change (Logic.eq (I.List_cons_inst1 _ (sub_nat_to_imported s)
      (I.List_range' (sub_nat_to_imported (S s)) (sub_nat_to_imported n) (Lean.Nat_succ Lean.Nat_zero)))
    (I.List_cons_inst1 _ (sub_nat_to_imported s) (cab_snatl (iota (S s) n)))).
  by rewrite IH.
Qed.

Lemma cab_foldr_add (f : Lean.Nat -> Lean.Nat) (g : nat -> nat) (Hf : forall k, Logic.eq (f (sub_nat_to_imported k)) (sub_nat_to_imported (g k))) :
  forall s, Logic.eq (I.List_foldr_inst3 Lean.Nat Lean.Nat Lean.Nat_add Lean.Nat_zero (I.List_map_inst3 Lean.Nat Lean.Nat f (cab_snatl s)))
                     (sub_nat_to_imported (foldr addn 0 (map g s))).
Proof.
  elim => [|k s IH] //=.
  change (Logic.eq (Lean.Nat_add (f (sub_nat_to_imported k))
            (I.List_foldr_inst3 Lean.Nat Lean.Nat Lean.Nat_add Lean.Nat_zero (I.List_map_inst3 Lean.Nat Lean.Nat f (cab_snatl s))))
         (sub_nat_to_imported (g k + foldr addn 0 (map g s)))).
  rewrite IH Hf. exact (imported_eq_to_coq_eq _ _ (sub_add_canonical _ _)).
Qed.

Lemma cab_big_fold (xs : seq nat) (F : nat -> nat) : Logic.eq (\sum_(i <- xs) F i) (foldr addn 0 (map F xs)).
Proof. elim: xs => [|x xs IH]; first by rewrite big_nil. by rewrite big_cons IH. Qed.

Definition CabFunRel (FR : nat -> nat) (FL : Lean.Nat -> Lean.Nat) : SProp :=
  forall kR kL, SubNatRel kR kL -> SubNatRel (FR kR) (FL kL).

Lemma cab_fun_canonical FR FL (HF : CabFunRel FR FL) k : Logic.eq (FL (sub_nat_to_imported k)) (sub_nat_to_imported (FR k)).
Proof. exact (cl_nat_logic _ _ (HF _ _ (sub_nat_rel_canonical k))). Qed.

Lemma cab_nat_sub_canonical (a b : nat) :
  Logic.eq (I.Nat_sub (sub_nat_to_imported a) (sub_nat_to_imported b)) (sub_nat_to_imported (a - b)).
Proof.
  elim: b => [|b IH]; first by rewrite subn0.
  change (Logic.eq (I.Nat_pred (I.Nat_sub (sub_nat_to_imported a) (sub_nat_to_imported b))) (sub_nat_to_imported (a - b.+1))).
  rewrite IH subnS. case: (a - b) => [|k]; reflexivity.
Qed.

Lemma cab_ico mR mL nR nL FR FL (Hm : SubNatRel mR mL) (Hn : SubNatRel nR nL) (HF : CabFunRel FR FL) :
  SubNatRel (\sum_(mR <= i < nR) FR i)
    (I.List_foldr_inst3 Lean.Nat Lean.Nat Lean.Nat_add Lean.Nat_zero
       (I.List_map_inst3 Lean.Nat Lean.Nat FL (I.List_range' mL (I.Nat_sub nL mL) (Lean.Nat_succ Lean.Nat_zero)))).
Proof.
  rewrite (cl_nat_logic _ _ Hm) (cl_nat_logic _ _ Hn).
  have -> : Logic.eq (I.Nat_sub (sub_nat_to_imported nR) (sub_nat_to_imported mR)) (sub_nat_to_imported (nR - mR))
    := cab_nat_sub_canonical nR mR.
  rewrite cab_siota_range.
  apply: coq_eq_to_imported_eq. apply: Logic.eq_sym. rewrite (cab_foldr_add FL FR (cab_fun_canonical FR FL HF)).
  by rewrite cab_big_fold.
Qed.

(* ------------------------------------------------------------------ *)
(** * Options and uniprocessor schedules *)

(** Transport along the target equality (definitional UIP), as in the accepted global schedule certificate. *)
Definition cab_tr {A : Type} {x y : A} (E : Lean.eq x y) (P : A -> Type) (h : P x) : P y :=
  match E in Lean.eq _ z return P z with Lean.eq_refl => h end.

Definition cab_trs {A : Type} {x y : A} (E : Lean.eq x y) (P : A -> SProp) (h : P x) : P y :=
  match E in Lean.eq _ z return P z with Lean.eq_refl => h end.

Lemma cab_opt_inj (A : Type) (o1 o2 : option A) : Logic.eq (cl_opt o1) (cl_opt o2) -> Logic.eq o1 o2.
Proof. intro E. by rewrite -(cl_unopt_opt o1) -(cl_unopt_opt o2) E. Qed.

Lemma cab_opt_eqb_rel (A : eqType) (o1 o2 : option A) :
  PropSPropRel (is_true (o1 == o2)) (Lean.eq (cl_opt o1) (cl_opt o2)).
Proof.
  apply prop_sprop_rel_intro.
  - move=> /eqP E. rewrite E. exact (@Lean.eq_refl _ _).
  - intro E. apply strictly_inhabits. apply/eqP. exact (cab_opt_inj A o1 o2 (imported_eq_to_coq_eq _ _ E)).
Qed.

Section Sched.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).
Notation LSched := (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job dJ).

Definition CabSchedRel (sR : UniprocessorSchedule.schedule Job) (sL : LSched) : SProp :=
  forall tR tL, SubNatRel tR tL -> Lean.eq (cl_opt (sR tR)) (sL tL).

Definition cab_sched_to_target (sR : UniprocessorSchedule.schedule Job) : LSched := fun tL => cl_opt (sR (sub_nat_to_rocq tL)).
Definition cab_sched_to_source (sL : LSched) : UniprocessorSchedule.schedule Job := fun tR => cl_unopt (sL (sub_nat_to_imported tR)).

Lemma cab_sched_canonical sR : CabSchedRel sR (cab_sched_to_target sR).
Proof. intros tR tL Ht. apply: coq_eq_to_imported_eq. by rewrite /cab_sched_to_target (cl_nat_input _ _ Ht). Qed.

Lemma cab_sched_surjective sL : CabSchedRel (cab_sched_to_source sL) sL.
Proof.
  intros tR tL Ht. apply: coq_eq_to_imported_eq. rewrite /cab_sched_to_source cl_opt_unopt.
  by rewrite (cl_nat_logic _ _ Ht).
Qed.

Lemma cab_forall_sched (PR : UniprocessorSchedule.schedule Job -> Prop) (PL : LSched -> SProp) :
  (forall sR sL, CabSchedRel sR sL -> PropSPropRel (PR sR) (PL sL)) -> PropSPropRel (forall s, PR s) (forall s, PL s).
Proof. exact (cab_forall_cover _ _ CabSchedRel cab_sched_to_target cab_sched_to_source cab_sched_canonical cab_sched_surjective PR PL). Qed.

End Sched.

(* ------------------------------------------------------------------ *)
(** * Definitions *)

Lemma cab_US_schedule (Job : eqType) :
  And (forall sR : UniprocessorSchedule.schedule Job, CabSchedRel Job sR (cab_sched_to_target Job sR))
      (forall sL : I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job (ct_decidable_eq Job), CabSchedRel Job (cab_sched_to_source Job sL) sL).
Proof. exact (And_intro _ _ (cab_sched_canonical Job) (cab_sched_surjective Job)). Qed.

Section USchedDefs.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).
Variables (sR : UniprocessorSchedule.schedule Job) (sL : I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job dJ).
Hypothesis Hs : CabSchedRel Job sR sL.

Lemma cab_US_scheduled_at j tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (UniprocessorSchedule.scheduled_at sR j tR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_scheduled_at Job dJ sL j tL).
Proof.
  apply: ct_decide_bool.
  exact (cab_tr (Hs tR tL Ht) (fun z => PropSPropRel (sR tR == Some j) (Lean.eq z (cl_opt (Some j))))
           (cab_opt_eqb_rel Job (sR tR) (Some j))).
Qed.

Lemma cab_US_service_at j tR tL (Ht : SubNatRel tR tL) :
  SubNatRel (UniprocessorSchedule.service_at sR j tR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_service_at Job dJ sL j tL).
Proof. exact (ct_bool_to_nat _ _ (cab_US_scheduled_at j tR tL Ht)). Qed.

Lemma cab_service_at_fun j : CabFunRel (fun t => UniprocessorSchedule.service_at sR j t) (fun t => I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_service_at Job dJ sL j t).
Proof. intros kR kL Hk. exact (cab_US_service_at j kR kL Hk). Qed.

Lemma cab_US_service_during j t1R t1L (H1 : SubNatRel t1R t1L) t2R t2L (H2 : SubNatRel t2R t2L) :
  SubNatRel (UniprocessorSchedule.service_during sR j t1R t2R) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_service_during Job dJ sL j t1L t2L).
Proof. exact (cab_ico _ _ _ _ _ _ H1 H2 (cab_service_at_fun j)). Qed.

Lemma cab_US_service j tR tL (Ht : SubNatRel tR tL) :
  SubNatRel (UniprocessorSchedule.service sR j tR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_service Job dJ sL j tL).
Proof. exact (cab_US_service_during j 0 _ (sub_nat_rel_canonical 0) tR tL Ht). Qed.

Lemma cab_US_completed_by cR cL (Hc : CabParRel Job cR cL) j tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (UniprocessorSchedule.completed_by cR sR j tR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_completed_by Job dJ cL sL j tL).
Proof. exact (ct_decide_le _ _ _ _ (Hc j) (cab_US_service j tR tL Ht)). Qed.

Lemma cab_US_pending_earlier_and_at aR aL (Ha : CabParRel Job aR aL) cR cL (Hc : CabParRel Job cR cL) j
    tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (UniprocessorSchedule.pending_earlier_and_at aR cR sR j tR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_pending_earlier_and_at Job dJ aL cL sL j tL).
Proof.
  exact (ct_bool_and _ _ _ _ (cab_arrived_before Job aR aL Ha j tR tL Ht)
           (ct_bool_not _ _ (cab_US_completed_by cR cL Hc j tR tL Ht))).
Qed.

Lemma cab_US_jobs_must_arrive_to_execute aR aL (Ha : CabParRel Job aR aL) :
  PropSPropRel (UniprocessorSchedule.jobs_must_arrive_to_execute aR sR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_jobs_must_arrive_to_execute Job dJ aL sL).
Proof.
  apply: ct_forall_identity => j. apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (ct_bool_truth _ _ (cab_US_scheduled_at j tR tL Ht)).
  exact (ct_bool_truth _ _ (cab_has_arrived Job aR aL Ha j tR tL Ht)).
Qed.

Lemma cab_US_completed_jobs_dont_execute cR cL (Hc : CabParRel Job cR cL) :
  PropSPropRel (UniprocessorSchedule.completed_jobs_dont_execute cR sR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_completed_jobs_dont_execute Job dJ cL sL).
Proof.
  apply: ct_forall_identity => j. apply: ct_forall_nat => tR tL Ht.
  exact (sub_nat_le_correspondence _ _ _ _ (cab_US_service j tR tL Ht) (Hc j)).
Qed.

End USchedDefs.

(** The imported [Job] definitions (as in the accepted classic job certificate). *)
Section JobDefs.
Notation c0 := (sub_nat_rel_canonical 0).
Variables (Task Job : eqType).
Notation dT := (ct_decidable_eq Task).
Notation dJ := (ct_decidable_eq Job).

Lemma cab_J_job_cost_positive cR cL (Hc : CabParRel Job cR cL) j :
  CtBoolRel (Job.job_cost_positive cR j) (I.Prosa_Classic_Model_Arrival_Basic_Job_Job_job_cost_positive Job dJ cL j).
Proof. exact (ct_decide_lt _ _ _ _ c0 (Hc j)). Qed.

Lemma cab_J_job_cost_le_task_cost tcR tcL (Htc : CabParRel Task tcR tcL) cR cL (Hc : CabParRel Job cR cL)
    (job_task : Job -> Task) j :
  CtBoolRel (Job.job_cost_le_task_cost tcR cR job_task j)
    (I.Prosa_Classic_Model_Arrival_Basic_Job_Job_job_cost_le_task_cost Task dT tcL Job dJ cL job_task j).
Proof. exact (ct_decide_le _ _ _ _ (Hc j) (Htc (job_task j))). Qed.

Lemma cab_J_cost_of_jobs_from_arrival_sequence_le_task_cost tcR tcL (Htc : CabParRel Task tcR tcL)
    cR cL (Hc : CabParRel Job cR cL) (job_task : Job -> Task) aR aL (Ha : CabArrRel Job aR aL) :
  PropSPropRel (Job.cost_of_jobs_from_arrival_sequence_le_task_cost tcR cR job_task aR)
    (I.Prosa_Classic_Model_Arrival_Basic_Job_Job_cost_of_jobs_from_arrival_sequence_le_task_cost Task dT tcL Job dJ cL job_task aL).
Proof.
  apply: ct_forall_identity => j.
  apply: ct_imp.
  - apply: ct_exists_nat => tR tL Ht. exact (cab_mem Job j _ _ (Ha tR tL Ht)).
  - exact (ct_bool_truth _ _ (cab_J_job_cost_le_task_cost tcR tcL Htc cR cL Hc job_task j)).
Qed.

End JobDefs.

Section UrtDefs.
Variables (Task Job : eqType).
Notation dT := (ct_decidable_eq Task).
Notation dJ := (ct_decidable_eq Job).
Variables (sR : UniprocessorSchedule.schedule Job) (sL : I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job dJ).
Hypothesis Hs : CabSchedRel Job sR sL.

Lemma cab_RT_is_response_time_bound_of_job aR aL (Ha : CabParRel Job aR aL) cR cL (Hc : CabParRel Job cR cL)
    j rR rL (Hr : SubNatRel rR rL) :
  CtBoolRel (ResponseTime.is_response_time_bound_of_job aR cR sR j rR) (I.Prosa_Classic_Model_Schedule_Uni_ResponseTime_ResponseTime_is_response_time_bound_of_job Job dJ aL cL sL j rL).
Proof. exact (cab_US_completed_by Job sR sL Hs cR cL Hc j _ _ (sub_add_correspondence _ _ _ _ (Ha j) Hr)). Qed.

Lemma cab_RT_is_response_time_bound_of_task aR aL (Ha : CabParRel Job aR aL) cR cL (Hc : CabParRel Job cR cL)
    (job_task : Job -> Task) arrR arrL (Harr : CabArrRel Job arrR arrL) tsk rR rL (Hr : SubNatRel rR rL) :
  PropSPropRel (ResponseTime.is_response_time_bound_of_task aR cR job_task arrR sR tsk rR)
    (I.Prosa_Classic_Model_Schedule_Uni_ResponseTime_ResponseTime_is_response_time_bound_of_task Task dT Job dJ aL cL job_task arrL sL tsk rL).
Proof.
  apply: ct_forall_identity => j.
  apply: ct_imp; first exact (cab_arrives_in Job arrR arrL Harr j).
  apply: ct_imp; first exact (ct_eq_rel Task (job_task j) tsk).
  exact (ct_bool_truth _ _ (cab_RT_is_response_time_bound_of_job aR aL Ha cR cL Hc j rR rL Hr)).
Qed.

End UrtDefs.

Lemma cab_iff (P Q : Prop) (PL QL : SProp) :
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
(** * Relations *)

Lemma cab_eq_transport (T : Type) (a b : T) aL bL : Lean.eq a aL -> Lean.eq b bL ->
  PropSPropRel (Logic.eq a b) (Lean.eq aL bL).
Proof. intros Ha Hb. destruct Ha. destruct Hb. exact (ct_eq_rel T a b). Qed.

(** Functions [nat -> T] (identical values) and [nat -> nat] (values by [SubNatRel]), pointwise on related arguments. *)
Definition CabRsFunRel (T : Type) (fR : nat -> T) (fL : Lean.Nat -> T) : SProp :=
  forall nR nL, SubNatRel nR nL -> Lean.eq (fR nR) (fL nL).
Definition CabNatFunRel (fR : nat -> nat) (fL : Lean.Nat -> Lean.Nat) : SProp :=
  forall nR nL, SubNatRel nR nL -> SubNatRel (fR nR) (fL nL).

(** Interference bound functions [Task -> time -> time -> time], pointwise on related arguments and values. *)
Definition CabIbfRel (Task : Type) (fR : Task -> nat -> nat -> nat) (fL : Task -> Lean.Nat -> Lean.Nat -> Lean.Nat) : SProp :=
  forall tsk, forall aR aL, SubNatRel aR aL -> CabNatFunRel (fR tsk aR) (fL tsk aL).

Definition cab_ibf_to_target (Task : Type) (fR : Task -> nat -> nat -> nat) : Task -> Lean.Nat -> Lean.Nat -> Lean.Nat :=
  fun tsk aL xL => sub_nat_to_imported (fR tsk (sub_nat_to_rocq aL) (sub_nat_to_rocq xL)).
Definition cab_ibf_to_source (Task : Type) (fL : Task -> Lean.Nat -> Lean.Nat -> Lean.Nat) : Task -> nat -> nat -> nat :=
  fun tsk aR xR => sub_nat_to_rocq (fL tsk (sub_nat_to_imported aR) (sub_nat_to_imported xR)).

Lemma cab_ibf_canonical (Task : Type) fR : CabIbfRel Task fR (cab_ibf_to_target Task fR).
Proof.
  intros tsk aR aL Ha xR xL Hx. have Ea := cl_nat_logic _ _ Ha. have Ex := cl_nat_logic _ _ Hx. subst aL xL.
  unfold cab_ibf_to_target. rewrite !sub_nat_rocq_roundtrip. exact (sub_nat_rel_canonical _).
Qed.

Lemma cab_ibf_surjective (Task : Type) fL : CabIbfRel Task (cab_ibf_to_source Task fL) fL.
Proof.
  intros tsk aR aL Ha xR xL Hx. have Ea := cl_nat_logic _ _ Ha. have Ex := cl_nat_logic _ _ Hx. subst aL xL.
  exact (sub_nat_rel_surjective _).
Qed.

Lemma cab_forall_ibf (Task : Type) (PR : (Task -> nat -> nat -> nat) -> Prop) (PL : (Task -> Lean.Nat -> Lean.Nat -> Lean.Nat) -> SProp) :
  (forall fR fL, CabIbfRel Task fR fL -> PropSPropRel (PR fR) (PL fL)) -> PropSPropRel (forall f, PR f) (forall f, PL f).
Proof. exact (cab_forall_cover _ _ (CabIbfRel Task) (cab_ibf_to_target Task) (cab_ibf_to_source Task) (cab_ibf_canonical Task) (cab_ibf_surjective Task) PR PL). Qed.

(* ------------------------------------------------------------------ *)
(** * Definitions *)

Lemma cab_RS_are_equivalent_at_values_less_than (T : eqType) f1R f1L (H1 : CabRsFunRel T f1R f1L)
    f2R f2L (H2 : CabRsFunRel T f2R f2L) BR BL (HB : SubNatRel BR BL) :
  PropSPropRel (AbstractRTAReduction.are_equivalent_at_values_less_than f1R f2R BR)
    (I.Prosa_Classic_Model_Schedule_Uni_Limited_AbstractRTA_ReductionOfSearchSpace_AbstractRTAReduction_are_equivalent_at_values_less_than T (ct_decidable_eq T) f1L f2L BL).
Proof.
  apply: ct_forall_nat => xR xL Hx.
  apply: ct_imp; first exact (sub_nat_lt_correspondence _ _ _ _ Hx HB).
  exact (cab_eq_transport T _ _ _ _ (H1 xR xL Hx) (H2 xR xL Hx)).
Qed.

Lemma cab_RS_are_not_equivalent_at_values_less_than (T : eqType) f1R f1L (H1 : CabRsFunRel T f1R f1L)
    f2R f2L (H2 : CabRsFunRel T f2R f2L) BR BL (HB : SubNatRel BR BL) :
  PropSPropRel (AbstractRTAReduction.are_not_equivalent_at_values_less_than f1R f2R BR)
    (I.Prosa_Classic_Model_Schedule_Uni_Limited_AbstractRTA_ReductionOfSearchSpace_AbstractRTAReduction_are_not_equivalent_at_values_less_than T (ct_decidable_eq T) f1L f2L BL).
Proof.
  apply: ct_exists_nat => xR xL Hx.
  apply: ct_and; first exact (sub_nat_lt_correspondence _ _ _ _ Hx HB).
  exact (ct_imp _ _ _ _ (cab_eq_transport T _ _ _ _ (H1 xR xL Hx) (H2 xR xL Hx)) cab_false_rel).
Qed.

(** The [T = nat] instances used by [is_in_search_space] and the statements. *)
Lemma cab_equiv_nat f1R f1L (H1 : CabNatFunRel f1R f1L) f2R f2L (H2 : CabNatFunRel f2R f2L) BR BL (HB : SubNatRel BR BL) :
  PropSPropRel (AbstractRTAReduction.are_equivalent_at_values_less_than f1R f2R BR)
    (I.Prosa_Classic_Model_Schedule_Uni_Limited_AbstractRTA_ReductionOfSearchSpace_AbstractRTAReduction_are_equivalent_at_values_less_than_inst1 Lean.Nat I.instDecidableEqNat f1L f2L BL).
Proof.
  apply: ct_forall_nat => xR xL Hx.
  apply: ct_imp; first exact (sub_nat_lt_correspondence _ _ _ _ Hx HB).
  exact (sub_nat_eq_correspondence _ _ _ _ (H1 xR xL Hx) (H2 xR xL Hx)).
Qed.

Lemma cab_not_equiv_nat f1R f1L (H1 : CabNatFunRel f1R f1L) f2R f2L (H2 : CabNatFunRel f2R f2L) BR BL (HB : SubNatRel BR BL) :
  PropSPropRel (AbstractRTAReduction.are_not_equivalent_at_values_less_than f1R f2R BR)
    (I.Prosa_Classic_Model_Schedule_Uni_Limited_AbstractRTA_ReductionOfSearchSpace_AbstractRTAReduction_are_not_equivalent_at_values_less_than_inst1 Lean.Nat I.instDecidableEqNat f1L f2L BL).
Proof.
  apply: ct_exists_nat => xR xL Hx.
  apply: ct_and; first exact (sub_nat_lt_correspondence _ _ _ _ Hx HB).
  exact (ct_imp _ _ _ _ (sub_nat_eq_correspondence _ _ _ _ (H1 xR xL Hx) (H2 xR xL Hx)) cab_false_rel).
Qed.

Lemma cab_RS_is_in_search_space (Task : eqType) tsk BR BL (HB : SubNatRel BR BL)
    fR fL (Hf : CabIbfRel Task fR fL) AR AL (HA : SubNatRel AR AL) :
  PropSPropRel (AbstractRTAReduction.is_in_search_space tsk BR fR AR) (I.Prosa_Classic_Model_Schedule_Uni_Limited_AbstractRTA_ReductionOfSearchSpace_AbstractRTAReduction_is_in_search_space Task (ct_decidable_eq Task) tsk BL fL AL).
Proof.
  apply: ct_or; first exact (sub_nat_eq_correspondence _ _ _ _ HA (sub_nat_rel_canonical 0)).
  apply: ct_and.
  - exact (ct_bool_truth _ _ (ct_bool_and _ _ _ _ (ct_decide_lt _ _ _ _ (sub_nat_rel_canonical 0) HA) (ct_decide_lt _ _ _ _ HA HB))).
  - exact (cab_not_equiv_nat _ _ (Hf tsk _ _ (ct_sub_rel _ _ _ _ HA (sub_nat_rel_canonical 1))) _ _ (Hf tsk _ _ HA) _ _ HB).
Qed.

(* ------------------------------------------------------------------ *)
(** * Interference predicates and interfering workloads *)

Section ARDIRel.
Variable Job : eqType.

Definition CabIntRel (iR : Job -> nat -> bool) (iL : Job -> Lean.Nat -> I.Bool) : SProp :=
  forall j tR tL, SubNatRel tR tL -> CtBoolRel (iR j tR) (iL j tL).

Lemma cab_int_canonical iR : CabIntRel iR (fun j tL => ct_b2l (iR j (sub_nat_to_rocq tL))).
Proof. intros j tR tL Ht. have E := cl_nat_logic _ _ Ht. subst tL. rewrite sub_nat_rocq_roundtrip. exact (ct_bool_canonical _). Qed.

Lemma cab_int_surjective iL : CabIntRel (fun j tR => ct_l2b (iL j (sub_nat_to_imported tR))) iL.
Proof. intros j tR tL Ht. have E := cl_nat_logic _ _ Ht. subst tL. exact (ct_bool_surjective _). Qed.

Lemma cab_forall_int (PR : (Job -> nat -> bool) -> Prop) (PL : (Job -> Lean.Nat -> I.Bool) -> SProp) :
  (forall iR iL, CabIntRel iR iL -> PropSPropRel (PR iR) (PL iL)) -> PropSPropRel (forall i, PR i) (forall i, PL i).
Proof. exact (cab_forall_cover _ _ CabIntRel _ _ cab_int_canonical cab_int_surjective PR PL). Qed.

Definition CabWlRel (wR : Job -> nat -> nat) (wL : Job -> Lean.Nat -> Lean.Nat) : SProp :=
  forall j tR tL, SubNatRel tR tL -> SubNatRel (wR j tR) (wL j tL).

Lemma cab_wl_canonical wR : CabWlRel wR (fun j tL => sub_nat_to_imported (wR j (sub_nat_to_rocq tL))).
Proof. intros j tR tL Ht. have E := cl_nat_logic _ _ Ht. subst tL. rewrite sub_nat_rocq_roundtrip. exact (sub_nat_rel_canonical _). Qed.

Lemma cab_wl_surjective wL : CabWlRel (fun j tR => sub_nat_to_rocq (wL j (sub_nat_to_imported tR))) wL.
Proof. intros j tR tL Ht. have E := cl_nat_logic _ _ Ht. subst tL. exact (sub_nat_rel_surjective _). Qed.

Lemma cab_forall_wl (PR : (Job -> nat -> nat) -> Prop) (PL : (Job -> Lean.Nat -> Lean.Nat) -> SProp) :
  (forall wR wL, CabWlRel wR wL -> PropSPropRel (PR wR) (PL wL)) -> PropSPropRel (forall w, PR w) (forall w, PL w).
Proof. exact (cab_forall_cover _ _ CabWlRel _ _ cab_wl_canonical cab_wl_surjective PR PL). Qed.

End ARDIRel.

(* ------------------------------------------------------------------ *)
(** * Definitions *)

Section ARDDefs.
Variables (Task Job : eqType).
Notation dT := (ct_decidable_eq Task).
Notation dJ := (ct_decidable_eq Job).

Lemma cab_ARD_cumul_interference iR iL (Hi : CabIntRel Job iR iL) j t1R t1L (H1 : SubNatRel t1R t1L)
    t2R t2L (H2 : SubNatRel t2R t2L) :
  SubNatRel (AbstractRTADefinitions.cumul_interference iR j t1R t2R) (I.Prosa_Classic_Model_Schedule_Uni_Limited_AbstractRTA_Definitions_AbstractRTADefinitions_cumul_interference Job dJ iL j t1L t2L).
Proof. exact (cab_ico _ _ _ _ _ _ H1 H2 (fun kR kL Hk => ct_bool_to_nat _ _ (Hi j kR kL Hk))). Qed.

Lemma cab_ARD_cumul_interfering_workload wR wL (Hw : CabWlRel Job wR wL) j t1R t1L (H1 : SubNatRel t1R t1L)
    t2R t2L (H2 : SubNatRel t2R t2L) :
  SubNatRel (AbstractRTADefinitions.cumul_interfering_workload wR j t1R t2R) (I.Prosa_Classic_Model_Schedule_Uni_Limited_AbstractRTA_Definitions_AbstractRTADefinitions_cumul_interfering_workload Job dJ wL j t1L t2L).
Proof. exact (cab_ico _ _ _ _ _ _ H1 H2 (fun kR kL Hk => Hw j kR kL Hk)). Qed.

Notation CI := cab_ARD_cumul_interference.
Notation CW := cab_ARD_cumul_interfering_workload.

Section ARDSched.
Variables (sR : UniprocessorSchedule.schedule Job) (sL : I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job dJ).
Hypothesis Hs : CabSchedRel Job sR sL.
Variables (aR : Job -> nat) (aL : Job -> Lean.Nat) (cR : Job -> nat) (cL : Job -> Lean.Nat).
Hypotheses (Ha : CabParRel Job aR aL) (Hc : CabParRel Job cR cL).
Variables (iR : Job -> nat -> bool) (iL : Job -> Lean.Nat -> I.Bool) (wR : Job -> nat -> nat) (wL : Job -> Lean.Nat -> Lean.Nat).
Hypotheses (Hi : CabIntRel Job iR iL) (Hw : CabWlRel Job wR wL).

Lemma cab_ARD_quiet_time j tR tL (Ht : SubNatRel tR tL) :
  PropSPropRel (AbstractRTADefinitions.quiet_time aR cR sR iR wR j tR) (I.Prosa_Classic_Model_Schedule_Uni_Limited_AbstractRTA_Definitions_AbstractRTADefinitions_quiet_time Job dJ aL cL sL iL wL j tL).
Proof.
  apply: ct_and.
  - exact (sub_nat_eq_correspondence _ _ _ _ (CI iR iL Hi j 0 _ (sub_nat_rel_canonical 0) tR tL Ht)
             (CW wR wL Hw j 0 _ (sub_nat_rel_canonical 0) tR tL Ht)).
  - exact (ct_bool_truth _ _ (ct_bool_not _ _ (cab_US_pending_earlier_and_at Job sR sL Hs aR aL Ha cR cL Hc j tR tL Ht))).
Qed.

Lemma cab_ARD_busy_interval_prefix j t1R t1L (H1 : SubNatRel t1R t1L) t2R t2L (H2 : SubNatRel t2R t2L) :
  PropSPropRel (AbstractRTADefinitions.busy_interval_prefix aR cR sR iR wR j t1R t2R) (I.Prosa_Classic_Model_Schedule_Uni_Limited_AbstractRTA_Definitions_AbstractRTADefinitions_busy_interval_prefix Job dJ aL cL sL iL wL j t1L t2L).
Proof.
  apply: ct_and; first exact (ct_bool_truth _ _ (ct_bool_and _ _ _ _ (ct_decide_le _ _ _ _ H1 (Ha j)) (ct_decide_lt _ _ _ _ (Ha j) H2))).
  apply: ct_and; first exact (cab_ARD_quiet_time j t1R t1L H1).
  apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (ct_bool_truth _ _ (ct_bool_and _ _ _ _ (ct_decide_lt _ _ _ _ H1 Ht) (ct_decide_lt _ _ _ _ Ht H2))).
  exact (ct_imp _ _ _ _ (cab_ARD_quiet_time j tR tL Ht) cab_false_rel).
Qed.

Lemma cab_ARD_busy_interval j t1R t1L (H1 : SubNatRel t1R t1L) t2R t2L (H2 : SubNatRel t2R t2L) :
  PropSPropRel (AbstractRTADefinitions.busy_interval aR cR sR iR wR j t1R t2R) (I.Prosa_Classic_Model_Schedule_Uni_Limited_AbstractRTA_Definitions_AbstractRTADefinitions_busy_interval Job dJ aL cL sL iL wL j t1L t2L).
Proof.
  apply: ct_and; first exact (cab_ARD_busy_interval_prefix j t1R t1L H1 t2R t2L H2).
  exact (cab_ARD_quiet_time j t2R t2L H2).
Qed.

Notation BI := cab_ARD_busy_interval.

Lemma cab_ARD_work_conserving (job_task : Job -> Task) arrR arrL (Harr : CabArrRel Job arrR arrL) tsk :
  PropSPropRel (AbstractRTADefinitions.work_conserving aR cR job_task arrR sR tsk iR wR)
    (I.Prosa_Classic_Model_Schedule_Uni_Limited_AbstractRTA_Definitions_AbstractRTADefinitions_work_conserving Task dT Job dJ aL cL job_task arrL sL tsk iL wL).
Proof.
  apply: ct_forall_identity => j.
  apply: ct_forall_nat => t1R t1L H1. apply: ct_forall_nat => t2R t2L H2. apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (cab_arrives_in Job arrR arrL Harr j).
  apply: ct_imp; first exact (ct_eq_rel Task (job_task j) tsk).
  apply: ct_imp; first exact (sub_nat_lt_correspondence _ _ _ _ (sub_nat_rel_canonical 0) (Hc j)).
  apply: ct_imp; first exact (BI j t1R t1L H1 t2R t2L H2).
  apply: ct_imp; first exact (ct_bool_truth _ _ (ct_bool_and _ _ _ _ (ct_decide_le _ _ _ _ H1 Ht) (ct_decide_lt _ _ _ _ Ht H2))).
  apply: cab_iff.
  - exact (ct_imp _ _ _ _ (ct_bool_truth _ _ (Hi j tR tL Ht)) cab_false_rel).
  - exact (ct_bool_truth _ _ (cab_US_scheduled_at Job sR sL Hs j tR tL Ht)).
Qed.

Lemma cab_ARD_busy_intervals_are_bounded_by (job_task : Job -> Task) arrR arrL (Harr : CabArrRel Job arrR arrL)
    tsk LR LL (HL : SubNatRel LR LL) :
  PropSPropRel (AbstractRTADefinitions.busy_intervals_are_bounded_by aR cR job_task arrR sR tsk iR wR LR)
    (I.Prosa_Classic_Model_Schedule_Uni_Limited_AbstractRTA_Definitions_AbstractRTADefinitions_busy_intervals_are_bounded_by Task dT Job dJ aL cL job_task arrL sL tsk iL wL LL).
Proof.
  apply: ct_forall_identity => j.
  apply: ct_imp; first exact (cab_arrives_in Job arrR arrL Harr j).
  apply: ct_imp; first exact (ct_eq_rel Task (job_task j) tsk).
  apply: ct_imp; first exact (sub_nat_lt_correspondence _ _ _ _ (sub_nat_rel_canonical 0) (Hc j)).
  apply: ct_exists_nat => t1R t1L H1. apply: ct_exists_nat => t2R t2L H2.
  apply: ct_and; first exact (ct_bool_truth _ _ (ct_bool_and _ _ _ _ (ct_decide_le _ _ _ _ H1 (Ha j)) (ct_decide_lt _ _ _ _ (Ha j) H2))).
  apply: ct_and; first exact (sub_nat_le_correspondence _ _ _ _ H2 (sub_add_correspondence _ _ _ _ H1 HL)).
  exact (BI j t1R t1L H1 t2R t2L H2).
Qed.

Lemma cab_ARD_job_interference_is_bounded_by (job_task : Job -> Task) arrR arrL (Harr : CabArrRel Job arrR arrL)
    tsk fR fL (Hf : forall tsk aR' aL', SubNatRel aR' aL' -> forall xR xL, SubNatRel xR xL -> SubNatRel (fR tsk aR' xR) (fL tsk aL' xL)) :
  PropSPropRel (AbstractRTADefinitions.job_interference_is_bounded_by aR cR job_task arrR sR tsk iR wR fR)
    (I.Prosa_Classic_Model_Schedule_Uni_Limited_AbstractRTA_Definitions_AbstractRTADefinitions_job_interference_is_bounded_by Task dT Job dJ aL cL job_task arrL sL tsk iL wL fL).
Proof.
  apply: ct_forall_nat => t1R t1L H1. apply: ct_forall_nat => t2R t2L H2. apply: ct_forall_nat => dR dL Hd.
  apply: ct_forall_identity => j.
  apply: ct_imp; first exact (BI j t1R t1L H1 t2R t2L H2).
  have H1d := sub_add_correspondence _ _ _ _ H1 Hd.
  apply: ct_imp; first exact (sub_nat_lt_correspondence _ _ _ _ H1d H2).
  apply: ct_imp; first exact (cab_arrives_in Job arrR arrL Harr j).
  apply: ct_imp; first exact (ct_eq_rel Task (job_task j) tsk).
  apply: ct_imp; first exact (ct_bool_truth _ _ (ct_bool_not _ _ (cab_US_completed_by Job sR sL Hs cR cL Hc j _ _ H1d))).
  cbv zeta.
  exact (sub_nat_le_correspondence _ _ _ _ (CI iR iL Hi j _ _ H1 _ _ H1d) (Hf tsk _ _ (ct_sub_rel _ _ _ _ (Ha j) H1) _ _ Hd)).
Qed.

End ARDSched.

End ARDDefs.

(* ------------------------------------------------------------------ *)
(** * Definitions *)

Module LS := prosa.classic.model.schedule.uni.limited.schedule.

Section LSDefs.
Variables (Task Job : eqType).
Notation dT := (ct_decidable_eq Task).
Notation dJ := (ct_decidable_eq Job).
Variables (cR : Job -> nat) (cL : Job -> Lean.Nat).
Hypothesis Hc : CabParRel Job cR cL.
Variables (arrR : ArrivalSequence.arrival_sequence Job)
  (arrL : I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrival_sequence Job dJ).
Hypothesis Harr : CabArrRel Job arrR arrL.
Variables (lR : Job -> nat) (lL : Job -> Lean.Nat).
Hypothesis Hl : CabParRel Job lR lL.

Lemma cab_LS_job_lock_in_service_positive :
  PropSPropRel (LS.job_lock_in_service_positive cR arrR lR) (I.Prosa_Classic_Model_Schedule_Uni_Limited_Schedule_job_lock_in_service_positive Job dJ cL arrL lL).
Proof.
  apply: ct_forall_identity => j.
  apply: ct_imp; first exact (cab_arrives_in Job arrR arrL Harr j).
  apply: ct_imp; first exact (ct_bool_truth _ _ (cab_J_job_cost_positive Job cR cL Hc j)).
  exact (sub_nat_lt_correspondence _ _ _ _ (sub_nat_rel_canonical 0) (Hl j)).
Qed.

Lemma cab_LS_job_lock_in_service_le_job_cost :
  PropSPropRel (LS.job_lock_in_service_le_job_cost cR arrR lR) (I.Prosa_Classic_Model_Schedule_Uni_Limited_Schedule_job_lock_in_service_le_job_cost Job dJ cL arrL lL).
Proof.
  apply: ct_forall_identity => j.
  apply: ct_imp; first exact (cab_arrives_in Job arrR arrL Harr j).
  apply: ct_imp; first exact (ct_bool_truth _ _ (cab_J_job_cost_positive Job cR cL Hc j)).
  exact (sub_nat_le_correspondence _ _ _ _ (Hl j) (Hc j)).
Qed.

Section LSSched.
Variables (sR : UniprocessorSchedule.schedule Job) (sL : I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job dJ).
Hypothesis Hs : CabSchedRel Job sR sL.

Lemma cab_LS_job_nonpreemptive_after_lock_in_service :
  PropSPropRel (LS.job_nonpreemptive_after_lock_in_service cR arrR sR lR)
    (I.Prosa_Classic_Model_Schedule_Uni_Limited_Schedule_job_nonpreemptive_after_lock_in_service Job dJ cL arrL sL lL).
Proof.
  apply: ct_forall_identity => j. apply: ct_forall_nat => tR tL Ht. apply: ct_forall_nat => t'R t'L Ht'.
  apply: ct_imp; first exact (cab_arrives_in Job arrR arrL Harr j).
  apply: ct_imp; first exact (sub_nat_le_correspondence _ _ _ _ Ht Ht').
  apply: ct_imp; first exact (sub_nat_le_correspondence _ _ _ _ (Hl j) (cab_US_service Job sR sL Hs j _ _ Ht)).
  apply: ct_imp; first exact (ct_bool_truth _ _ (ct_bool_not _ _ (cab_US_completed_by Job sR sL Hs cR cL Hc j _ _ Ht'))).
  exact (ct_bool_truth _ _ (cab_US_scheduled_at Job sR sL Hs j _ _ Ht')).
Qed.

Lemma cab_LS_proper_job_lock_in_service :
  PropSPropRel (LS.proper_job_lock_in_service cR arrR sR lR) (I.Prosa_Classic_Model_Schedule_Uni_Limited_Schedule_proper_job_lock_in_service Job dJ cL arrL sL lL).
Proof.
  apply: ct_and; first exact cab_LS_job_lock_in_service_positive.
  apply: ct_and; first exact cab_LS_job_lock_in_service_le_job_cost.
  exact cab_LS_job_nonpreemptive_after_lock_in_service.
Qed.

End LSSched.

Variables (tcR : Task -> nat) (tcL : Task -> Lean.Nat) (tlR : Task -> nat) (tlL : Task -> Lean.Nat).
Hypotheses (Htc : CabParRel Task tcR tcL) (Htl : CabParRel Task tlR tlL).

Lemma cab_LS_task_lock_in_service_le_task_cost tsk :
  PropSPropRel (LS.task_lock_in_service_le_task_cost tcR tlR tsk) (I.Prosa_Classic_Model_Schedule_Uni_Limited_Schedule_task_lock_in_service_le_task_cost Task dT tcL tlL tsk).
Proof. exact (sub_nat_le_correspondence _ _ _ _ (Htl tsk) (Htc tsk)). Qed.

Lemma cab_LS_task_lock_in_service_bounds_job_lock_in_service (job_task : Job -> Task) tsk :
  PropSPropRel (LS.task_lock_in_service_bounds_job_lock_in_service job_task arrR lR tlR tsk)
    (I.Prosa_Classic_Model_Schedule_Uni_Limited_Schedule_task_lock_in_service_bounds_job_lock_in_service Task dT Job dJ job_task arrL lL tlL tsk).
Proof.
  apply: ct_forall_identity => j.
  apply: ct_imp; first exact (cab_arrives_in Job arrR arrL Harr j).
  apply: ct_imp; first exact (ct_eq_rel Task (job_task j) tsk).
  exact (sub_nat_le_correspondence _ _ _ _ (Hl j) (Htl tsk)).
Qed.

Lemma cab_LS_proper_task_lock_in_service (job_task : Job -> Task) tsk :
  PropSPropRel (LS.proper_task_lock_in_service tcR job_task arrR lR tlR tsk)
    (I.Prosa_Classic_Model_Schedule_Uni_Limited_Schedule_proper_task_lock_in_service Task dT tcL Job dJ job_task arrL lL tlL tsk).
Proof.
  apply: ct_and; first exact (cab_LS_task_lock_in_service_le_task_cost tsk).
  exact (cab_LS_task_lock_in_service_bounds_job_lock_in_service job_task tsk).
Qed.

End LSDefs.

(* ------------------------------------------------------------------ *)
(** * Statements *)

Definition src_t2_le_arrival_plus_R (Task Job : eqType) : Prop :=
  forall task_cost : Task -> Time.time,
    ltac:(type_of_term (@AbstractRTA.t2_le_arrival_plus_R Task task_cost Job)).
Definition tgt_t2_le_arrival_plus_R (Task Job : eqType) : SProp :=
  forall task_cost : Task -> Lean.Nat,
    ltac:(type_of_term (I.Prosa_Classic_Model_Schedule_Uni_Limited_AbstractRTA_AbstractRta_AbstractRTA_t2_le_arrival_plus_R Task (ct_decidable_eq Task) task_cost Job (ct_decidable_eq Job))).
Theorem AbstractRTA_t2_le_arrival_plus_R_correspondence (Task Job : eqType) :
  PropSPropRel (src_t2_le_arrival_plus_R Task Job) (tgt_t2_le_arrival_plus_R Task Job).
Proof.
  unfold src_t2_le_arrival_plus_R, tgt_t2_le_arrival_plus_R.
  apply: cab_forall_par => tcR tcL Htc.
  apply: cab_forall_par => aR aL Ha. apply: cab_forall_par => cR cL Hc.
  apply: (cab_forall_sched Job) => sR sL Hs.
  apply: ct_forall_identity => tsk.
  apply: cab_forall_par => tlR tlL Htl.
  apply: (cab_forall_int Job) => iR iL Hi. apply: (cab_forall_wl Job) => wR wL Hw.
  apply: ct_forall_nat => RR RL HR.
  apply: ct_forall_identity => j.
  apply: ct_forall_nat => t1R t1L H1. apply: ct_forall_nat => t2R t2L H2.
  apply: ct_imp; first exact (cab_ARD_busy_interval Job sR sL Hs aR aL cR cL Ha Hc iR iL wR wL Hi Hw j _ _ H1 _ _ H2).
  apply: ct_forall_nat => AR AL HA. apply: ct_forall_nat => FR FL HF.
  apply: ct_imp; first exact (sub_nat_le_correspondence _ _ _ _ HA (ct_sub_rel _ _ _ _ (Ha j) H1)).
  apply: ct_imp; first exact (sub_nat_le_correspondence _ _ _ _ (sub_add_correspondence _ _ _ _ HF (ct_sub_rel _ _ _ _ (Htc tsk) (Htl tsk))) HR).
  apply: ct_imp; first exact (sub_nat_le_correspondence _ _ _ _ H2 (sub_add_correspondence _ _ _ _ H1 (sub_add_correspondence _ _ _ _ HA HF))).
  exact (sub_nat_le_correspondence _ _ _ _ H2 (sub_add_correspondence _ _ _ _ (Ha j) HR)).
Qed.

Definition src_job_completed_by_arrival_plus_R_1 (Task Job : eqType) : Prop :=
  forall task_cost : Task -> Time.time,
    ltac:(type_of_term (@AbstractRTA.job_completed_by_arrival_plus_R_1 Task task_cost Job)).
Definition tgt_job_completed_by_arrival_plus_R_1 (Task Job : eqType) : SProp :=
  forall task_cost : Task -> Lean.Nat,
    ltac:(type_of_term (I.Prosa_Classic_Model_Schedule_Uni_Limited_AbstractRTA_AbstractRta_AbstractRTA_job_completed_by_arrival_plus_R_1 Task (ct_decidable_eq Task) task_cost Job (ct_decidable_eq Job))).
Theorem AbstractRTA_job_completed_by_arrival_plus_R_1_correspondence (Task Job : eqType) :
  PropSPropRel (src_job_completed_by_arrival_plus_R_1 Task Job) (tgt_job_completed_by_arrival_plus_R_1 Task Job).
Proof.
  unfold src_job_completed_by_arrival_plus_R_1, tgt_job_completed_by_arrival_plus_R_1.
  apply: cab_forall_par => tcR tcL Htc.
  apply: cab_forall_par => aR aL Ha. apply: cab_forall_par => cR cL Hc.
  apply: (cab_forall_sched Job) => sR sL Hs.
  apply: ct_forall_identity => tsk.
  apply: cab_forall_par => tlR tlL Htl.
  apply: (cab_forall_int Job) => iR iL Hi. apply: (cab_forall_wl Job) => wR wL Hw.
  apply: ct_forall_nat => RR RL HR.
  apply: ct_forall_identity => j.
  apply: ct_forall_nat => t1R t1L H1. apply: ct_forall_nat => t2R t2L H2.
  apply: ct_imp; first exact (cab_ARD_busy_interval Job sR sL Hs aR aL cR cL Ha Hc iR iL wR wL Hi Hw j _ _ H1 _ _ H2).
  apply: ct_forall_nat => AR AL HA. apply: ct_forall_nat => FR FL HF.
  apply: ct_imp; first exact (sub_nat_le_correspondence _ _ _ _ HA (ct_sub_rel _ _ _ _ (Ha j) H1)).
  apply: ct_imp; first exact (sub_nat_le_correspondence _ _ _ _ (sub_add_correspondence _ _ _ _ HF (ct_sub_rel _ _ _ _ (Htc tsk) (Htl tsk))) HR).
  apply: ct_imp; first exact (sub_nat_le_correspondence _ _ _ _ H2 (sub_add_correspondence _ _ _ _ H1 (sub_add_correspondence _ _ _ _ HA HF))).
  exact (ct_bool_truth _ _ (cab_US_completed_by Job sR sL Hs cR cL Hc j _ _ (sub_add_correspondence _ _ _ _ (Ha j) HR))).

Qed.

Definition src_solution_for_A_exists' (Task Job : eqType) : Prop :=
  ltac:(type_of_term (@AbstractRTA.solution_for_A_exists' Task Job)).
Definition tgt_solution_for_A_exists' (Task Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Model_Schedule_Uni_Limited_AbstractRTA_AbstractRta_AbstractRTA_solution_for_A_exists' Task (ct_decidable_eq Task) Job (ct_decidable_eq Job))).
Theorem AbstractRTA_solution_for_A_exists'_correspondence (Task Job : eqType) :
  PropSPropRel (src_solution_for_A_exists' Task Job) (tgt_solution_for_A_exists' Task Job).
Proof.
  unfold src_solution_for_A_exists', tgt_solution_for_A_exists'.
  apply: cab_forall_par => aR aL Ha. apply: cab_forall_par => cR cL Hc.
  apply: ct_forall_identity => job_task.
  apply: (cab_forall_arr Job) => arrR arrL Harr.
  apply: (cab_forall_sched Job) => sR sL Hs.
  apply: ct_forall_identity => tsk.
  apply: cab_forall_par => tlR tlL Htl.
  apply: (cab_forall_int Job) => iR iL Hi. apply: (cab_forall_wl Job) => wR wL Hw.
  apply: ct_forall_nat => LR LL HL.
  apply: ct_imp; first exact (cab_ARD_busy_intervals_are_bounded_by Task Job sR sL Hs aR aL cR cL Ha Hc iR iL wR wL Hi Hw job_task arrR arrL Harr tsk LR LL HL).
  apply: (cab_forall_ibf Task) => fR fL Hf.
  apply: ct_forall_identity => j.
  apply: ct_imp; first exact (cab_arrives_in Job arrR arrL Harr j).
  apply: ct_imp; first exact (ct_eq_rel Task (job_task j) tsk).
  apply: ct_imp; first exact (ct_bool_truth _ _ (cab_J_job_cost_positive Job cR cL Hc j)).
  apply: ct_forall_nat => t1R t1L H1. apply: ct_forall_nat => t2R t2L H2.
  apply: ct_imp; first exact (cab_ARD_busy_interval Job sR sL Hs aR aL cR cL Ha Hc iR iL wR wL Hi Hw j _ _ H1 _ _ H2).
  apply: ct_forall_nat => AR AL HA. apply: ct_forall_nat => FR FL HF.
  apply: ct_imp; first exact (sub_nat_le_correspondence _ _ _ _ HA (ct_sub_rel _ _ _ _ (Ha j) H1)).
  apply: ct_imp; first exact (cab_equiv_nat _ _ (Hf tsk _ _ (ct_sub_rel _ _ _ _ (Ha j) H1)) _ _ (Hf tsk _ _ HA) _ _ HL).
  apply: ct_imp; first exact (sub_nat_eq_correspondence _ _ _ _ (sub_add_correspondence _ _ _ _ HA HF) (sub_add_correspondence _ _ _ _ (Htl tsk) (Hf tsk _ _ HA _ _ (sub_add_correspondence _ _ _ _ HA HF)))).
  apply: ct_imp; first exact (sub_nat_lt_correspondence _ _ _ _ (sub_add_correspondence _ _ _ _ H1 (sub_add_correspondence _ _ _ _ HA HF)) H2).
  apply: ct_imp; first exact (sub_nat_le_correspondence _ _ _ _ (ct_sub_rel _ _ _ _ (Ha j) H1) (sub_add_correspondence _ _ _ _ HA HF)).
  apply: ct_exists_nat => XR XL HX.
  apply: ct_and; first exact (sub_nat_eq_correspondence _ _ _ _ (sub_add_correspondence _ _ _ _ HA HF) (sub_add_correspondence _ _ _ _ (ct_sub_rel _ _ _ _ (Ha j) H1) HX)).
  apply: ct_and; first exact (sub_nat_le_correspondence _ _ _ _ HX HF).
  exact (sub_nat_eq_correspondence _ _ _ _ (sub_add_correspondence _ _ _ _ (ct_sub_rel _ _ _ _ (Ha j) H1) HX) (sub_add_correspondence _ _ _ _ (Htl tsk) (Hf tsk _ _ (ct_sub_rel _ _ _ _ (Ha j) H1) _ _ (sub_add_correspondence _ _ _ _ (ct_sub_rel _ _ _ _ (Ha j) H1) HX)))).
Qed.

Definition src_job_completed_by_arrival_plus_R_2 (Task Job : eqType) : Prop :=
  forall task_cost : Task -> Time.time,
    ltac:(type_of_term (@AbstractRTA.job_completed_by_arrival_plus_R_2 Task task_cost Job)).
Definition tgt_job_completed_by_arrival_plus_R_2 (Task Job : eqType) : SProp :=
  forall task_cost : Task -> Lean.Nat,
    ltac:(type_of_term (I.Prosa_Classic_Model_Schedule_Uni_Limited_AbstractRTA_AbstractRta_AbstractRTA_job_completed_by_arrival_plus_R_2 Task (ct_decidable_eq Task) task_cost Job (ct_decidable_eq Job))).
Theorem AbstractRTA_job_completed_by_arrival_plus_R_2_correspondence (Task Job : eqType) :
  PropSPropRel (src_job_completed_by_arrival_plus_R_2 Task Job) (tgt_job_completed_by_arrival_plus_R_2 Task Job).
Proof.
  unfold src_job_completed_by_arrival_plus_R_2, tgt_job_completed_by_arrival_plus_R_2.
  apply: cab_forall_par => tcR tcL Htc.
  apply: cab_forall_par => aR aL Ha. apply: cab_forall_par => cR cL Hc.
  apply: ct_forall_identity => job_task.
  apply: (cab_forall_arr Job) => arrR arrL Harr.
  apply: (cab_forall_sched Job) => sR sL Hs.
  apply: ct_imp; first exact (cab_US_jobs_must_arrive_to_execute Job sR sL Hs aR aL Ha).
  apply: ct_imp; first exact (cab_US_completed_jobs_dont_execute Job sR sL Hs cR cL Hc).
  apply: ct_imp; first exact (cab_J_cost_of_jobs_from_arrival_sequence_le_task_cost Task Job tcR tcL Htc cR cL Hc job_task arrR arrL Harr).
  apply: ct_forall_identity => tsk.
  apply: cab_forall_par => lR lL Hl.
  apply: cab_forall_par => tlR tlL Htl.
  apply: ct_imp; first exact (cab_LS_proper_job_lock_in_service Job cR cL Hc arrR arrL Harr lR lL Hl sR sL Hs).
  apply: ct_imp; first exact (cab_LS_proper_task_lock_in_service Task Job arrR arrL Harr lR lL Hl tcR tcL tlR tlL Htc Htl job_task tsk).
  apply: (cab_forall_int Job) => iR iL Hi. apply: (cab_forall_wl Job) => wR wL Hw.
  apply: ct_imp; first exact (cab_ARD_work_conserving Task Job sR sL Hs aR aL cR cL Ha Hc iR iL wR wL Hi Hw job_task arrR arrL Harr tsk).
  apply: ct_forall_nat => LR LL HL.
  apply: ct_imp; first exact (cab_ARD_busy_intervals_are_bounded_by Task Job sR sL Hs aR aL cR cL Ha Hc iR iL wR wL Hi Hw job_task arrR arrL Harr tsk LR LL HL).
  apply: (cab_forall_ibf Task) => fR fL Hf.
  apply: ct_imp; first exact (cab_ARD_job_interference_is_bounded_by Task Job sR sL Hs aR aL cR cL Ha Hc iR iL wR wL Hi Hw job_task arrR arrL Harr tsk fR fL (fun tsk aR' aL' Ha' xR xL Hx => Hf tsk aR' aL' Ha' xR xL Hx)).
  apply: ct_forall_nat => RR RL HR.
  apply: ct_forall_identity => j.
  apply: ct_imp; first exact (cab_arrives_in Job arrR arrL Harr j).
  apply: ct_imp; first exact (ct_eq_rel Task (job_task j) tsk).
  apply: ct_imp; first exact (ct_bool_truth _ _ (cab_J_job_cost_positive Job cR cL Hc j)).
  apply: ct_forall_nat => t1R t1L H1. apply: ct_forall_nat => t2R t2L H2.
  apply: ct_imp; first exact (cab_ARD_busy_interval Job sR sL Hs aR aL cR cL Ha Hc iR iL wR wL Hi Hw j _ _ H1 _ _ H2).
  apply: ct_forall_nat => AR AL HA. apply: ct_forall_nat => FR FL HF.
  apply: ct_imp; first exact (sub_nat_le_correspondence _ _ _ _ HA (ct_sub_rel _ _ _ _ (Ha j) H1)).
  apply: ct_imp; first exact (cab_equiv_nat _ _ (Hf tsk _ _ (ct_sub_rel _ _ _ _ (Ha j) H1)) _ _ (Hf tsk _ _ HA) _ _ HL).
  apply: ct_imp; first exact (sub_nat_eq_correspondence _ _ _ _ (sub_add_correspondence _ _ _ _ HA HF) (sub_add_correspondence _ _ _ _ (Htl tsk) (Hf tsk _ _ HA _ _ (sub_add_correspondence _ _ _ _ HA HF)))).
  apply: ct_imp; first exact (sub_nat_le_correspondence _ _ _ _ (sub_add_correspondence _ _ _ _ HF (ct_sub_rel _ _ _ _ (Htc tsk) (Htl tsk))) HR).
  apply: ct_imp; first exact (sub_nat_lt_correspondence _ _ _ _ (sub_add_correspondence _ _ _ _ H1 (sub_add_correspondence _ _ _ _ HA HF)) H2).
  apply: ct_imp; first exact (sub_nat_le_correspondence _ _ _ _ (ct_sub_rel _ _ _ _ (Ha j) H1) (sub_add_correspondence _ _ _ _ HA HF)).
  exact (ct_bool_truth _ _ (cab_US_completed_by Job sR sL Hs cR cL Hc j _ _ (sub_add_correspondence _ _ _ _ (Ha j) HR))).

Qed.

Definition src_relative_arrival_is_bounded (Task Job : eqType) : Prop :=
  ltac:(type_of_term (@AbstractRTA.relative_arrival_is_bounded Task Job)).
Definition tgt_relative_arrival_is_bounded (Task Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Model_Schedule_Uni_Limited_AbstractRTA_AbstractRta_AbstractRTA_relative_arrival_is_bounded Task (ct_decidable_eq Task) Job (ct_decidable_eq Job))).
Theorem AbstractRTA_relative_arrival_is_bounded_correspondence (Task Job : eqType) :
  PropSPropRel (src_relative_arrival_is_bounded Task Job) (tgt_relative_arrival_is_bounded Task Job).
Proof.
  unfold src_relative_arrival_is_bounded, tgt_relative_arrival_is_bounded.
  apply: cab_forall_par => aR aL Ha. apply: cab_forall_par => cR cL Hc.
  apply: ct_forall_identity => job_task.
  apply: (cab_forall_arr Job) => arrR arrL Harr.
  apply: (cab_forall_sched Job) => sR sL Hs.
  apply: ct_forall_identity => tsk.
  apply: (cab_forall_int Job) => iR iL Hi. apply: (cab_forall_wl Job) => wR wL Hw.
  apply: ct_forall_nat => LR LL HL.
  apply: ct_imp; first exact (cab_ARD_busy_intervals_are_bounded_by Task Job sR sL Hs aR aL cR cL Ha Hc iR iL wR wL Hi Hw job_task arrR arrL Harr tsk LR LL HL).
  apply: ct_forall_identity => j.
  apply: ct_imp; first exact (cab_arrives_in Job arrR arrL Harr j).
  apply: ct_imp; first exact (ct_eq_rel Task (job_task j) tsk).
  apply: ct_imp; first exact (ct_bool_truth _ _ (cab_J_job_cost_positive Job cR cL Hc j)).
  apply: ct_forall_nat => t1R t1L H1. apply: ct_forall_nat => t2R t2L H2.
  apply: ct_imp; first exact (cab_ARD_busy_interval Job sR sL Hs aR aL cR cL Ha Hc iR iL wR wL Hi Hw j _ _ H1 _ _ H2).
  exact (sub_nat_lt_correspondence _ _ _ _ (ct_sub_rel _ _ _ _ (Ha j) H1) HL).
Qed.

Definition src_service_of_job_ge_lock_in_service (Task Job : eqType) : Prop :=
  forall task_cost : Task -> Time.time,
    ltac:(type_of_term (@AbstractRTA.service_of_job_ge_lock_in_service Task task_cost Job)).
Definition tgt_service_of_job_ge_lock_in_service (Task Job : eqType) : SProp :=
  forall task_cost : Task -> Lean.Nat,
    ltac:(type_of_term (I.Prosa_Classic_Model_Schedule_Uni_Limited_AbstractRTA_AbstractRta_AbstractRTA_service_of_job_ge_lock_in_service Task (ct_decidable_eq Task) task_cost Job (ct_decidable_eq Job))).
Theorem AbstractRTA_service_of_job_ge_lock_in_service_correspondence (Task Job : eqType) :
  PropSPropRel (src_service_of_job_ge_lock_in_service Task Job) (tgt_service_of_job_ge_lock_in_service Task Job).
Proof.
  unfold src_service_of_job_ge_lock_in_service, tgt_service_of_job_ge_lock_in_service.
  apply: cab_forall_par => tcR tcL Htc.
  apply: cab_forall_par => aR aL Ha. apply: cab_forall_par => cR cL Hc.
  apply: ct_forall_identity => job_task.
  apply: (cab_forall_arr Job) => arrR arrL Harr.
  apply: (cab_forall_sched Job) => sR sL Hs.
  apply: ct_imp; first exact (cab_US_jobs_must_arrive_to_execute Job sR sL Hs aR aL Ha).
  apply: ct_forall_identity => tsk.
  apply: cab_forall_par => lR lL Hl.
  apply: cab_forall_par => tlR tlL Htl.
  apply: ct_imp; first exact (cab_LS_proper_job_lock_in_service Job cR cL Hc arrR arrL Harr lR lL Hl sR sL Hs).
  apply: ct_imp; first exact (cab_LS_proper_task_lock_in_service Task Job arrR arrL Harr lR lL Hl tcR tcL tlR tlL Htc Htl job_task tsk).
  apply: (cab_forall_int Job) => iR iL Hi. apply: (cab_forall_wl Job) => wR wL Hw.
  apply: ct_imp; first exact (cab_ARD_work_conserving Task Job sR sL Hs aR aL cR cL Ha Hc iR iL wR wL Hi Hw job_task arrR arrL Harr tsk).
  apply: ct_forall_nat => LR LL HL.
  apply: ct_imp; first exact (cab_ARD_busy_intervals_are_bounded_by Task Job sR sL Hs aR aL cR cL Ha Hc iR iL wR wL Hi Hw job_task arrR arrL Harr tsk LR LL HL).
  apply: (cab_forall_ibf Task) => fR fL Hf.
  apply: ct_imp; first exact (cab_ARD_job_interference_is_bounded_by Task Job sR sL Hs aR aL cR cL Ha Hc iR iL wR wL Hi Hw job_task arrR arrL Harr tsk fR fL (fun tsk aR' aL' Ha' xR xL Hx => Hf tsk aR' aL' Ha' xR xL Hx)).
  apply: ct_forall_identity => j.
  apply: ct_imp; first exact (cab_arrives_in Job arrR arrL Harr j).
  apply: ct_imp; first exact (ct_eq_rel Task (job_task j) tsk).
  apply: ct_imp; first exact (ct_bool_truth _ _ (cab_J_job_cost_positive Job cR cL Hc j)).
  apply: ct_forall_nat => t1R t1L H1. apply: ct_forall_nat => t2R t2L H2.
  apply: ct_imp; first exact (cab_ARD_busy_interval Job sR sL Hs aR aL cR cL Ha Hc iR iL wR wL Hi Hw j _ _ H1 _ _ H2).
  apply: ct_forall_nat => AR AL HA. apply: ct_forall_nat => FR FL HF.
  apply: ct_imp; first exact (cab_equiv_nat _ _ (Hf tsk _ _ (ct_sub_rel _ _ _ _ (Ha j) H1)) _ _ (Hf tsk _ _ HA) _ _ HL).
  apply: ct_imp; first exact (sub_nat_eq_correspondence _ _ _ _ (sub_add_correspondence _ _ _ _ HA HF) (sub_add_correspondence _ _ _ _ (Htl tsk) (Hf tsk _ _ HA _ _ (sub_add_correspondence _ _ _ _ HA HF)))).
  apply: ct_imp; first exact (sub_nat_lt_correspondence _ _ _ _ (sub_add_correspondence _ _ _ _ H1 (sub_add_correspondence _ _ _ _ HA HF)) H2).
  apply: ct_imp; first exact (sub_nat_lt_correspondence _ _ _ _ (sub_add_correspondence _ _ _ _ HA HF) (ct_sub_rel _ _ _ _ (Ha j) H1)).
  exact (sub_nat_le_correspondence _ _ _ _ (Hl j) (cab_US_service Job sR sL Hs j _ _ (sub_add_correspondence _ _ _ _ H1 (sub_add_correspondence _ _ _ _ HA HF)))).
Qed.

Definition src_relative_arrival_time_is_no_less_than_fixpoint (Task Job : eqType) : Prop :=
  forall task_cost : Task -> Time.time,
    ltac:(type_of_term (@AbstractRTA.relative_arrival_time_is_no_less_than_fixpoint Task task_cost Job)).
Definition tgt_relative_arrival_time_is_no_less_than_fixpoint (Task Job : eqType) : SProp :=
  forall task_cost : Task -> Lean.Nat,
    ltac:(type_of_term (I.Prosa_Classic_Model_Schedule_Uni_Limited_AbstractRTA_AbstractRta_AbstractRTA_relative_arrival_time_is_no_less_than_fixpoint Task (ct_decidable_eq Task) task_cost Job (ct_decidable_eq Job))).
Theorem AbstractRTA_relative_arrival_time_is_no_less_than_fixpoint_correspondence (Task Job : eqType) :
  PropSPropRel (src_relative_arrival_time_is_no_less_than_fixpoint Task Job) (tgt_relative_arrival_time_is_no_less_than_fixpoint Task Job).
Proof.
  unfold src_relative_arrival_time_is_no_less_than_fixpoint, tgt_relative_arrival_time_is_no_less_than_fixpoint.
  apply: cab_forall_par => tcR tcL Htc.
  apply: cab_forall_par => aR aL Ha. apply: cab_forall_par => cR cL Hc.
  apply: ct_forall_identity => job_task.
  apply: (cab_forall_arr Job) => arrR arrL Harr.
  apply: (cab_forall_sched Job) => sR sL Hs.
  apply: ct_imp; first exact (cab_US_jobs_must_arrive_to_execute Job sR sL Hs aR aL Ha).
  apply: ct_forall_identity => tsk.
  apply: cab_forall_par => lR lL Hl.
  apply: cab_forall_par => tlR tlL Htl.
  apply: ct_imp; first exact (cab_LS_proper_job_lock_in_service Job cR cL Hc arrR arrL Harr lR lL Hl sR sL Hs).
  apply: ct_imp; first exact (cab_LS_proper_task_lock_in_service Task Job arrR arrL Harr lR lL Hl tcR tcL tlR tlL Htc Htl job_task tsk).
  apply: (cab_forall_int Job) => iR iL Hi. apply: (cab_forall_wl Job) => wR wL Hw.
  apply: ct_imp; first exact (cab_ARD_work_conserving Task Job sR sL Hs aR aL cR cL Ha Hc iR iL wR wL Hi Hw job_task arrR arrL Harr tsk).
  apply: ct_forall_nat => LR LL HL.
  apply: ct_imp; first exact (cab_ARD_busy_intervals_are_bounded_by Task Job sR sL Hs aR aL cR cL Ha Hc iR iL wR wL Hi Hw job_task arrR arrL Harr tsk LR LL HL).
  apply: (cab_forall_ibf Task) => fR fL Hf.
  apply: ct_imp; first exact (cab_ARD_job_interference_is_bounded_by Task Job sR sL Hs aR aL cR cL Ha Hc iR iL wR wL Hi Hw job_task arrR arrL Harr tsk fR fL (fun tsk aR' aL' Ha' xR xL Hx => Hf tsk aR' aL' Ha' xR xL Hx)).
  apply: ct_forall_identity => j.
  apply: ct_imp; first exact (cab_arrives_in Job arrR arrL Harr j).
  apply: ct_imp; first exact (ct_eq_rel Task (job_task j) tsk).
  apply: ct_imp; first exact (ct_bool_truth _ _ (cab_J_job_cost_positive Job cR cL Hc j)).
  apply: ct_forall_nat => t1R t1L H1. apply: ct_forall_nat => t2R t2L H2.
  apply: ct_imp; first exact (cab_ARD_busy_interval Job sR sL Hs aR aL cR cL Ha Hc iR iL wR wL Hi Hw j _ _ H1 _ _ H2).
  apply: ct_forall_nat => AR AL HA. apply: ct_forall_nat => FR FL HF.
  apply: ct_imp; first exact (cab_equiv_nat _ _ (Hf tsk _ _ (ct_sub_rel _ _ _ _ (Ha j) H1)) _ _ (Hf tsk _ _ HA) _ _ HL).
  apply: ct_imp; first exact (sub_nat_eq_correspondence _ _ _ _ (sub_add_correspondence _ _ _ _ HA HF) (sub_add_correspondence _ _ _ _ (Htl tsk) (Hf tsk _ _ HA _ _ (sub_add_correspondence _ _ _ _ HA HF)))).
  apply: ct_imp; first exact (sub_nat_lt_correspondence _ _ _ _ (sub_add_correspondence _ _ _ _ H1 (sub_add_correspondence _ _ _ _ HA HF)) H2).
  apply: ct_imp; first exact (sub_nat_lt_correspondence _ _ _ _ (sub_add_correspondence _ _ _ _ HA HF) (ct_sub_rel _ _ _ _ (Ha j) H1)).
  exact cab_false_rel.
Qed.

Definition src_uniprocessor_response_time_bound (Task Job : eqType) : Prop :=
  forall task_cost : Task -> Time.time,
    ltac:(type_of_term (@AbstractRTA.uniprocessor_response_time_bound Task task_cost Job)).
Definition tgt_uniprocessor_response_time_bound (Task Job : eqType) : SProp :=
  forall task_cost : Task -> Lean.Nat,
    ltac:(type_of_term (I.Prosa_Classic_Model_Schedule_Uni_Limited_AbstractRTA_AbstractRta_AbstractRTA_uniprocessor_response_time_bound Task (ct_decidable_eq Task) task_cost Job (ct_decidable_eq Job))).
Theorem AbstractRTA_uniprocessor_response_time_bound_correspondence (Task Job : eqType) :
  PropSPropRel (src_uniprocessor_response_time_bound Task Job) (tgt_uniprocessor_response_time_bound Task Job).
Proof.
  unfold src_uniprocessor_response_time_bound, tgt_uniprocessor_response_time_bound.
  apply: cab_forall_par => tcR tcL Htc.
  apply: cab_forall_par => aR aL Ha. apply: cab_forall_par => cR cL Hc.
  apply: ct_forall_identity => job_task.
  apply: (cab_forall_arr Job) => arrR arrL Harr.
  apply: (cab_forall_sched Job) => sR sL Hs.
  apply: ct_imp; first exact (cab_US_jobs_must_arrive_to_execute Job sR sL Hs aR aL Ha).
  apply: ct_imp; first exact (cab_US_completed_jobs_dont_execute Job sR sL Hs cR cL Hc).
  apply: ct_imp; first exact (cab_J_cost_of_jobs_from_arrival_sequence_le_task_cost Task Job tcR tcL Htc cR cL Hc job_task arrR arrL Harr).
  apply: ct_forall_identity => tsk.
  apply: cab_forall_par => lR lL Hl.
  apply: cab_forall_par => tlR tlL Htl.
  apply: ct_imp; first exact (cab_LS_proper_job_lock_in_service Job cR cL Hc arrR arrL Harr lR lL Hl sR sL Hs).
  apply: ct_imp; first exact (cab_LS_proper_task_lock_in_service Task Job arrR arrL Harr lR lL Hl tcR tcL tlR tlL Htc Htl job_task tsk).
  apply: (cab_forall_int Job) => iR iL Hi. apply: (cab_forall_wl Job) => wR wL Hw.
  apply: ct_imp; first exact (cab_ARD_work_conserving Task Job sR sL Hs aR aL cR cL Ha Hc iR iL wR wL Hi Hw job_task arrR arrL Harr tsk).
  apply: ct_forall_nat => LR LL HL.
  apply: ct_imp; first exact (cab_ARD_busy_intervals_are_bounded_by Task Job sR sL Hs aR aL cR cL Ha Hc iR iL wR wL Hi Hw job_task arrR arrL Harr tsk LR LL HL).
  apply: (cab_forall_ibf Task) => fR fL Hf.
  apply: ct_imp; first exact (cab_ARD_job_interference_is_bounded_by Task Job sR sL Hs aR aL cR cL Ha Hc iR iL wR wL Hi Hw job_task arrR arrL Harr tsk fR fL (fun tsk aR' aL' Ha' xR xL Hx => Hf tsk aR' aL' Ha' xR xL Hx)).
  apply: ct_forall_nat => RR RL HR.
  apply: ct_imp.
  { apply: ct_forall_nat => AR AL HA.
    apply: ct_imp; first exact (cab_RS_is_in_search_space Task tsk _ _ HL _ _ Hf _ _ HA).
    apply: ct_exists_nat => FR FL HF.
    apply: ct_and; first exact (sub_nat_eq_correspondence _ _ _ _ (sub_add_correspondence _ _ _ _ HA HF) (sub_add_correspondence _ _ _ _ (Htl tsk) (Hf tsk _ _ HA _ _ (sub_add_correspondence _ _ _ _ HA HF)))).
    exact (sub_nat_le_correspondence _ _ _ _ (sub_add_correspondence _ _ _ _ HF (ct_sub_rel _ _ _ _ (Htc tsk) (Htl tsk))) HR). }
  exact (cab_RT_is_response_time_bound_of_task Task Job sR sL Hs aR aL Ha cR cL Hc job_task arrR arrL Harr tsk RR RL HR).
Qed.
