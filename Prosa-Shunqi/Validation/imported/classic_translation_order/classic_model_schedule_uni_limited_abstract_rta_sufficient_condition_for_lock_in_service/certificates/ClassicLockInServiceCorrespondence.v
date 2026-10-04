From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq fintype bigop.
From prosa Require Import classic.model.time classic.model.arrival.basic.arrival_sequence classic.model.arrival.basic.job classic.model.schedule.uni.schedule classic.model.schedule.uni.limited.schedule classic.model.schedule.uni.limited.abstract_RTA.definitions classic.model.schedule.uni.limited.abstract_RTA.sufficient_condition_for_lock_in_service.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedClassicLockInService.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence ClassicLockInServiceBase ClassicLockInServiceList.



Module I := ImportedClassicLockInService.
Local Open Scope nat_scope.

(** Certificates for [classic/model/schedule/uni/limited/abstract_RTA/sufficient_condition_for_lock_in_service.v] (ProsaBuddy classic, commit f692cb7).

    Inputs: the job and task types are [eqType]s, identified, with the Lean [DecidableEq] instances given by the eqTypes'
    decision procedures ([ct_decidable_eq]); [job_task] identified; times by [SubNatRel]; job parameters pointwise
    through [SubNatRel]; arrival sequences pointwise on related times; interference predicates and interfering
    workloads pointwise on related times; uniprocessor schedules pointwise through the option map; all with two-way
    totals.  The abstract-RTA definitions ([busy_interval], [work_conserving], [cumul_interference]) and the
    limited-preemption lock-in-service notions as in the accepted classic certificates (re-bound below).

    Statements: the source side is the exact elaborated type of the pinned lemma (via [type of]; the source proof is not
    used); every input is quantified and covered in both directions. *)

Ltac type_of_term t := let T := type of t in exact T.
Notation cid := (fun z => z).

(* ------------------------------------------------------------------ *)
(** * Helpers (re-bound to this export from the accepted classic certificates) *)

(** Base definitions (as in the accepted classic base library), provided here when this export's library lacks them. *)

(* ------------------------------------------------------------------ *)
(** * Generic covers and helpers *)

Lemma clk_forall_cover (A B : Type) (Rel : A -> B -> SProp) (toB : A -> B) (toA : B -> A)
    (HB : forall a, Rel a (toB a)) (HA : forall b, Rel (toA b) b) (PR : A -> Prop) (PL : B -> SProp) :
  (forall a b, Rel a b -> PropSPropRel (PR a) (PL b)) -> PropSPropRel (forall a, PR a) (forall b, PL b).
Proof.
  intro H. apply prop_sprop_rel_intro.
  - intros HR b. exact (prop_to_sprop _ _ (H _ _ (HA b)) (HR _)).
  - intro HL. apply strictly_inhabits. intro a. exact (sprop_to_prop _ _ (H _ _ (HB a)) (HL _)).
Qed.

Lemma clk_false_rel : PropSPropRel Logic.False I.False.
Proof.
  apply prop_sprop_rel_intro.
  - exact ct_coq_false_to_target.
  - exact ct_target_false_to_strict.
Qed.

Lemma clk_mem (T : eqType) x s sL : ClListRel cid s sL ->
  PropSPropRel (x \in s) (I.Membership_mem T (I.List T) (I.List_instMembership T) sL x).
Proof. exact (cl_mem_rel_list T T cid cid (fun _ => Logic.eq_refl _) x s sL). Qed.

Lemma clk_unmap_rel (T : Type) (l : I.List T) : ClListRel cid (cl_unmap cid l) l.
Proof. apply: coq_eq_to_imported_eq. exact (cl_map_unmap cid cid (fun _ => Logic.eq_refl _) l). Qed.

Lemma clk_cl_map_inj (T : Type) (s1 s2 : seq T) : Logic.eq (cl_map cid s1) (cl_map cid s2) -> Logic.eq s1 s2.
Proof.
  intro E. rewrite -(cl_unmap_map cid cid (fun _ => Logic.eq_refl _) s1) -(cl_unmap_map cid cid (fun _ => Logic.eq_refl _) s2).
  by rewrite E.
Qed.

Lemma clk_succ_rel nR nL : SubNatRel nR nL ->
  SubNatRel nR.+1 (I.HAdd_hAdd_inst7 Lean.Nat Lean.Nat Lean.Nat (I.instHAdd_inst1 Lean.Nat I.instAddNat) nL
                     (I.OfNat_ofNat_inst1 Lean.Nat 1 (I.instOfNatNat 1))).
Proof. intro Hn. exact (sub_imported_eq_congr Lean.Nat_succ _ _ Hn). Qed.

(* ------------------------------------------------------------------ *)
(** * Big concatenation over a half-open interval (as in the accepted arrival_sequence certificate) *)

Lemma clk_forall_list (T : Type) (PR : seq T -> Prop) (PL : I.List T -> SProp) :
  (forall sR sL, ClListRel (B := T) cid sR sL -> PropSPropRel (PR sR) (PL sL)) -> PropSPropRel (forall s, PR s) (forall s, PL s).
Proof.
  exact (clk_forall_cover _ _ (fun sR sL => ClListRel (B := T) cid sR sL) (cl_map cid) (cl_unmap cid)
           (fun s => @Lean.eq_refl _ _) (fun l => clk_unmap_rel T l) PR PL).
Qed.

Definition ClkParRel (T : Type) (pR : T -> nat) (pL : T -> Lean.Nat) : SProp := forall x, SubNatRel (pR x) (pL x).

Lemma clk_forall_par (T : Type) (PR : (T -> nat) -> Prop) (PL : (T -> Lean.Nat) -> SProp) :
  (forall pR pL, ClkParRel T pR pL -> PropSPropRel (PR pR) (PL pL)) -> PropSPropRel (forall p, PR p) (forall p, PL p).
Proof.
  exact (clk_forall_cover _ _ (ClkParRel T) (fun pR j => sub_nat_to_imported (pR j)) (fun pL j => sub_nat_to_rocq (pL j))
           (fun pR j => sub_nat_rel_canonical (pR j)) (fun pL j => sub_nat_rel_surjective (pL j)) PR PL).
Qed.

Fixpoint clk_natl (s : seq nat) : I.List_inst1 Lean.Nat :=
  match s with [::] => I.List_nil_inst1 _ | x :: s' => I.List_cons_inst1 _ (sub_nat_to_imported x) (clk_natl s') end.

Definition clk_one : Lean.Nat := I.OfNat_ofNat_inst1 Lean.Nat 1 (I.instOfNatNat 1).

Lemma clk_iota_range : forall n s,
  Logic.eq (I.List_range' (sub_nat_to_imported s) (sub_nat_to_imported n) clk_one) (clk_natl (iota s n)).
Proof.
  elim => [|n IH] s; first reflexivity.
  change (Logic.eq (I.List_cons_inst1 _ (sub_nat_to_imported s)
      (I.List_range' (sub_nat_to_imported (S s)) (sub_nat_to_imported n) clk_one))
    (I.List_cons_inst1 _ (sub_nat_to_imported s) (clk_natl (iota (S s) n)))).
  by rewrite IH.
Qed.

Lemma clk_cl_map_comp {A B C : Type} (f : A -> B) (g : B -> C) : forall s : seq A,
  Logic.eq (cl_map (fun x => g (f x)) s) (cl_map g (map f s)).
Proof. elim => [|x s IH] //=. by rewrite IH. Qed.

Lemma clk_cl_map_ext {A B : Type} (f g : A -> B) (H : forall x, Logic.eq (f x) (g x)) : forall s : seq A,
  Logic.eq (cl_map f s) (cl_map g s).
Proof. elim => [|x s IH] //=. by rewrite H IH. Qed.

Lemma clk_big_seq {A : Type} (F : nat -> seq A) : forall s : seq nat,
  Logic.eq (\big[cat/[::]]_(i <- s) F i) (flatten (map F s)).
Proof. elim => [|x s IH]; first by rewrite big_nil. by rewrite big_cons IH. Qed.

Definition ClkFamRel (A : Type) (fR : nat -> seq A) (fL : Lean.Nat -> I.List A) : SProp :=
  forall nR nL, SubNatRel nR nL -> ClListRel cid (fR nR) (fL nL).

(* ------------------------------------------------------------------ *)
(** * Arrival sequences and parameters *)

Section Rel.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).
Notation LArr := (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrival_sequence Job dJ).

Definition ClkArrRel (aR : ArrivalSequence.arrival_sequence Job) (aL : LArr) : SProp :=
  forall tR tL, SubNatRel tR tL -> ClListRel cid (aR tR) (aL tL).

Definition clk_arr_to_target (aR : ArrivalSequence.arrival_sequence Job) : LArr :=
  fun tL => cl_map cid (aR (sub_nat_to_rocq tL)).

Definition clk_arr_to_source (aL : LArr) : ArrivalSequence.arrival_sequence Job :=
  fun tR => cl_unmap cid (aL (sub_nat_to_imported tR)).

Lemma clk_arr_canonical aR : ClkArrRel aR (clk_arr_to_target aR).
Proof.
  intros tR tL Ht. have E := cl_nat_logic _ _ Ht. subst tL.
  apply: coq_eq_to_imported_eq. rewrite /clk_arr_to_target sub_nat_rocq_roundtrip. reflexivity.
Qed.

Lemma clk_arr_surjective aL : ClkArrRel (clk_arr_to_source aL) aL.
Proof.
  intros tR tL Ht. have E := cl_nat_logic _ _ Ht. subst tL.
  apply: coq_eq_to_imported_eq. exact (cl_map_unmap cid cid (fun _ => Logic.eq_refl _) _).
Qed.

Lemma clk_forall_arr (PR : ArrivalSequence.arrival_sequence Job -> Prop) (PL : LArr -> SProp) :
  (forall aR aL, ClkArrRel aR aL -> PropSPropRel (PR aR) (PL aL)) -> PropSPropRel (forall a, PR a) (forall a, PL a).
Proof. exact (clk_forall_cover _ _ ClkArrRel clk_arr_to_target clk_arr_to_source clk_arr_canonical clk_arr_surjective PR PL). Qed.

End Rel.

(** The imported [ArrivalSequence] definitions this file's statements mention, related on related inputs. *)
Section ArrivalDefs.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).

Lemma clk_arrives_in aR aL (Ha : ClkArrRel Job aR aL) j :
  PropSPropRel (ArrivalSequence.arrives_in aR j)
    (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrives_in Job dJ aL j).
Proof. apply: ct_exists_nat => tR tL Ht. exact (clk_mem Job j _ _ (Ha tR tL Ht)). Qed.

End ArrivalDefs.

Section ArrivalDefs2.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).

Lemma clk_arrived_before pR pL (Hp : ClkParRel Job pR pL) j tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (ArrivalSequence.arrived_before pR j tR)
    (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrived_before Job dJ pL j tL).
Proof. exact (ct_decide_lt _ _ _ _ (Hp j) Ht). Qed.

End ArrivalDefs2.

Fixpoint clk_snatl (s : seq nat) : I.List_inst1 Lean.Nat :=
  match s with [::] => I.List_nil_inst1 _ | x :: s' => I.List_cons_inst1 _ (sub_nat_to_imported x) (clk_snatl s') end.

Lemma clk_siota_range : forall n s,
  Logic.eq (I.List_range' (sub_nat_to_imported s) (sub_nat_to_imported n) (Lean.Nat_succ Lean.Nat_zero)) (clk_snatl (iota s n)).
Proof.
  elim => [|n IH] s; first reflexivity.
  change (Logic.eq (I.List_cons_inst1 _ (sub_nat_to_imported s)
      (I.List_range' (sub_nat_to_imported (S s)) (sub_nat_to_imported n) (Lean.Nat_succ Lean.Nat_zero)))
    (I.List_cons_inst1 _ (sub_nat_to_imported s) (clk_snatl (iota (S s) n)))).
  by rewrite IH.
Qed.

Lemma clk_foldr_add (f : Lean.Nat -> Lean.Nat) (g : nat -> nat) (Hf : forall k, Logic.eq (f (sub_nat_to_imported k)) (sub_nat_to_imported (g k))) :
  forall s, Logic.eq (I.List_foldr_inst3 Lean.Nat Lean.Nat Lean.Nat_add Lean.Nat_zero (I.List_map_inst3 Lean.Nat Lean.Nat f (clk_snatl s)))
                     (sub_nat_to_imported (foldr addn 0 (map g s))).
Proof.
  elim => [|k s IH] //=.
  change (Logic.eq (Lean.Nat_add (f (sub_nat_to_imported k))
            (I.List_foldr_inst3 Lean.Nat Lean.Nat Lean.Nat_add Lean.Nat_zero (I.List_map_inst3 Lean.Nat Lean.Nat f (clk_snatl s))))
         (sub_nat_to_imported (g k + foldr addn 0 (map g s)))).
  rewrite IH Hf. exact (imported_eq_to_coq_eq _ _ (sub_add_canonical _ _)).
Qed.

Lemma clk_big_fold (xs : seq nat) (F : nat -> nat) : Logic.eq (\sum_(i <- xs) F i) (foldr addn 0 (map F xs)).
Proof. elim: xs => [|x xs IH]; first by rewrite big_nil. by rewrite big_cons IH. Qed.

Definition ClkFunRel (FR : nat -> nat) (FL : Lean.Nat -> Lean.Nat) : SProp :=
  forall kR kL, SubNatRel kR kL -> SubNatRel (FR kR) (FL kL).

Lemma clk_fun_canonical FR FL (HF : ClkFunRel FR FL) k : Logic.eq (FL (sub_nat_to_imported k)) (sub_nat_to_imported (FR k)).
Proof. exact (cl_nat_logic _ _ (HF _ _ (sub_nat_rel_canonical k))). Qed.

Lemma clk_nat_sub_canonical (a b : nat) :
  Logic.eq (I.Nat_sub (sub_nat_to_imported a) (sub_nat_to_imported b)) (sub_nat_to_imported (a - b)).
Proof.
  elim: b => [|b IH]; first by rewrite subn0.
  change (Logic.eq (I.Nat_pred (I.Nat_sub (sub_nat_to_imported a) (sub_nat_to_imported b))) (sub_nat_to_imported (a - b.+1))).
  rewrite IH subnS. case: (a - b) => [|k]; reflexivity.
Qed.

Lemma clk_ico mR mL nR nL FR FL (Hm : SubNatRel mR mL) (Hn : SubNatRel nR nL) (HF : ClkFunRel FR FL) :
  SubNatRel (\sum_(mR <= i < nR) FR i)
    (I.List_foldr_inst3 Lean.Nat Lean.Nat Lean.Nat_add Lean.Nat_zero
       (I.List_map_inst3 Lean.Nat Lean.Nat FL (I.List_range' mL (I.Nat_sub nL mL) (Lean.Nat_succ Lean.Nat_zero)))).
Proof.
  rewrite (cl_nat_logic _ _ Hm) (cl_nat_logic _ _ Hn).
  have -> : Logic.eq (I.Nat_sub (sub_nat_to_imported nR) (sub_nat_to_imported mR)) (sub_nat_to_imported (nR - mR))
    := clk_nat_sub_canonical nR mR.
  rewrite clk_siota_range.
  apply: coq_eq_to_imported_eq. apply: Logic.eq_sym. rewrite (clk_foldr_add FL FR (clk_fun_canonical FR FL HF)).
  by rewrite clk_big_fold.
Qed.

(* ------------------------------------------------------------------ *)
(** * Options and uniprocessor schedules *)

(** Transport along the target equality (definitional UIP), as in the accepted global schedule certificate. *)
Definition clk_tr {A : Type} {x y : A} (E : Lean.eq x y) (P : A -> Type) (h : P x) : P y :=
  match E in Lean.eq _ z return P z with Lean.eq_refl => h end.

Definition clk_trs {A : Type} {x y : A} (E : Lean.eq x y) (P : A -> SProp) (h : P x) : P y :=
  match E in Lean.eq _ z return P z with Lean.eq_refl => h end.

Lemma clk_opt_inj (A : Type) (o1 o2 : option A) : Logic.eq (cl_opt o1) (cl_opt o2) -> Logic.eq o1 o2.
Proof. intro E. by rewrite -(cl_unopt_opt o1) -(cl_unopt_opt o2) E. Qed.

Lemma clk_opt_eqb_rel (A : eqType) (o1 o2 : option A) :
  PropSPropRel (is_true (o1 == o2)) (Lean.eq (cl_opt o1) (cl_opt o2)).
Proof.
  apply prop_sprop_rel_intro.
  - move=> /eqP E. rewrite E. exact (@Lean.eq_refl _ _).
  - intro E. apply strictly_inhabits. apply/eqP. exact (clk_opt_inj A o1 o2 (imported_eq_to_coq_eq _ _ E)).
Qed.

Section Sched.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).
Notation LSched := (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job dJ).

Definition ClkSchedRel (sR : UniprocessorSchedule.schedule Job) (sL : LSched) : SProp :=
  forall tR tL, SubNatRel tR tL -> Lean.eq (cl_opt (sR tR)) (sL tL).

Definition clk_sched_to_target (sR : UniprocessorSchedule.schedule Job) : LSched := fun tL => cl_opt (sR (sub_nat_to_rocq tL)).
Definition clk_sched_to_source (sL : LSched) : UniprocessorSchedule.schedule Job := fun tR => cl_unopt (sL (sub_nat_to_imported tR)).

Lemma clk_sched_canonical sR : ClkSchedRel sR (clk_sched_to_target sR).
Proof. intros tR tL Ht. apply: coq_eq_to_imported_eq. by rewrite /clk_sched_to_target (cl_nat_input _ _ Ht). Qed.

Lemma clk_sched_surjective sL : ClkSchedRel (clk_sched_to_source sL) sL.
Proof.
  intros tR tL Ht. apply: coq_eq_to_imported_eq. rewrite /clk_sched_to_source cl_opt_unopt.
  by rewrite (cl_nat_logic _ _ Ht).
Qed.

Lemma clk_forall_sched (PR : UniprocessorSchedule.schedule Job -> Prop) (PL : LSched -> SProp) :
  (forall sR sL, ClkSchedRel sR sL -> PropSPropRel (PR sR) (PL sL)) -> PropSPropRel (forall s, PR s) (forall s, PL s).
Proof. exact (clk_forall_cover _ _ ClkSchedRel clk_sched_to_target clk_sched_to_source clk_sched_canonical clk_sched_surjective PR PL). Qed.

End Sched.

(* ------------------------------------------------------------------ *)
(** * Definitions *)

Lemma clk_US_schedule (Job : eqType) :
  And (forall sR : UniprocessorSchedule.schedule Job, ClkSchedRel Job sR (clk_sched_to_target Job sR))
      (forall sL : I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job (ct_decidable_eq Job), ClkSchedRel Job (clk_sched_to_source Job sL) sL).
Proof. exact (And_intro _ _ (clk_sched_canonical Job) (clk_sched_surjective Job)). Qed.

Section USchedDefs.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).
Variables (sR : UniprocessorSchedule.schedule Job) (sL : I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job dJ).
Hypothesis Hs : ClkSchedRel Job sR sL.

Lemma clk_US_scheduled_at j tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (UniprocessorSchedule.scheduled_at sR j tR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_scheduled_at Job dJ sL j tL).
Proof.
  apply: ct_decide_bool.
  exact (clk_tr (Hs tR tL Ht) (fun z => PropSPropRel (sR tR == Some j) (Lean.eq z (cl_opt (Some j))))
           (clk_opt_eqb_rel Job (sR tR) (Some j))).
Qed.

Lemma clk_US_service_at j tR tL (Ht : SubNatRel tR tL) :
  SubNatRel (UniprocessorSchedule.service_at sR j tR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_service_at Job dJ sL j tL).
Proof. exact (ct_bool_to_nat _ _ (clk_US_scheduled_at j tR tL Ht)). Qed.

Lemma clk_service_at_fun j : ClkFunRel (fun t => UniprocessorSchedule.service_at sR j t) (fun t => I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_service_at Job dJ sL j t).
Proof. intros kR kL Hk. exact (clk_US_service_at j kR kL Hk). Qed.

Lemma clk_US_service_during j t1R t1L (H1 : SubNatRel t1R t1L) t2R t2L (H2 : SubNatRel t2R t2L) :
  SubNatRel (UniprocessorSchedule.service_during sR j t1R t2R) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_service_during Job dJ sL j t1L t2L).
Proof. exact (clk_ico _ _ _ _ _ _ H1 H2 (clk_service_at_fun j)). Qed.

Lemma clk_US_service j tR tL (Ht : SubNatRel tR tL) :
  SubNatRel (UniprocessorSchedule.service sR j tR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_service Job dJ sL j tL).
Proof. exact (clk_US_service_during j 0 _ (sub_nat_rel_canonical 0) tR tL Ht). Qed.

Lemma clk_US_completed_by cR cL (Hc : ClkParRel Job cR cL) j tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (UniprocessorSchedule.completed_by cR sR j tR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_completed_by Job dJ cL sL j tL).
Proof. exact (ct_decide_le _ _ _ _ (Hc j) (clk_US_service j tR tL Ht)). Qed.

Lemma clk_US_pending_earlier_and_at aR aL (Ha : ClkParRel Job aR aL) cR cL (Hc : ClkParRel Job cR cL) j
    tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (UniprocessorSchedule.pending_earlier_and_at aR cR sR j tR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_pending_earlier_and_at Job dJ aL cL sL j tL).
Proof.
  exact (ct_bool_and _ _ _ _ (clk_arrived_before Job aR aL Ha j tR tL Ht)
           (ct_bool_not _ _ (clk_US_completed_by cR cL Hc j tR tL Ht))).
Qed.

Lemma clk_US_completed_jobs_dont_execute cR cL (Hc : ClkParRel Job cR cL) :
  PropSPropRel (UniprocessorSchedule.completed_jobs_dont_execute cR sR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_completed_jobs_dont_execute Job dJ cL sL).
Proof.
  apply: ct_forall_identity => j. apply: ct_forall_nat => tR tL Ht.
  exact (sub_nat_le_correspondence _ _ _ _ (clk_US_service j tR tL Ht) (Hc j)).
Qed.

End USchedDefs.

(** The imported [Job] definitions (as in the accepted classic job certificate). *)
Section JobDefs.
Notation c0 := (sub_nat_rel_canonical 0).
Variables (Task Job : eqType).
Notation dT := (ct_decidable_eq Task).
Notation dJ := (ct_decidable_eq Job).

Lemma clk_J_job_cost_positive cR cL (Hc : ClkParRel Job cR cL) j :
  CtBoolRel (Job.job_cost_positive cR j) (I.Prosa_Classic_Model_Arrival_Basic_Job_Job_job_cost_positive Job dJ cL j).
Proof. exact (ct_decide_lt _ _ _ _ c0 (Hc j)). Qed.

End JobDefs.

Lemma clk_iff (P Q : Prop) (PL QL : SProp) :
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

Definition ClkIntRel (iR : Job -> nat -> bool) (iL : Job -> Lean.Nat -> I.Bool) : SProp :=
  forall j tR tL, SubNatRel tR tL -> CtBoolRel (iR j tR) (iL j tL).

Lemma clk_int_canonical iR : ClkIntRel iR (fun j tL => ct_b2l (iR j (sub_nat_to_rocq tL))).
Proof. intros j tR tL Ht. have E := cl_nat_logic _ _ Ht. subst tL. rewrite sub_nat_rocq_roundtrip. exact (ct_bool_canonical _). Qed.

Lemma clk_int_surjective iL : ClkIntRel (fun j tR => ct_l2b (iL j (sub_nat_to_imported tR))) iL.
Proof. intros j tR tL Ht. have E := cl_nat_logic _ _ Ht. subst tL. exact (ct_bool_surjective _). Qed.

Lemma clk_forall_int (PR : (Job -> nat -> bool) -> Prop) (PL : (Job -> Lean.Nat -> I.Bool) -> SProp) :
  (forall iR iL, ClkIntRel iR iL -> PropSPropRel (PR iR) (PL iL)) -> PropSPropRel (forall i, PR i) (forall i, PL i).
Proof. exact (clk_forall_cover _ _ ClkIntRel _ _ clk_int_canonical clk_int_surjective PR PL). Qed.

Definition ClkWlRel (wR : Job -> nat -> nat) (wL : Job -> Lean.Nat -> Lean.Nat) : SProp :=
  forall j tR tL, SubNatRel tR tL -> SubNatRel (wR j tR) (wL j tL).

Lemma clk_wl_canonical wR : ClkWlRel wR (fun j tL => sub_nat_to_imported (wR j (sub_nat_to_rocq tL))).
Proof. intros j tR tL Ht. have E := cl_nat_logic _ _ Ht. subst tL. rewrite sub_nat_rocq_roundtrip. exact (sub_nat_rel_canonical _). Qed.

Lemma clk_wl_surjective wL : ClkWlRel (fun j tR => sub_nat_to_rocq (wL j (sub_nat_to_imported tR))) wL.
Proof. intros j tR tL Ht. have E := cl_nat_logic _ _ Ht. subst tL. exact (sub_nat_rel_surjective _). Qed.

Lemma clk_forall_wl (PR : (Job -> nat -> nat) -> Prop) (PL : (Job -> Lean.Nat -> Lean.Nat) -> SProp) :
  (forall wR wL, ClkWlRel wR wL -> PropSPropRel (PR wR) (PL wL)) -> PropSPropRel (forall w, PR w) (forall w, PL w).
Proof. exact (clk_forall_cover _ _ ClkWlRel _ _ clk_wl_canonical clk_wl_surjective PR PL). Qed.

End IRel.

(* ------------------------------------------------------------------ *)
(** * Definitions *)

Section Defs.
Variables (Task Job : eqType).
Notation dT := (ct_decidable_eq Task).
Notation dJ := (ct_decidable_eq Job).

Lemma clk_ARD_cumul_interference iR iL (Hi : ClkIntRel Job iR iL) j t1R t1L (H1 : SubNatRel t1R t1L)
    t2R t2L (H2 : SubNatRel t2R t2L) :
  SubNatRel (AbstractRTADefinitions.cumul_interference iR j t1R t2R) (I.Prosa_Classic_Model_Schedule_Uni_Limited_AbstractRTA_Definitions_AbstractRTADefinitions_cumul_interference Job dJ iL j t1L t2L).
Proof. exact (clk_ico _ _ _ _ _ _ H1 H2 (fun kR kL Hk => ct_bool_to_nat _ _ (Hi j kR kL Hk))). Qed.

Lemma clk_ARD_cumul_interfering_workload wR wL (Hw : ClkWlRel Job wR wL) j t1R t1L (H1 : SubNatRel t1R t1L)
    t2R t2L (H2 : SubNatRel t2R t2L) :
  SubNatRel (AbstractRTADefinitions.cumul_interfering_workload wR j t1R t2R) (I.Prosa_Classic_Model_Schedule_Uni_Limited_AbstractRTA_Definitions_AbstractRTADefinitions_cumul_interfering_workload Job dJ wL j t1L t2L).
Proof. exact (clk_ico _ _ _ _ _ _ H1 H2 (fun kR kL Hk => Hw j kR kL Hk)). Qed.

Notation CI := clk_ARD_cumul_interference.
Notation CW := clk_ARD_cumul_interfering_workload.

Section Sched.
Variables (sR : UniprocessorSchedule.schedule Job) (sL : I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job dJ).
Hypothesis Hs : ClkSchedRel Job sR sL.
Variables (aR : Job -> nat) (aL : Job -> Lean.Nat) (cR : Job -> nat) (cL : Job -> Lean.Nat).
Hypotheses (Ha : ClkParRel Job aR aL) (Hc : ClkParRel Job cR cL).
Variables (iR : Job -> nat -> bool) (iL : Job -> Lean.Nat -> I.Bool) (wR : Job -> nat -> nat) (wL : Job -> Lean.Nat -> Lean.Nat).
Hypotheses (Hi : ClkIntRel Job iR iL) (Hw : ClkWlRel Job wR wL).

Lemma clk_ARD_quiet_time j tR tL (Ht : SubNatRel tR tL) :
  PropSPropRel (AbstractRTADefinitions.quiet_time aR cR sR iR wR j tR) (I.Prosa_Classic_Model_Schedule_Uni_Limited_AbstractRTA_Definitions_AbstractRTADefinitions_quiet_time Job dJ aL cL sL iL wL j tL).
Proof.
  apply: ct_and.
  - exact (sub_nat_eq_correspondence _ _ _ _ (CI iR iL Hi j 0 _ (sub_nat_rel_canonical 0) tR tL Ht)
             (CW wR wL Hw j 0 _ (sub_nat_rel_canonical 0) tR tL Ht)).
  - exact (ct_bool_truth _ _ (ct_bool_not _ _ (clk_US_pending_earlier_and_at Job sR sL Hs aR aL Ha cR cL Hc j tR tL Ht))).
Qed.

Lemma clk_ARD_busy_interval_prefix j t1R t1L (H1 : SubNatRel t1R t1L) t2R t2L (H2 : SubNatRel t2R t2L) :
  PropSPropRel (AbstractRTADefinitions.busy_interval_prefix aR cR sR iR wR j t1R t2R) (I.Prosa_Classic_Model_Schedule_Uni_Limited_AbstractRTA_Definitions_AbstractRTADefinitions_busy_interval_prefix Job dJ aL cL sL iL wL j t1L t2L).
Proof.
  apply: ct_and; first exact (ct_bool_truth _ _ (ct_bool_and _ _ _ _ (ct_decide_le _ _ _ _ H1 (Ha j)) (ct_decide_lt _ _ _ _ (Ha j) H2))).
  apply: ct_and; first exact (clk_ARD_quiet_time j t1R t1L H1).
  apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (ct_bool_truth _ _ (ct_bool_and _ _ _ _ (ct_decide_lt _ _ _ _ H1 Ht) (ct_decide_lt _ _ _ _ Ht H2))).
  exact (ct_imp _ _ _ _ (clk_ARD_quiet_time j tR tL Ht) clk_false_rel).
Qed.

Lemma clk_ARD_busy_interval j t1R t1L (H1 : SubNatRel t1R t1L) t2R t2L (H2 : SubNatRel t2R t2L) :
  PropSPropRel (AbstractRTADefinitions.busy_interval aR cR sR iR wR j t1R t2R) (I.Prosa_Classic_Model_Schedule_Uni_Limited_AbstractRTA_Definitions_AbstractRTADefinitions_busy_interval Job dJ aL cL sL iL wL j t1L t2L).
Proof.
  apply: ct_and; first exact (clk_ARD_busy_interval_prefix j t1R t1L H1 t2R t2L H2).
  exact (clk_ARD_quiet_time j t2R t2L H2).
Qed.

Notation BI := clk_ARD_busy_interval.

Lemma clk_ARD_work_conserving (job_task : Job -> Task) arrR arrL (Harr : ClkArrRel Job arrR arrL) tsk :
  PropSPropRel (AbstractRTADefinitions.work_conserving aR cR job_task arrR sR tsk iR wR)
    (I.Prosa_Classic_Model_Schedule_Uni_Limited_AbstractRTA_Definitions_AbstractRTADefinitions_work_conserving Task dT Job dJ aL cL job_task arrL sL tsk iL wL).
Proof.
  apply: ct_forall_identity => j.
  apply: ct_forall_nat => t1R t1L H1. apply: ct_forall_nat => t2R t2L H2. apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (clk_arrives_in Job arrR arrL Harr j).
  apply: ct_imp; first exact (ct_eq_rel Task (job_task j) tsk).
  apply: ct_imp; first exact (sub_nat_lt_correspondence _ _ _ _ (sub_nat_rel_canonical 0) (Hc j)).
  apply: ct_imp; first exact (BI j t1R t1L H1 t2R t2L H2).
  apply: ct_imp; first exact (ct_bool_truth _ _ (ct_bool_and _ _ _ _ (ct_decide_le _ _ _ _ H1 Ht) (ct_decide_lt _ _ _ _ Ht H2))).
  apply: clk_iff.
  - exact (ct_imp _ _ _ _ (ct_bool_truth _ _ (Hi j tR tL Ht)) clk_false_rel).
  - exact (ct_bool_truth _ _ (clk_US_scheduled_at Job sR sL Hs j tR tL Ht)).
Qed.

End Sched.

End Defs.

(* ------------------------------------------------------------------ *)
(** * Definitions *)

Module LS := prosa.classic.model.schedule.uni.limited.schedule.

Section LSDefs.
Variables (Task Job : eqType).
Notation dT := (ct_decidable_eq Task).
Notation dJ := (ct_decidable_eq Job).
Variables (cR : Job -> nat) (cL : Job -> Lean.Nat).
Hypothesis Hc : ClkParRel Job cR cL.
Variables (arrR : ArrivalSequence.arrival_sequence Job)
  (arrL : I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrival_sequence Job dJ).
Hypothesis Harr : ClkArrRel Job arrR arrL.
Variables (lR : Job -> nat) (lL : Job -> Lean.Nat).
Hypothesis Hl : ClkParRel Job lR lL.

Lemma clk_LS_job_lock_in_service_le_job_cost :
  PropSPropRel (LS.job_lock_in_service_le_job_cost cR arrR lR) (I.Prosa_Classic_Model_Schedule_Uni_Limited_Schedule_job_lock_in_service_le_job_cost Job dJ cL arrL lL).
Proof.
  apply: ct_forall_identity => j.
  apply: ct_imp; first exact (clk_arrives_in Job arrR arrL Harr j).
  apply: ct_imp; first exact (ct_bool_truth _ _ (clk_J_job_cost_positive Job cR cL Hc j)).
  exact (sub_nat_le_correspondence _ _ _ _ (Hl j) (Hc j)).
Qed.

Section LSSched.
Variables (sR : UniprocessorSchedule.schedule Job) (sL : I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job dJ).
Hypothesis Hs : ClkSchedRel Job sR sL.

Lemma clk_LS_job_nonpreemptive_after_lock_in_service :
  PropSPropRel (LS.job_nonpreemptive_after_lock_in_service cR arrR sR lR)
    (I.Prosa_Classic_Model_Schedule_Uni_Limited_Schedule_job_nonpreemptive_after_lock_in_service Job dJ cL arrL sL lL).
Proof.
  apply: ct_forall_identity => j. apply: ct_forall_nat => tR tL Ht. apply: ct_forall_nat => t'R t'L Ht'.
  apply: ct_imp; first exact (clk_arrives_in Job arrR arrL Harr j).
  apply: ct_imp; first exact (sub_nat_le_correspondence _ _ _ _ Ht Ht').
  apply: ct_imp; first exact (sub_nat_le_correspondence _ _ _ _ (Hl j) (clk_US_service Job sR sL Hs j _ _ Ht)).
  apply: ct_imp; first exact (ct_bool_truth _ _ (ct_bool_not _ _ (clk_US_completed_by Job sR sL Hs cR cL Hc j _ _ Ht'))).
  exact (ct_bool_truth _ _ (clk_US_scheduled_at Job sR sL Hs j _ _ Ht')).
Qed.

End LSSched.

End LSDefs.

(* ------------------------------------------------------------------ *)
(** * Statements *)

Definition src_job_completes_within_busy_interval (Job : eqType) : Prop :=
  ltac:(type_of_term (@AbstractRTALockInService.job_completes_within_busy_interval Job)).
Definition tgt_job_completes_within_busy_interval (Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Model_Schedule_Uni_Limited_AbstractRTA_SufficientConditionForLockInService_AbstractRTALockInService_job_completes_within_busy_interval Job (ct_decidable_eq Job))).
Theorem AbstractRTALockInService_job_completes_within_busy_interval_correspondence (Job : eqType) :
  PropSPropRel (src_job_completes_within_busy_interval Job) (tgt_job_completes_within_busy_interval Job).
Proof.
  unfold src_job_completes_within_busy_interval, tgt_job_completes_within_busy_interval.
  apply: clk_forall_par => aR aL Ha. apply: clk_forall_par => cR cL Hc.
  apply: (clk_forall_sched Job) => sR sL Hs.
  apply: (clk_forall_int Job) => iR iL Hi. apply: (clk_forall_wl Job) => wR wL Hw.
  apply: ct_forall_identity => j.
  apply: ct_forall_nat => t1R t1L H1. apply: ct_forall_nat => t2R t2L H2.
  apply: ct_imp; first exact ((clk_ARD_busy_interval Job sR sL Hs aR aL cR cL Ha Hc iR iL wR wL Hi Hw j _ _ H1 _ _ H2)).
  exact (ct_bool_truth _ _ (clk_US_completed_by Job sR sL Hs cR cL Hc j _ _ H2)).
Qed.

Definition src_interference_is_complement_to_schedule (Task Job : eqType) : Prop :=
  ltac:(type_of_term (@AbstractRTALockInService.interference_is_complement_to_schedule Task Job)).
Definition tgt_interference_is_complement_to_schedule (Task Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Model_Schedule_Uni_Limited_AbstractRTA_SufficientConditionForLockInService_AbstractRTALockInService_interference_is_complement_to_schedule Task (ct_decidable_eq Task) Job (ct_decidable_eq Job))).
Theorem AbstractRTALockInService_interference_is_complement_to_schedule_correspondence (Task Job : eqType) :
  PropSPropRel (src_interference_is_complement_to_schedule Task Job) (tgt_interference_is_complement_to_schedule Task Job).
Proof.
  unfold src_interference_is_complement_to_schedule, tgt_interference_is_complement_to_schedule.
  apply: clk_forall_par => aR aL Ha. apply: clk_forall_par => cR cL Hc.
  apply: ct_forall_identity => job_task.
  apply: (clk_forall_arr Job) => arrR arrL Harr.
  apply: (clk_forall_sched Job) => sR sL Hs.
  apply: ct_forall_identity => tsk.
  apply: (clk_forall_int Job) => iR iL Hi. apply: (clk_forall_wl Job) => wR wL Hw.
  apply: ct_imp; first exact (clk_ARD_work_conserving Task Job sR sL Hs aR aL cR cL Ha Hc iR iL wR wL Hi Hw job_task arrR arrL Harr tsk).
  apply: ct_forall_identity => j.
  apply: ct_imp; first exact (clk_arrives_in Job arrR arrL Harr j).
  apply: ct_imp; first exact (ct_eq_rel Task (job_task j) tsk).
  apply: ct_imp; first exact (ct_bool_truth _ _ (clk_J_job_cost_positive Job cR cL Hc j)).
  apply: ct_forall_nat => t1R t1L H1. apply: ct_forall_nat => t2R t2L H2.
  apply: ct_imp; first exact ((clk_ARD_busy_interval Job sR sL Hs aR aL cR cL Ha Hc iR iL wR wL Hi Hw j _ _ H1 _ _ H2)).
  apply: ct_forall_nat => tR tL Ht. apply: ct_forall_nat => dR dL Hd.
  apply: ct_imp; first exact (sub_nat_le_correspondence _ _ _ _ H1 Ht).
  apply: ct_imp; first exact (sub_nat_le_correspondence _ _ _ _ (sub_add_correspondence _ _ _ _ Ht Hd) H2).
  exact (sub_nat_eq_correspondence _ _ _ _ (sub_add_correspondence _ _ _ _ (clk_US_service_during Job sR sL Hs j _ _ Ht _ _ (sub_add_correspondence _ _ _ _ Ht Hd))
           (clk_ARD_cumul_interference Job iR iL Hi j _ _ Ht _ _ (sub_add_correspondence _ _ _ _ Ht Hd))) Hd).
Qed.

Definition src_j_receives_at_least_lock_in_service (Task Job : eqType) : Prop :=
  ltac:(type_of_term (@AbstractRTALockInService.j_receives_at_least_lock_in_service Task Job)).
Definition tgt_j_receives_at_least_lock_in_service (Task Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Model_Schedule_Uni_Limited_AbstractRTA_SufficientConditionForLockInService_AbstractRTALockInService_j_receives_at_least_lock_in_service Task (ct_decidable_eq Task) Job (ct_decidable_eq Job))).
Theorem AbstractRTALockInService_j_receives_at_least_lock_in_service_correspondence (Task Job : eqType) :
  PropSPropRel (src_j_receives_at_least_lock_in_service Task Job) (tgt_j_receives_at_least_lock_in_service Task Job).
Proof.
  unfold src_j_receives_at_least_lock_in_service, tgt_j_receives_at_least_lock_in_service.
  apply: clk_forall_par => aR aL Ha. apply: clk_forall_par => cR cL Hc.
  apply: ct_forall_identity => job_task.
  apply: (clk_forall_arr Job) => arrR arrL Harr.
  apply: (clk_forall_sched Job) => sR sL Hs.
  apply: ct_forall_identity => tsk.
  apply: (clk_forall_int Job) => iR iL Hi. apply: (clk_forall_wl Job) => wR wL Hw.
  apply: ct_imp; first exact (clk_ARD_work_conserving Task Job sR sL Hs aR aL cR cL Ha Hc iR iL wR wL Hi Hw job_task arrR arrL Harr tsk).
  apply: ct_forall_identity => j.
  apply: ct_imp; first exact (clk_arrives_in Job arrR arrL Harr j).
  apply: ct_imp; first exact (ct_eq_rel Task (job_task j) tsk).
  apply: ct_imp; first exact (ct_bool_truth _ _ (clk_J_job_cost_positive Job cR cL Hc j)).
  apply: ct_forall_nat => t1R t1L H1. apply: ct_forall_nat => t2R t2L H2.
  apply: ct_imp; first exact ((clk_ARD_busy_interval Job sR sL Hs aR aL cR cL Ha Hc iR iL wR wL Hi Hw j _ _ H1 _ _ H2)).
  apply: ct_forall_nat => pR pL Hp.
  apply: ct_imp; first exact (sub_nat_le_correspondence _ _ _ _ Hp (Hc j)).
  apply: ct_forall_nat => dR dL Hd.
  apply: ct_imp; first exact (sub_nat_le_correspondence _ _ _ _ (sub_add_correspondence _ _ _ _ Hp (clk_ARD_cumul_interference Job iR iL Hi j _ _ H1 _ _ (sub_add_correspondence _ _ _ _ H1 Hd))) Hd).
  exact (sub_nat_le_correspondence _ _ _ _ Hp (clk_US_service Job sR sL Hs j _ _ (sub_add_correspondence _ _ _ _ H1 Hd))).
Qed.

Definition src_job_completes_after_reaching_lock_in_service (Job : eqType) : Prop :=
  ltac:(type_of_term (@AbstractRTALockInService.job_completes_after_reaching_lock_in_service Job)).
Definition tgt_job_completes_after_reaching_lock_in_service (Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Model_Schedule_Uni_Limited_AbstractRTA_SufficientConditionForLockInService_AbstractRTALockInService_job_completes_after_reaching_lock_in_service Job (ct_decidable_eq Job))).
Theorem AbstractRTALockInService_job_completes_after_reaching_lock_in_service_correspondence (Job : eqType) :
  PropSPropRel (src_job_completes_after_reaching_lock_in_service Job) (tgt_job_completes_after_reaching_lock_in_service Job).
Proof.
  unfold src_job_completes_after_reaching_lock_in_service, tgt_job_completes_after_reaching_lock_in_service.
  apply: clk_forall_par => cR cL Hc.
  apply: (clk_forall_arr Job) => arrR arrL Harr.
  apply: (clk_forall_sched Job) => sR sL Hs.
  apply: ct_forall_identity => j.
  apply: ct_imp; first exact (clk_arrives_in Job arrR arrL Harr j).
  apply: ct_imp; first exact (ct_bool_truth _ _ (clk_J_job_cost_positive Job cR cL Hc j)).
  apply: ct_imp; first exact (clk_US_completed_jobs_dont_execute Job sR sL Hs cR cL Hc).
  apply: clk_forall_par => lR lL Hl.
  apply: ct_imp; first exact (clk_LS_job_lock_in_service_le_job_cost Job cR cL Hc arrR arrL Harr lR lL Hl).
  apply: ct_imp; first exact (clk_LS_job_nonpreemptive_after_lock_in_service Job cR cL Hc arrR arrL Harr lR lL Hl sR sL Hs).
  apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (sub_nat_le_correspondence _ _ _ _ (Hl j) (clk_US_service Job sR sL Hs j _ _ Ht)).
  exact (ct_bool_truth _ _ (clk_US_completed_by Job sR sL Hs cR cL Hc j _ _ (sub_add_correspondence _ _ _ _ Ht (ct_sub_rel _ _ _ _ (Hc j) (Hl j))))).
Qed.
