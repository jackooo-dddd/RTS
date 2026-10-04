From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq fintype bigop.
From prosa Require Import classic.model.time classic.model.arrival.basic.arrival_sequence classic.model.schedule.uni.schedule classic.model.schedule.uni.response_time.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedClassicUniResponseTime.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence ClassicUniResponseTimeBase ClassicUniResponseTimeList.

Module I := ImportedClassicUniResponseTime.
Local Open Scope nat_scope.

(** Certificates for [classic/model/schedule/uni/response_time.v] (ProsaBuddy classic, commit f692cb7).

    Inputs: the job and task types are [eqType]s, identified, with the Lean [DecidableEq] instances given by the
    eqTypes' decision procedures ([ct_decidable_eq]); [job_task] identified; times by [SubNatRel]; job parameters
    pointwise through [SubNatRel]; uniprocessor schedules pointwise through the option map; arrival sequences pointwise
    on related times; all with two-way totals.  The imported uniprocessor schedule definitions are related as in the
    accepted classic uniprocessor schedule certificate (re-bound below); the two statements whose types contain
    [Finset.Ico] sums are exported through kernel-checked normalization guards.

    Statements: the source side is the exact elaborated type of the pinned lemma (via [type of]; the source proof
    is not used). *)

Ltac type_of_term t := let T := type of t in exact T.
Notation cid := (fun z => z).

(* ------------------------------------------------------------------ *)
(** * Helpers (re-bound to this export from the accepted classic certificates) *)

(** Base definitions (as in the accepted classic base library), provided here when this export's library lacks them. *)

(* ------------------------------------------------------------------ *)
(** * Generic covers and helpers *)

Lemma crt_forall_cover (A B : Type) (Rel : A -> B -> SProp) (toB : A -> B) (toA : B -> A)
    (HB : forall a, Rel a (toB a)) (HA : forall b, Rel (toA b) b) (PR : A -> Prop) (PL : B -> SProp) :
  (forall a b, Rel a b -> PropSPropRel (PR a) (PL b)) -> PropSPropRel (forall a, PR a) (forall b, PL b).
Proof.
  intro H. apply prop_sprop_rel_intro.
  - intros HR b. exact (prop_to_sprop _ _ (H _ _ (HA b)) (HR _)).
  - intro HL. apply strictly_inhabits. intro a. exact (sprop_to_prop _ _ (H _ _ (HB a)) (HL _)).
Qed.

Lemma crt_false_rel : PropSPropRel Logic.False I.False.
Proof.
  apply prop_sprop_rel_intro.
  - exact ct_coq_false_to_target.
  - exact ct_target_false_to_strict.
Qed.

Lemma crt_mem (T : eqType) x s sL : ClListRel cid s sL ->
  PropSPropRel (x \in s) (I.Membership_mem T (I.List T) (I.List_instMembership T) sL x).
Proof. exact (cl_mem_rel_list T T cid cid (fun _ => Logic.eq_refl _) x s sL). Qed.

Lemma crt_unmap_rel (T : Type) (l : I.List T) : ClListRel cid (cl_unmap cid l) l.
Proof. apply: coq_eq_to_imported_eq. exact (cl_map_unmap cid cid (fun _ => Logic.eq_refl _) l). Qed.

Lemma crt_cl_map_inj (T : Type) (s1 s2 : seq T) : Logic.eq (cl_map cid s1) (cl_map cid s2) -> Logic.eq s1 s2.
Proof.
  intro E. rewrite -(cl_unmap_map cid cid (fun _ => Logic.eq_refl _) s1) -(cl_unmap_map cid cid (fun _ => Logic.eq_refl _) s2).
  by rewrite E.
Qed.

Lemma crt_succ_rel nR nL : SubNatRel nR nL ->
  SubNatRel nR.+1 (I.HAdd_hAdd_inst7 Lean.Nat Lean.Nat Lean.Nat (I.instHAdd_inst1 Lean.Nat I.instAddNat) nL
                     (I.OfNat_ofNat_inst1 Lean.Nat 1 (I.instOfNatNat 1))).
Proof. intro Hn. exact (sub_imported_eq_congr Lean.Nat_succ _ _ Hn). Qed.

(* ------------------------------------------------------------------ *)
(** * Big concatenation over a half-open interval (as in the accepted arrival_sequence certificate) *)

Definition CrtParRel (T : Type) (pR : T -> nat) (pL : T -> Lean.Nat) : SProp := forall x, SubNatRel (pR x) (pL x).

Lemma crt_forall_par (T : Type) (PR : (T -> nat) -> Prop) (PL : (T -> Lean.Nat) -> SProp) :
  (forall pR pL, CrtParRel T pR pL -> PropSPropRel (PR pR) (PL pL)) -> PropSPropRel (forall p, PR p) (forall p, PL p).
Proof.
  exact (crt_forall_cover _ _ (CrtParRel T) (fun pR j => sub_nat_to_imported (pR j)) (fun pL j => sub_nat_to_rocq (pL j))
           (fun pR j => sub_nat_rel_canonical (pR j)) (fun pL j => sub_nat_rel_surjective (pL j)) PR PL).
Qed.

Fixpoint crt_natl (s : seq nat) : I.List_inst1 Lean.Nat :=
  match s with [::] => I.List_nil_inst1 _ | x :: s' => I.List_cons_inst1 _ (sub_nat_to_imported x) (crt_natl s') end.

Definition crt_one : Lean.Nat := I.OfNat_ofNat_inst1 Lean.Nat 1 (I.instOfNatNat 1).

Lemma crt_iota_range : forall n s,
  Logic.eq (I.List_range' (sub_nat_to_imported s) (sub_nat_to_imported n) crt_one) (crt_natl (iota s n)).
Proof.
  elim => [|n IH] s; first reflexivity.
  change (Logic.eq (I.List_cons_inst1 _ (sub_nat_to_imported s)
      (I.List_range' (sub_nat_to_imported (S s)) (sub_nat_to_imported n) crt_one))
    (I.List_cons_inst1 _ (sub_nat_to_imported s) (crt_natl (iota (S s) n)))).
  by rewrite IH.
Qed.

Lemma crt_cl_map_comp {A B C : Type} (f : A -> B) (g : B -> C) : forall s : seq A,
  Logic.eq (cl_map (fun x => g (f x)) s) (cl_map g (map f s)).
Proof. elim => [|x s IH] //=. by rewrite IH. Qed.

Lemma crt_cl_map_ext {A B : Type} (f g : A -> B) (H : forall x, Logic.eq (f x) (g x)) : forall s : seq A,
  Logic.eq (cl_map f s) (cl_map g s).
Proof. elim => [|x s IH] //=. by rewrite H IH. Qed.

Lemma crt_big_seq {A : Type} (F : nat -> seq A) : forall s : seq nat,
  Logic.eq (\big[cat/[::]]_(i <- s) F i) (flatten (map F s)).
Proof. elim => [|x s IH]; first by rewrite big_nil. by rewrite big_cons IH. Qed.

Definition CrtFamRel (A : Type) (fR : nat -> seq A) (fL : Lean.Nat -> I.List A) : SProp :=
  forall nR nL, SubNatRel nR nL -> ClListRel cid (fR nR) (fL nL).

(* ------------------------------------------------------------------ *)
(** * Arrival sequences and parameters *)

Section Rel.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).
Notation LArr := (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrival_sequence Job dJ).

Definition CrtArrRel (aR : ArrivalSequence.arrival_sequence Job) (aL : LArr) : SProp :=
  forall tR tL, SubNatRel tR tL -> ClListRel cid (aR tR) (aL tL).

Definition crt_arr_to_target (aR : ArrivalSequence.arrival_sequence Job) : LArr :=
  fun tL => cl_map cid (aR (sub_nat_to_rocq tL)).

Definition crt_arr_to_source (aL : LArr) : ArrivalSequence.arrival_sequence Job :=
  fun tR => cl_unmap cid (aL (sub_nat_to_imported tR)).

Lemma crt_arr_canonical aR : CrtArrRel aR (crt_arr_to_target aR).
Proof.
  intros tR tL Ht. have E := cl_nat_logic _ _ Ht. subst tL.
  apply: coq_eq_to_imported_eq. rewrite /crt_arr_to_target sub_nat_rocq_roundtrip. reflexivity.
Qed.

Lemma crt_arr_surjective aL : CrtArrRel (crt_arr_to_source aL) aL.
Proof.
  intros tR tL Ht. have E := cl_nat_logic _ _ Ht. subst tL.
  apply: coq_eq_to_imported_eq. exact (cl_map_unmap cid cid (fun _ => Logic.eq_refl _) _).
Qed.

Lemma crt_forall_arr (PR : ArrivalSequence.arrival_sequence Job -> Prop) (PL : LArr -> SProp) :
  (forall aR aL, CrtArrRel aR aL -> PropSPropRel (PR aR) (PL aL)) -> PropSPropRel (forall a, PR a) (forall a, PL a).
Proof. exact (crt_forall_cover _ _ CrtArrRel crt_arr_to_target crt_arr_to_source crt_arr_canonical crt_arr_surjective PR PL). Qed.

End Rel.

(** The imported [ArrivalSequence] definitions this file's statements mention, related on related inputs. *)
Section ArrivalDefs.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).

Lemma crt_arrives_in aR aL (Ha : CrtArrRel Job aR aL) j :
  PropSPropRel (ArrivalSequence.arrives_in aR j)
    (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrives_in Job dJ aL j).
Proof. apply: ct_exists_nat => tR tL Ht. exact (crt_mem Job j _ _ (Ha tR tL Ht)). Qed.

End ArrivalDefs.

Section ArrivalDefs2.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).

End ArrivalDefs2.

Fixpoint crt_snatl (s : seq nat) : I.List_inst1 Lean.Nat :=
  match s with [::] => I.List_nil_inst1 _ | x :: s' => I.List_cons_inst1 _ (sub_nat_to_imported x) (crt_snatl s') end.

Lemma crt_siota_range : forall n s,
  Logic.eq (I.List_range' (sub_nat_to_imported s) (sub_nat_to_imported n) (Lean.Nat_succ Lean.Nat_zero)) (crt_snatl (iota s n)).
Proof.
  elim => [|n IH] s; first reflexivity.
  change (Logic.eq (I.List_cons_inst1 _ (sub_nat_to_imported s)
      (I.List_range' (sub_nat_to_imported (S s)) (sub_nat_to_imported n) (Lean.Nat_succ Lean.Nat_zero)))
    (I.List_cons_inst1 _ (sub_nat_to_imported s) (crt_snatl (iota (S s) n)))).
  by rewrite IH.
Qed.

Lemma crt_foldr_add (f : Lean.Nat -> Lean.Nat) (g : nat -> nat) (Hf : forall k, Logic.eq (f (sub_nat_to_imported k)) (sub_nat_to_imported (g k))) :
  forall s, Logic.eq (I.List_foldr_inst3 Lean.Nat Lean.Nat Lean.Nat_add Lean.Nat_zero (I.List_map_inst3 Lean.Nat Lean.Nat f (crt_snatl s)))
                     (sub_nat_to_imported (foldr addn 0 (map g s))).
Proof.
  elim => [|k s IH] //=.
  change (Logic.eq (Lean.Nat_add (f (sub_nat_to_imported k))
            (I.List_foldr_inst3 Lean.Nat Lean.Nat Lean.Nat_add Lean.Nat_zero (I.List_map_inst3 Lean.Nat Lean.Nat f (crt_snatl s))))
         (sub_nat_to_imported (g k + foldr addn 0 (map g s)))).
  rewrite IH Hf. exact (imported_eq_to_coq_eq _ _ (sub_add_canonical _ _)).
Qed.

Lemma crt_big_fold (xs : seq nat) (F : nat -> nat) : Logic.eq (\sum_(i <- xs) F i) (foldr addn 0 (map F xs)).
Proof. elim: xs => [|x xs IH]; first by rewrite big_nil. by rewrite big_cons IH. Qed.

Definition CrtFunRel (FR : nat -> nat) (FL : Lean.Nat -> Lean.Nat) : SProp :=
  forall kR kL, SubNatRel kR kL -> SubNatRel (FR kR) (FL kL).

Lemma crt_fun_canonical FR FL (HF : CrtFunRel FR FL) k : Logic.eq (FL (sub_nat_to_imported k)) (sub_nat_to_imported (FR k)).
Proof. exact (cl_nat_logic _ _ (HF _ _ (sub_nat_rel_canonical k))). Qed.

Lemma crt_nat_sub_canonical (a b : nat) :
  Logic.eq (I.Nat_sub (sub_nat_to_imported a) (sub_nat_to_imported b)) (sub_nat_to_imported (a - b)).
Proof.
  elim: b => [|b IH]; first by rewrite subn0.
  change (Logic.eq (I.Nat_pred (I.Nat_sub (sub_nat_to_imported a) (sub_nat_to_imported b))) (sub_nat_to_imported (a - b.+1))).
  rewrite IH subnS. case: (a - b) => [|k]; reflexivity.
Qed.

Lemma crt_ico mR mL nR nL FR FL (Hm : SubNatRel mR mL) (Hn : SubNatRel nR nL) (HF : CrtFunRel FR FL) :
  SubNatRel (\sum_(mR <= i < nR) FR i)
    (I.List_foldr_inst3 Lean.Nat Lean.Nat Lean.Nat_add Lean.Nat_zero
       (I.List_map_inst3 Lean.Nat Lean.Nat FL (I.List_range' mL (I.Nat_sub nL mL) (Lean.Nat_succ Lean.Nat_zero)))).
Proof.
  rewrite (cl_nat_logic _ _ Hm) (cl_nat_logic _ _ Hn).
  have -> : Logic.eq (I.Nat_sub (sub_nat_to_imported nR) (sub_nat_to_imported mR)) (sub_nat_to_imported (nR - mR))
    := crt_nat_sub_canonical nR mR.
  rewrite crt_siota_range.
  apply: coq_eq_to_imported_eq. apply: Logic.eq_sym. rewrite (crt_foldr_add FL FR (crt_fun_canonical FR FL HF)).
  by rewrite crt_big_fold.
Qed.

(* ------------------------------------------------------------------ *)
(** * Options and uniprocessor schedules *)

(** Transport along the target equality (definitional UIP), as in the accepted global schedule certificate. *)
Definition crt_tr {A : Type} {x y : A} (E : Lean.eq x y) (P : A -> Type) (h : P x) : P y :=
  match E in Lean.eq _ z return P z with Lean.eq_refl => h end.

Definition crt_trs {A : Type} {x y : A} (E : Lean.eq x y) (P : A -> SProp) (h : P x) : P y :=
  match E in Lean.eq _ z return P z with Lean.eq_refl => h end.

Lemma crt_opt_inj (A : Type) (o1 o2 : option A) : Logic.eq (cl_opt o1) (cl_opt o2) -> Logic.eq o1 o2.
Proof. intro E. by rewrite -(cl_unopt_opt o1) -(cl_unopt_opt o2) E. Qed.

Lemma crt_opt_eqb_rel (A : eqType) (o1 o2 : option A) :
  PropSPropRel (is_true (o1 == o2)) (Lean.eq (cl_opt o1) (cl_opt o2)).
Proof.
  apply prop_sprop_rel_intro.
  - move=> /eqP E. rewrite E. exact (@Lean.eq_refl _ _).
  - intro E. apply strictly_inhabits. apply/eqP. exact (crt_opt_inj A o1 o2 (imported_eq_to_coq_eq _ _ E)).
Qed.

Section Sched.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).
Notation LSched := (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job dJ).

Definition CrtSchedRel (sR : UniprocessorSchedule.schedule Job) (sL : LSched) : SProp :=
  forall tR tL, SubNatRel tR tL -> Lean.eq (cl_opt (sR tR)) (sL tL).

Definition crt_sched_to_target (sR : UniprocessorSchedule.schedule Job) : LSched := fun tL => cl_opt (sR (sub_nat_to_rocq tL)).
Definition crt_sched_to_source (sL : LSched) : UniprocessorSchedule.schedule Job := fun tR => cl_unopt (sL (sub_nat_to_imported tR)).

Lemma crt_sched_canonical sR : CrtSchedRel sR (crt_sched_to_target sR).
Proof. intros tR tL Ht. apply: coq_eq_to_imported_eq. by rewrite /crt_sched_to_target (cl_nat_input _ _ Ht). Qed.

Lemma crt_sched_surjective sL : CrtSchedRel (crt_sched_to_source sL) sL.
Proof.
  intros tR tL Ht. apply: coq_eq_to_imported_eq. rewrite /crt_sched_to_source cl_opt_unopt.
  by rewrite (cl_nat_logic _ _ Ht).
Qed.

Lemma crt_forall_sched (PR : UniprocessorSchedule.schedule Job -> Prop) (PL : LSched -> SProp) :
  (forall sR sL, CrtSchedRel sR sL -> PropSPropRel (PR sR) (PL sL)) -> PropSPropRel (forall s, PR s) (forall s, PL s).
Proof. exact (crt_forall_cover _ _ CrtSchedRel crt_sched_to_target crt_sched_to_source crt_sched_canonical crt_sched_surjective PR PL). Qed.

End Sched.

(* ------------------------------------------------------------------ *)
(** * Definitions *)

Lemma crt_US_schedule (Job : eqType) :
  And (forall sR : UniprocessorSchedule.schedule Job, CrtSchedRel Job sR (crt_sched_to_target Job sR))
      (forall sL : I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job (ct_decidable_eq Job), CrtSchedRel Job (crt_sched_to_source Job sL) sL).
Proof. exact (And_intro _ _ (crt_sched_canonical Job) (crt_sched_surjective Job)). Qed.

Section USchedDefs.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).
Variables (sR : UniprocessorSchedule.schedule Job) (sL : I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job dJ).
Hypothesis Hs : CrtSchedRel Job sR sL.

Lemma crt_US_scheduled_at j tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (UniprocessorSchedule.scheduled_at sR j tR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_scheduled_at Job dJ sL j tL).
Proof.
  apply: ct_decide_bool.
  exact (crt_tr (Hs tR tL Ht) (fun z => PropSPropRel (sR tR == Some j) (Lean.eq z (cl_opt (Some j))))
           (crt_opt_eqb_rel Job (sR tR) (Some j))).
Qed.

Lemma crt_US_service_at j tR tL (Ht : SubNatRel tR tL) :
  SubNatRel (UniprocessorSchedule.service_at sR j tR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_service_at Job dJ sL j tL).
Proof. exact (ct_bool_to_nat _ _ (crt_US_scheduled_at j tR tL Ht)). Qed.

Lemma crt_service_at_fun j : CrtFunRel (fun t => UniprocessorSchedule.service_at sR j t) (fun t => I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_service_at Job dJ sL j t).
Proof. intros kR kL Hk. exact (crt_US_service_at j kR kL Hk). Qed.

Lemma crt_US_service_during j t1R t1L (H1 : SubNatRel t1R t1L) t2R t2L (H2 : SubNatRel t2R t2L) :
  SubNatRel (UniprocessorSchedule.service_during sR j t1R t2R) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_service_during Job dJ sL j t1L t2L).
Proof. exact (crt_ico _ _ _ _ _ _ H1 H2 (crt_service_at_fun j)). Qed.

Lemma crt_US_service j tR tL (Ht : SubNatRel tR tL) :
  SubNatRel (UniprocessorSchedule.service sR j tR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_service Job dJ sL j tL).
Proof. exact (crt_US_service_during j 0 _ (sub_nat_rel_canonical 0) tR tL Ht). Qed.

Lemma crt_US_completed_by cR cL (Hc : CrtParRel Job cR cL) j tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (UniprocessorSchedule.completed_by cR sR j tR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_completed_by Job dJ cL sL j tL).
Proof. exact (ct_decide_le _ _ _ _ (Hc j) (crt_US_service j tR tL Ht)). Qed.

Lemma crt_US_completed_jobs_dont_execute cR cL (Hc : CrtParRel Job cR cL) :
  PropSPropRel (UniprocessorSchedule.completed_jobs_dont_execute cR sR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_completed_jobs_dont_execute Job dJ cL sL).
Proof.
  apply: ct_forall_identity => j. apply: ct_forall_nat => tR tL Ht.
  exact (sub_nat_le_correspondence _ _ _ _ (crt_US_service j tR tL Ht) (Hc j)).
Qed.

End USchedDefs.


(* ------------------------------------------------------------------ *)
(** * Definitions *)

Section Defs.
Variables (Task Job : eqType).
Notation dT := (ct_decidable_eq Task).
Notation dJ := (ct_decidable_eq Job).
Variables (sR : UniprocessorSchedule.schedule Job) (sL : I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job dJ).
Hypothesis Hs : CrtSchedRel Job sR sL.

Theorem ResponseTime_is_response_time_bound_of_job_correspondence aR aL (Ha : CrtParRel Job aR aL) cR cL (Hc : CrtParRel Job cR cL)
    j rR rL (Hr : SubNatRel rR rL) :
  CtBoolRel (ResponseTime.is_response_time_bound_of_job aR cR sR j rR) (I.Prosa_Classic_Model_Schedule_Uni_ResponseTime_ResponseTime_is_response_time_bound_of_job Job dJ aL cL sL j rL).
Proof. exact (crt_US_completed_by Job sR sL Hs cR cL Hc j _ _ (sub_add_correspondence _ _ _ _ (Ha j) Hr)). Qed.

Theorem ResponseTime_is_response_time_bound_of_task_correspondence aR aL (Ha : CrtParRel Job aR aL) cR cL (Hc : CrtParRel Job cR cL)
    (job_task : Job -> Task) arrR arrL (Harr : CrtArrRel Job arrR arrL) tsk rR rL (Hr : SubNatRel rR rL) :
  PropSPropRel (ResponseTime.is_response_time_bound_of_task aR cR job_task arrR sR tsk rR)
    (I.Prosa_Classic_Model_Schedule_Uni_ResponseTime_ResponseTime_is_response_time_bound_of_task Task dT Job dJ aL cL job_task arrL sL tsk rL).
Proof.
  apply: ct_forall_identity => j.
  apply: ct_imp; first exact (crt_arrives_in Job arrR arrL Harr j).
  apply: ct_imp; first exact (ct_eq_rel Task (job_task j) tsk).
  exact (ct_bool_truth _ _ (ResponseTime_is_response_time_bound_of_job_correspondence aR aL Ha cR cL Hc j rR rL Hr)).
Qed.
End Defs.

(* ------------------------------------------------------------------ *)
(** * Statements *)

Notation c0 := (sub_nat_rel_canonical 0).
Notation RTJ := ResponseTime_is_response_time_bound_of_job_correspondence.

Definition src_service_after_job_rt_zero (Job : eqType) : Prop :=
  ltac:(type_of_term (@ResponseTime.service_after_job_rt_zero Job)).
Definition tgt_service_after_job_rt_zero (Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Model_Schedule_Uni_ResponseTime_ResponseTime_service_after_job_rt_zero Job (ct_decidable_eq Job))).

Theorem ResponseTime_service_after_job_rt_zero_correspondence (Job : eqType) :
  PropSPropRel (src_service_after_job_rt_zero Job) (tgt_service_after_job_rt_zero Job).
Proof.
  unfold src_service_after_job_rt_zero, tgt_service_after_job_rt_zero.
  apply: crt_forall_par => aR aL Ha. apply: crt_forall_par => cR cL Hc. apply: crt_forall_sched => sR sL Hs.
  apply: ct_imp; first exact (crt_US_completed_jobs_dont_execute Job sR sL Hs cR cL Hc).
  apply: ct_forall_identity => j. apply: ct_forall_nat => rR rL Hr.
  apply: ct_imp; first exact (ct_bool_truth _ _ (RTJ Job sR sL Hs aR aL Ha cR cL Hc j rR rL Hr)).
  apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (sub_nat_le_correspondence _ _ _ _ (sub_add_correspondence _ _ _ _ (Ha j) Hr) Ht).
  exact (sub_nat_eq_correspondence _ _ _ _ (crt_US_service_at Job sR sL Hs j tR tL Ht) c0).
Qed.

Definition src_cumulative_service_after_job_rt_zero (Job : eqType) : Prop :=
  ltac:(type_of_term (@ResponseTime.cumulative_service_after_job_rt_zero Job)).
Definition tgt_cumulative_service_after_job_rt_zero (Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Model_Schedule_Uni_ResponseTime_ResponseTime_cumulative_service_after_job_rt_zero Job (ct_decidable_eq Job))).

Theorem ResponseTime_cumulative_service_after_job_rt_zero_correspondence (Job : eqType) :
  PropSPropRel (src_cumulative_service_after_job_rt_zero Job) (tgt_cumulative_service_after_job_rt_zero Job).
Proof.
  unfold src_cumulative_service_after_job_rt_zero, tgt_cumulative_service_after_job_rt_zero.
  apply: crt_forall_par => aR aL Ha. apply: crt_forall_par => cR cL Hc. apply: crt_forall_sched => sR sL Hs.
  apply: ct_imp; first exact (crt_US_completed_jobs_dont_execute Job sR sL Hs cR cL Hc).
  apply: ct_forall_identity => j. apply: ct_forall_nat => rR rL Hr.
  apply: ct_imp; first exact (ct_bool_truth _ _ (RTJ Job sR sL Hs aR aL Ha cR cL Hc j rR rL Hr)).
  apply: ct_forall_nat => t1R t1L H1. apply: ct_forall_nat => t2R t2L H2.
  apply: ct_imp; first exact (sub_nat_le_correspondence _ _ _ _ (sub_add_correspondence _ _ _ _ (Ha j) Hr) H1).
  exact (sub_nat_eq_correspondence _ _ _ _ (crt_ico _ _ _ _ _ _ H1 H2 (crt_service_at_fun Job sR sL Hs j)) c0).
Qed.

Definition src_service_after_task_rt_zero (Task Job : eqType) : Prop :=
  ltac:(type_of_term (@ResponseTime.service_after_task_rt_zero Task Job)).
Definition tgt_service_after_task_rt_zero (Task Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Model_Schedule_Uni_ResponseTime_ResponseTime_service_after_task_rt_zero Task (ct_decidable_eq Task) Job (ct_decidable_eq Job))).

Theorem ResponseTime_service_after_task_rt_zero_correspondence (Task Job : eqType) :
  PropSPropRel (src_service_after_task_rt_zero Task Job) (tgt_service_after_task_rt_zero Task Job).
Proof.
  unfold src_service_after_task_rt_zero, tgt_service_after_task_rt_zero.
  apply: crt_forall_par => aR aL Ha. apply: crt_forall_par => cR cL Hc. apply: ct_forall_identity => job_task.
  apply: crt_forall_arr => arrR arrL Harr. apply: crt_forall_sched => sR sL Hs.
  apply: ct_imp; first exact (crt_US_completed_jobs_dont_execute Job sR sL Hs cR cL Hc).
  apply: ct_forall_identity => tsk. apply: ct_forall_nat => rR rL Hr.
  apply: ct_imp; first exact (ResponseTime_is_response_time_bound_of_task_correspondence Task Job sR sL Hs aR aL Ha cR cL Hc job_task arrR arrL Harr tsk rR rL Hr).
  apply: ct_forall_identity => j.
  apply: ct_imp; first exact (crt_arrives_in Job arrR arrL Harr j).
  apply: ct_imp; first exact (ct_eq_rel Task (job_task j) tsk).
  apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (sub_nat_le_correspondence _ _ _ _ (sub_add_correspondence _ _ _ _ (Ha j) Hr) Ht).
  exact (sub_nat_eq_correspondence _ _ _ _ (crt_US_service_at Job sR sL Hs j tR tL Ht) c0).
Qed.

Definition src_cumulative_service_after_task_rt_zero (Task Job : eqType) : Prop :=
  ltac:(type_of_term (@ResponseTime.cumulative_service_after_task_rt_zero Task Job)).
Definition tgt_cumulative_service_after_task_rt_zero (Task Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Model_Schedule_Uni_ResponseTime_ResponseTime_cumulative_service_after_task_rt_zero Task (ct_decidable_eq Task) Job (ct_decidable_eq Job))).

Theorem ResponseTime_cumulative_service_after_task_rt_zero_correspondence (Task Job : eqType) :
  PropSPropRel (src_cumulative_service_after_task_rt_zero Task Job) (tgt_cumulative_service_after_task_rt_zero Task Job).
Proof.
  unfold src_cumulative_service_after_task_rt_zero, tgt_cumulative_service_after_task_rt_zero.
  apply: crt_forall_par => aR aL Ha. apply: crt_forall_par => cR cL Hc. apply: ct_forall_identity => job_task.
  apply: crt_forall_arr => arrR arrL Harr. apply: crt_forall_sched => sR sL Hs.
  apply: ct_imp; first exact (crt_US_completed_jobs_dont_execute Job sR sL Hs cR cL Hc).
  apply: ct_forall_identity => tsk. apply: ct_forall_nat => rR rL Hr.
  apply: ct_imp; first exact (ResponseTime_is_response_time_bound_of_task_correspondence Task Job sR sL Hs aR aL Ha cR cL Hc job_task arrR arrL Harr tsk rR rL Hr).
  apply: ct_forall_identity => j.
  apply: ct_imp; first exact (crt_arrives_in Job arrR arrL Harr j).
  apply: ct_imp; first exact (ct_eq_rel Task (job_task j) tsk).
  apply: ct_forall_nat => t1R t1L H1. apply: ct_forall_nat => t2R t2L H2.
  apply: ct_imp; first exact (sub_nat_le_correspondence _ _ _ _ (sub_add_correspondence _ _ _ _ (Ha j) Hr) H1).
  exact (sub_nat_eq_correspondence _ _ _ _ (crt_ico _ _ _ _ _ _ H1 H2 (crt_service_at_fun Job sR sL Hs j)) c0).
Qed.
