From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq fintype bigop.
From prosa Require Import classic.model.time classic.model.arrival.basic.arrival_sequence classic.model.arrival.basic.job
  classic.model.schedule.global.basic.schedule classic.model.schedule.global.schedulability.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedClassicSchedulability.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence ClassicSchedulabilityBase ClassicSchedulabilityList ClassicSchedulabilityOrd.

Module I := ImportedClassicSchedulability.
Local Open Scope nat_scope.

(** Certificates for [classic/model/schedule/global/schedulability.v] (ProsaBuddy classic, commit f692cb7).

    Inputs, relations and computation as in the accepted classic schedule
    certificate (re-stated below for this export): eqTypes identified with their
    canonical Lean [DecidableEq] instances; times and [num_cpus] by [SubNatRel];
    processors by their values; schedules pointwise ([CsSchedRel]); job and task
    parameters pointwise; arrival sequences pointwise on related times; all with
    two-way totals.  [service_at] through the exported kernel-checked
    [service_at_sum] and [fin_sum_range']; [service] through its kernel-guarded
    [rfl] body projection; the half-open [\sum_(t' <= t < t'') F t] of the two
    cumulative statements through their kernel-guarded type normalization, related
    by [cs_ico].

    Statements: the source side is the exact elaborated type of the pinned lemma
    (via [type of]; the source proof is not used).  For the task lemmas, whose
    Rocq and Lean binder lists put [task_cost task_deadline] before the job type,
    the job type is fixed as an [eqType] with its canonical Lean instance and the
    two task parameters stay universally quantified on both sides. *)

Ltac type_of_term t := let T := type of t in exact T.

Lemma cs_forall_cover (A B : Type) (Rel : A -> B -> SProp) (toB : A -> B) (toA : B -> A)
    (HB : forall a, Rel a (toB a)) (HA : forall b, Rel (toA b) b) (PR : A -> Prop) (PL : B -> SProp) :
  (forall a b, Rel a b -> PropSPropRel (PR a) (PL b)) -> PropSPropRel (forall a, PR a) (forall b, PL b).
Proof.
  intro H. apply prop_sprop_rel_intro.
  - intros HR b. exact (prop_to_sprop _ _ (H _ _ (HA b)) (HR _)).
  - intro HL. apply strictly_inhabits. intro a. exact (sprop_to_prop _ _ (H _ _ (HB a)) (HL _)).
Qed.

Lemma cs_mem (T : eqType) x s sL : ClListRel cid s sL ->
  PropSPropRel (x \in s) (I.Membership_mem T (I.List T) (I.List_instMembership T) sL x).
Proof. exact (cl_mem_rel_list T T cid cid (fun _ => Logic.eq_refl _) x s sL). Qed.

Lemma cs_uniq (T : eqType) s sL : ClListRel cid s sL -> PropSPropRel (uniq s) (I.List_Nodup T sL).
Proof. exact (cl_uniq_rel_list T T cid cid (fun _ => Logic.eq_refl _) (fun _ => Logic.eq_refl _) s sL). Qed.

Lemma cs_list_size (T : Type) s sL : ClListRel (B := T) cid s sL -> SubNatRel (size s) (I.List_length T sL).
Proof. intro H. destruct H. exact (cl_size cid s). Qed.

Lemma cs_lean_eq_logic (A : Type) (x y : A) : Lean.eq x y -> Logic.eq x y.
Proof. exact (imported_eq_to_coq_eq x y). Qed.

Definition cs_tr {A : Type} {x y : A} (E : Lean.eq x y) (P : A -> Type) (h : P x) : P y :=
  match E in Lean.eq _ z return P z with Lean.eq_refl => h end.

Definition cs_trs {A : Type} {x y : A} (E : Lean.eq x y) (P : A -> SProp) (h : P x) : P y :=
  match E in Lean.eq _ z return P z with Lean.eq_refl => h end.

Lemma cs_opt_inj (A : Type) (o1 o2 : option A) : Logic.eq (cl_opt o1) (cl_opt o2) -> Logic.eq o1 o2.
Proof. intro E. by rewrite -(cl_unopt_opt o1) -(cl_unopt_opt o2) E. Qed.

Lemma cs_opt_eq_rel (A : Type) (o1 o2 : option A) :
  PropSPropRel (Logic.eq o1 o2) (Lean.eq (cl_opt o1) (cl_opt o2)).
Proof.
  apply prop_sprop_rel_intro.
  - intro E. rewrite E. exact (@Lean.eq_refl _ _).
  - intro E. apply strictly_inhabits. exact (cs_opt_inj A o1 o2 (imported_eq_to_coq_eq _ _ E)).
Qed.

Lemma cs_opt_eqb_rel (A : eqType) (o1 o2 : option A) :
  PropSPropRel (is_true (o1 == o2)) (Lean.eq (cl_opt o1) (cl_opt o2)).
Proof.
  apply prop_sprop_rel_intro.
  - move=> /eqP E. rewrite E. exact (@Lean.eq_refl _ _).
  - intro E. apply strictly_inhabits. apply/eqP. exact (cs_opt_inj A o1 o2 (imported_eq_to_coq_eq _ _ E)).
Qed.

Fixpoint cs_natl (s : seq nat) : I.List_inst1 Lean.Nat :=
  match s with [::] => I.List_nil_inst1 _ | x :: s' => I.List_cons_inst1 _ (sub_nat_to_imported x) (cs_natl s') end.

Lemma cs_iota_range : forall n s,
  Logic.eq (I.List_range' (sub_nat_to_imported s) (sub_nat_to_imported n) (Lean.Nat_succ Lean.Nat_zero)) (cs_natl (iota s n)).
Proof.
  elim => [|n IH] s; first reflexivity.
  change (Logic.eq (I.List_cons_inst1 _ (sub_nat_to_imported s)
      (I.List_range' (sub_nat_to_imported (S s)) (sub_nat_to_imported n) (Lean.Nat_succ Lean.Nat_zero)))
    (I.List_cons_inst1 _ (sub_nat_to_imported s) (cs_natl (iota (S s) n)))).
  by rewrite IH.
Qed.

Lemma cs_foldr_add (f : Lean.Nat -> Lean.Nat) (g : nat -> nat) (Hf : forall k, Logic.eq (f (sub_nat_to_imported k)) (sub_nat_to_imported (g k))) :
  forall s, Logic.eq (I.List_foldr_inst3 Lean.Nat Lean.Nat Lean.Nat_add Lean.Nat_zero (I.List_map_inst3 Lean.Nat Lean.Nat f (cs_natl s)))
                     (sub_nat_to_imported (foldr addn 0 (map g s))).
Proof.
  elim => [|k s IH] //=.
  change (Logic.eq (Lean.Nat_add (f (sub_nat_to_imported k))
            (I.List_foldr_inst3 Lean.Nat Lean.Nat Lean.Nat_add Lean.Nat_zero (I.List_map_inst3 Lean.Nat Lean.Nat f (cs_natl s))))
         (sub_nat_to_imported (g k + foldr addn 0 (map g s)))).
  rewrite IH Hf. exact (imported_eq_to_coq_eq _ _ (sub_add_canonical _ _)).
Qed.

Lemma cs_big_fold (xs : seq nat) (F : nat -> nat) : Logic.eq (\sum_(i <- xs) F i) (foldr addn 0 (map F xs)).
Proof. elim: xs => [|x xs IH]; first by rewrite big_nil. by rewrite big_cons IH. Qed.

Definition CsFunRel (FR : nat -> nat) (FL : Lean.Nat -> Lean.Nat) : SProp :=
  forall kR kL, SubNatRel kR kL -> SubNatRel (FR kR) (FL kL).

Lemma cs_fun_canonical FR FL (HF : CsFunRel FR FL) k : Logic.eq (FL (sub_nat_to_imported k)) (sub_nat_to_imported (FR k)).
Proof. exact (co_nat_logic _ _ (HF _ _ (sub_nat_rel_canonical k))). Qed.

Lemma cs_ico mR mL nR nL FR FL (Hm : SubNatRel mR mL) (Hn : SubNatRel nR nL) (HF : CsFunRel FR FL) :
  SubNatRel (\sum_(mR <= i < nR) FR i)
    (I.List_foldr_inst3 Lean.Nat Lean.Nat Lean.Nat_add Lean.Nat_zero
       (I.List_map_inst3 Lean.Nat Lean.Nat FL (I.List_range' mL (I.Nat_sub nL mL) (Lean.Nat_succ Lean.Nat_zero)))).
Proof.
  rewrite (co_nat_logic _ _ Hm) (co_nat_logic _ _ Hn).
  have -> : Logic.eq (I.Nat_sub (sub_nat_to_imported nR) (sub_nat_to_imported mR)) (sub_nat_to_imported (nR - mR))
    := ct_sub_canonical nR mR.
  rewrite cs_iota_range.
  apply: coq_eq_to_imported_eq. apply: Logic.eq_sym. rewrite (cs_foldr_add FL FR (cs_fun_canonical FR FL HF)).
  by rewrite cs_big_fold.
Qed.

Definition CsParRel (T : Type) (pR : T -> nat) (pL : T -> Lean.Nat) : SProp := forall x, SubNatRel (pR x) (pL x).

Lemma cs_forall_par (T : Type) (PR : (T -> nat) -> Prop) (PL : (T -> Lean.Nat) -> SProp) :
  (forall pR pL, CsParRel T pR pL -> PropSPropRel (PR pR) (PL pL)) -> PropSPropRel (forall p, PR p) (forall p, PL p).
Proof.
  exact (cs_forall_cover _ _ (CsParRel T) (fun pR j => sub_nat_to_imported (pR j)) (fun pL j => sub_nat_to_rocq (pL j))
           (fun pR j => sub_nat_rel_canonical (pR j)) (fun pL j => sub_nat_rel_surjective (pL j)) PR PL).
Qed.

Section Sched.
Variables (Job : eqType) (nR : nat) (nL : Lean.Nat).
Hypothesis Hn : SubNatRel nR nL.
Notation dJ := (ct_decidable_eq Job).
Notation LSched := (I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_schedule Job dJ nL).

Definition CsSchedRel (sR : Schedule.schedule Job nR) (sL : LSched) : SProp :=
  forall oR oL, CoOrdRel nR nL oR oL -> forall tR tL, SubNatRel tR tL -> Lean.eq (cl_opt (sR oR tR)) (sL oL tL).

Definition cs_sched_to_target (sR : Schedule.schedule Job nR) : LSched :=
  fun oL tL => cl_opt (sR (co_fin_to_ord nR nL Hn oL) (sub_nat_to_rocq tL)).

Definition cs_sched_to_source (sL : LSched) : Schedule.schedule Job nR :=
  fun oR tR => cl_unopt (sL (co_ord_to_fin nR nL Hn oR) (sub_nat_to_imported tR)).

Lemma cs_sched_canonical sR : CsSchedRel sR (cs_sched_to_target sR).
Proof.
  intros oR oL Ho tR tL Ht. apply: coq_eq_to_imported_eq. rewrite /cs_sched_to_target (co_nat_input _ _ Ht).
  by rewrite (co_ord_eq _ _ _ _ _ Ho (co_ord_surjective nR nL Hn oL)).
Qed.

Lemma cs_sched_surjective sL : CsSchedRel (cs_sched_to_source sL) sL.
Proof.
  intros oR oL Ho tR tL Ht. apply: coq_eq_to_imported_eq. rewrite /cs_sched_to_source cl_opt_unopt.
  rewrite (co_nat_logic _ _ Ht). by rewrite (co_fin_rel_eq _ _ _ _ _ (co_ord_canonical nR nL Hn oR) Ho).
Qed.

Lemma cs_forall_sched (PR : Schedule.schedule Job nR -> Prop) (PL : LSched -> SProp) :
  (forall sR sL, CsSchedRel sR sL -> PropSPropRel (PR sR) (PL sL)) -> PropSPropRel (forall s, PR s) (forall s, PL s).
Proof. exact (cs_forall_cover _ _ CsSchedRel cs_sched_to_target cs_sched_to_source cs_sched_canonical cs_sched_surjective PR PL). Qed.
End Sched.

Section Arr.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).
Notation LArr := (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrival_sequence Job dJ).

Definition CsArrRel (aR : ArrivalSequence.arrival_sequence Job) (aL : LArr) : SProp :=
  forall tR tL, SubNatRel tR tL -> ClListRel cid (aR tR) (aL tL).

Definition cs_arr_to_target (aR : ArrivalSequence.arrival_sequence Job) : LArr :=
  fun tL => cl_map cid (aR (sub_nat_to_rocq tL)).

Definition cs_arr_to_source (aL : LArr) : ArrivalSequence.arrival_sequence Job :=
  fun tR => cl_unmap cid (aL (sub_nat_to_imported tR)).

Lemma cs_arr_canonical aR : CsArrRel aR (cs_arr_to_target aR).
Proof.
  intros tR tL Ht. have E := co_nat_logic _ _ Ht. subst tL.
  apply: coq_eq_to_imported_eq. rewrite /cs_arr_to_target sub_nat_rocq_roundtrip. reflexivity.
Qed.

Lemma cs_arr_surjective aL : CsArrRel (cs_arr_to_source aL) aL.
Proof.
  intros tR tL Ht. have E := co_nat_logic _ _ Ht. subst tL.
  apply: coq_eq_to_imported_eq. exact (cl_map_unmap cid cid (fun _ => Logic.eq_refl _) _).
Qed.

Lemma cs_arrives_in aR aL (Ha : CsArrRel aR aL) j :
  PropSPropRel (ArrivalSequence.arrives_in aR j)
    (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrives_in Job dJ aL j).
Proof. apply: ct_exists_nat => tR tL Ht. exact (cs_mem Job j _ _ (Ha tR tL Ht)). Qed.
End Arr.

Section Defs.
Variables (Job : eqType) (nR : nat) (nL : Lean.Nat).
Hypothesis Hn : SubNatRel nR nL.
Notation dJ := (ct_decidable_eq Job).
Variables (sR : Schedule.schedule Job nR)
  (sL : I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_schedule Job dJ nL).
Hypothesis Hs : CsSchedRel Job nR nL sR sL.

Lemma cf_Schedule_scheduled_on j oR oL (Ho : CoOrdRel nR nL oR oL) tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (Schedule.scheduled_on sR j oR tR)
    (I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_scheduled_on Job dJ nL sL j oL tL).
Proof.
  apply: ct_decide_bool.
  exact (cs_tr (Hs oR oL Ho tR tL Ht) (fun z => PropSPropRel (sR oR tR == Some j) (Lean.eq z (cl_opt (Some j))))
           (cs_opt_eqb_rel Job (sR oR tR) (Some j))).
Qed.

Lemma cf_Schedule_service_at j tR tL (Ht : SubNatRel tR tL) :
  SubNatRel (Schedule.service_at sR j tR)
    (I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_service_at Job dJ nL sL j tL).
Proof.
  apply: coq_eq_to_imported_eq.
  rewrite (imported_eq_to_coq_eq _ _ (I.Prosa_Validation_ClassicSchedulabilityInterface_service_at_sum Job dJ nL sL j tL)).
  apply: imported_eq_to_coq_eq.
  rewrite /Schedule.service_at big_mkcond /=.
  apply: (co_sum_rel nR nL Hn). intros oR oL Ho.
  have H := cf_Schedule_scheduled_on j oR oL Ho tR tL Ht.
  rewrite (ct_bool_rel_logic _ _ H). destruct (Schedule.scheduled_on sR j oR tR).
  - exact (sub_nat_rel_canonical 1).
  - exact (sub_nat_rel_canonical 0).
Qed.

Lemma cs_service_at_fun j : CsFunRel (fun t => Schedule.service_at sR j t)
    (fun t => I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_service_at Job dJ nL sL j t).
Proof. intros kR kL Hk. exact (cf_Schedule_service_at j kR kL Hk). Qed.

Lemma cf_Schedule_service j tR tL (Ht : SubNatRel tR tL) :
  SubNatRel (Schedule.service sR j tR)
    (I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_service Job dJ nL sL j tL).
Proof. exact (cs_ico 0 _ tR tL _ _ (sub_nat_rel_canonical 0) Ht (cs_service_at_fun j)). Qed.

Lemma cf_Schedule_completed cR cL (Hc : CsParRel Job cR cL) j tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (Schedule.completed cR sR j tR)
    (I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_completed Job dJ cL nL sL j tL).
Proof. exact (ct_decide_le _ _ _ _ (Hc j) (cf_Schedule_service j tR tL Ht)). Qed.

Lemma cf_Schedule_completed_jobs_dont_execute cR cL (Hc : CsParRel Job cR cL) :
  PropSPropRel (Schedule.completed_jobs_dont_execute cR sR)
    (I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_completed_jobs_dont_execute Job dJ cL nL sL).
Proof.
  apply: ct_forall_identity => j. apply: ct_forall_nat => tR tL Ht.
  exact (sub_nat_le_correspondence _ _ _ _ (cf_Schedule_service j tR tL Ht) (Hc j)).
Qed.


End Defs.

Lemma cs_forall_ncpus_sched (Job : eqType)
    (PR : forall n : nat, Schedule.schedule Job n -> Prop)
    (PL : forall n : Lean.Nat, I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_schedule Job (ct_decidable_eq Job) n -> SProp) :
  (forall nR nL (Hn : SubNatRel nR nL) sR sL, CsSchedRel Job nR nL sR sL -> PropSPropRel (PR nR sR) (PL nL sL)) ->
  PropSPropRel (forall n s, PR n s) (forall n s, PL n s).
Proof.
  intro H. apply: ct_forall_nat => nR nL Hn. exact (cs_forall_sched Job nR nL Hn _ _ (H nR nL Hn)).
Qed.

(* ------------------------------------------------------------------ *)
(** * Definitions *)

Section Defs.
Variables (Task Job : eqType) (nR : nat) (nL : Lean.Nat).
Hypothesis Hn : SubNatRel nR nL.
Variables (sR : Schedule.schedule Job nR)
  (sL : I.Prosa_Classic_Model_Schedule_Global_Basic_Schedule_Schedule_schedule Job (ct_decidable_eq Job) nL).
Hypothesis Hs : CsSchedRel Job nR nL sR sL.
Variables (jaR : Job -> nat) (jaL : Job -> Lean.Nat) (cR : Job -> nat) (cL : Job -> Lean.Nat) (dR : Job -> nat) (dL : Job -> Lean.Nat).
Hypotheses (Hja : CsParRel Job jaR jaL) (Hc : CsParRel Job cR cL) (Hd : CsParRel Job dR dL).

Theorem Schedulability_job_misses_no_deadline_correspondence j :
  CtBoolRel (Schedulability.job_misses_no_deadline jaR cR dR sR j)
    (I.Prosa_Classic_Model_Schedule_Global_Schedulability_Schedulability_job_misses_no_deadline Job (ct_decidable_eq Job) jaL cL dL nL sL j).
Proof. exact (cf_Schedule_completed Job nR nL Hn sR sL Hs cR cL Hc j _ _ (sub_add_correspondence _ _ _ _ (Hja j) (Hd j))). Qed.

Theorem Schedulability_task_misses_no_deadline_correspondence (job_task : Job -> Task) aR aL (Ha : CsArrRel Job aR aL) tsk :
  PropSPropRel (Schedulability.task_misses_no_deadline jaR cR dR job_task aR sR tsk)
    (I.Prosa_Classic_Model_Schedule_Global_Schedulability_Schedulability_task_misses_no_deadline
       Task Job (ct_decidable_eq Task) (ct_decidable_eq Job) jaL cL dL job_task aL nL sL tsk).
Proof.
  apply: ct_forall_identity => j.
  apply: ct_imp; first exact (cs_arrives_in Job aR aL Ha j).
  apply: ct_imp; first exact (ct_eq_rel Task (job_task j) tsk).
  exact (ct_bool_truth _ _ (Schedulability_job_misses_no_deadline_correspondence j)).
Qed.

Theorem Schedulability_task_misses_no_deadline_before_correspondence (job_task : Job -> Task) aR aL (Ha : CsArrRel Job aR aL) tsk
    tR tL (Ht : SubNatRel tR tL) :
  PropSPropRel (Schedulability.task_misses_no_deadline_before jaR cR dR job_task aR sR tsk tR)
    (I.Prosa_Classic_Model_Schedule_Global_Schedulability_Schedulability_task_misses_no_deadline_before
       Task Job (ct_decidable_eq Task) (ct_decidable_eq Job) jaL cL dL job_task aL nL sL tsk tL).
Proof.
  apply: ct_forall_identity => j.
  apply: ct_imp; first exact (cs_arrives_in Job aR aL Ha j).
  apply: ct_imp; first exact (ct_eq_rel Task (job_task j) tsk).
  apply: ct_imp; first exact (sub_nat_lt_correspondence _ _ _ _ (sub_add_correspondence _ _ _ _ (Hja j) (Hd j)) Ht).
  exact (ct_bool_truth _ _ (Schedulability_job_misses_no_deadline_correspondence j)).
Qed.
End Defs.

Lemma csch_forall_arr (Job : eqType) PR PL :
  (forall aR aL, CsArrRel Job aR aL -> PropSPropRel (PR aR) (PL aL)) -> PropSPropRel (forall a, PR a) (forall a, PL a).
Proof. exact (cs_forall_cover _ _ (CsArrRel Job) (cs_arr_to_target Job) (cs_arr_to_source Job) (cs_arr_canonical Job) (cs_arr_surjective Job) PR PL). Qed.

Lemma csch_valid_sporadic_job (Task Job : eqType) tcR tcL (Htc : CsParRel Task tcR tcL) tdR tdL (Htd : CsParRel Task tdR tdL)
    cR cL (Hc : CsParRel Job cR cL) dR dL (Hd : CsParRel Job dR dL) (job_task : Job -> Task) j :
  PropSPropRel (Job.valid_sporadic_job tcR tdR cR dR job_task j)
    (I.Prosa_Classic_Model_Arrival_Basic_Job_Job_valid_sporadic_job Task (ct_decidable_eq Task) tcL tdL Job (ct_decidable_eq Job) cL dL job_task j).
Proof.
  apply: ct_and.
  { apply: ct_and; first exact (ct_bool_truth _ _ (ct_decide_lt _ _ _ _ (sub_nat_rel_canonical 0) (Hc j))).
    apply: ct_and; first exact (ct_bool_truth _ _ (ct_decide_le _ _ _ _ (Hc j) (Hd j))).
    exact (ct_bool_truth _ _ (ct_decide_lt _ _ _ _ (sub_nat_rel_canonical 0) (Hd j))). }
  apply: ct_and; first exact (ct_bool_truth _ _ (ct_decide_le _ _ _ _ (Hc j) (Htc (job_task j)))).
  exact (sub_nat_eq_correspondence _ _ _ _ (Hd j) (Htd (job_task j))).
Qed.

(* ------------------------------------------------------------------ *)
(** * Statements *)

Notation jmnd := Schedulability_job_misses_no_deadline_correspondence.
Notation tmnd := Schedulability_task_misses_no_deadline_correspondence.

Definition src_service_after_job_deadline_zero (Job : eqType) : Prop :=
  ltac:(type_of_term (@Schedulability.service_after_job_deadline_zero Job)).
Definition tgt_service_after_job_deadline_zero (Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Model_Schedule_Global_Schedulability_Schedulability_service_after_job_deadline_zero Job (ct_decidable_eq Job))).
Theorem Schedulability_service_after_job_deadline_zero_correspondence (Job : eqType) :
  PropSPropRel (src_service_after_job_deadline_zero Job) (tgt_service_after_job_deadline_zero Job).
Proof.
  unfold src_service_after_job_deadline_zero, tgt_service_after_job_deadline_zero.
  apply: cs_forall_par => jaR jaL Hja. apply: cs_forall_par => cR cL Hc. apply: cs_forall_par => dR dL Hd.
  apply: cs_forall_ncpus_sched => nR nL Hn sR sL Hs.
  apply: ct_imp; first exact (cf_Schedule_completed_jobs_dont_execute Job nR nL Hn sR sL Hs cR cL Hc).
  apply: ct_forall_identity => j.
  apply: ct_imp; first exact (ct_bool_truth _ _ (jmnd Job nR nL Hn sR sL Hs jaR jaL cR cL dR dL Hja Hc Hd j)).
  apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (sub_nat_le_correspondence _ _ _ _ (sub_add_correspondence _ _ _ _ (Hja j) (Hd j)) Ht).
  exact (sub_nat_eq_correspondence _ _ _ _ (cf_Schedule_service_at Job nR nL Hn sR sL Hs j tR tL Ht) (sub_nat_rel_canonical 0)).
Qed.

Definition src_cumulative_service_after_job_deadline_zero (Job : eqType) : Prop :=
  ltac:(type_of_term (@Schedulability.cumulative_service_after_job_deadline_zero Job)).
Definition tgt_cumulative_service_after_job_deadline_zero (Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Model_Schedule_Global_Schedulability_Schedulability_cumulative_service_after_job_deadline_zero Job (ct_decidable_eq Job))).
Theorem Schedulability_cumulative_service_after_job_deadline_zero_correspondence (Job : eqType) :
  PropSPropRel (src_cumulative_service_after_job_deadline_zero Job) (tgt_cumulative_service_after_job_deadline_zero Job).
Proof.
  unfold src_cumulative_service_after_job_deadline_zero, tgt_cumulative_service_after_job_deadline_zero.
  apply: cs_forall_par => jaR jaL Hja. apply: cs_forall_par => cR cL Hc. apply: cs_forall_par => dR dL Hd.
  apply: cs_forall_ncpus_sched => nR nL Hn sR sL Hs.
  apply: ct_imp; first exact (cf_Schedule_completed_jobs_dont_execute Job nR nL Hn sR sL Hs cR cL Hc).
  apply: ct_forall_identity => j.
  apply: ct_imp; first exact (ct_bool_truth _ _ (jmnd Job nR nL Hn sR sL Hs jaR jaL cR cL dR dL Hja Hc Hd j)).
  apply: ct_forall_nat => t1R t1L H1. apply: ct_forall_nat => t2R t2L H2.
  apply: ct_imp; first exact (sub_nat_le_correspondence _ _ _ _ (sub_add_correspondence _ _ _ _ (Hja j) (Hd j)) H1).
  exact (sub_nat_eq_correspondence _ _ _ _ (cs_ico _ _ _ _ _ _ H1 H2 (cs_service_at_fun Job nR nL Hn sR sL Hs j))
           (sub_nat_rel_canonical 0)).
Qed.

Definition src_service_after_task_deadline_zero (Task Job : eqType) : Prop :=
  forall task_cost task_deadline : Task -> Time.time,
    ltac:(type_of_term (@Schedulability.service_after_task_deadline_zero Task task_cost task_deadline Job)).
Definition tgt_service_after_task_deadline_zero (Task Job : eqType) : SProp :=
  forall task_cost task_deadline : Task -> Lean.Nat,
    ltac:(type_of_term (I.Prosa_Classic_Model_Schedule_Global_Schedulability_Schedulability_service_after_task_deadline_zero
                          Task (ct_decidable_eq Task) task_cost task_deadline Job (ct_decidable_eq Job))).
Theorem Schedulability_service_after_task_deadline_zero_correspondence (Task Job : eqType) :
  PropSPropRel (src_service_after_task_deadline_zero Task Job) (tgt_service_after_task_deadline_zero Task Job).
Proof.
  unfold src_service_after_task_deadline_zero, tgt_service_after_task_deadline_zero.
  apply: cs_forall_par => tcR tcL Htc. apply: cs_forall_par => tdR tdL Htd.
  apply: cs_forall_par => jaR jaL Hja. apply: cs_forall_par => cR cL Hc. apply: cs_forall_par => dR dL Hd.
  apply: ct_forall_identity => job_task. apply: csch_forall_arr => aR aL Ha.
  apply: cs_forall_ncpus_sched => nR nL Hn sR sL Hs.
  apply: ct_imp; first exact (cf_Schedule_completed_jobs_dont_execute Job nR nL Hn sR sL Hs cR cL Hc).
  apply: ct_forall_identity => tsk.
  apply: ct_imp; first exact (tmnd Task Job nR nL Hn sR sL Hs jaR jaL cR cL dR dL Hja Hc Hd job_task aR aL Ha tsk).
  apply: ct_forall_identity => j.
  apply: ct_imp; first exact (cs_arrives_in Job aR aL Ha j).
  apply: ct_imp; first exact (ct_eq_rel Task (job_task j) tsk).
  apply: ct_imp; first exact (csch_valid_sporadic_job Task Job tcR tcL Htc tdR tdL Htd cR cL Hc dR dL Hd job_task j).
  apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (sub_nat_le_correspondence _ _ _ _ (sub_add_correspondence _ _ _ _ (Hja j) (Htd tsk)) Ht).
  exact (sub_nat_eq_correspondence _ _ _ _ (cf_Schedule_service_at Job nR nL Hn sR sL Hs j tR tL Ht) (sub_nat_rel_canonical 0)).
Qed.

Definition src_cumulative_service_after_task_deadline_zero (Task Job : eqType) : Prop :=
  forall task_cost task_deadline : Task -> Time.time,
    ltac:(type_of_term (@Schedulability.cumulative_service_after_task_deadline_zero Task task_cost task_deadline Job)).
Definition tgt_cumulative_service_after_task_deadline_zero (Task Job : eqType) : SProp :=
  forall task_cost task_deadline : Task -> Lean.Nat,
    ltac:(type_of_term (I.Prosa_Classic_Model_Schedule_Global_Schedulability_Schedulability_cumulative_service_after_task_deadline_zero
                          Task (ct_decidable_eq Task) task_cost task_deadline Job (ct_decidable_eq Job))).
Theorem Schedulability_cumulative_service_after_task_deadline_zero_correspondence (Task Job : eqType) :
  PropSPropRel (src_cumulative_service_after_task_deadline_zero Task Job) (tgt_cumulative_service_after_task_deadline_zero Task Job).
Proof.
  unfold src_cumulative_service_after_task_deadline_zero, tgt_cumulative_service_after_task_deadline_zero.
  apply: cs_forall_par => tcR tcL Htc. apply: cs_forall_par => tdR tdL Htd.
  apply: cs_forall_par => jaR jaL Hja. apply: cs_forall_par => cR cL Hc. apply: cs_forall_par => dR dL Hd.
  apply: ct_forall_identity => job_task. apply: csch_forall_arr => aR aL Ha.
  apply: cs_forall_ncpus_sched => nR nL Hn sR sL Hs.
  apply: ct_imp; first exact (cf_Schedule_completed_jobs_dont_execute Job nR nL Hn sR sL Hs cR cL Hc).
  apply: ct_forall_identity => tsk.
  apply: ct_imp; first exact (tmnd Task Job nR nL Hn sR sL Hs jaR jaL cR cL dR dL Hja Hc Hd job_task aR aL Ha tsk).
  apply: ct_forall_identity => j.
  apply: ct_imp; first exact (cs_arrives_in Job aR aL Ha j).
  apply: ct_imp; first exact (ct_eq_rel Task (job_task j) tsk).
  apply: ct_imp; first exact (csch_valid_sporadic_job Task Job tcR tcL Htc tdR tdL Htd cR cL Hc dR dL Hd job_task j).
  apply: ct_forall_nat => t1R t1L H1. apply: ct_forall_nat => t2R t2L H2.
  apply: ct_imp; first exact (sub_nat_le_correspondence _ _ _ _ (sub_add_correspondence _ _ _ _ (Hja j) (Htd tsk)) H1).
  exact (sub_nat_eq_correspondence _ _ _ _ (cs_ico _ _ _ _ _ _ H1 H2 (cs_service_at_fun Job nR nL Hn sR sL Hs j))
           (sub_nat_rel_canonical 0)).
Qed.
