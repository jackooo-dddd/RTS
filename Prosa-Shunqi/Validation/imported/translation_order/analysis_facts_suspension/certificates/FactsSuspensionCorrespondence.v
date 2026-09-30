From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq bigop.
From prosa Require Import FactsSuspensionSemanticSource.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedFactsSuspension ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence
  JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations
  JitterSvcScheduleOperations JitterSvcJobOperations ProgressHelpers SuspensionCorrespondence.

Module I := ImportedFactsSuspension.
Module S := FactsSuspensionSemanticSource.FactsSuspensionSemanticSource.

(** Statement certificates for [analysis/facts/suspension.v].  For related
    processor states (the accepted two-sided [SvcProcessorStateRel]),
    schedules, job-arrival, job-cost and job-suspension instances and arrival
    sequences (the accepted relations, each with two-way totals), each
    extracted source statement (the authoritative elaborated type, specialised
    at these inputs) and the imported Lean theorem type are related; jobs are
    an identity carrier and instants, durations and service levels are
    covered in both directions by [SubNatRel].  The section-local readiness
    instance is the accepted [suspension_ready_instance] on both sides; its
    readiness is related through the accepted [suspension_has_passed] and
    [completed_by] relations.  The filtered interval sums go through
    [big_mkcond] and the accepted interval-sum relation. *)

Ltac body_of f := let T := type of f in match T with _ -> ?B => exact B end.
Ltac type_of_term t := let T := type of t in exact T.

(** ** Nat-list membership (the Nat-list form of the accepted membership relation) *)

Fixpoint fs_nat_list_to_rocq (xs : I.List_inst1 Lean.Nat) : seq nat :=
  match xs with
  | I.List_nil_inst1 => [::]
  | I.List_cons_inst1 x tail => sub_nat_to_rocq x :: fs_nat_list_to_rocq tail
  end.

Lemma fs_nat_list_source_roundtrip (xs : seq nat) :
  Logic.eq (fs_nat_list_to_rocq (svc_nat_list_to_imported xs)) xs.
Proof.
  elim: xs => [|x xs IH]; first reflexivity.
  cbn [fs_nat_list_to_rocq svc_nat_list_to_imported].
  rewrite sub_nat_rocq_roundtrip IH. reflexivity.
Qed.

Definition fs_target_mem (x : Lean.Nat) (xs : I.List_inst1 Lean.Nat) : SProp :=
  I.Membership_mem_inst3 Lean.Nat (I.List_inst1 Lean.Nat) (I.List_instMembership_inst1 Lean.Nat) xs x.

Definition fs_target_mem_list_transport (x : Lean.Nat) (xs ys : I.List_inst1 Lean.Nat) :
  Lean.eq xs ys -> fs_target_mem x xs -> fs_target_mem x ys :=
  fun Hxy Hmem =>
    match Hxy in Lean.eq _ zs return fs_target_mem x xs -> fs_target_mem x zs with
    | Lean.eq_refl => fun H => H
    end Hmem.

Definition fs_target_mem_element_transport (x y : Lean.Nat) (xs : I.List_inst1 Lean.Nat) :
  Lean.eq x y -> fs_target_mem x xs -> fs_target_mem y xs :=
  fun Hxy Hmem =>
    match Hxy in Lean.eq _ z return fs_target_mem x xs -> fs_target_mem z xs with
    | Lean.eq_refl => fun H => H
    end Hmem.

Definition fs_mem_head_of_source_eq (x y : nat) (xs : I.List_inst1 Lean.Nat) :
  Logic.eq x y ->
  I.List_Mem_inst1 Lean.Nat (sub_nat_to_imported x)
    (I.List_cons_inst1 Lean.Nat (sub_nat_to_imported y) xs) :=
  fun H => match H in Logic.eq _ z return
      I.List_Mem_inst1 Lean.Nat (sub_nat_to_imported x)
        (I.List_cons_inst1 Lean.Nat (sub_nat_to_imported z) xs)
    with
    | Logic.eq_refl => I.List_Mem_head_inst1 Lean.Nat (sub_nat_to_imported x) xs
    end.

Definition fs_eq_refl_truth (x : nat) : SubNatTruth (x == x).
Proof. rewrite eqxx. exact sub_nat_truth_intro. Defined.

Definition fs_mem_head_truth (a b : bool) : SubNatTruth a -> SubNatTruth (a || b) :=
  match a, b return SubNatTruth a -> SubNatTruth (a || b) with
  | true, _ => fun _ => sub_nat_truth_intro
  | false, _ => sub_nat_false_elim _
  end.

Definition fs_mem_tail_truth (a b : bool) : SubNatTruth b -> SubNatTruth (a || b) :=
  match a, b return SubNatTruth b -> SubNatTruth (a || b) with
  | true, _ => fun _ => sub_nat_truth_intro
  | false, true => fun _ => sub_nat_truth_intro
  | false, false => fun H => H
  end.

Fixpoint fs_source_mem_forward (x : nat) (xs : seq nat) :
  SubNatTruth (x \in xs) ->
  I.List_Mem_inst1 Lean.Nat (sub_nat_to_imported x) (svc_nat_list_to_imported xs) :=
  match xs as zs return SubNatTruth (x \in zs) ->
      I.List_Mem_inst1 Lean.Nat (sub_nat_to_imported x) (svc_nat_list_to_imported zs)
  with
  | [::] => sub_nat_false_elim _
  | y :: ys =>
      match @eqP _ x y as r in reflect _ b return
        SubNatTruth (b || (x \in ys)) ->
        I.List_Mem_inst1 Lean.Nat (sub_nat_to_imported x)
          (I.List_cons_inst1 Lean.Nat (sub_nat_to_imported y) (svc_nat_list_to_imported ys))
      with
      | ReflectT Hxy => fun _ => fs_mem_head_of_source_eq x y _ Hxy
      | ReflectF _ => fun H =>
          I.List_Mem_tail_inst1 Lean.Nat (sub_nat_to_imported x) (sub_nat_to_imported y) _
            (fs_source_mem_forward x ys H)
      end
  end.

Fixpoint fs_target_mem_decoded (x : Lean.Nat) (xs : I.List_inst1 Lean.Nat)
    (H : I.List_Mem_inst1 Lean.Nat x xs) :
  SubNatTruth (sub_nat_to_rocq x \in fs_nat_list_to_rocq xs) :=
  match H with
  | I.List_Mem_head_inst1 ys => fs_mem_head_truth _ _ (fs_eq_refl_truth (sub_nat_to_rocq x))
  | I.List_Mem_tail_inst1 y ys Htail => fs_mem_tail_truth _ _ (fs_target_mem_decoded x ys Htail)
  end.

Definition fs_source_mem_truth_transport (x : nat) (xs ys : seq nat) :
  Logic.eq xs ys -> SubNatTruth (x \in xs) -> SubNatTruth (x \in ys) :=
  fun H Htruth =>
    match H in Logic.eq _ zs return SubNatTruth (x \in xs) -> SubNatTruth (x \in zs) with
    | Logic.eq_refl => fun Ht => Ht
    end Htruth.

Lemma fs_membership_correspondence xR xL xsR xsL :
  SubNatRel xR xL -> SvcNatListRel xsR xsL ->
  PropSPropRel (xR \in xsR) (fs_target_mem xL xsL).
Proof.
  intros Hx Hxs. apply prop_sprop_rel_intro.
  - intro Hmem. unfold fs_target_mem.
    apply (fs_target_mem_element_transport (sub_nat_to_imported xR) xL xsL Hx).
    apply (fs_target_mem_list_transport (sub_nat_to_imported xR) (svc_nat_list_to_imported xsR) xsL Hxs).
    apply fs_source_mem_forward.
    exact (sub_nat_prop_to_truth _ Hmem).
  - intro Hmem. apply sub_nat_truth_to_strict_prop.
    apply (fs_source_mem_truth_transport xR _ _ (fs_nat_list_source_roundtrip xsR)).
    rewrite -{1}(sub_nat_rocq_roundtrip xR).
    apply fs_target_mem_decoded.
    apply (fs_target_mem_element_transport xL (sub_nat_to_imported xR) (svc_nat_list_to_imported xsR)
      (sub_imported_eq_sym _ _ Hx)).
    apply (fs_target_mem_list_transport xL xsL (svc_nat_list_to_imported xsR)
      (sub_imported_eq_sym _ _ Hxs)).
    exact Hmem.
Qed.

(** ** Connectives *)

Lemma fs_and_prop_correspondence (P Q : Prop) (PL QL : SProp) :
  PropSPropRel P PL -> PropSPropRel Q QL -> PropSPropRel (P /\ Q) (Lean.And PL QL).
Proof. exact (ar_and_correspondence P Q PL QL). Qed.

Lemma fs_exists2_nat_correspondence (PR QR : nat -> Prop) (PL QL : Lean.Nat -> SProp) :
  (forall nR nL, SubNatRel nR nL -> PropSPropRel (PR nR) (PL nL)) ->
  (forall nR nL, SubNatRel nR nL -> PropSPropRel (QR nR) (QL nL)) ->
  PropSPropRel (exists2 n, PR n & QR n) (I.Exists Lean.Nat (fun n => Lean.And (PL n) (QL n))).
Proof.
  intros HP HQ.
  have H := ar_exists_nat_correspondence (fun n => PR n /\ QR n) (fun n => Lean.And (PL n) (QL n))
    (fun nR nL Hn => fs_and_prop_correspondence _ _ _ _ (HP nR nL Hn) (HQ nR nL Hn)).
  apply prop_sprop_rel_intro.
  - intros [n Hp Hq]. exact (prop_to_sprop _ _ H (ex_intro _ n (conj Hp Hq))).
  - intro HL. apply strictly_inhabits.
    have [n [Hp Hq]] := sprop_to_prop _ _ H HL. exact (ex_intro2 _ _ n Hp Hq).
Qed.

Lemma fs_ite_related (bR : bool) (P : SProp) (d : I.Decidable P) (aR : nat) (aL : Lean.Nat) :
  PropSPropRel (is_true bR) P -> SubNatRel aR aL ->
  SubNatRel (if bR then aR else O) (I.ite Lean.Nat P d aL svc_target_zero).
Proof.
  intros HP Ha. have Hb := svc_decide_bool_correspondence bR P d HP.
  destruct d as [Hf|Ht]; destruct bR; cbn in *;
    try exact Ha; try exact (sub_nat_rel_canonical O);
    try exact (svc_false_elim _ (svc_false_ne_true Hb));
    try exact (svc_false_elim _ (svc_false_ne_true (sub_imported_eq_sym _ _ Hb))).
Qed.

Lemma fs_eqn_prop_related aR aL bR bL :
  SubNatRel aR aL -> SubNatRel bR bL -> PropSPropRel (is_true (aR == bR)) (Lean.eq aL bL).
Proof.
  intros Ha Hb. have H := sub_nat_eq_correspondence aR aL bR bL Ha Hb.
  apply prop_sprop_rel_intro.
  - intro E. exact (prop_to_sprop _ _ H (eqP E)).
  - intro E. apply strictly_inhabits. apply/eqP. exact (sprop_to_prop _ _ H E).
Qed.

Lemma fs_nat_of_bool_related (bR : bool) (bL : I.Bool) :
  SvcBoolRel bR bL -> SubNatRel (nat_of_bool bR) (I.Bool_toNat bL).
Proof.
  intro Hb. destruct Hb. destruct bR; exact (@Lean.eq_refl _ _).
Qed.

Section FactsSuspension.
  Context (Job : eqType).
  Let dJ := svc_decidable_eq Job.
  Context (PStateR : prosa.behavior.schedule.ProcessorState Job).
  Variable PStateL : I.Prosa_Behavior_Schedule_ProcessorState Job dJ.
  Variable R : SvcProcessorStateRel Job PStateR PStateL.
  Variable schedR : @prosa.behavior.schedule.schedule Job PStateR.
  Variable schedL : I.Prosa_Behavior_Schedule_schedule Job dJ PStateL.
  Hypothesis Hsched : SvcScheduleRel Job PStateR PStateL R schedR schedL.
  Variable jaR : prosa.behavior.job.JobArrival Job.
  Variable jaL : I.Prosa_Behavior_Job_JobArrival Job dJ.
  Hypothesis Hja : SvcJobArrivalRel Job jaR jaL.
  Variable costR : prosa.behavior.job.JobCost Job.
  Variable costL : I.Prosa_Behavior_Job_JobCost Job dJ.
  Hypothesis Hcost : SvcJobCostRel Job costR costL.
  Variable sR : prosa.model.readiness.suspension.JobSuspension Job.
  Variable sL : I.Prosa_Model_Readiness_Suspension_JobSuspension Job dJ.
  Hypothesis Hs : SuspJobSuspensionRel Job sR sL.

  Let readyR := @prosa.model.readiness.suspension.suspension_ready_instance Job PStateR jaR costR sR.
  Let readyL := I.Prosa_Model_Readiness_Suspension_suspension_ready_instance Job dJ PStateL jaL costL sL.

  Lemma fs_suspended_related (j : Job) tR tL : SubNatRel tR tL ->
    SvcBoolRel (@prosa.model.readiness.suspension.suspended Job PStateR jaR costR sR schedR j tR)
      (I.Prosa_Model_Readiness_Suspension_suspended Job dJ PStateL jaL costL sL schedL j tL).
  Proof.
    exact (suspended_correspondence Job PStateR PStateL R schedR schedL Hsched jaR jaL Hja
      costR costL Hcost sR sL Hs j tR tL).
  Qed.

  Lemma fs_service_related (j : Job) tR tL : SubNatRel tR tL ->
    SubNatRel (@prosa.behavior.service.service Job PStateR schedR j tR)
      (I.Prosa_Behavior_Service_service Job dJ PStateL schedL j tL).
  Proof. exact (pg_service_related Job PStateR PStateL R schedR schedL Hsched j tR tL). Qed.

  Lemma fs_ready_related (j : Job) tR tL : SubNatRel tR tL ->
    SvcBoolRel (@prosa.behavior.ready.job_ready Job PStateR costR jaR readyR schedR j tR)
      (I.Prosa_Behavior_Ready_JobReady_job_ready Job dJ PStateL costL jaL readyL schedL j tL).
  Proof.
    intro Ht.
    exact (svc_bool_and_related _ _ _ _
      (suspension_has_passed_correspondence Job PStateR PStateL R schedR schedL Hsched jaR jaL Hja
        sR sL Hs j tR tL Ht)
      (svc_bool_not_related _ _ (susp_completed_by_related Job PStateR PStateL R schedR schedL Hsched
        costR costL Hcost j tR tL Ht))).
  Qed.

  Lemma fs_scheduled_related (j : Job) tR tL : SubNatRel tR tL ->
    SvcBoolRel (@prosa.behavior.service.scheduled_at Job PStateR schedR j tR)
      (I.Prosa_Behavior_Service_scheduled_at Job dJ PStateL schedL j tL).
  Proof.
    intro Ht. exact (svc_scheduled_in_related Job PStateR PStateL R j _ _ (Hsched tR tL Ht)).
  Qed.

  Lemma fs_between_related t1R t1L tR tL t2R t2L :
    SubNatRel t1R t1L -> SubNatRel tR tL -> SubNatRel t2R t2L ->
    SvcBoolRel ((leq t1R tR) && (ltn tR t2R))
      (I.Bool_and (svc_target_decide_le t1L tL) (svc_target_decide_lt tL t2L)).
  Proof.
    intros H1 H H2.
    exact (svc_bool_and_related _ _ _ _ (svc_decide_le_related _ _ _ _ H1 H) (svc_decide_lt_related _ _ _ _ H H2)).
  Qed.

  Lemma fs_suspended_at_service_related (j : Job) tR tL rR rL :
    SubNatRel tR tL -> SubNatRel rR rL ->
    SvcBoolRel (@prosa.model.readiness.suspension.suspended Job PStateR jaR costR sR schedR j tR
        && (@prosa.behavior.service.service Job PStateR schedR j tR == rR))
      (I.Bool_and (I.Prosa_Model_Readiness_Suspension_suspended Job dJ PStateL jaL costL sL schedL j tL)
        (svc_target_decide_eq (I.Prosa_Behavior_Service_service Job dJ PStateL schedL j tL) rL)).
  Proof.
    intros Ht Hr.
    exact (svc_bool_and_related _ _ _ _ (fs_suspended_related j tR tL Ht)
      (svc_decide_eq_related _ _ _ _ (fs_service_related j tR tL Ht) Hr)).
  Qed.

  (** The filtered interval sum of the suspension indicator. *)
  Lemma fs_filtered_sum_related (j : Job) aR aL bR bL rR rL :
    SubNatRel aR aL -> SubNatRel bR bL -> SubNatRel rR rL ->
    SubNatRel (\sum_(aR <= t < bR | @prosa.behavior.service.service Job PStateR schedR j t == rR)
        @prosa.model.readiness.suspension.suspended Job PStateR jaR costR sR schedR j t)
      (svc_target_interval_value aL bL (fun t =>
        I.ite Lean.Nat (Lean.eq (I.Prosa_Behavior_Service_service Job dJ PStateL schedL j t) rL)
          (I.instDecidableEqNat (I.Prosa_Behavior_Service_service Job dJ PStateL schedL j t) rL)
          (I.Bool_toNat (I.Prosa_Model_Readiness_Suspension_suspended Job dJ PStateL jaL costL sL schedL j t))
          svc_target_zero)).
  Proof.
    intros Ha Hb Hr. rewrite big_mkcond /=.
    apply svc_interval_sum_related; [exact Ha | exact Hb |].
    intros tR tL Ht.
    apply fs_ite_related.
    - exact (fs_eqn_prop_related _ _ _ _ (fs_service_related j tR tL Ht) Hr).
    - exact (fs_nat_of_bool_related _ _ (fs_suspended_related j tR tL Ht)).
  Qed.

  (** ** Statement correspondences *)

  Ltac fs_forall_nat := apply pg_forall_nat_correspondence; intros ? ? ?.

  Definition src_suspended_implies_job_not_ready : Prop :=
    ltac:(body_of (fun s : S.statement_suspended_implies_job_not_ready => s Job jaR costR sR PStateR schedR)).
  Definition tgt_suspended_implies_job_not_ready : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Suspension_suspended_implies_job_not_ready Job dJ jaL costL sL PStateL schedL)).
  Theorem suspended_implies_job_not_ready_correspondence :
    PropSPropRel src_suspended_implies_job_not_ready tgt_suspended_implies_job_not_ready.
  Proof.
    unfold src_suspended_implies_job_not_ready, tgt_suspended_implies_job_not_ready.
    apply pg_forall_identity_correspondence; intro j.
    apply pg_forall_nat_correspondence; intros tR tL Ht.
    apply pg_imp_correspondence.
    - exact (svc_bool_truth_correspondence _ _ (fs_suspended_related j tR tL Ht)).
    - exact (svc_bool_truth_correspondence _ _ (svc_bool_not_related _ _ (fs_ready_related j tR tL Ht))).
  Qed.

  Section Arr.
    Variable arrR : prosa.behavior.arrival_sequence.arrival_sequence Job.
    Variable arrL : I.Prosa_Behavior_Arrival_sequence_arrival_sequence Job dJ.
    Hypothesis Harr : ArArrivalSequenceRel Job arrR arrL.

    Lemma fs_valid_schedule_related :
      PropSPropRel (@prosa.behavior.ready.valid_schedule Job jaR PStateR schedR costR readyR arrR)
        (I.Prosa_Behavior_Ready_valid_schedule Job dJ jaL PStateL schedL costL readyL arrL).
    Proof.
      unfold prosa.behavior.ready.valid_schedule, prosa.behavior.ready.jobs_must_be_ready_to_execute,
        prosa.behavior.ready.jobs_come_from_arrival_sequence.
      cbn [I.Prosa_Behavior_Ready_valid_schedule I.Prosa_Behavior_Ready_jobs_must_be_ready_to_execute
        I.Prosa_Behavior_Ready_jobs_come_from_arrival_sequence].
      apply fs_and_prop_correspondence.
      - apply pg_forall_identity_correspondence; intro j.
        apply pg_forall_nat_correspondence; intros tR tL Ht.
        apply pg_imp_correspondence.
        + exact (svc_bool_truth_correspondence _ _ (fs_scheduled_related j tR tL Ht)).
        + exact (arrives_in_correspondence_certificate Job arrR arrL j Harr).
      - apply pg_forall_identity_correspondence; intro j.
        apply pg_forall_nat_correspondence; intros tR tL Ht.
        apply pg_imp_correspondence.
        + exact (svc_bool_truth_correspondence _ _ (fs_scheduled_related j tR tL Ht)).
        + exact (svc_bool_truth_correspondence _ _ (fs_ready_related j tR tL Ht)).
    Qed.

    Definition src_suspended_implies_not_scheduled : Prop :=
      ltac:(body_of (fun s : S.statement_suspended_implies_not_scheduled => s Job jaR costR sR arrR PStateR schedR)).
    Definition tgt_suspended_implies_not_scheduled : SProp :=
      ltac:(type_of_term (@I.Prosa_Analysis_Facts_Suspension_suspended_implies_not_scheduled
        Job dJ jaL costL sL PStateL schedL arrL)).
    Theorem suspended_implies_not_scheduled_correspondence :
      PropSPropRel src_suspended_implies_not_scheduled tgt_suspended_implies_not_scheduled.
    Proof.
      unfold src_suspended_implies_not_scheduled, tgt_suspended_implies_not_scheduled.
      apply pg_imp_correspondence; [exact fs_valid_schedule_related|].
      apply pg_forall_identity_correspondence; intro j.
      apply pg_forall_nat_correspondence; intros tR tL Ht.
      apply pg_imp_correspondence.
      - exact (svc_bool_truth_correspondence _ _ (fs_suspended_related j tR tL Ht)).
      - exact (svc_bool_truth_correspondence _ _ (svc_bool_not_related _ _ (fs_scheduled_related j tR tL Ht))).
    Qed.
  End Arr.

  Definition src_suspended_implies_arrived : Prop :=
    ltac:(body_of (fun s : S.statement_suspended_implies_arrived => s Job jaR costR sR PStateR schedR)).
  Definition tgt_suspended_implies_arrived : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Suspension_suspended_implies_arrived Job dJ jaL costL sL PStateL schedL)).
  Theorem suspended_implies_arrived_correspondence :
    PropSPropRel src_suspended_implies_arrived tgt_suspended_implies_arrived.
  Proof.
    unfold src_suspended_implies_arrived, tgt_suspended_implies_arrived.
    apply pg_forall_identity_correspondence; intro j.
    apply pg_forall_nat_correspondence; intros tR tL Ht.
    apply pg_imp_correspondence.
    - exact (svc_bool_truth_correspondence _ _ (fs_suspended_related j tR tL Ht)).
    - exact (svc_bool_truth_correspondence _ _ (svc_has_arrived_related Job jaR jaL j Hja tR tL Ht)).
  Qed.

  Definition src_suspended_implies_pending : Prop :=
    ltac:(body_of (fun s : S.statement_suspended_implies_pending => s Job jaR costR sR PStateR schedR)).
  Definition tgt_suspended_implies_pending : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Suspension_suspended_implies_pending Job dJ jaL costL sL PStateL schedL)).
  Theorem suspended_implies_pending_correspondence :
    PropSPropRel src_suspended_implies_pending tgt_suspended_implies_pending.
  Proof.
    unfold src_suspended_implies_pending, tgt_suspended_implies_pending.
    apply pg_forall_identity_correspondence; intro j.
    apply pg_forall_nat_correspondence; intros tR tL Ht.
    apply pg_imp_correspondence.
    - exact (svc_bool_truth_correspondence _ _ (fs_suspended_related j tR tL Ht)).
    - exact (svc_bool_truth_correspondence _ _ (susp_pending_related Job PStateR PStateL R schedR schedL Hsched
        jaR jaL Hja costR costL Hcost j tR tL Ht)).
  Qed.

  Definition src_suspended_implies_not_backlogged : Prop :=
    ltac:(body_of (fun s : S.statement_suspended_implies_not_backlogged => s Job jaR costR sR PStateR schedR)).
  Definition tgt_suspended_implies_not_backlogged : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Suspension_suspended_implies_not_backlogged Job dJ jaL costL sL PStateL schedL)).
  Theorem suspended_implies_not_backlogged_correspondence :
    PropSPropRel src_suspended_implies_not_backlogged tgt_suspended_implies_not_backlogged.
  Proof.
    unfold src_suspended_implies_not_backlogged, tgt_suspended_implies_not_backlogged.
    apply pg_forall_identity_correspondence; intro j.
    apply pg_forall_nat_correspondence; intros tR tL Ht.
    apply pg_imp_correspondence.
    - exact (svc_bool_truth_correspondence _ _ (fs_suspended_related j tR tL Ht)).
    - exact (svc_bool_truth_correspondence _ _ (svc_bool_not_related _ _
        (svc_bool_and_related _ _ _ _ (fs_ready_related j tR tL Ht)
          (svc_bool_not_related _ _ (fs_scheduled_related j tR tL Ht))))).
  Qed.

  Definition src_pending_and_not_suspended_implies_ready : Prop :=
    ltac:(body_of (fun s : S.statement_pending_and_not_suspended_implies_ready => s Job jaR costR sR PStateR schedR)).
  Definition tgt_pending_and_not_suspended_implies_ready : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Suspension_pending_and_not_suspended_implies_ready Job dJ jaL costL sL PStateL schedL)).
  Theorem pending_and_not_suspended_implies_ready_correspondence :
    PropSPropRel src_pending_and_not_suspended_implies_ready tgt_pending_and_not_suspended_implies_ready.
  Proof.
    unfold src_pending_and_not_suspended_implies_ready, tgt_pending_and_not_suspended_implies_ready.
    apply pg_forall_identity_correspondence; intro j.
    apply pg_forall_nat_correspondence; intros tR tL Ht.
    apply pg_imp_correspondence.
    - exact (svc_bool_truth_correspondence _ _ (susp_pending_related Job PStateR PStateL R schedR schedL Hsched
        jaR jaL Hja costR costL Hcost j tR tL Ht)).
    - apply pg_imp_correspondence.
      + exact (svc_bool_truth_correspondence _ _ (svc_bool_not_related _ _ (fs_suspended_related j tR tL Ht))).
      + exact (svc_bool_truth_correspondence _ _ (fs_ready_related j tR tL Ht)).
  Qed.

  (** The common premises of the three step lemmas. *)
  Lemma fs_step_premises (j : Job) t1R t1L t2R t2L rR rL tfR tfL
      (H1 : SubNatRel t1R t1L) (H2 : SubNatRel t2R t2L) (Hr : SubNatRel rR rL) (Hf : SubNatRel tfR tfL)
      (PR : Prop) (PL : SProp) :
    PropSPropRel PR PL ->
    PropSPropRel
      (is_true ((leq t1R tfR) && (ltn tfR t2R)) ->
        @prosa.model.readiness.suspension.suspended Job PStateR jaR costR sR schedR j tfR ->
        @prosa.behavior.service.service Job PStateR schedR j tfR = rR -> PR)
      (Lean.eq (I.Bool_and (svc_target_decide_le t1L tfL) (svc_target_decide_lt tfL t2L)) I.Bool_true ->
        Lean.eq (I.Prosa_Model_Readiness_Suspension_suspended Job dJ PStateL jaL costL sL schedL j tfL) I.Bool_true ->
        Lean.eq (I.Prosa_Behavior_Service_service Job dJ PStateL schedL j tfL) rL -> PL).
  Proof.
    intro HP.
    apply pg_imp_correspondence; [exact (svc_bool_truth_correspondence _ _ (fs_between_related _ _ _ _ _ _ H1 Hf H2))|].
    apply pg_imp_correspondence; [exact (svc_bool_truth_correspondence _ _ (fs_suspended_related j _ _ Hf))|].
    apply pg_imp_correspondence; [exact (sub_nat_eq_correspondence _ _ _ _ (fs_service_related j _ _ Hf) Hr)|].
    exact HP.
  Qed.

  Definition src_suspension_bounded_trivial : Prop :=
    ltac:(body_of (fun s : S.statement_suspension_bounded_trivial => s Job jaR costR sR PStateR schedR)).
  Definition tgt_suspension_bounded_trivial : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Suspension_suspension_bounded_trivial Job dJ jaL costL sL PStateL schedL)).
  Theorem suspension_bounded_trivial_correspondence :
    PropSPropRel src_suspension_bounded_trivial tgt_suspension_bounded_trivial.
  Proof.
    unfold src_suspension_bounded_trivial, tgt_suspension_bounded_trivial.
    apply pg_forall_identity_correspondence; intro j.
    apply pg_forall_nat_correspondence; intros t1R t1L H1.
    apply pg_forall_nat_correspondence; intros t2R t2L H2.
    apply pg_forall_nat_correspondence; intros rR rL Hr.
    apply pg_forall_nat_correspondence; intros tfR tfL Hf.
    apply (fs_step_premises j _ _ _ _ _ _ _ _ H1 H2 Hr Hf).
    apply pg_imp_correspondence.
    - exact (sub_nat_le_correspondence _ _ _ _ (svc_target_sub_related _ _ _ _ H2 Hf) (Hs j _ _ Hr)).
    - exact (sub_nat_le_correspondence _ _ _ _ (fs_filtered_sum_related j _ _ _ _ _ _ Hf H2 Hr) (Hs j _ _ Hr)).
  Qed.

  Definition src_suspension_bounded_longer_interval : Prop :=
    ltac:(body_of (fun s : S.statement_suspension_bounded_longer_interval => s Job jaR costR sR PStateR schedR)).
  Definition tgt_suspension_bounded_longer_interval : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Suspension_suspension_bounded_longer_interval Job dJ jaL costL sL PStateL schedL)).
  Theorem suspension_bounded_longer_interval_correspondence :
    PropSPropRel src_suspension_bounded_longer_interval tgt_suspension_bounded_longer_interval.
  Proof.
    unfold src_suspension_bounded_longer_interval, tgt_suspension_bounded_longer_interval.
    apply pg_forall_identity_correspondence; intro j.
    apply pg_forall_nat_correspondence; intros t1R t1L H1.
    apply pg_forall_nat_correspondence; intros t2R t2L H2.
    apply pg_forall_nat_correspondence; intros rR rL Hr.
    apply pg_forall_nat_correspondence; intros tfR tfL Hf.
    apply (fs_step_premises j _ _ _ _ _ _ _ _ H1 H2 Hr Hf).
    apply pg_imp_correspondence.
    - exact (sub_nat_lt_correspondence _ _ _ _ (Hs j _ _ Hr) (svc_target_sub_related _ _ _ _ H2 Hf)).
    - exact (sub_nat_le_correspondence _ _ _ _ (fs_filtered_sum_related j _ _ _ _ _ _ Hf H2 Hr) (Hs j _ _ Hr)).
  Qed.

  Lemma fs_before_related (j : Job) t1R t1L tfR tfL rR rL :
    SubNatRel t1R t1L -> SubNatRel tfR tfL -> SubNatRel rR rL ->
    PropSPropRel
      (forall t0 : nat, is_true ((leq t1R t0) && (ltn t0 tfR)) ->
        ~~ (@prosa.model.readiness.suspension.suspended Job PStateR jaR costR sR schedR j t0
          && (@prosa.behavior.service.service Job PStateR schedR j t0 == rR)))
      (forall t0 : Lean.Nat,
        Lean.eq (I.Bool_and (svc_target_decide_le t1L t0) (svc_target_decide_lt t0 tfL)) I.Bool_true ->
        Lean.eq (I.Bool_not (I.Bool_and (I.Prosa_Model_Readiness_Suspension_suspended Job dJ PStateL jaL costL sL schedL j t0)
          (svc_target_decide_eq (I.Prosa_Behavior_Service_service Job dJ PStateL schedL j t0) rL))) I.Bool_true).
  Proof.
    intros H1 Hf Hr.
    apply pg_forall_nat_correspondence; intros tR tL Ht.
    apply pg_imp_correspondence.
    - exact (svc_bool_truth_correspondence _ _ (fs_between_related _ _ _ _ _ _ H1 Ht Hf)).
    - exact (svc_bool_truth_correspondence _ _ (svc_bool_not_related _ _
        (fs_suspended_at_service_related j _ _ _ _ Ht Hr))).
  Qed.

  Definition src_suspension_bounded_in_interval_aux : Prop :=
    ltac:(body_of (fun s : S.statement_suspension_bounded_in_interval_aux => s Job jaR costR sR PStateR schedR)).
  Definition tgt_suspension_bounded_in_interval_aux : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Suspension_suspension_bounded_in_interval_aux Job dJ jaL costL sL PStateL schedL)).
  Theorem suspension_bounded_in_interval_aux_correspondence :
    PropSPropRel src_suspension_bounded_in_interval_aux tgt_suspension_bounded_in_interval_aux.
  Proof.
    unfold src_suspension_bounded_in_interval_aux, tgt_suspension_bounded_in_interval_aux.
    apply pg_forall_identity_correspondence; intro j.
    apply pg_forall_nat_correspondence; intros t1R t1L H1.
    apply pg_forall_nat_correspondence; intros t2R t2L H2.
    apply pg_forall_nat_correspondence; intros rR rL Hr.
    apply pg_forall_nat_correspondence; intros tfR tfL Hf.
    apply (fs_step_premises j _ _ _ _ _ _ _ _ H1 H2 Hr Hf).
    apply pg_imp_correspondence.
    - exact (fs_before_related j _ _ _ _ _ _ H1 Hf Hr).
    - exact (sub_nat_le_correspondence _ _ _ _ (fs_filtered_sum_related j _ _ _ _ _ _ H1 H2 Hr) (Hs j _ _ Hr)).
  Qed.

  Definition src_exists_some_point : Prop :=
    ltac:(body_of (fun s : S.statement_exists_some_point => s Job jaR costR sR PStateR schedR)).
  Definition tgt_exists_some_point : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Suspension_exists_some_point Job dJ jaL costL sL PStateL schedL)).
  Theorem exists_some_point_correspondence :
    PropSPropRel src_exists_some_point tgt_exists_some_point.
  Proof.
    unfold src_exists_some_point, tgt_exists_some_point.
    apply pg_forall_identity_correspondence; intro j.
    apply pg_forall_nat_correspondence; intros t1R t1L H1.
    apply pg_forall_nat_correspondence; intros t2R t2L H2.
    apply pg_forall_nat_correspondence; intros rR rL Hr.
    apply pg_imp_correspondence.
    - apply fs_exists2_nat_correspondence; intros tR tL Ht.
      + apply svc_bool_truth_correspondence. apply svc_decide_bool_correspondence.
        exact (fs_membership_correspondence _ _ _ _ Ht
          (svc_range_related _ _ _ _ H1 (svc_target_sub_related _ _ _ _ H2 H1))).
      + exact (svc_bool_truth_correspondence _ _ (fs_suspended_at_service_related j _ _ _ _ Ht Hr)).
    - apply ar_exists_nat_correspondence; intros tR tL Ht.
      apply fs_and_prop_correspondence;
        [exact (svc_bool_truth_correspondence _ _ (fs_between_related _ _ _ _ _ _ H1 Ht H2))|].
      apply fs_and_prop_correspondence;
        [exact (svc_bool_truth_correspondence _ _ (fs_suspended_related j _ _ Ht))|].
      apply fs_and_prop_correspondence;
        [exact (sub_nat_eq_correspondence _ _ _ _ (fs_service_related j _ _ Ht) Hr)|].
      exact (fs_before_related j _ _ _ _ _ _ H1 Ht Hr).
  Qed.

  Definition src_suspension_bounded_in_interval : Prop :=
    ltac:(body_of (fun s : S.statement_suspension_bounded_in_interval => s Job jaR costR sR PStateR schedR)).
  Definition tgt_suspension_bounded_in_interval : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Suspension_suspension_bounded_in_interval Job dJ jaL costL sL PStateL schedL)).
  Theorem suspension_bounded_in_interval_correspondence :
    PropSPropRel src_suspension_bounded_in_interval tgt_suspension_bounded_in_interval.
  Proof.
    unfold src_suspension_bounded_in_interval, tgt_suspension_bounded_in_interval.
    apply pg_forall_identity_correspondence; intro j.
    apply pg_forall_nat_correspondence; intros t1R t1L H1.
    apply pg_forall_nat_correspondence; intros t2R t2L H2.
    apply pg_forall_nat_correspondence; intros rR rL Hr.
    exact (sub_nat_le_correspondence _ _ _ _ (fs_filtered_sum_related j _ _ _ _ _ _ H1 H2 Hr) (Hs j _ _ Hr)).
  Qed.
End FactsSuspension.
