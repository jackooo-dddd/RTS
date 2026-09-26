From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq fintype bigop.
From prosa Require Import FactsServiceOfJobsSemanticSource.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedFactsServiceOfJobs ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence ArrivalsCorrespondence
  JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations
  JitterSvcScheduleOperations JitterSvcJobOperations PreemptionParameterCorrespondence
  WorkloadCorrespondence ServiceOfJobsCorrespondence.

Module I := ImportedFactsServiceOfJobs.
Module S := FactsServiceOfJobsSemanticSource.FactsServiceOfJobsSemanticSource.
Module B := BusyIntervalClassicalSemanticSource.BusyIntervalClassicalSemanticSource.

(** Statement correspondences for [analysis/facts/model/service_of_jobs.v].

    Source side: the extracted statements [S.statement_X] specialised at
    their leading type-level inputs (job type, job arrival / job cost
    instances, processor state); target side: the imported Lean theorem
    types at related inputs ([ArJobArrivalRel], [SvcJobCostRel], the
    accepted two-sided [SvcProcessorStateRel]).  Every other binder is
    covered in both directions: schedules through the state conversion with
    its roundtrips, arrival sequences and job lists through the list
    conversion with its roundtrips, job predicates and JLFP policies
    pointwise on Booleans, processor states through the accepted state
    conversion; jobs are identity carriers, Nats are covered in both
    directions.  [service_of_jobs], [service_of_jobs_at],
    [total_service_of_jobs_in], [service_of_other_hep_jobs],
    [service_of_hep_jobs] and [workload_of_jobs] are closed by the accepted
    service-of-jobs and workload certificates; [quiet_time],
    [served_jobs_at] and [has] replay the accepted busy-interval and
    service-inversion proofs (with this artifact's kernel-checked
    [List.any] constructor equations); the two half-open interval sums are
    related through the accepted [svc_interval_sum_related] against the
    kernel-guarded [List.foldr] form of the exported theorem types.  No
    source or target theorem is used. *)

Ltac body_of f := let T := type of f in match T with _ -> ?B => exact B end.
Ltac type_of_term t := let T := type of t in exact T.

Lemma fsoj_forall_cover_sprop (A B : Type) (Rel : A -> B -> SProp)
    (toB : A -> B) (toA : B -> A)
    (HtoB : forall a, Rel a (toB a)) (HtoA : forall b, Rel (toA b) b)
    (PR : A -> Prop) (PL : B -> SProp) :
  (forall a b, Rel a b -> PropSPropRel (PR a) (PL b)) ->
  PropSPropRel (forall a, PR a) (forall b, PL b).
Proof.
  intro H. apply prop_sprop_rel_intro.
  - intros HR b. exact (prop_to_sprop _ _ (H _ _ (HtoA b)) (HR (toA b))).
  - intro HL. apply strictly_inhabits. intro a.
    exact (sprop_to_prop _ _ (H _ _ (HtoB a)) (HL (toB a))).
Qed.

Lemma fsoj_lean_transport {A : Type} (P : A -> SProp) (x y : A) :
  Lean.eq x y -> P x -> P y.
Proof. intros H. destruct H. exact (fun p => p). Qed.

Lemma fsoj_nat_input (nR : nat) (nL : Lean.Nat) :
  SubNatRel nR nL -> Logic.eq (sub_nat_to_rocq nL) nR.
Proof.
  intro H. have E := f_equal sub_nat_to_rocq (imported_eq_to_coq_eq _ _ H).
  rewrite sub_nat_rocq_roundtrip in E. exact (Logic.eq_sym E).
Qed.

Lemma fsoj_eq_correspondence (T : Type) (x y : T) : PropSPropRel (x = y) (Lean.eq x y).
Proof.
  apply prop_sprop_rel_intro.
  - intro E. destruct E. exact (@Lean.eq_refl _ _).
  - intro E. apply strictly_inhabits. exact (imported_eq_to_coq_eq _ _ E).
Qed.

Lemma fsoj_bool_eq_correspondence (bR cR : bool) (bL cL : I.Bool) :
  ArBoolRel bR bL -> ArBoolRel cR cL -> PropSPropRel (bR = cR) (Lean.eq bL cL).
Proof.
  intros Hb Hc. apply prop_sprop_rel_intro.
  - intro E. destruct E.
    exact (sub_imported_eq_trans _ _ _ (sub_imported_eq_sym _ _ Hb) Hc).
  - intro E. apply strictly_inhabits.
    have EL := imported_eq_to_coq_eq _ _
      (sub_imported_eq_trans _ _ _ Hb (sub_imported_eq_trans _ _ _ E (sub_imported_eq_sym _ _ Hc))).
    destruct bR, cR; cbn in EL; solve [reflexivity | discriminate EL].
Qed.

Lemma fsoj_exists_identity (T : Type) (PR : T -> Prop) (PL : T -> SProp) :
  (forall x, PropSPropRel (PR x) (PL x)) ->
  PropSPropRel (exists x, PR x) (I.Exists T PL).
Proof.
  intro HP. apply prop_sprop_rel_intro.
  - intros [x Hx]. exact (I.Exists_intro T PL x (prop_to_sprop _ _ (HP x) Hx)).
  - intros [x Hx]. apply strictly_inhabits. exists x. exact (sprop_to_prop _ _ (HP x) Hx).
Qed.

Lemma fsoj_bool_to_nat_related (bR : bool) (bL : I.Bool) :
  ArBoolRel bR bL -> SubNatRel (nat_of_bool bR) (I.Bool_toNat bL).
Proof.
  intro Hb. unfold ArBoolRel in Hb.
  refine (sub_imported_eq_trans _ _ _ _ (sub_imported_eq_congr I.Bool_toNat _ _ Hb)).
  destruct bR; exact (@Lean.eq_refl _ _).
Qed.

Lemma fsoj_window_le_le aR aL bR bL cR cL :
  SubNatRel aR aL -> SubNatRel bR bL -> SubNatRel cR cL ->
  PropSPropRel (is_true (aR <= bR <= cR))
    (Lean.eq (I.Bool_and (ar_target_decide_le aL bL) (ar_target_decide_le bL cL)) I.Bool_true).
Proof.
  intros Ha Hb Hc.
  exact (ar_bool_truth_correspondence _ _
    (ar_bool_and_related _ _ _ _ (ar_decide_le_related _ _ _ _ Ha Hb)
      (ar_decide_le_related _ _ _ _ Hb Hc))).
Qed.

Lemma fsoj_window_le_lt aR aL bR bL cR cL :
  SubNatRel aR aL -> SubNatRel bR bL -> SubNatRel cR cL ->
  PropSPropRel (is_true (aR <= bR < cR))
    (Lean.eq (I.Bool_and (ar_target_decide_le aL bL) (ar_target_decide_lt bL cL)) I.Bool_true).
Proof.
  intros Ha Hb Hc.
  exact (ar_bool_truth_correspondence _ _
    (ar_bool_and_related _ _ _ _ (ar_decide_le_related _ _ _ _ Ha Hb)
      (ar_decide_lt_related _ _ _ _ Hb Hc))).
Qed.

Section Any.
  Context (X : Type).
  Variable PR : X -> bool.
  Variable PL : X -> I.Bool.
  Hypothesis HP : forall x, ArBoolRel (PR x) (PL x).

  Lemma fsoj_has_canonical (xs : seq X) :
    ArBoolRel (has PR xs) (I.List_any X (ar_list_to_imported xs) PL).
  Proof.
    induction xs as [|x xs IH].
    - exact (sub_imported_eq_sym _ _
        (I.Prosa_Validation_FactsServiceOfJobsInterface_production_any_nil X PL)).
    - cbn [has ar_list_to_imported].
      refine (sub_imported_eq_trans _ _ _ _ (sub_imported_eq_sym _ _
        (I.Prosa_Validation_FactsServiceOfJobsInterface_production_any_cons
          X PL x (ar_list_to_imported xs)))).
      exact (pp_bool_or_related _ _ _ _ (HP x) IH).
  Qed.

  Lemma fsoj_has_related (xsR : seq X) (xsL : I.List X) :
    ArListRel xsR xsL -> ArBoolRel (has PR xsR) (I.List_any X xsL PL).
  Proof.
    intro Hxs.
    exact (sub_imported_eq_trans _ _ _ (fsoj_has_canonical xsR)
      (sub_imported_eq_congr (fun l => I.List_any X l PL) _ _ Hxs)).
  Qed.
End Any.

Section Facts.
  Context (Job : eqType).
  Let dJ := ar_decidable_eq Job.
  Variable jaR : prosa.behavior.job.JobArrival Job.
  Variable jaL : I.Prosa_Behavior_Job_JobArrival Job dJ.
  Hypothesis Hja : ArJobArrivalRel Job jaR jaL.
  Variable costR : prosa.behavior.job.JobCost Job.
  Variable costL : I.Prosa_Behavior_Job_JobCost Job dJ.
  Hypothesis Hcost : SvcJobCostRel Job costR costL.
  Context (PStateR : prosa.behavior.schedule.ProcessorState Job).
  Variable PStateL : I.Prosa_Behavior_Schedule_ProcessorState Job dJ.
  Variable R : SvcProcessorStateRel Job PStateR PStateL.

  Let SchedR := @prosa.behavior.schedule.schedule Job PStateR.
  Let SchedL := I.Prosa_Behavior_Schedule_schedule Job dJ PStateL.
  Let ArrR := prosa.behavior.arrival_sequence.arrival_sequence Job.
  Let ArrL := I.Prosa_Behavior_Arrival_sequence_arrival_sequence Job dJ.

  (** *** Covers for inner binders *)

  Definition fsoj_schedule_to_target (schedR : SchedR) : SchedL :=
    fun tL => svc_ps_state_to_target Job PStateR PStateL R (schedR (sub_nat_to_rocq tL)).

  Definition fsoj_schedule_to_source (schedL : SchedL) : SchedR :=
    fun tR => svc_ps_state_to_source Job PStateR PStateL R (schedL (sub_nat_to_imported tR)).

  Lemma fsoj_schedule_to_target_rel schedR :
    SvcScheduleRel Job PStateR PStateL R schedR (fsoj_schedule_to_target schedR).
  Proof.
    intros tR tL Ht. unfold fsoj_schedule_to_target.
    rewrite (fsoj_nat_input _ _ Ht).
    exact (svc_ps_state_rel_canonical Job PStateR PStateL R (schedR tR)).
  Qed.

  Lemma fsoj_schedule_to_source_rel schedL :
    SvcScheduleRel Job PStateR PStateL R (fsoj_schedule_to_source schedL) schedL.
  Proof.
    intros tR tL Ht. unfold fsoj_schedule_to_source.
    exact (fsoj_lean_transport
      (fun sL => svc_ps_state_rel Job PStateR PStateL R
        (svc_ps_state_to_source Job PStateR PStateL R (schedL (sub_nat_to_imported tR))) sL)
      _ _ (sub_imported_eq_congr schedL _ _ Ht)
      (svc_ps_state_rel_surjective Job PStateR PStateL R _)).
  Qed.

  Let cover_schedule :=
    fsoj_forall_cover_sprop _ _ (SvcScheduleRel Job PStateR PStateL R)
      fsoj_schedule_to_target fsoj_schedule_to_source
      fsoj_schedule_to_target_rel fsoj_schedule_to_source_rel.

  Definition fsoj_arrival_sequence_to_source (arrL : ArrL) : ArrR :=
    fun tR => ar_list_to_rocq (arrL (sub_nat_to_imported tR)).

  Lemma fsoj_arrival_sequence_to_source_rel (arrL : ArrL) :
    ArArrivalSequenceRel Job (fsoj_arrival_sequence_to_source arrL) arrL.
  Proof.
    intros tR tL Ht. unfold ArListRel, fsoj_arrival_sequence_to_source.
    exact (sub_imported_eq_trans _ _ _ (ar_list_target_roundtrip _)
      (sub_imported_eq_congr arrL _ _ Ht)).
  Qed.

  Let cover_arr :=
    fsoj_forall_cover_sprop _ _ (ArArrivalSequenceRel Job)
      (ar_arrival_sequence_to_imported Job) fsoj_arrival_sequence_to_source
      (ar_arrival_sequence_canonical Job) fsoj_arrival_sequence_to_source_rel.

  Definition fsoj_pred_to_source (PL : Job -> I.Bool) : pred Job :=
    fun x => ar_bool_to_rocq (PL x).

  Lemma fsoj_pred_to_source_rel (PL : Job -> I.Bool) :
    ArPredRel (fsoj_pred_to_source PL) PL.
  Proof. intro x. exact (ar_bool_target_roundtrip (PL x)). Qed.

  Let cover_pred :=
    fsoj_forall_cover_sprop _ _ (@ArPredRel Job)
      (@ar_pred_to_imported Job) fsoj_pred_to_source
      (@ar_pred_canonical Job) fsoj_pred_to_source_rel.

  Lemma fsoj_list_to_target_rel (xs : seq Job) : ArListRel xs (ar_list_to_imported xs).
  Proof. exact (@Lean.eq_refl _ _). Qed.

  Lemma fsoj_list_to_source_rel (xs : I.List Job) : ArListRel (ar_list_to_rocq xs) xs.
  Proof. exact (ar_list_target_roundtrip xs). Qed.

  Let cover_list :=
    fsoj_forall_cover_sprop _ _ (@ArListRel Job)
      ar_list_to_imported ar_list_to_rocq
      fsoj_list_to_target_rel fsoj_list_to_source_rel.

  Definition fsoj_jlfp_to_target (pR : prosa.model.priority.definitions.JLFP_policy Job) :
      I.Prosa_Model_Priority_Definitions_JLFP_policy Job dJ :=
    I.Prosa_Model_Priority_Definitions_JLFP_policy_mk Job dJ
      (fun x y => ar_bool_to_imported (@prosa.model.priority.definitions.hep_job Job pR x y)).

  Definition fsoj_jlfp_to_source (pL : I.Prosa_Model_Priority_Definitions_JLFP_policy Job dJ) :
      prosa.model.priority.definitions.JLFP_policy Job :=
    fun x y => ar_bool_to_rocq (I.Prosa_Model_Priority_Definitions_JLFP_policy_hep_job Job dJ pL x y).

  Lemma fsoj_jlfp_to_target_rel pR : SojJLFPRel Job pR (fsoj_jlfp_to_target pR).
  Proof. intros x y. exact (@Lean.eq_refl _ _). Qed.

  Lemma fsoj_jlfp_to_source_rel pL : SojJLFPRel Job (fsoj_jlfp_to_source pL) pL.
  Proof. intros x y. exact (ar_bool_target_roundtrip _). Qed.

  Let cover_jlfp :=
    fsoj_forall_cover_sprop _ _ (SojJLFPRel Job) fsoj_jlfp_to_target fsoj_jlfp_to_source
      fsoj_jlfp_to_target_rel fsoj_jlfp_to_source_rel.

  Let cover_state :=
    fsoj_forall_cover_sprop _ _ (svc_ps_state_rel Job PStateR PStateL R)
      (svc_ps_state_to_target Job PStateR PStateL R) (svc_ps_state_to_source Job PStateR PStateL R)
      (svc_ps_state_rel_canonical Job PStateR PStateL R) (svc_ps_state_rel_surjective Job PStateR PStateL R).

  (** *** Platform properties *)

  Lemma fsoj_unit_service_related :
    PropSPropRel (@prosa.model.processor.platform_properties.unit_service_proc_model Job PStateR)
      (I.Prosa_Model_Processor_PlatformProperties_unit_service_proc_model Job dJ PStateL).
  Proof.
    unfold prosa.model.processor.platform_properties.unit_service_proc_model.
    cbn [I.Prosa_Model_Processor_PlatformProperties_unit_service_proc_model].
    apply ar_forall_identity_correspondence. intro j'.
    apply cover_state. intros sR sL Hs.
    exact (sub_nat_le_correspondence _ _ _ _ (svc_service_in_related Job PStateR PStateL R j' sR sL Hs)
      (sub_nat_rel_canonical 1)).
  Qed.

  Lemma fsoj_ideal_progress_related :
    PropSPropRel (@prosa.model.processor.platform_properties.ideal_progress_proc_model Job PStateR)
      (I.Prosa_Model_Processor_PlatformProperties_ideal_progress_proc_model Job dJ PStateL).
  Proof.
    unfold prosa.model.processor.platform_properties.ideal_progress_proc_model.
    cbn [I.Prosa_Model_Processor_PlatformProperties_ideal_progress_proc_model].
    apply ar_forall_identity_correspondence. intro j'.
    apply cover_state. intros sR sL Hs.
    apply ar_imp_correspondence;
      [exact (ar_bool_truth_correspondence _ _ (svc_scheduled_in_related Job PStateR PStateL R j' sR sL Hs))|].
    exact (sub_nat_lt_correspondence _ _ _ _ (sub_nat_rel_canonical O)
      (svc_service_in_related Job PStateR PStateL R j' sR sL Hs)).
  Qed.

  Lemma fsoj_uniprocessor_related :
    PropSPropRel (@prosa.model.processor.platform_properties.uniprocessor_model Job PStateR)
      (I.Prosa_Model_Processor_PlatformProperties_uniprocessor_model Job dJ PStateL).
  Proof.
    unfold prosa.model.processor.platform_properties.uniprocessor_model.
    cbn [I.Prosa_Model_Processor_PlatformProperties_uniprocessor_model].
    apply ar_forall_identity_correspondence. intro j1.
    apply ar_forall_identity_correspondence. intro j2.
    apply cover_schedule. intros schedR schedL Hsched.
    apply ar_forall_nat_correspondence. intros tR tL Ht.
    apply ar_imp_correspondence;
      [exact (ar_bool_truth_correspondence _ _ (pp_scheduled_at_related Job PStateR PStateL R schedR schedL Hsched j1 tR tL Ht))|].
    apply ar_imp_correspondence;
      [exact (ar_bool_truth_correspondence _ _ (pp_scheduled_at_related Job PStateR PStateL R schedR schedL Hsched j2 tR tL Ht))|].
    exact (fsoj_eq_correspondence Job j1 j2).
  Qed.

  (** *** Schedule hypotheses *)

  Section Sched.
    Variable schedR : SchedR.
    Variable schedL : SchedL.
    Hypothesis Hsched : SvcScheduleRel Job PStateR PStateL R schedR schedL.

    Let SCHED := pp_scheduled_at_related Job PStateR PStateL R schedR schedL Hsched.
    Let SERVICE := pp_service_related Job PStateR PStateL R schedR schedL Hsched.

    Lemma fsoj_jobs_must_arrive_related :
      PropSPropRel (@prosa.behavior.ready.jobs_must_arrive_to_execute Job jaR PStateR schedR)
        (I.Prosa_Behavior_Ready_jobs_must_arrive_to_execute Job dJ jaL PStateL schedL).
    Proof.
      unfold prosa.behavior.ready.jobs_must_arrive_to_execute.
      cbn [I.Prosa_Behavior_Ready_jobs_must_arrive_to_execute].
      apply ar_forall_identity_correspondence. intro j.
      apply ar_forall_nat_correspondence. intros tR tL Ht.
      apply ar_imp_correspondence; [exact (ar_bool_truth_correspondence _ _ (SCHED j tR tL Ht))|].
      exact (ar_bool_truth_correspondence _ _ (has_arrived_correspondence_certificate Job jaR jaL j Hja tR tL Ht)).
    Qed.

    Lemma fsoj_completed_jobs_dont_execute_related :
      PropSPropRel (@prosa.behavior.ready.completed_jobs_dont_execute Job PStateR schedR costR)
        (I.Prosa_Behavior_Ready_completed_jobs_dont_execute Job dJ PStateL schedL costL).
    Proof.
      unfold prosa.behavior.ready.completed_jobs_dont_execute.
      cbn [I.Prosa_Behavior_Ready_completed_jobs_dont_execute].
      apply ar_forall_identity_correspondence. intro j.
      apply ar_forall_nat_correspondence. intros tR tL Ht.
      apply ar_imp_correspondence; [exact (ar_bool_truth_correspondence _ _ (SCHED j _ _ Ht))|].
      exact (sub_nat_lt_correspondence _ _ _ _ (SERVICE j _ _ Ht) (Hcost j)).
    Qed.

    Section Pred.
      Variable PR : pred Job.
      Variable PL : Job -> I.Bool.
      Hypothesis HP : ArPredRel PR PL.

      Lemma fsoj_soj_related jobsR jobsL (Hjobs : ArListRel jobsR jobsL) t1R t1L t2R t2L :
        SubNatRel t1R t1L -> SubNatRel t2R t2L ->
        SubNatRel
          (@prosa.model.aggregate.service_of_jobs.service_of_jobs Job PStateR schedR PR jobsR t1R t2R)
          (I.Prosa_Model_Aggregate_ServiceOfJobs_service_of_jobs Job dJ PStateL schedL PL jobsL t1L t2L).
      Proof.
        intros H1 H2.
        exact (service_of_jobs_correspondence Job PStateR PStateL R schedR schedL Hsched
          PR PL HP jobsR jobsL Hjobs t1R t2R t1L t2L H1 H2).
      Qed.

      Lemma fsoj_soj_at_related jobsR jobsL (Hjobs : ArListRel jobsR jobsL) tR tL :
        SubNatRel tR tL ->
        SubNatRel
          (@prosa.model.aggregate.service_of_jobs.service_of_jobs_at Job PStateR schedR PR jobsR tR)
          (I.Prosa_Model_Aggregate_ServiceOfJobs_service_of_jobs_at Job dJ PStateL schedL PL jobsL tL).
      Proof.
        intro Ht.
        exact (service_of_jobs_at_correspondence Job PStateR PStateL R schedR schedL Hsched
          PR PL HP jobsR jobsL Hjobs tR tL Ht).
      Qed.
    End Pred.

    Lemma fsoj_receives_service_at_related (j : Job) (tR : nat) (tL : Lean.Nat) :
      SubNatRel tR tL ->
      ArBoolRel (@prosa.behavior.service.receives_service_at Job PStateR schedR j tR)
        (I.Prosa_Behavior_Service_receives_service_at Job dJ PStateL schedL j tL).
    Proof.
      intro Ht. unfold prosa.behavior.service.receives_service_at.
      cbn [I.Prosa_Behavior_Service_receives_service_at].
      exact (svc_decide_lt_related _ _ _ _ (sub_nat_rel_canonical O)
        (pp_service_at_related Job PStateR PStateL R schedR schedL Hsched j tR tL Ht)).
    Qed.

    Section Arr.
      Variable arrR : ArrR.
      Variable arrL : ArrL.
      Hypothesis Harr : ArArrivalSequenceRel Job arrR arrL.

      Lemma fsoj_served_jobs_at_related (tR : nat) (tL : Lean.Nat) :
        SubNatRel tR tL ->
        ArListRel (@prosa.analysis.definitions.service.served_jobs_at Job PStateR arrR schedR tR)
          (I.Prosa_Analysis_Definitions_Service_served_jobs_at Job dJ PStateL arrL schedL tL).
      Proof.
        intro Ht. unfold prosa.analysis.definitions.service.served_jobs_at.
        cbn [I.Prosa_Analysis_Definitions_Service_served_jobs_at].
        apply ar_filter_related.
        - intro j. exact (fsoj_receives_service_at_related j tR tL Ht).
        - exact (arrivals_up_to_correspondence_certificate Job arrR arrL Harr tR tL Ht).
      Qed.

      Section Policy.
        Variable pR : prosa.model.priority.definitions.JLFP_policy Job.
        Variable pL : I.Prosa_Model_Priority_Definitions_JLFP_policy Job dJ.
        Hypothesis Hp : SojJLFPRel Job pR pL.

        Let COMPLETED := pp_completed_by_related Job costR costL Hcost PStateR PStateL R schedR schedL Hsched.

        Lemma fsoj_quiet_time_related (j : Job) (tR : nat) (tL : Lean.Nat) :
          SubNatRel tR tL ->
          PropSPropRel (@B.quiet_time Job jaR costR PStateR arrR schedR pR j tR)
            (I.Prosa_Analysis_Definitions_BusyInterval_Classical_quiet_time
              Job dJ jaL costL PStateL arrL schedL pL j tL).
        Proof.
          intro Ht. unfold B.quiet_time.
          cbn [I.Prosa_Analysis_Definitions_BusyInterval_Classical_quiet_time].
          apply ar_forall_identity_correspondence. intro j_hp.
          apply ar_imp_correspondence; [exact (arrives_in_correspondence_certificate Job arrR arrL j_hp Harr)|].
          apply ar_imp_correspondence; [exact (ar_bool_truth_correspondence _ _ (Hp j_hp j))|].
          apply ar_imp_correspondence;
            [exact (ar_bool_truth_correspondence _ _
              (arrived_before_correspondence_certificate Job jaR jaL j_hp Hja tR tL Ht))|].
          exact (ar_bool_truth_correspondence _ _ (COMPLETED j_hp tR tL Ht)).
        Qed.
      End Policy.
    End Arr.
  End Sched.

  Lemma fsoj_reflexive_related pR pL :
    SojJLFPRel Job pR pL ->
    PropSPropRel (@prosa.model.priority.definitions.reflexive_job_priorities Job pR)
      (I.Prosa_Model_Priority_Definitions_reflexive_job_priorities Job dJ pL).
  Proof.
    intro Hp.
    unfold prosa.model.priority.definitions.reflexive_job_priorities.
    cbn [I.Prosa_Model_Priority_Definitions_reflexive_job_priorities].
    apply ar_forall_identity_correspondence. intro j.
    exact (ar_bool_truth_correspondence _ _ (Hp j j)).
  Qed.

  Let CONSISTENT arrR arrL (Harr : ArArrivalSequenceRel Job arrR arrL) :=
    consistent_arrival_times_correspondence_certificate Job jaR jaL arrR arrL Hja Harr.

  Let ARRB arrR arrL (Harr : ArArrivalSequenceRel Job arrR arrL) :=
    arrivals_between_correspondence_certificate Job arrR arrL Harr.

  Ltac fsoj_nat3 :=
    let t1R := fresh "t1R" in let t1L := fresh "t1L" in let H1 := fresh "H1" in
    let t2R := fresh "t2R" in let t2L := fresh "t2L" in let H2 := fresh "H2" in
    let tR := fresh "tR" in let tL := fresh "tL" in let Ht := fresh "Ht" in
    apply ar_forall_nat_correspondence; intros t1R t1L H1;
    apply ar_forall_nat_correspondence; intros t2R t2L H2;
    apply ar_forall_nat_correspondence; intros tR tL Ht.

  (** *** Generic-model statements *)

  Definition src_service_of_jobs_cat_scheduling_interval : Prop :=
    ltac:(body_of (fun s : S.statement_service_of_jobs_cat_scheduling_interval => s Job jaR PStateR)).
  Definition tgt_service_of_jobs_cat_scheduling_interval : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Model_ServiceOfJobs_service_of_jobs_cat_scheduling_interval
      Job dJ jaL PStateL)).
  Theorem service_of_jobs_cat_scheduling_interval_correspondence :
    PropSPropRel src_service_of_jobs_cat_scheduling_interval tgt_service_of_jobs_cat_scheduling_interval.
  Proof.
    apply cover_arr. intros arrR arrL Harr.
    apply ar_imp_correspondence; [exact (CONSISTENT arrR arrL Harr)|].
    apply cover_schedule. intros schedR schedL Hsched.
    apply ar_imp_correspondence; [exact (fsoj_jobs_must_arrive_related schedR schedL Hsched)|].
    apply cover_pred. intros PR PL HP.
    fsoj_nat3.
    apply ar_imp_correspondence; [exact (fsoj_window_le_le _ _ _ _ _ _ H1 Ht H2)|].
    have SOJ := fsoj_soj_related schedR schedL Hsched PR PL HP.
    apply sub_nat_eq_correspondence.
    - exact (SOJ _ _ (ARRB arrR arrL Harr _ _ _ _ H1 H2) _ _ _ _ H1 H2).
    - apply svc_target_add_related; [apply svc_target_add_related|].
      + exact (SOJ _ _ (ARRB arrR arrL Harr _ _ _ _ H1 Ht) _ _ _ _ H1 Ht).
      + exact (SOJ _ _ (ARRB arrR arrL Harr _ _ _ _ H1 Ht) _ _ _ _ Ht H2).
      + exact (SOJ _ _ (ARRB arrR arrL Harr _ _ _ _ Ht H2) _ _ _ _ Ht H2).
  Qed.

  Definition src_service_of_jobs_cat_arrival_interval : Prop :=
    ltac:(body_of (fun s : S.statement_service_of_jobs_cat_arrival_interval => s Job PStateR)).
  Definition tgt_service_of_jobs_cat_arrival_interval : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Model_ServiceOfJobs_service_of_jobs_cat_arrival_interval
      Job dJ PStateL)).
  Theorem service_of_jobs_cat_arrival_interval_correspondence :
    PropSPropRel src_service_of_jobs_cat_arrival_interval tgt_service_of_jobs_cat_arrival_interval.
  Proof.
    apply cover_arr. intros arrR arrL Harr.
    apply cover_schedule. intros schedR schedL Hsched.
    apply cover_pred. intros PR PL HP.
    fsoj_nat3.
    apply ar_imp_correspondence; [exact (fsoj_window_le_le _ _ _ _ _ _ H1 Ht H2)|].
    have SOJ := fsoj_soj_related schedR schedL Hsched PR PL HP.
    apply sub_nat_eq_correspondence.
    - exact (SOJ _ _ (ARRB arrR arrL Harr _ _ _ _ H1 H2) _ _ _ _ Ht H2).
    - apply svc_target_add_related.
      + exact (SOJ _ _ (ARRB arrR arrL Harr _ _ _ _ H1 Ht) _ _ _ _ Ht H2).
      + exact (SOJ _ _ (ARRB arrR arrL Harr _ _ _ _ Ht H2) _ _ _ _ Ht H2).
  Qed.

  Definition src_service_of_jobs_case_on_pred : Prop :=
    ltac:(body_of (fun s : S.statement_service_of_jobs_case_on_pred => s Job PStateR)).
  Definition tgt_service_of_jobs_case_on_pred : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Model_ServiceOfJobs_service_of_jobs_case_on_pred
      Job dJ PStateL)).
  Theorem service_of_jobs_case_on_pred_correspondence :
    PropSPropRel src_service_of_jobs_case_on_pred tgt_service_of_jobs_case_on_pred.
  Proof.
    apply cover_schedule. intros schedR schedL Hsched.
    apply cover_list. intros jobsR jobsL Hjobs.
    apply ar_forall_nat_correspondence. intros t1R t1L H1.
    apply ar_forall_nat_correspondence. intros t2R t2L H2.
    apply cover_pred. intros P1R P1L HP1.
    apply cover_pred. intros P2R P2L HP2.
    apply sub_nat_eq_correspondence.
    - exact (fsoj_soj_related schedR schedL Hsched P1R P1L HP1 _ _ Hjobs _ _ _ _ H1 H2).
    - apply svc_target_add_related.
      + exact (fsoj_soj_related schedR schedL Hsched _ _
          (fun x => ar_bool_and_related _ _ _ _ (HP1 x) (HP2 x)) _ _ Hjobs _ _ _ _ H1 H2).
      + exact (fsoj_soj_related schedR schedL Hsched _ _
          (fun x => ar_bool_and_related _ _ _ _ (HP1 x) (svc_bool_not_related _ _ (HP2 x)))
          _ _ Hjobs _ _ _ _ H1 H2).
  Qed.

  Definition src_service_of_jobs_negate_pred : Prop :=
    ltac:(body_of (fun s : S.statement_service_of_jobs_negate_pred => s Job PStateR)).
  Definition tgt_service_of_jobs_negate_pred : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Model_ServiceOfJobs_service_of_jobs_negate_pred
      Job dJ PStateL)).
  Theorem service_of_jobs_negate_pred_correspondence :
    PropSPropRel src_service_of_jobs_negate_pred tgt_service_of_jobs_negate_pred.
  Proof.
    apply cover_schedule. intros schedR schedL Hsched.
    apply cover_pred. intros PR PL HP.
    apply cover_list. intros jobsR jobsL Hjobs.
    apply ar_forall_nat_correspondence. intros t1R t1L H1.
    apply ar_forall_nat_correspondence. intros t2R t2L H2.
    apply sub_nat_eq_correspondence.
    - exact (fsoj_soj_related schedR schedL Hsched PR PL HP _ _ Hjobs _ _ _ _ H1 H2).
    - apply svc_target_sub_related.
      + exact (total_service_of_jobs_in_correspondence Job PStateR PStateL R schedR schedL Hsched
          jobsR jobsL Hjobs t1R t2R t1L t2L H1 H2).
      + exact (fsoj_soj_related schedR schedL Hsched _ _
          (fun x => svc_bool_not_related _ _ (HP x)) _ _ Hjobs _ _ _ _ H1 H2).
  Qed.

  Definition src_service_of_jobs_pred_impl : Prop :=
    ltac:(body_of (fun s : S.statement_service_of_jobs_pred_impl => s Job PStateR)).
  Definition tgt_service_of_jobs_pred_impl : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Model_ServiceOfJobs_service_of_jobs_pred_impl
      Job dJ PStateL)).
  Theorem service_of_jobs_pred_impl_correspondence :
    PropSPropRel src_service_of_jobs_pred_impl tgt_service_of_jobs_pred_impl.
  Proof.
    apply cover_schedule. intros schedR schedL Hsched.
    apply cover_list. intros jobsR jobsL Hjobs.
    apply ar_forall_nat_correspondence. intros t1R t1L H1.
    apply ar_forall_nat_correspondence. intros t2R t2L H2.
    apply cover_pred. intros P1R P1L HP1.
    apply cover_pred. intros P2R P2L HP2.
    apply ar_imp_correspondence.
    - apply ar_forall_identity_correspondence. intro j.
      apply ar_imp_correspondence;
        [exact (ar_bool_truth_correspondence _ _ (ar_decide_mem_related Job j _ _ Hjobs))|].
      apply ar_imp_correspondence; [exact (ar_bool_truth_correspondence _ _ (HP1 j))|].
      exact (ar_bool_truth_correspondence _ _ (HP2 j)).
    - exact (sub_nat_le_correspondence _ _ _ _
        (fsoj_soj_related schedR schedL Hsched P1R P1L HP1 _ _ Hjobs _ _ _ _ H1 H2)
        (fsoj_soj_related schedR schedL Hsched P2R P2L HP2 _ _ Hjobs _ _ _ _ H1 H2)).
  Qed.

  Definition src_service_of_jobs_equiv_pred : Prop :=
    ltac:(body_of (fun s : S.statement_service_of_jobs_equiv_pred => s Job PStateR)).
  Definition tgt_service_of_jobs_equiv_pred : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Model_ServiceOfJobs_service_of_jobs_equiv_pred
      Job dJ PStateL)).
  Theorem service_of_jobs_equiv_pred_correspondence :
    PropSPropRel src_service_of_jobs_equiv_pred tgt_service_of_jobs_equiv_pred.
  Proof.
    apply cover_schedule. intros schedR schedL Hsched.
    apply cover_list. intros jobsR jobsL Hjobs.
    apply ar_forall_nat_correspondence. intros t1R t1L H1.
    apply ar_forall_nat_correspondence. intros t2R t2L H2.
    apply cover_pred. intros P1R P1L HP1.
    apply cover_pred. intros P2R P2L HP2.
    apply ar_imp_correspondence.
    - unfold prop_in1.
      apply ar_forall_identity_correspondence. intro j.
      apply ar_imp_correspondence;
        [exact (ar_bool_truth_correspondence _ _ (ar_decide_mem_related Job j _ _ Hjobs))|].
      exact (fsoj_bool_eq_correspondence _ _ _ _ (HP1 j) (HP2 j)).
    - apply sub_nat_eq_correspondence.
      + exact (fsoj_soj_related schedR schedL Hsched P1R P1L HP1 _ _ Hjobs _ _ _ _ H1 H2).
      + exact (fsoj_soj_related schedR schedL Hsched P2R P2L HP2 _ _ Hjobs _ _ _ _ H1 H2).
  Qed.

  Definition src_service_of_jobs_sum_over_time_interval : Prop :=
    ltac:(body_of (fun s : S.statement_service_of_jobs_sum_over_time_interval => s Job PStateR)).
  Definition tgt_service_of_jobs_sum_over_time_interval : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Model_ServiceOfJobs_service_of_jobs_sum_over_time_interval
      Job dJ PStateL)).
  Theorem service_of_jobs_sum_over_time_interval_correspondence :
    PropSPropRel src_service_of_jobs_sum_over_time_interval tgt_service_of_jobs_sum_over_time_interval.
  Proof.
    apply cover_schedule. intros schedR schedL Hsched.
    apply cover_pred. intros PR PL HP.
    apply cover_list. intros jobsR jobsL Hjobs.
    apply ar_forall_nat_correspondence. intros t1R t1L H1.
    apply ar_forall_nat_correspondence. intros t2R t2L H2.
    apply sub_nat_eq_correspondence.
    - exact (fsoj_soj_related schedR schedL Hsched PR PL HP _ _ Hjobs _ _ _ _ H1 H2).
    - exact (svc_interval_sum_related t1R t2R t1L t2L _ _ H1 H2
        (fun aR aL Ha => fsoj_soj_at_related schedR schedL Hsched PR PL HP _ _ Hjobs aR aL Ha)).
  Qed.

  Definition src_service_of_jobs_pred0 : Prop :=
    ltac:(body_of (fun s : S.statement_service_of_jobs_pred0 => s Job PStateR)).
  Definition tgt_service_of_jobs_pred0 : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Model_ServiceOfJobs_service_of_jobs_pred0
      Job dJ PStateL)).
  Theorem service_of_jobs_pred0_correspondence :
    PropSPropRel src_service_of_jobs_pred0 tgt_service_of_jobs_pred0.
  Proof.
    apply cover_schedule. intros schedR schedL Hsched.
    apply cover_list. intros jobsR jobsL Hjobs.
    apply ar_forall_nat_correspondence. intros t1R t1L H1.
    apply ar_forall_nat_correspondence. intros t2R t2L H2.
    apply sub_nat_eq_correspondence.
    - exact (fsoj_soj_related schedR schedL Hsched pred0 (fun _ => I.Bool_false)
        (fun _ => @Lean.eq_refl _ _) _ _ Hjobs _ _ _ _ H1 H2).
    - exact (sub_nat_rel_canonical O).
  Qed.

  Definition src_service_of_jobs_nsched_or_unsat : Prop :=
    ltac:(body_of (fun s : S.statement_service_of_jobs_nsched_or_unsat => s Job PStateR)).
  Definition tgt_service_of_jobs_nsched_or_unsat : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Model_ServiceOfJobs_service_of_jobs_nsched_or_unsat
      Job dJ PStateL)).
  Theorem service_of_jobs_nsched_or_unsat_correspondence :
    PropSPropRel src_service_of_jobs_nsched_or_unsat tgt_service_of_jobs_nsched_or_unsat.
  Proof.
    apply cover_schedule. intros schedR schedL Hsched.
    apply cover_pred. intros PR PL HP.
    apply cover_list. intros jobsR jobsL Hjobs.
    apply ar_forall_nat_correspondence. intros tR tL Ht.
    apply ar_imp_correspondence.
    - apply ar_forall_identity_correspondence. intro j.
      apply ar_imp_correspondence;
        [exact (ar_bool_truth_correspondence _ _ (ar_decide_mem_related Job j _ _ Hjobs))|].
      exact (ar_bool_truth_correspondence _ _ (svc_bool_not_related _ _
        (ar_bool_and_related _ _ _ _ (HP j)
          (pp_scheduled_at_related Job PStateR PStateL R schedR schedL Hsched j tR tL Ht)))).
    - apply sub_nat_eq_correspondence.
      + exact (fsoj_soj_at_related schedR schedL Hsched PR PL HP _ _ Hjobs _ _ Ht).
      + exact (sub_nat_rel_canonical O).
  Qed.

  Definition src_service_of_jobs_geq : Prop :=
    ltac:(body_of (fun s : S.statement_service_of_jobs_geq => s Job PStateR)).
  Definition tgt_service_of_jobs_geq : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Model_ServiceOfJobs_service_of_jobs_geq
      Job dJ PStateL)).
  Theorem service_of_jobs_geq_correspondence :
    PropSPropRel src_service_of_jobs_geq tgt_service_of_jobs_geq.
  Proof.
    apply cover_schedule. intros schedR schedL Hsched.
    apply cover_pred. intros PR PL HP.
    apply cover_list. intros jobsR jobsL Hjobs.
    apply ar_forall_nat_correspondence. intros t1R t1L H1.
    apply ar_forall_nat_correspondence. intros t2R t2L H2.
    apply ar_imp_correspondence; [exact (sub_nat_le_correspondence _ _ _ _ H2 H1)|].
    apply sub_nat_eq_correspondence.
    - exact (fsoj_soj_related schedR schedL Hsched PR PL HP _ _ Hjobs _ _ _ _ H1 H2).
    - exact (sub_nat_rel_canonical O).
  Qed.

  Definition src_service_of_jobs_cat_last : Prop :=
    ltac:(body_of (fun s : S.statement_service_of_jobs_cat_last => s Job PStateR)).
  Definition tgt_service_of_jobs_cat_last : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Model_ServiceOfJobs_service_of_jobs_cat_last
      Job dJ PStateL)).
  Theorem service_of_jobs_cat_last_correspondence :
    PropSPropRel src_service_of_jobs_cat_last tgt_service_of_jobs_cat_last.
  Proof.
    apply cover_schedule. intros schedR schedL Hsched.
    apply cover_pred. intros PR PL HP.
    apply cover_list. intros jobsR jobsL Hjobs.
    apply ar_forall_nat_correspondence. intros t1R t1L H1.
    apply ar_forall_nat_correspondence. intros t2R t2L H2.
    apply ar_imp_correspondence; [exact (sub_nat_le_correspondence _ _ _ _ H1 H2)|].
    have SOJ := fsoj_soj_related schedR schedL Hsched PR PL HP _ _ Hjobs.
    apply sub_nat_eq_correspondence.
    - exact (SOJ _ _ _ _ H1 (pp_succ_related _ _ H2)).
    - apply svc_target_add_related.
      + exact (SOJ _ _ _ _ H1 H2).
      + exact (fsoj_soj_at_related schedR schedL Hsched PR PL HP _ _ Hjobs _ _ H2).
  Qed.

  (** *** Higher-or-equal-priority service *)

  Definition src_service_plus_ahep_eq_service_hep : Prop :=
    ltac:(body_of (fun s : S.statement_service_plus_ahep_eq_service_hep => s Job jaR PStateR)).
  Definition tgt_service_plus_ahep_eq_service_hep : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Model_ServiceOfJobs_service_plus_ahep_eq_service_hep
      Job dJ jaL PStateL)).
  Theorem service_plus_ahep_eq_service_hep_correspondence :
    PropSPropRel src_service_plus_ahep_eq_service_hep tgt_service_plus_ahep_eq_service_hep.
  Proof.
    apply cover_arr. intros arrR arrL Harr.
    apply ar_imp_correspondence;
      [exact (valid_arrival_sequence_correspondence_certificate Job jaR jaL arrR arrL Hja Harr)|].
    apply cover_schedule. intros schedR schedL Hsched.
    apply ar_imp_correspondence; [exact (fsoj_jobs_must_arrive_related schedR schedL Hsched)|].
    apply cover_jlfp. intros pR pL Hp.
    apply ar_imp_correspondence; [exact (fsoj_reflexive_related pR pL Hp)|].
    apply ar_forall_nat_correspondence. intros t1R t1L H1.
    apply ar_forall_nat_correspondence. intros t2R t2L H2.
    apply ar_forall_identity_correspondence. intro j.
    apply ar_imp_correspondence; [exact (arrives_in_correspondence_certificate Job arrR arrL j Harr)|].
    apply ar_imp_correspondence; [exact (sub_nat_le_correspondence _ _ _ _ H1 (Hja j))|].
    apply sub_nat_eq_correspondence.
    - apply svc_target_add_related.
      + exact (soj_service_during_related Job PStateR PStateL R schedR schedL Hsched j
          t1R t2R t1L t2L H1 H2).
      + exact (service_of_other_hep_jobs_correspondence Job PStateR PStateL R schedR schedL Hsched
          pR pL Hp arrR arrL Harr j t1R t2R t1L t2L H1 H2).
    - exact (service_of_hep_jobs_correspondence Job PStateR PStateL R schedR schedL Hsched
        pR pL Hp arrR arrL Harr j t1R t2R t1L t2L H1 H2).
  Qed.

  (** *** Unit-service statements *)

  Definition src_service_of_jobs_le_workload : Prop :=
    ltac:(body_of (fun s : S.statement_service_of_jobs_le_workload => s Job costR PStateR)).
  Definition tgt_service_of_jobs_le_workload : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Model_ServiceOfJobs_service_of_jobs_le_workload
      Job dJ costL PStateL)).
  Theorem service_of_jobs_le_workload_correspondence :
    PropSPropRel src_service_of_jobs_le_workload tgt_service_of_jobs_le_workload.
  Proof.
    apply ar_imp_correspondence; [exact fsoj_unit_service_related|].
    apply cover_schedule. intros schedR schedL Hsched.
    apply ar_imp_correspondence; [exact (fsoj_completed_jobs_dont_execute_related schedR schedL Hsched)|].
    apply cover_pred. intros PR PL HP.
    apply cover_list. intros jobsR jobsL Hjobs.
    apply ar_forall_nat_correspondence. intros t1R t1L H1.
    apply ar_forall_nat_correspondence. intros t2R t2L H2.
    exact (sub_nat_le_correspondence _ _ _ _
      (fsoj_soj_related schedR schedL Hsched PR PL HP _ _ Hjobs _ _ _ _ H1 H2)
      (workload_of_jobs_correspondence Job costR costL Hcost PR PL HP jobsR jobsL Hjobs)).
  Qed.

  Section Completion.
    Variable arrR : ArrR.
    Variable arrL : ArrL.
    Hypothesis Harr : ArArrivalSequenceRel Job arrR arrL.
    Variable schedR : SchedR.
    Variable schedL : SchedL.
    Hypothesis Hsched : SvcScheduleRel Job PStateR PStateL R schedR schedL.
    Variable PR : pred Job.
    Variable PL : Job -> I.Bool.
    Hypothesis HP : ArPredRel PR PL.
    Variables (t1R t2R tcR : nat) (t1L t2L tcL : Lean.Nat).
    Hypotheses (H1 : SubNatRel t1R t1L) (H2 : SubNatRel t2R t2L) (Hc : SubNatRel tcR tcL).

    Let JOBS := ARRB arrR arrL Harr _ _ _ _ H1 H2.

    Lemma fsoj_all_completed_related :
      PropSPropRel
        (forall j : Job, j \in prosa.behavior.arrival_sequence.arrivals_between arrR t1R t2R ->
          PR j -> @prosa.behavior.service.completed_by Job PStateR schedR costR j tcR)
        (forall j : Job,
          Lean.eq (ar_target_decide_mem Job j
            (I.Prosa_Behavior_Arrival_sequence_arrivals_between Job dJ arrL t1L t2L)) I.Bool_true ->
          Lean.eq (PL j) I.Bool_true ->
          Lean.eq (I.Prosa_Behavior_Service_completed_by Job dJ PStateL schedL costL j tcL) I.Bool_true).
    Proof.
      apply ar_forall_identity_correspondence. intro j.
      apply ar_imp_correspondence;
        [exact (ar_bool_truth_correspondence _ _ (ar_decide_mem_related Job j _ _ JOBS))|].
      apply ar_imp_correspondence; [exact (ar_bool_truth_correspondence _ _ (HP j))|].
      exact (ar_bool_truth_correspondence _ _
        (pp_completed_by_related Job costR costL Hcost PStateR PStateL R schedR schedL Hsched j tcR tcL Hc)).
    Qed.

    Lemma fsoj_workload_eq_service_related :
      PropSPropRel
        (@prosa.model.aggregate.workload.workload_of_jobs Job costR PR
            (prosa.behavior.arrival_sequence.arrivals_between arrR t1R t2R) =
          @prosa.model.aggregate.service_of_jobs.service_of_jobs Job PStateR schedR PR
            (prosa.behavior.arrival_sequence.arrivals_between arrR t1R t2R) t1R tcR)
        (Lean.eq
          (I.Prosa_Model_Aggregate_Workload_workload_of_jobs Job dJ costL PL
            (I.Prosa_Behavior_Arrival_sequence_arrivals_between Job dJ arrL t1L t2L))
          (I.Prosa_Model_Aggregate_ServiceOfJobs_service_of_jobs Job dJ PStateL schedL PL
            (I.Prosa_Behavior_Arrival_sequence_arrivals_between Job dJ arrL t1L t2L) t1L tcL)).
    Proof.
      apply sub_nat_eq_correspondence.
      - exact (workload_of_jobs_correspondence Job costR costL Hcost PR PL HP _ _ JOBS).
      - exact (fsoj_soj_related schedR schedL Hsched PR PL HP _ _ JOBS _ _ _ _ H1 Hc).
    Qed.
  End Completion.

  Ltac fsoj_completion_prefix :=
    apply ar_imp_correspondence; [exact fsoj_unit_service_related|];
    apply cover_arr; let arrR := fresh "arrR" in let arrL := fresh "arrL" in
      let Harr := fresh "Harr" in intros arrR arrL Harr;
    apply ar_imp_correspondence; [exact (CONSISTENT arrR arrL Harr)|];
    apply cover_schedule; let schedR := fresh "schedR" in let schedL := fresh "schedL" in
      let Hsched := fresh "Hsched" in intros schedR schedL Hsched;
    apply ar_imp_correspondence; [exact (fsoj_jobs_must_arrive_related schedR schedL Hsched)|];
    apply ar_imp_correspondence; [exact (fsoj_completed_jobs_dont_execute_related schedR schedL Hsched)|];
    apply cover_pred; let PR := fresh "PR" in let PL := fresh "PL" in
      let HP := fresh "HP" in intros PR PL HP;
    fsoj_nat3.

  Definition src_workload_eq_service_impl_all_jobs_have_completed : Prop :=
    ltac:(body_of (fun s : S.statement_workload_eq_service_impl_all_jobs_have_completed =>
      s Job jaR costR PStateR)).
  Definition tgt_workload_eq_service_impl_all_jobs_have_completed : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Model_ServiceOfJobs_workload_eq_service_impl_all_jobs_have_completed
      Job dJ jaL costL PStateL)).
  Theorem workload_eq_service_impl_all_jobs_have_completed_correspondence :
    PropSPropRel src_workload_eq_service_impl_all_jobs_have_completed
      tgt_workload_eq_service_impl_all_jobs_have_completed.
  Proof.
    fsoj_completion_prefix.
    apply ar_imp_correspondence;
      [exact (fsoj_workload_eq_service_related _ _ Harr _ _ Hsched _ _ HP _ _ _ _ _ _ H1 H2 Ht)|].
    exact (fsoj_all_completed_related _ _ Harr _ _ Hsched _ _ HP _ _ _ _ _ _ H1 H2 Ht).
  Qed.

  Definition src_all_jobs_have_completed_impl_workload_eq_service : Prop :=
    ltac:(body_of (fun s : S.statement_all_jobs_have_completed_impl_workload_eq_service =>
      s Job jaR costR PStateR)).
  Definition tgt_all_jobs_have_completed_impl_workload_eq_service : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Model_ServiceOfJobs_all_jobs_have_completed_impl_workload_eq_service
      Job dJ jaL costL PStateL)).
  Theorem all_jobs_have_completed_impl_workload_eq_service_correspondence :
    PropSPropRel src_all_jobs_have_completed_impl_workload_eq_service
      tgt_all_jobs_have_completed_impl_workload_eq_service.
  Proof.
    fsoj_completion_prefix.
    apply ar_imp_correspondence;
      [exact (fsoj_all_completed_related _ _ Harr _ _ Hsched _ _ HP _ _ _ _ _ _ H1 H2 Ht)|].
    exact (fsoj_workload_eq_service_related _ _ Harr _ _ Hsched _ _ HP _ _ _ _ _ _ H1 H2 Ht).
  Qed.

  Definition src_all_jobs_have_completed_equiv_workload_eq_service : Prop :=
    ltac:(body_of (fun s : S.statement_all_jobs_have_completed_equiv_workload_eq_service =>
      s Job jaR costR PStateR)).
  Definition tgt_all_jobs_have_completed_equiv_workload_eq_service : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Model_ServiceOfJobs_all_jobs_have_completed_equiv_workload_eq_service
      Job dJ jaL costL PStateL)).
  Theorem all_jobs_have_completed_equiv_workload_eq_service_correspondence :
    PropSPropRel src_all_jobs_have_completed_equiv_workload_eq_service
      tgt_all_jobs_have_completed_equiv_workload_eq_service.
  Proof.
    fsoj_completion_prefix.
    exact (pp_iff_correspondence _ _ _ _
      (fsoj_all_completed_related _ _ Harr _ _ Hsched _ _ HP _ _ _ _ _ _ H1 H2 Ht)
      (fsoj_workload_eq_service_related _ _ Harr _ _ Hsched _ _ HP _ _ _ _ _ _ H1 H2 Ht)).
  Qed.

  (** *** Unit-service uniprocessor statements *)

  Ltac fsoj_uni_prefix :=
    apply ar_imp_correspondence; [exact fsoj_unit_service_related|];
    apply ar_imp_correspondence; [exact fsoj_uniprocessor_related|];
    apply cover_schedule; let schedR := fresh "schedR" in let schedL := fresh "schedL" in
      let Hsched := fresh "Hsched" in intros schedR schedL Hsched;
    apply cover_pred; let PR := fresh "PR" in let PL := fresh "PL" in
      let HP := fresh "HP" in intros PR PL HP.

  Ltac fsoj_uniq_prefix :=
    apply cover_list; let jobsR := fresh "jobsR" in let jobsL := fresh "jobsL" in
      let Hjobs := fresh "Hjobs" in intros jobsR jobsL Hjobs;
    apply ar_imp_correspondence; [exact (ar_uniq_correspondence Job _ _ Hjobs)|].

  Definition src_service_of_jobs_le_1 : Prop :=
    ltac:(body_of (fun s : S.statement_service_of_jobs_le_1 => s Job PStateR)).
  Definition tgt_service_of_jobs_le_1 : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Model_ServiceOfJobs_service_of_jobs_le_1
      Job dJ PStateL)).
  Theorem service_of_jobs_le_1_correspondence :
    PropSPropRel src_service_of_jobs_le_1 tgt_service_of_jobs_le_1.
  Proof.
    fsoj_uni_prefix. fsoj_uniq_prefix.
    apply ar_forall_nat_correspondence. intros tR tL Ht.
    exact (sub_nat_le_correspondence _ _ _ _
      (fsoj_soj_at_related schedR schedL Hsched PR PL HP _ _ Hjobs _ _ Ht)
      (sub_nat_rel_canonical 1)).
  Qed.

  Definition src_service_of_jobs_le_length_of_interval : Prop :=
    ltac:(body_of (fun s : S.statement_service_of_jobs_le_length_of_interval => s Job PStateR)).
  Definition tgt_service_of_jobs_le_length_of_interval : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Model_ServiceOfJobs_service_of_jobs_le_length_of_interval
      Job dJ PStateL)).
  Theorem service_of_jobs_le_length_of_interval_correspondence :
    PropSPropRel src_service_of_jobs_le_length_of_interval tgt_service_of_jobs_le_length_of_interval.
  Proof.
    fsoj_uni_prefix. fsoj_uniq_prefix.
    apply ar_forall_nat_correspondence. intros tR tL Ht.
    apply ar_forall_nat_correspondence. intros dR dL Hd.
    exact (sub_nat_le_correspondence _ _ _ _
      (fsoj_soj_related schedR schedL Hsched PR PL HP _ _ Hjobs _ _ _ _ Ht
        (svc_target_add_related _ _ _ _ Ht Hd))
      Hd).
  Qed.

  Definition src_service_of_jobs_le_length_of_interval' : Prop :=
    ltac:(body_of (fun s : S.statement_service_of_jobs_le_length_of_interval' => s Job PStateR)).
  Definition tgt_service_of_jobs_le_length_of_interval' : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Model_ServiceOfJobs_service_of_jobs_le_length_of_interval'
      Job dJ PStateL)).
  Theorem service_of_jobs_le_length_of_interval'_correspondence :
    PropSPropRel src_service_of_jobs_le_length_of_interval' tgt_service_of_jobs_le_length_of_interval'.
  Proof.
    fsoj_uni_prefix. fsoj_uniq_prefix.
    apply ar_forall_nat_correspondence. intros t1R t1L H1.
    apply ar_forall_nat_correspondence. intros t2R t2L H2.
    exact (sub_nat_le_correspondence _ _ _ _
      (fsoj_soj_related schedR schedL Hsched PR PL HP _ _ Hjobs _ _ _ _ H1 H2)
      (svc_target_sub_related _ _ _ _ H2 H1)).
  Qed.

  Section Scheduled.
    Variable schedR : SchedR.
    Variable schedL : SchedL.
    Hypothesis Hsched : SvcScheduleRel Job PStateR PStateL R schedR schedL.
    Variable PR : pred Job.
    Variable PL : Job -> I.Bool.
    Hypothesis HP : ArPredRel PR PL.
    Variable jobsR : seq Job.
    Variable jobsL : I.List Job.
    Hypothesis Hjobs : ArListRel jobsR jobsL.

    Lemma fsoj_some_scheduled_related (tR : nat) (tL : Lean.Nat) :
      SubNatRel tR tL ->
      PropSPropRel
        (exists j : Job, j \in jobsR /\
          @prosa.behavior.service.scheduled_at Job PStateR schedR j tR /\ PR j)
        (I.Exists Job (fun j =>
          Lean.And (Lean.eq (ar_target_decide_mem Job j jobsL) I.Bool_true)
            (Lean.And (Lean.eq (I.Prosa_Behavior_Service_scheduled_at Job dJ PStateL schedL j tL) I.Bool_true)
              (Lean.eq (PL j) I.Bool_true)))).
    Proof.
      intro Ht. apply fsoj_exists_identity. intro j.
      apply ar_and_correspondence;
        [exact (ar_bool_truth_correspondence _ _ (ar_decide_mem_related Job j _ _ Hjobs))|].
      apply ar_and_correspondence;
        [exact (ar_bool_truth_correspondence _ _
          (pp_scheduled_at_related Job PStateR PStateL R schedR schedL Hsched j tR tL Ht))|].
      exact (ar_bool_truth_correspondence _ _ (HP j)).
    Qed.
  End Scheduled.

  Definition src_service_of_jobs_at_scheduled1 : Prop :=
    ltac:(body_of (fun s : S.statement_service_of_jobs_at_scheduled1 => s Job PStateR)).
  Definition tgt_service_of_jobs_at_scheduled1 : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Model_ServiceOfJobs_service_of_jobs_at_scheduled1
      Job dJ PStateL)).
  Theorem service_of_jobs_at_scheduled1_correspondence :
    PropSPropRel src_service_of_jobs_at_scheduled1 tgt_service_of_jobs_at_scheduled1.
  Proof.
    fsoj_uni_prefix.
    apply ar_imp_correspondence; [exact fsoj_ideal_progress_related|].
    fsoj_uniq_prefix.
    apply ar_forall_nat_correspondence. intros tR tL Ht.
    apply ar_imp_correspondence;
      [exact (fsoj_some_scheduled_related schedR schedL Hsched PR PL HP jobsR jobsL Hjobs tR tL Ht)|].
    apply sub_nat_eq_correspondence.
    - exact (fsoj_soj_at_related schedR schedL Hsched PR PL HP _ _ Hjobs _ _ Ht).
    - exact (sub_nat_rel_canonical 1).
  Qed.

  Definition src_service_of_jobs_always_scheduled : Prop :=
    ltac:(body_of (fun s : S.statement_service_of_jobs_always_scheduled => s Job PStateR)).
  Definition tgt_service_of_jobs_always_scheduled : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Model_ServiceOfJobs_service_of_jobs_always_scheduled
      Job dJ PStateL)).
  Theorem service_of_jobs_always_scheduled_correspondence :
    PropSPropRel src_service_of_jobs_always_scheduled tgt_service_of_jobs_always_scheduled.
  Proof.
    fsoj_uni_prefix.
    apply ar_imp_correspondence; [exact fsoj_ideal_progress_related|].
    fsoj_uniq_prefix.
    apply ar_forall_nat_correspondence. intros t1R t1L H1.
    apply ar_forall_nat_correspondence. intros t2R t2L H2.
    apply ar_imp_correspondence.
    - apply ar_forall_nat_correspondence. intros tR tL Ht.
      apply ar_imp_correspondence; [exact (fsoj_window_le_lt _ _ _ _ _ _ H1 Ht H2)|].
      exact (fsoj_some_scheduled_related schedR schedL Hsched PR PL HP jobsR jobsL Hjobs tR tL Ht).
    - apply sub_nat_eq_correspondence.
      + exact (fsoj_soj_related schedR schedL Hsched PR PL HP _ _ Hjobs _ _ _ _ H1 H2).
      + exact (svc_target_sub_related _ _ _ _ H2 H1).
  Qed.

  Definition src_cumulative_pred_served_eq_service : Prop :=
    ltac:(body_of (fun s : S.statement_cumulative_pred_served_eq_service => s Job jaR costR PStateR)).
  Definition tgt_cumulative_pred_served_eq_service : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Model_ServiceOfJobs_cumulative_pred_served_eq_service
      Job dJ jaL costL PStateL)).
  Theorem cumulative_pred_served_eq_service_correspondence :
    PropSPropRel src_cumulative_pred_served_eq_service tgt_cumulative_pred_served_eq_service.
  Proof.
    apply ar_imp_correspondence; [exact fsoj_unit_service_related|].
    apply ar_imp_correspondence; [exact fsoj_uniprocessor_related|].
    apply cover_arr. intros arrR arrL Harr.
    apply ar_imp_correspondence; [exact (CONSISTENT arrR arrL Harr)|].
    apply cover_schedule. intros schedR schedL Hsched.
    apply ar_imp_correspondence; [exact (fsoj_jobs_must_arrive_related schedR schedL Hsched)|].
    apply ar_imp_correspondence; [exact (fsoj_completed_jobs_dont_execute_related schedR schedL Hsched)|].
    apply cover_pred. intros PR PL HP.
    apply ar_imp_correspondence;
      [exact (arrival_sequence_uniq_correspondence_certificate Job arrR arrL Harr)|].
    apply cover_jlfp. intros pR pL Hp.
    apply ar_forall_identity_correspondence. intro j.
    apply ar_forall_nat_correspondence. intros t1R t1L H1.
    apply ar_forall_nat_correspondence. intros tR tL Ht.
    apply ar_imp_correspondence;
      [exact (fsoj_quiet_time_related schedR schedL Hsched arrR arrL Harr pR pL Hp j t1R t1L H1)|].
    apply ar_imp_correspondence.
    - apply ar_forall_identity_correspondence. intro j'.
      apply ar_imp_correspondence; [exact (ar_bool_truth_correspondence _ _ (HP j'))|].
      exact (ar_bool_truth_correspondence _ _ (Hp j' j)).
    - apply sub_nat_eq_correspondence.
      + exact (svc_interval_sum_related t1R tR t1L tL _ _ H1 Ht
          (fun aR aL Ha => fsoj_bool_to_nat_related _ _
            (fsoj_has_related Job PR PL HP _ _
              (fsoj_served_jobs_at_related schedR schedL Hsched arrR arrL Harr aR aL Ha)))).
      + exact (fsoj_soj_related schedR schedL Hsched PR PL HP _ _
          (ARRB arrR arrL Harr _ _ _ _ H1 Ht) _ _ _ _ H1 Ht).
  Qed.
End Facts.
