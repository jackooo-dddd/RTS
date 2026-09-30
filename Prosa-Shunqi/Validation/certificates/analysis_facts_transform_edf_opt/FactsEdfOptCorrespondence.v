From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From prosa Require Import FactsEdfOptSemanticSource.
From prosa Require Import model.processor.ideal model.schedule.edf model.readiness.basic
  analysis.definitions.schedule_prefix analysis.transform.swap.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedFactsEdfOpt ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence
  JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations
  JitterSvcScheduleOperations JitterSvcJobOperations PreemptionParameterCorrespondence
  IdealUniSchedulerCorrespondence EdfDefinitionsHelpers EdfTransCorrespondence.

Module I := ImportedFactsEdfOpt.
Module S := FactsEdfOptSemanticSource.FactsEdfOptSemanticSource.
Module ET := EdfTransSemanticSource.EdfTransSemanticSource.
Module G := GeneratedSearchArgSource.GeneratedSearchArgSource.
Module SC := SchedulabilitySemanticSource.SchedulabilitySemanticSource.

(** Statement correspondences for [analysis/facts/transform/edf_opt.v].

    Source side: the extracted statements [S.statement_X] specialised at
    their leading instance inputs; target side: the imported Lean theorem
    types.  The processor model is fixed to the ideal uniprocessor on both
    sides: states are related by the accepted constructor-preserving Option
    map ([IdOptRel]), schedules pointwise ([IdScheduleRel]) and covered in
    both directions by the accepted schedule cover; [job_cost] by
    [SvcJobCostRel], [job_deadline] pointwise by [SubNatRel], [job_arrival]
    by [ArJobArrivalRel], arrival sequences by [ArArrivalSequenceRel]
    (covered in both directions), instants and naturals by [SubNatRel]; jobs
    are identity carriers.  The transformation definitions are related by the
    accepted edf-trans definition certificates ([search_arg] through the
    accepted [FetOptNatRel]); the readiness model of the optimality section is
    the source's local basic instance on both sides, related through the
    accepted [pending] relation.  No source or target theorem is used. *)

Ltac body_of f := let T := type of f in match T with _ -> ?B => exact B end.
Ltac type_of_term t := let T := type of t in exact T.

(** ** Options of naturals ([search_arg] results) *)

Definition feo_optnat_to_rocq (o : I.Option_inst1 Lean.Nat) : option nat :=
  match o with
  | I.Option_none_inst1 => None
  | I.Option_some_inst1 n => Some (sub_nat_to_rocq n)
  end.

Lemma feo_optnat_roundtrip (o : option nat) : feo_optnat_to_rocq (fet_optnat_to_imported o) = o.
Proof. destruct o as [n|]; cbn; [by rewrite sub_nat_rocq_roundtrip | reflexivity]. Qed.

Lemma feo_optnat_some_eq (oR : option nat) (oL : I.Option_inst1 Lean.Nat) (tR : nat) (tL : Lean.Nat) :
  FetOptNatRel oR oL -> SubNatRel tR tL ->
  PropSPropRel (oR = Some tR) (Lean.eq oL (I.Option_some_inst1 Lean.Nat tL)).
Proof.
  intros Ho Ht. apply prop_sprop_rel_intro.
  - intro E. rewrite E in Ho.
    refine (sub_imported_eq_trans _ _ _ (sub_imported_eq_sym _ _ Ho) _).
    exact (sub_imported_eq_congr (I.Option_some_inst1 Lean.Nat) _ _ Ht).
  - intro E. apply strictly_inhabits.
    have EL := imported_eq_to_coq_eq _ _
      (sub_imported_eq_trans _ _ _ Ho (sub_imported_eq_trans _ _ _ E
        (sub_imported_eq_sym _ _ (sub_imported_eq_congr (I.Option_some_inst1 Lean.Nat) _ _ Ht)))).
    have ES := f_equal feo_optnat_to_rocq EL.
    rewrite feo_optnat_roundtrip in ES. cbn in ES. rewrite sub_nat_rocq_roundtrip in ES. exact ES.
Qed.

Section EdfOpt.
  Context (Job : eqType).
  Let dJ := ar_decidable_eq Job.
  Let PSR := prosa.model.processor.ideal.processor_state Job.
  Let PSL := I.Prosa_Model_Processor_Ideal_processor_state Job dJ.
  Let StL := I.Prosa_Behavior_Schedule_ProcessorState_State_inst2 Job dJ PSL.
  Let SchedR := @prosa.behavior.schedule.schedule Job PSR.
  Let SchedL := I.Prosa_Behavior_Schedule_schedule_inst4 Job dJ PSL.

  Variable jcR : prosa.behavior.job.JobCost Job.
  Variable jcL : I.Prosa_Behavior_Job_JobCost Job dJ.
  Hypothesis Hjc : SvcJobCostRel Job jcR jcL.
  Variable dlR : prosa.behavior.job.JobDeadline Job.
  Variable dlL : I.Prosa_Behavior_Job_JobDeadline Job dJ.
  Hypothesis Hdl : forall j : Job,
    SubNatRel (@prosa.behavior.job.job_deadline Job dlR j)
      (I.Prosa_Behavior_Job_JobDeadline_job_deadline Job dJ dlL j).
  Variable jaR : prosa.behavior.job.JobArrival Job.
  Variable jaL : I.Prosa_Behavior_Job_JobArrival Job dJ.
  Hypothesis Hja : ArJobArrivalRel Job jaR jaL.

  (** *** Covers *)

  Definition feo_arr_to_source (arrL : I.Prosa_Behavior_Arrival_sequence_arrival_sequence Job dJ) :
      prosa.behavior.arrival_sequence.arrival_sequence Job :=
    fun tR => ar_list_to_rocq (arrL (sub_nat_to_imported tR)).

  Lemma feo_arr_to_source_rel arrL : ArArrivalSequenceRel Job (feo_arr_to_source arrL) arrL.
  Proof.
    intros tR tL Ht. unfold ArListRel, feo_arr_to_source.
    refine (sub_imported_eq_trans _ _ _ (ar_list_target_roundtrip _) _).
    exact (sub_imported_eq_congr arrL _ _ Ht).
  Qed.

  Lemma feo_forall_arr (PR : prosa.behavior.arrival_sequence.arrival_sequence Job -> Prop)
      (PL : I.Prosa_Behavior_Arrival_sequence_arrival_sequence Job dJ -> SProp) :
    (forall aR aL, ArArrivalSequenceRel Job aR aL -> PropSPropRel (PR aR) (PL aL)) ->
    PropSPropRel (forall a, PR a) (forall a, PL a).
  Proof.
    exact (pa_forall_cover _ _ (ArArrivalSequenceRel Job) (ar_arrival_sequence_to_imported Job)
      feo_arr_to_source (ar_arrival_sequence_canonical Job) feo_arr_to_source_rel PR PL).
  Qed.

  (** *** Transformed schedules (accepted edf-trans definition certificates) *)

  Lemma feo_fsc (sR : SchedR) (sL : SchedL) (Hs : IdScheduleRel Job sR sL) (tR : nat) (tL : Lean.Nat)
      (Ht : SubNatRel tR tL) (j : Job) :
    SubNatRel (@ET.find_swap_candidate Job dlR jaR sR tR j)
      (I.Prosa_Analysis_Transform_EdfTrans_find_swap_candidate Job dJ dlL jaL sL tL j).
  Proof. exact (find_swap_candidate_correspondence Job dlR dlL Hdl jaR jaL Hja sR sL tR tL j Hs Ht). Qed.

  Lemma feo_mea (sR : SchedR) (sL : SchedL) (Hs : IdScheduleRel Job sR sL) (tR : nat) (tL : Lean.Nat)
      (Ht : SubNatRel tR tL) :
    IdScheduleRel Job (@ET.make_edf_at Job dlR jaR sR tR)
      (I.Prosa_Analysis_Transform_EdfTrans_make_edf_at Job dJ dlL jaL sL tL).
  Proof. exact (make_edf_at_correspondence Job dlR dlL Hdl jaR jaL Hja sR sL tR tL Hs Ht). Qed.

  Lemma feo_prefix (sR : SchedR) (sL : SchedL) (Hs : IdScheduleRel Job sR sL) (hR : nat) (hL : Lean.Nat)
      (Hh : SubNatRel hR hL) :
    IdScheduleRel Job (@ET.edf_transform_prefix Job dlR jaR sR hR)
      (I.Prosa_Analysis_Transform_EdfTrans_edf_transform_prefix Job dJ dlL jaL sL hL).
  Proof. exact (edf_transform_prefix_correspondence Job dlR dlL Hdl jaR jaL Hja sR sL hR hL Hs Hh). Qed.

  Lemma feo_transform (sR : SchedR) (sL : SchedL) (Hs : IdScheduleRel Job sR sL) :
    IdScheduleRel Job (@ET.edf_transform Job dlR jaR sR)
      (I.Prosa_Analysis_Transform_EdfTrans_edf_transform Job dJ dlL jaL sL).
  Proof.
    intros tR tL Ht. exact (edf_transform_correspondence Job dlR dlL Hdl jaR jaL Hja sR sL tR tL Hs Ht).
  Qed.

  Lemma feo_search_arg (sR : SchedR) (sL : SchedL) (Hs : IdScheduleRel Job sR sL)
      (t1R : nat) (t1L : Lean.Nat) (Ht1 : SubNatRel t1R t1L) (bR : nat) (bL : Lean.Nat) (Hb : SubNatRel bR bL) :
    FetOptNatRel (G.search_arg sR (@ET.relevant_pstate Job jaR t1R) (@ET.earlier_deadline Job dlR) t1R bR)
      (I.Prosa_Util_SearchArg_search_arg StL sL (I.Prosa_Analysis_Transform_EdfTrans_relevant_pstate Job dJ jaL t1L)
        (I.Prosa_Analysis_Transform_EdfTrans_earlier_deadline Job dJ dlL) t1L bL).
  Proof.
    exact (fet_search_arg_related Job sR sL Hs
      (@ET.relevant_pstate Job jaR t1R) (I.Prosa_Analysis_Transform_EdfTrans_relevant_pstate Job dJ jaL t1L)
      (fun sR' sL' H => relevant_pstate_correspondence Job jaR jaL Hja t1R t1L sR' sL' Ht1 H)
      (@ET.earlier_deadline Job dlR) (I.Prosa_Analysis_Transform_EdfTrans_earlier_deadline Job dJ dlL)
      (fun s1R s1L s2R s2L H1 H2 => earlier_deadline_correspondence Job dlR dlL Hdl s1R s2R s1L s2L H1 H2)
      t1R t1L Ht1 bR bL Hb).
  Qed.

  (** *** Schedule properties on related schedules *)

  Section Sched.
    Variable sR : SchedR.
    Variable sL : SchedL.
    Hypothesis Hs : IdScheduleRel Job sR sL.

    Lemma feo_sched_at (j : Job) (tR : nat) (tL : Lean.Nat) (Ht : SubNatRel tR tL) :
      PropSPropRel (is_true (@prosa.behavior.service.scheduled_at Job PSR sR j tR))
        (Lean.eq (I.Prosa_Behavior_Service_scheduled_at_inst4 Job dJ PSL sL j tL) I.Bool_true).
    Proof. exact (svc_bool_truth_correspondence _ _ (iu_scheduled_at_related Job sR sL Hs j tR tL Ht)). Qed.

    Lemma feo_must_rel :
      PropSPropRel (@prosa.behavior.ready.jobs_must_arrive_to_execute Job jaR PSR sR)
        (I.Prosa_Behavior_Ready_jobs_must_arrive_to_execute_inst4 Job dJ jaL PSL sL).
    Proof.
      unfold prosa.behavior.ready.jobs_must_arrive_to_execute.
      cbn [I.Prosa_Behavior_Ready_jobs_must_arrive_to_execute_inst4].
      apply ar_forall_identity_correspondence. intro j.
      apply ar_forall_nat_correspondence. intros tR tL Ht.
      apply ar_imp_correspondence; [exact (feo_sched_at j tR tL Ht)|].
      exact (ar_bool_truth_correspondence _ _ (has_arrived_correspondence_certificate Job jaR jaL j Hja tR tL Ht)).
    Qed.

    Lemma feo_cde_rel :
      PropSPropRel (@prosa.behavior.ready.completed_jobs_dont_execute Job PSR sR jcR)
        (I.Prosa_Behavior_Ready_completed_jobs_dont_execute_inst4 Job dJ PSL sL jcL).
    Proof.
      unfold prosa.behavior.ready.completed_jobs_dont_execute.
      cbn [I.Prosa_Behavior_Ready_completed_jobs_dont_execute_inst4].
      apply ar_forall_identity_correspondence. intro j.
      apply ar_forall_nat_correspondence. intros tR tL Ht.
      apply ar_imp_correspondence; [exact (feo_sched_at j tR tL Ht)|].
      exact (sub_nat_lt_correspondence _ _ _ _ (iu_service_related Job sR sL Hs j tR tL Ht) (Hjc j)).
    Qed.

    Lemma feo_meets_rel (j : Job) :
      PropSPropRel (is_true (@prosa.behavior.service.job_meets_deadline Job PSR sR jcR dlR j))
        (Lean.eq (I.Prosa_Behavior_Service_job_meets_deadline_inst4 Job dJ PSL sL jcL dlL j) I.Bool_true).
    Proof.
      unfold prosa.behavior.service.job_meets_deadline, prosa.behavior.service.completed_by.
      exact (svc_bool_truth_correspondence _ _
        (svc_decide_le_related _ _ _ _ (Hjc j) (iu_service_related Job sR sL Hs j _ _ (Hdl j)))).
    Qed.

    Lemma feo_dm_rel :
      PropSPropRel (@SC.all_deadlines_met Job jcR dlR PSR sR)
        (I.Prosa_Analysis_Definitions_Schedulability_all_deadlines_met_inst4 Job dJ jcL dlL PSL sL).
    Proof.
      unfold SC.all_deadlines_met.
      cbn [I.Prosa_Analysis_Definitions_Schedulability_all_deadlines_met_inst4].
      apply ar_forall_identity_correspondence. intro j.
      apply ar_forall_nat_correspondence. intros tR tL Ht.
      apply ar_imp_correspondence; [exact (feo_sched_at j tR tL Ht)|].
      exact (feo_meets_rel j).
    Qed.

    Lemma feo_EDF_at_rel (tR : nat) (tL : Lean.Nat) (Ht : SubNatRel tR tL) :
      PropSPropRel (@prosa.model.schedule.edf.EDF_at Job dlR jaR PSR sR tR)
        (I.Prosa_Model_Schedule_Edf_EDF_at_inst4 Job dJ dlL jaL PSL sL tL).
    Proof.
      unfold prosa.model.schedule.edf.EDF_at.
      cbn [I.Prosa_Model_Schedule_Edf_EDF_at_inst4].
      apply ar_forall_identity_correspondence. intro j.
      apply ar_imp_correspondence; [exact (feo_sched_at j tR tL Ht)|].
      apply ar_forall_nat_correspondence. intros t'R t'L Ht'.
      apply ar_forall_identity_correspondence. intro j'.
      apply ar_imp_correspondence; [exact (sub_nat_le_correspondence _ _ _ _ Ht Ht')|].
      apply ar_imp_correspondence; [exact (feo_sched_at j' t'R t'L Ht')|].
      apply ar_imp_correspondence; [exact (sub_nat_le_correspondence _ _ _ _ (Hja j') Ht)|].
      exact (sub_nat_le_correspondence _ _ _ _ (Hdl j) (Hdl j')).
    Qed.

    Lemma feo_EDF_schedule_rel :
      PropSPropRel (@prosa.model.schedule.edf.EDF_schedule Job dlR jaR PSR sR)
        (I.Prosa_Model_Schedule_Edf_EDF_schedule_inst4 Job dJ dlL jaL PSL sL).
    Proof.
      unfold prosa.model.schedule.edf.EDF_schedule.
      cbn [I.Prosa_Model_Schedule_Edf_EDF_schedule_inst4].
      apply ar_forall_nat_correspondence. intros tR tL Ht.
      exact (feo_EDF_at_rel tR tL Ht).
    Qed.

    Lemma feo_ready_rel :
      PropSPropRel
        (@prosa.behavior.ready.jobs_must_be_ready_to_execute Job jaR PSR sR jcR
          (@prosa.model.readiness.basic.basic_ready_instance Job PSR jaR jcR))
        (I.Prosa_Behavior_Ready_jobs_must_be_ready_to_execute_inst4 Job dJ jaL PSL sL jcL
          (I.Prosa_Model_Readiness_Basic_basic_ready_instance_inst4 Job dJ PSL jaL jcL)).
    Proof.
      unfold prosa.behavior.ready.jobs_must_be_ready_to_execute.
      cbn [I.Prosa_Behavior_Ready_jobs_must_be_ready_to_execute_inst4].
      apply ar_forall_identity_correspondence. intro j.
      apply ar_forall_nat_correspondence. intros tR tL Ht.
      apply ar_imp_correspondence; [exact (feo_sched_at j tR tL Ht)|].
      exact (svc_bool_truth_correspondence _ _
        (pa_pending_related Job jcR jcL Hjc jaR jaL Hja sR sL Hs j tR tL Ht)).
    Qed.

    Section Arr.
      Variable arrR : prosa.behavior.arrival_sequence.arrival_sequence Job.
      Variable arrL : I.Prosa_Behavior_Arrival_sequence_arrival_sequence Job dJ.
      Hypothesis Harr : ArArrivalSequenceRel Job arrR arrL.

      Lemma feo_jcf_rel :
        PropSPropRel (prosa.behavior.ready.jobs_come_from_arrival_sequence sR arrR)
          (I.Prosa_Behavior_Ready_jobs_come_from_arrival_sequence_inst4 Job dJ PSL sL arrL).
      Proof. exact (pa_jobs_come_from_rel Job arrR arrL Harr sR sL Hs). Qed.

      Lemma feo_valid_rel :
        PropSPropRel
          (@prosa.behavior.ready.valid_schedule Job jaR PSR sR jcR
            (@prosa.model.readiness.basic.basic_ready_instance Job PSR jaR jcR) arrR)
          (I.Prosa_Behavior_Ready_valid_schedule_inst4 Job dJ jaL PSL sL jcL
            (I.Prosa_Model_Readiness_Basic_basic_ready_instance_inst4 Job dJ PSL jaL jcL) arrL).
      Proof.
        unfold prosa.behavior.ready.valid_schedule.
        cbn [I.Prosa_Behavior_Ready_valid_schedule_inst4].
        exact (ar_and_correspondence _ _ _ _ feo_jcf_rel feo_ready_rel).
      Qed.

      Lemma feo_doa_rel :
        PropSPropRel (@SC.all_deadlines_of_arrivals_met Job jcR dlR PSR arrR sR)
          (I.Prosa_Analysis_Definitions_Schedulability_all_deadlines_of_arrivals_met_inst4 Job dJ jcL dlL PSL arrL sL).
      Proof.
        unfold SC.all_deadlines_of_arrivals_met.
        cbn [I.Prosa_Analysis_Definitions_Schedulability_all_deadlines_of_arrivals_met_inst4].
        apply ar_forall_identity_correspondence. intro j.
        apply ar_imp_correspondence; [exact (arrives_in_correspondence_certificate Job arrR arrL j Harr)|].
        exact (feo_meets_rel j).
      Qed.
    End Arr.
  End Sched.

  Lemma feo_idp_rel (s1R : SchedR) (s1L : SchedL) (Hs1 : IdScheduleRel Job s1R s1L)
      (s2R : SchedR) (s2L : SchedL) (Hs2 : IdScheduleRel Job s2R s2L) (hR : nat) (hL : Lean.Nat)
      (Hh : SubNatRel hR hL) :
    PropSPropRel (@prosa.analysis.definitions.schedule_prefix.identical_prefix Job PSR s1R s2R hR)
      (I.Prosa_Analysis_Definitions_SchedulePrefix_identical_prefix_inst4 Job dJ PSL s1L s2L hL).
  Proof.
    unfold prosa.analysis.definitions.schedule_prefix.identical_prefix.
    cbn [I.Prosa_Analysis_Definitions_SchedulePrefix_identical_prefix_inst4].
    apply ar_forall_nat_correspondence. intros tR tL Ht.
    apply ar_imp_correspondence; [exact (sub_nat_lt_correspondence _ _ _ _ Ht Hh)|].
    exact (id_opt_eq_correspondence _ _ _ _ (Hs1 tR tL Ht) (Hs2 tR tL Ht)).
  Qed.

  (** Common hypothesis prefix: well-formedness and no deadline misses. *)
  Lemma feo_wf (sR : SchedR) (sL : SchedL) (Hs : IdScheduleRel Job sR sL) (PR : Prop) (PL : SProp) :
    PropSPropRel PR PL ->
    PropSPropRel
      (@prosa.behavior.ready.jobs_must_arrive_to_execute Job jaR PSR sR ->
       @prosa.behavior.ready.completed_jobs_dont_execute Job PSR sR jcR ->
       @SC.all_deadlines_met Job jcR dlR PSR sR -> PR)
      (I.Prosa_Behavior_Ready_jobs_must_arrive_to_execute_inst4 Job dJ jaL PSL sL ->
       I.Prosa_Behavior_Ready_completed_jobs_dont_execute_inst4 Job dJ PSL sL jcL ->
       I.Prosa_Analysis_Definitions_Schedulability_all_deadlines_met_inst4 Job dJ jcL dlL PSL sL -> PL).
  Proof.
    intro H.
    apply ar_imp_correspondence; [exact (feo_must_rel _ _ Hs)|].
    apply ar_imp_correspondence; [exact (feo_cde_rel _ _ Hs)|].
    apply ar_imp_correspondence; [exact (feo_dm_rel _ _ Hs)|].
    exact H.
  Qed.

  (** ** Statement correspondences *)

  (** [scheduled_at s j t], [t1 < job_deadline j1] on a related schedule and instants. *)
  Ltac sat Hs j Ht := exact (feo_sched_at _ _ Hs j _ _ Ht).
  Ltac dl_lt Ht j := exact (sub_nat_lt_correspondence _ _ _ _ Ht (Hdl j)).

  (** *** FindSwapCandidateFacts *)

  Definition src_t1_relevant : Prop :=
    ltac:(body_of (fun s : S.statement_t1_relevant => s Job jaR)).
  Definition tgt_t1_relevant : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Transform_EdfOpt_t1_relevant Job dJ jaL)).

  Theorem t1_relevant_correspondence : PropSPropRel src_t1_relevant tgt_t1_relevant.
  Proof.
    unfold src_t1_relevant, tgt_t1_relevant.
    apply pa_forall_sched. intros sR sL Hs.
    apply ar_imp_correspondence; [exact (feo_must_rel _ _ Hs)|].
    apply ar_forall_identity_correspondence. intro j1.
    apply ar_forall_nat_correspondence. intros t1R t1L Ht1.
    apply ar_imp_correspondence; [sat Hs j1 Ht1|].
    exact (svc_bool_truth_correspondence _ _
      (relevant_pstate_correspondence Job jaR jaL Hja t1R t1L _ _ Ht1 (Hs t1R t1L Ht1))).
  Qed.

  (** The common prefix of the [find_swap_candidate] facts. *)
  Lemma feo_fsc_prefix (sR : SchedR) (sL : SchedL) (Hs : IdScheduleRel Job sR sL)
      (PR : Job -> nat -> Prop) (PL : Job -> Lean.Nat -> SProp) :
    (forall j1 t1R t1L, SubNatRel t1R t1L -> PropSPropRel (PR j1 t1R) (PL j1 t1L)) ->
    PropSPropRel
      (@prosa.behavior.ready.jobs_must_arrive_to_execute Job jaR PSR sR ->
       forall (j1 : Job) (t1 : nat), @prosa.behavior.service.scheduled_at Job PSR sR j1 t1 ->
         is_true (ltn t1 (@prosa.behavior.job.job_deadline Job dlR j1)) -> PR j1 t1)
      (I.Prosa_Behavior_Ready_jobs_must_arrive_to_execute_inst4 Job dJ jaL PSL sL ->
       forall (j1 : Job) (t1 : Lean.Nat),
         Lean.eq (I.Prosa_Behavior_Service_scheduled_at_inst4 Job dJ PSL sL j1 t1) I.Bool_true ->
         svc_target_lt t1 (I.Prosa_Behavior_Job_JobDeadline_job_deadline Job dJ dlL j1) -> PL j1 t1).
  Proof.
    intro H.
    apply ar_imp_correspondence; [exact (feo_must_rel _ _ Hs)|].
    apply ar_forall_identity_correspondence. intro j1.
    apply ar_forall_nat_correspondence. intros t1R t1L Ht1.
    apply ar_imp_correspondence; [sat Hs j1 Ht1|].
    apply ar_imp_correspondence; [dl_lt Ht1 j1|].
    exact (H j1 t1R t1L Ht1).
  Qed.

  Definition src_fsc_search_successful : Prop :=
    ltac:(body_of (fun s : S.statement_fsc_search_successful => s Job dlR jaR)).
  Definition tgt_fsc_search_successful : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Transform_EdfOpt_fsc_search_successful Job dJ dlL jaL)).

  Theorem fsc_search_successful_correspondence :
    PropSPropRel src_fsc_search_successful tgt_fsc_search_successful.
  Proof.
    unfold src_fsc_search_successful, tgt_fsc_search_successful.
    apply pa_forall_sched. intros sR sL Hs.
    apply (feo_fsc_prefix _ _ Hs). intros j1 t1R t1L Ht1.
    apply ar_exists_nat_correspondence. intros tR tL Ht.
    exact (feo_optnat_some_eq _ _ _ _ (feo_search_arg _ _ Hs _ _ Ht1 _ _ (Hdl j1)) Ht).
  Qed.

  Definition src_fsc_search_result : Prop :=
    ltac:(body_of (fun s : S.statement_fsc_search_result => s Job dlR jaR)).
  Definition tgt_fsc_search_result : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Transform_EdfOpt_fsc_search_result Job dJ dlL jaL)).

  Theorem fsc_search_result_correspondence : PropSPropRel src_fsc_search_result tgt_fsc_search_result.
  Proof.
    unfold src_fsc_search_result, tgt_fsc_search_result.
    apply pa_forall_sched. intros sR sL Hs.
    apply (feo_fsc_prefix _ _ Hs). intros j1 t1R t1L Ht1.
    exact (feo_optnat_some_eq _ _ _ _ (feo_search_arg _ _ Hs _ _ Ht1 _ _ (Hdl j1)) (feo_fsc _ _ Hs _ _ Ht1 j1)).
  Qed.

  Definition src_fsc_not_idle : Prop :=
    ltac:(body_of (fun s : S.statement_fsc_not_idle => s Job dlR jaR)).
  Definition tgt_fsc_not_idle : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Transform_EdfOpt_fsc_not_idle Job dJ dlL jaL)).

  Theorem fsc_not_idle_correspondence : PropSPropRel src_fsc_not_idle tgt_fsc_not_idle.
  Proof.
    unfold src_fsc_not_idle, tgt_fsc_not_idle.
    apply pa_forall_sched. intros sR sL Hs.
    apply (feo_fsc_prefix _ _ Hs). intros j1 t1R t1L Ht1.
    apply pa_exists_identity_correspondence. intro j'.
    apply ar_and_correspondence; [sat Hs j' (feo_fsc _ _ Hs _ _ Ht1 j1)|].
    exact (sub_nat_le_correspondence _ _ _ _ (Hja j') Ht1).
  Qed.

  Definition src_fsc_found_job_arrival : Prop :=
    ltac:(body_of (fun s : S.statement_fsc_found_job_arrival => s Job dlR jaR)).
  Definition tgt_fsc_found_job_arrival : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Transform_EdfOpt_fsc_found_job_arrival Job dJ dlL jaL)).

  Theorem fsc_found_job_arrival_correspondence :
    PropSPropRel src_fsc_found_job_arrival tgt_fsc_found_job_arrival.
  Proof.
    unfold src_fsc_found_job_arrival, tgt_fsc_found_job_arrival.
    apply pa_forall_sched. intros sR sL Hs.
    apply (feo_fsc_prefix _ _ Hs). intros j1 t1R t1L Ht1.
    apply ar_forall_identity_correspondence. intro j2.
    apply ar_imp_correspondence; [sat Hs j2 (feo_fsc _ _ Hs _ _ Ht1 j1)|].
    exact (sub_nat_le_correspondence _ _ _ _ (Hja j2) Ht1).
  Qed.

  Definition src_fsc_range : Prop :=
    ltac:(body_of (fun s : S.statement_fsc_range => s Job dlR jaR)).
  Definition tgt_fsc_range : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Transform_EdfOpt_fsc_range Job dJ dlL jaL)).

  Theorem fsc_range_correspondence : PropSPropRel src_fsc_range tgt_fsc_range.
  Proof.
    unfold src_fsc_range, tgt_fsc_range.
    apply pa_forall_sched. intros sR sL Hs.
    apply (feo_fsc_prefix _ _ Hs). intros j1 t1R t1L Ht1.
    have Hf := feo_fsc _ _ Hs _ _ Ht1 j1.
    exact (svc_bool_truth_correspondence _ _
      (svc_bool_and_related _ _ _ _ (svc_decide_le_related _ _ _ _ Ht1 Hf)
        (svc_decide_lt_related _ _ _ _ Hf (Hdl j1)))).
  Qed.

  Definition src_fsc_range1 : Prop :=
    ltac:(body_of (fun s : S.statement_fsc_range1 => s Job dlR jaR)).
  Definition tgt_fsc_range1 : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Transform_EdfOpt_fsc_range1 Job dJ dlL jaL)).

  Theorem fsc_range1_correspondence : PropSPropRel src_fsc_range1 tgt_fsc_range1.
  Proof.
    unfold src_fsc_range1, tgt_fsc_range1.
    apply pa_forall_sched. intros sR sL Hs.
    apply (feo_fsc_prefix _ _ Hs). intros j1 t1R t1L Ht1.
    exact (sub_nat_le_correspondence _ _ _ _ Ht1 (feo_fsc _ _ Hs _ _ Ht1 j1)).
  Qed.

  Definition src_fsc_found_job_deadline : Prop :=
    ltac:(body_of (fun s : S.statement_fsc_found_job_deadline => s Job dlR jaR)).
  Definition tgt_fsc_found_job_deadline : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Transform_EdfOpt_fsc_found_job_deadline Job dJ dlL jaL)).

  Theorem fsc_found_job_deadline_correspondence :
    PropSPropRel src_fsc_found_job_deadline tgt_fsc_found_job_deadline.
  Proof.
    unfold src_fsc_found_job_deadline, tgt_fsc_found_job_deadline.
    apply pa_forall_sched. intros sR sL Hs.
    apply (feo_fsc_prefix _ _ Hs). intros j1 t1R t1L Ht1.
    apply ar_forall_identity_correspondence. intro j2.
    apply ar_imp_correspondence; [sat Hs j2 (feo_fsc _ _ Hs _ _ Ht1 j1)|].
    apply ar_forall_identity_correspondence. intro j.
    apply ar_forall_nat_correspondence. intros tR tL Ht.
    apply ar_imp_correspondence;
      [exact (svc_bool_truth_correspondence _ _
        (svc_bool_and_related _ _ _ _ (svc_decide_le_related _ _ _ _ Ht1 Ht)
          (svc_decide_lt_related _ _ _ _ Ht (Hdl j1))))|].
    apply ar_imp_correspondence; [sat Hs j Ht|].
    apply ar_imp_correspondence; [exact (sub_nat_le_correspondence _ _ _ _ (Hja j) Ht1)|].
    exact (sub_nat_le_correspondence _ _ _ _ (Hdl j2) (Hdl j)).
  Qed.

  Definition src_fsc_no_later_deadline : Prop :=
    ltac:(body_of (fun s : S.statement_fsc_no_later_deadline => s Job dlR jaR)).
  Definition tgt_fsc_no_later_deadline : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Transform_EdfOpt_fsc_no_later_deadline Job dJ dlL jaL)).

  Theorem fsc_no_later_deadline_correspondence :
    PropSPropRel src_fsc_no_later_deadline tgt_fsc_no_later_deadline.
  Proof.
    unfold src_fsc_no_later_deadline, tgt_fsc_no_later_deadline.
    apply pa_forall_sched. intros sR sL Hs.
    apply (feo_fsc_prefix _ _ Hs). intros j1 t1R t1L Ht1.
    apply ar_forall_identity_correspondence. intro j2.
    apply ar_imp_correspondence; [sat Hs j2 (feo_fsc _ _ Hs _ _ Ht1 j1)|].
    exact (sub_nat_le_correspondence _ _ _ _ (Hdl j2) (Hdl j1)).
  Qed.

  (** *** MakeEDFAtFacts *)

  Definition src_scheduled_job_in_sched_has_later_deadline : Prop :=
    ltac:(body_of (fun s : S.statement_scheduled_job_in_sched_has_later_deadline => s Job jcR dlR)).
  Definition tgt_scheduled_job_in_sched_has_later_deadline : SProp :=
    ltac:(type_of_term
      (@I.Prosa_Analysis_Facts_Transform_EdfOpt_scheduled_job_in_sched_has_later_deadline Job dJ jcL dlL)).

  Theorem scheduled_job_in_sched_has_later_deadline_correspondence :
    PropSPropRel src_scheduled_job_in_sched_has_later_deadline tgt_scheduled_job_in_sched_has_later_deadline.
  Proof.
    unfold src_scheduled_job_in_sched_has_later_deadline, tgt_scheduled_job_in_sched_has_later_deadline.
    apply pa_forall_sched. intros sR sL Hs.
    apply ar_imp_correspondence; [exact (feo_cde_rel _ _ Hs)|].
    apply ar_imp_correspondence; [exact (feo_dm_rel _ _ Hs)|].
    apply ar_forall_identity_correspondence. intro j.
    apply ar_forall_nat_correspondence. intros tR tL Ht.
    apply ar_imp_correspondence; [sat Hs j Ht|].
    dl_lt Ht j.
  Qed.

  Definition src_mea_completed_jobs : Prop :=
    ltac:(body_of (fun s : S.statement_mea_completed_jobs => s Job jcR dlR jaR)).
  Definition tgt_mea_completed_jobs : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Transform_EdfOpt_mea_completed_jobs Job dJ jcL dlL jaL)).

  Theorem mea_completed_jobs_correspondence : PropSPropRel src_mea_completed_jobs tgt_mea_completed_jobs.
  Proof.
    unfold src_mea_completed_jobs, tgt_mea_completed_jobs.
    apply pa_forall_sched. intros sR sL Hs. apply (feo_wf _ _ Hs).
    apply ar_forall_nat_correspondence. intros tR tL Ht.
    exact (feo_cde_rel _ _ (feo_mea _ _ Hs _ _ Ht)).
  Qed.

  Definition src_mea_no_deadline_misses : Prop :=
    ltac:(body_of (fun s : S.statement_mea_no_deadline_misses => s Job jcR dlR jaR)).
  Definition tgt_mea_no_deadline_misses : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Transform_EdfOpt_mea_no_deadline_misses Job dJ jcL dlL jaL)).

  Theorem mea_no_deadline_misses_correspondence :
    PropSPropRel src_mea_no_deadline_misses tgt_mea_no_deadline_misses.
  Proof.
    unfold src_mea_no_deadline_misses, tgt_mea_no_deadline_misses.
    apply pa_forall_sched. intros sR sL Hs. apply (feo_wf _ _ Hs).
    apply ar_forall_nat_correspondence. intros tR tL Ht.
    exact (feo_dm_rel _ _ (feo_mea _ _ Hs _ _ Ht)).
  Qed.

  Definition src_mea_scheduled_job_has_later_deadline : Prop :=
    ltac:(body_of (fun s : S.statement_mea_scheduled_job_has_later_deadline => s Job jcR dlR jaR)).
  Definition tgt_mea_scheduled_job_has_later_deadline : SProp :=
    ltac:(type_of_term
      (@I.Prosa_Analysis_Facts_Transform_EdfOpt_mea_scheduled_job_has_later_deadline Job dJ jcL dlL jaL)).

  Theorem mea_scheduled_job_has_later_deadline_correspondence :
    PropSPropRel src_mea_scheduled_job_has_later_deadline tgt_mea_scheduled_job_has_later_deadline.
  Proof.
    unfold src_mea_scheduled_job_has_later_deadline, tgt_mea_scheduled_job_has_later_deadline.
    apply pa_forall_sched. intros sR sL Hs. apply (feo_wf _ _ Hs).
    apply ar_forall_nat_correspondence. intros teR teL Hte.
    apply ar_forall_identity_correspondence. intro j.
    apply ar_forall_nat_correspondence. intros tR tL Ht.
    apply ar_imp_correspondence; [sat (feo_mea _ _ Hs _ _ Hte) j Ht|].
    dl_lt Ht j.
  Qed.

  Definition src_mea_guarantee_dl_orig : Prop :=
    ltac:(body_of (fun s : S.statement_mea_guarantee_dl_orig => s Job jcR dlR)).
  Definition tgt_mea_guarantee_dl_orig : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Transform_EdfOpt_mea_guarantee_dl_orig Job dJ jcL dlL)).

  Theorem mea_guarantee_dl_orig_correspondence : PropSPropRel src_mea_guarantee_dl_orig tgt_mea_guarantee_dl_orig.
  Proof.
    unfold src_mea_guarantee_dl_orig, tgt_mea_guarantee_dl_orig.
    apply pa_forall_sched. intros sR sL Hs.
    apply ar_imp_correspondence; [exact (feo_cde_rel _ _ Hs)|].
    apply ar_imp_correspondence; [exact (feo_dm_rel _ _ Hs)|].
    apply ar_forall_nat_correspondence. intros tR tL Ht.
    apply ar_forall_identity_correspondence. intro j.
    apply ar_imp_correspondence; [sat Hs j Ht|].
    dl_lt Ht j.
  Qed.

  Definition src_mea_guarantee_fsc_is_j_edf : Prop :=
    ltac:(body_of (fun s : S.statement_mea_guarantee_fsc_is_j_edf => s Job dlR jaR)).
  Definition tgt_mea_guarantee_fsc_is_j_edf : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Transform_EdfOpt_mea_guarantee_fsc_is_j_edf Job dJ dlL jaL)).

  Theorem mea_guarantee_fsc_is_j_edf_correspondence :
    PropSPropRel src_mea_guarantee_fsc_is_j_edf tgt_mea_guarantee_fsc_is_j_edf.
  Proof.
    unfold src_mea_guarantee_fsc_is_j_edf, tgt_mea_guarantee_fsc_is_j_edf.
    apply pa_forall_sched. intros sR sL Hs.
    apply ar_forall_nat_correspondence. intros tR tL Ht.
    apply ar_forall_identity_correspondence. intro jo.
    apply ar_imp_correspondence; [sat Hs jo Ht|].
    apply ar_forall_identity_correspondence. intro je.
    apply ar_imp_correspondence; [sat (feo_mea _ _ Hs _ _ Ht) je Ht|].
    exact (id_opt_eq_correspondence _ _ _ _ (Hs _ _ (feo_fsc _ _ Hs _ _ Ht jo)) (id_opt_rel_canonical (Some je))).
  Qed.

  (** The common prefix of the [make_edf_at] guarantee facts. *)
  Lemma feo_guarantee_prefix (sR : SchedR) (sL : SchedL) (Hs : IdScheduleRel Job sR sL)
      (PR : nat -> Job -> Job -> Prop) (PL : Lean.Nat -> Job -> Job -> SProp) :
    (forall tR tL, SubNatRel tR tL -> forall jo je, PropSPropRel (PR tR jo je) (PL tL jo je)) ->
    PropSPropRel
      (forall (t_edf : nat) (j_orig : Job), @prosa.behavior.service.scheduled_at Job PSR sR j_orig t_edf ->
        forall j_edf : Job,
          @prosa.behavior.service.scheduled_at Job PSR (@ET.make_edf_at Job dlR jaR sR t_edf) j_edf t_edf ->
          PR t_edf j_orig j_edf)
      (forall (t_edf : Lean.Nat) (j_orig : Job),
        Lean.eq (I.Prosa_Behavior_Service_scheduled_at_inst4 Job dJ PSL sL j_orig t_edf) I.Bool_true ->
        forall j_edf : Job,
          Lean.eq (I.Prosa_Behavior_Service_scheduled_at_inst4 Job dJ PSL
            (I.Prosa_Analysis_Transform_EdfTrans_make_edf_at Job dJ dlL jaL sL t_edf) j_edf t_edf) I.Bool_true ->
          PL t_edf j_orig j_edf).
  Proof.
    intro H.
    apply ar_forall_nat_correspondence. intros tR tL Ht.
    apply ar_forall_identity_correspondence. intro jo.
    apply ar_imp_correspondence; [sat Hs jo Ht|].
    apply ar_forall_identity_correspondence. intro je.
    apply ar_imp_correspondence; [sat (feo_mea _ _ Hs _ _ Ht) je Ht|].
    exact (H tR tL Ht jo je).
  Qed.

  Definition src_mea_guarantee_deadlines : Prop :=
    ltac:(body_of (fun s : S.statement_mea_guarantee_deadlines => s Job jcR dlR jaR)).
  Definition tgt_mea_guarantee_deadlines : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Transform_EdfOpt_mea_guarantee_deadlines Job dJ jcL dlL jaL)).

  Theorem mea_guarantee_deadlines_correspondence :
    PropSPropRel src_mea_guarantee_deadlines tgt_mea_guarantee_deadlines.
  Proof.
    unfold src_mea_guarantee_deadlines, tgt_mea_guarantee_deadlines.
    apply pa_forall_sched. intros sR sL Hs. apply (feo_wf _ _ Hs).
    apply (feo_guarantee_prefix _ _ Hs). intros tR tL Ht jo je.
    exact (sub_nat_le_correspondence _ _ _ _ (Hdl je) (Hdl jo)).
  Qed.

  Definition src_mea_guarantee_case_t'_past_deadline : Prop :=
    ltac:(body_of (fun s : S.statement_mea_guarantee_case_t'_past_deadline => s Job jcR dlR jaR)).
  Definition tgt_mea_guarantee_case_t'_past_deadline : SProp :=
    ltac:(type_of_term
      (@I.Prosa_Analysis_Facts_Transform_EdfOpt_mea_guarantee_case_t'_past_deadline Job dJ jcL dlL jaL)).

  Theorem mea_guarantee_case_t'_past_deadline_correspondence :
    PropSPropRel src_mea_guarantee_case_t'_past_deadline tgt_mea_guarantee_case_t'_past_deadline.
  Proof.
    unfold src_mea_guarantee_case_t'_past_deadline, tgt_mea_guarantee_case_t'_past_deadline.
    apply pa_forall_sched. intros sR sL Hs. apply (feo_wf _ _ Hs).
    apply (feo_guarantee_prefix _ _ Hs). intros tR tL Ht jo je.
    apply ar_forall_identity_correspondence. intro j'.
    apply ar_forall_nat_correspondence. intros t'R t'L Ht'.
    apply ar_imp_correspondence; [sat (feo_mea _ _ Hs _ _ Ht) j' Ht'|].
    apply ar_imp_correspondence; [exact (sub_nat_le_correspondence _ _ _ _ (Hdl jo) Ht')|].
    exact (sub_nat_le_correspondence _ _ _ _ (Hdl je) (Hdl j')).
  Qed.

  Definition src_mea_guarantee_case_t'_before_deadline : Prop :=
    ltac:(body_of (fun s : S.statement_mea_guarantee_case_t'_before_deadline => s Job jcR dlR jaR)).
  Definition tgt_mea_guarantee_case_t'_before_deadline : SProp :=
    ltac:(type_of_term
      (@I.Prosa_Analysis_Facts_Transform_EdfOpt_mea_guarantee_case_t'_before_deadline Job dJ jcL dlL jaL)).

  Theorem mea_guarantee_case_t'_before_deadline_correspondence :
    PropSPropRel src_mea_guarantee_case_t'_before_deadline tgt_mea_guarantee_case_t'_before_deadline.
  Proof.
    unfold src_mea_guarantee_case_t'_before_deadline, tgt_mea_guarantee_case_t'_before_deadline.
    apply pa_forall_sched. intros sR sL Hs. apply (feo_wf _ _ Hs).
    apply (feo_guarantee_prefix _ _ Hs). intros tR tL Ht jo je.
    apply ar_forall_identity_correspondence. intro j'.
    apply ar_forall_nat_correspondence. intros t'R t'L Ht'.
    apply ar_imp_correspondence; [exact (sub_nat_le_correspondence _ _ _ _ Ht Ht')|].
    apply ar_imp_correspondence; [sat (feo_mea _ _ Hs _ _ Ht) j' Ht'|].
    apply ar_imp_correspondence; [exact (sub_nat_le_correspondence _ _ _ _ (Hja j') Ht)|].
    apply ar_imp_correspondence; [exact (sub_nat_lt_correspondence _ _ _ _ Ht' (Hdl jo))|].
    exact (sub_nat_le_correspondence _ _ _ _ (Hdl je) (Hdl j')).
  Qed.

  Definition src_make_edf_at_guarantee : Prop :=
    ltac:(body_of (fun s : S.statement_make_edf_at_guarantee => s Job jcR dlR jaR)).
  Definition tgt_make_edf_at_guarantee : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Transform_EdfOpt_make_edf_at_guarantee Job dJ jcL dlL jaL)).

  Theorem make_edf_at_guarantee_correspondence : PropSPropRel src_make_edf_at_guarantee tgt_make_edf_at_guarantee.
  Proof.
    unfold src_make_edf_at_guarantee, tgt_make_edf_at_guarantee.
    apply pa_forall_sched. intros sR sL Hs. apply (feo_wf _ _ Hs).
    apply ar_forall_nat_correspondence. intros tR tL Ht.
    exact (feo_EDF_at_rel _ _ (feo_mea _ _ Hs _ _ Ht) _ _ Ht).
  Qed.

  Definition src_mea_jobs_must_arrive : Prop :=
    ltac:(body_of (fun s : S.statement_mea_jobs_must_arrive => s Job jcR dlR jaR)).
  Definition tgt_mea_jobs_must_arrive : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Transform_EdfOpt_mea_jobs_must_arrive Job dJ jcL dlL jaL)).

  Theorem mea_jobs_must_arrive_correspondence : PropSPropRel src_mea_jobs_must_arrive tgt_mea_jobs_must_arrive.
  Proof.
    unfold src_mea_jobs_must_arrive, tgt_mea_jobs_must_arrive.
    apply pa_forall_sched. intros sR sL Hs. apply (feo_wf _ _ Hs).
    apply ar_forall_nat_correspondence. intros tR tL Ht.
    exact (feo_must_rel _ _ (feo_mea _ _ Hs _ _ Ht)).
  Qed.

  (** [scheduled_at s1 j t -> exists t', scheduled_at s2 j t'] *)
  Lemma feo_sched_exists (s1R : SchedR) (s1L : SchedL) (Hs1 : IdScheduleRel Job s1R s1L)
      (s2R : SchedR) (s2L : SchedL) (Hs2 : IdScheduleRel Job s2R s2L) (j : Job) (tR : nat) (tL : Lean.Nat)
      (Ht : SubNatRel tR tL) :
    PropSPropRel
      (@prosa.behavior.service.scheduled_at Job PSR s1R j tR ->
        exists t' : nat, @prosa.behavior.service.scheduled_at Job PSR s2R j t')
      (Lean.eq (I.Prosa_Behavior_Service_scheduled_at_inst4 Job dJ PSL s1L j tL) I.Bool_true ->
        I.Exists Lean.Nat (fun t' => Lean.eq (I.Prosa_Behavior_Service_scheduled_at_inst4 Job dJ PSL s2L j t')
          I.Bool_true)).
  Proof.
    apply ar_imp_correspondence; [sat Hs1 j Ht|].
    apply ar_exists_nat_correspondence. intros t'R t'L Ht'.
    sat Hs2 j Ht'.
  Qed.

  Definition src_mea_job_scheduled : Prop :=
    ltac:(body_of (fun s : S.statement_mea_job_scheduled => s Job dlR jaR)).
  Definition tgt_mea_job_scheduled : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Transform_EdfOpt_mea_job_scheduled Job dJ dlL jaL)).

  Theorem mea_job_scheduled_correspondence : PropSPropRel src_mea_job_scheduled tgt_mea_job_scheduled.
  Proof.
    unfold src_mea_job_scheduled, tgt_mea_job_scheduled.
    apply pa_forall_sched. intros sR sL Hs.
    apply ar_forall_nat_correspondence. intros teR teL Hte.
    apply ar_forall_identity_correspondence. intro j.
    apply ar_forall_nat_correspondence. intros tR tL Ht.
    exact (feo_sched_exists _ _ (feo_mea _ _ Hs _ _ Hte) _ _ Hs j _ _ Ht).
  Qed.

  Definition src_mea_job_scheduled' : Prop :=
    ltac:(body_of (fun s : S.statement_mea_job_scheduled' => s Job dlR jaR)).
  Definition tgt_mea_job_scheduled' : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Transform_EdfOpt_mea_job_scheduled' Job dJ dlL jaL)).

  Theorem mea_job_scheduled'_correspondence : PropSPropRel src_mea_job_scheduled' tgt_mea_job_scheduled'.
  Proof.
    unfold src_mea_job_scheduled', tgt_mea_job_scheduled'.
    apply pa_forall_sched. intros sR sL Hs.
    apply ar_forall_nat_correspondence. intros teR teL Hte.
    apply ar_forall_identity_correspondence. intro j.
    apply ar_forall_nat_correspondence. intros tR tL Ht.
    exact (feo_sched_exists _ _ Hs _ _ (feo_mea _ _ Hs _ _ Hte) j _ _ Ht).
  Qed.

  Definition src_mea_jobs_come_from_arrival_sequence : Prop :=
    ltac:(body_of (fun s : S.statement_mea_jobs_come_from_arrival_sequence => s Job dlR jaR)).
  Definition tgt_mea_jobs_come_from_arrival_sequence : SProp :=
    ltac:(type_of_term
      (@I.Prosa_Analysis_Facts_Transform_EdfOpt_mea_jobs_come_from_arrival_sequence Job dJ dlL jaL)).

  Theorem mea_jobs_come_from_arrival_sequence_correspondence :
    PropSPropRel src_mea_jobs_come_from_arrival_sequence tgt_mea_jobs_come_from_arrival_sequence.
  Proof.
    unfold src_mea_jobs_come_from_arrival_sequence, tgt_mea_jobs_come_from_arrival_sequence.
    apply pa_forall_sched. intros sR sL Hs.
    apply ar_forall_nat_correspondence. intros tR tL Ht.
    apply feo_forall_arr. intros aR aL Ha.
    apply ar_imp_correspondence; [exact (feo_jcf_rel _ _ Hs _ _ Ha)|].
    exact (feo_jcf_rel _ _ (feo_mea _ _ Hs _ _ Ht) _ _ Ha).
  Qed.

  Definition src_mea_EDF_widen : Prop :=
    ltac:(body_of (fun s : S.statement_mea_EDF_widen => s Job jcR dlR jaR)).
  Definition tgt_mea_EDF_widen : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Transform_EdfOpt_mea_EDF_widen Job dJ jcL dlL jaL)).

  Theorem mea_EDF_widen_correspondence : PropSPropRel src_mea_EDF_widen tgt_mea_EDF_widen.
  Proof.
    unfold src_mea_EDF_widen, tgt_mea_EDF_widen.
    apply pa_forall_sched. intros sR sL Hs. apply (feo_wf _ _ Hs).
    apply ar_forall_nat_correspondence. intros teR teL Hte.
    apply ar_imp_correspondence.
    { apply ar_forall_nat_correspondence. intros tR tL Ht.
      apply ar_imp_correspondence; [exact (sub_nat_lt_correspondence _ _ _ _ Ht Hte)|].
      exact (feo_EDF_at_rel _ _ Hs _ _ Ht). }
    apply ar_forall_nat_correspondence. intros tR tL Ht.
    apply ar_imp_correspondence; [exact (sub_nat_le_correspondence _ _ _ _ Ht Hte)|].
    exact (feo_EDF_at_rel _ _ (feo_mea _ _ Hs _ _ Hte) _ _ Ht).
  Qed.

  (** *** EDFPrefixFacts *)

  Definition src_edf_prefix_well_formedness : Prop :=
    ltac:(body_of (fun s : S.statement_edf_prefix_well_formedness => s Job jcR dlR jaR)).
  Definition tgt_edf_prefix_well_formedness : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Transform_EdfOpt_edf_prefix_well_formedness Job dJ jcL dlL jaL)).

  Theorem edf_prefix_well_formedness_correspondence :
    PropSPropRel src_edf_prefix_well_formedness tgt_edf_prefix_well_formedness.
  Proof.
    unfold src_edf_prefix_well_formedness, tgt_edf_prefix_well_formedness.
    apply pa_forall_sched. intros sR sL Hs. apply (feo_wf _ _ Hs).
    apply ar_forall_nat_correspondence. intros hR hL Hh.
    have Hp := feo_prefix _ _ Hs _ _ Hh.
    apply ar_and_correspondence; [exact (feo_cde_rel _ _ Hp)|].
    apply ar_and_correspondence; [exact (feo_must_rel _ _ Hp)|].
    exact (feo_dm_rel _ _ Hp).
  Qed.

  Definition src_edf_prefix_jobs_must_arrive : Prop :=
    ltac:(body_of (fun s : S.statement_edf_prefix_jobs_must_arrive => s Job jcR dlR jaR)).
  Definition tgt_edf_prefix_jobs_must_arrive : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Transform_EdfOpt_edf_prefix_jobs_must_arrive Job dJ jcL dlL jaL)).

  Theorem edf_prefix_jobs_must_arrive_correspondence :
    PropSPropRel src_edf_prefix_jobs_must_arrive tgt_edf_prefix_jobs_must_arrive.
  Proof.
    unfold src_edf_prefix_jobs_must_arrive, tgt_edf_prefix_jobs_must_arrive.
    apply pa_forall_sched. intros sR sL Hs. apply (feo_wf _ _ Hs).
    apply ar_forall_nat_correspondence. intros hR hL Hh.
    exact (feo_must_rel _ _ (feo_prefix _ _ Hs _ _ Hh)).
  Qed.

  Definition src_edf_prefix_scheduled_job_has_later_deadline : Prop :=
    ltac:(body_of (fun s : S.statement_edf_prefix_scheduled_job_has_later_deadline => s Job jcR dlR jaR)).
  Definition tgt_edf_prefix_scheduled_job_has_later_deadline : SProp :=
    ltac:(type_of_term
      (@I.Prosa_Analysis_Facts_Transform_EdfOpt_edf_prefix_scheduled_job_has_later_deadline Job dJ jcL dlL jaL)).

  Theorem edf_prefix_scheduled_job_has_later_deadline_correspondence :
    PropSPropRel src_edf_prefix_scheduled_job_has_later_deadline tgt_edf_prefix_scheduled_job_has_later_deadline.
  Proof.
    unfold src_edf_prefix_scheduled_job_has_later_deadline, tgt_edf_prefix_scheduled_job_has_later_deadline.
    apply pa_forall_sched. intros sR sL Hs. apply (feo_wf _ _ Hs).
    apply ar_forall_nat_correspondence. intros hR hL Hh.
    apply ar_forall_identity_correspondence. intro j.
    apply ar_forall_nat_correspondence. intros tR tL Ht.
    apply ar_imp_correspondence; [sat (feo_prefix _ _ Hs _ _ Hh) j Ht|].
    dl_lt Ht j.
  Qed.

  Definition src_edf_prefix_job_scheduled : Prop :=
    ltac:(body_of (fun s : S.statement_edf_prefix_job_scheduled => s Job dlR jaR)).
  Definition tgt_edf_prefix_job_scheduled : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Transform_EdfOpt_edf_prefix_job_scheduled Job dJ dlL jaL)).

  Theorem edf_prefix_job_scheduled_correspondence :
    PropSPropRel src_edf_prefix_job_scheduled tgt_edf_prefix_job_scheduled.
  Proof.
    unfold src_edf_prefix_job_scheduled, tgt_edf_prefix_job_scheduled.
    apply pa_forall_sched. intros sR sL Hs.
    apply ar_forall_nat_correspondence. intros hR hL Hh.
    apply ar_forall_identity_correspondence. intro j.
    apply ar_forall_nat_correspondence. intros tR tL Ht.
    exact (feo_sched_exists _ _ (feo_prefix _ _ Hs _ _ Hh) _ _ Hs j _ _ Ht).
  Qed.

  Definition src_edf_prefix_job_scheduled' : Prop :=
    ltac:(body_of (fun s : S.statement_edf_prefix_job_scheduled' => s Job dlR jaR)).
  Definition tgt_edf_prefix_job_scheduled' : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Transform_EdfOpt_edf_prefix_job_scheduled' Job dJ dlL jaL)).

  Theorem edf_prefix_job_scheduled'_correspondence :
    PropSPropRel src_edf_prefix_job_scheduled' tgt_edf_prefix_job_scheduled'.
  Proof.
    unfold src_edf_prefix_job_scheduled', tgt_edf_prefix_job_scheduled'.
    apply pa_forall_sched. intros sR sL Hs.
    apply ar_forall_nat_correspondence. intros hR hL Hh.
    apply ar_forall_identity_correspondence. intro j.
    apply ar_forall_nat_correspondence. intros tR tL Ht.
    exact (feo_sched_exists _ _ Hs _ _ (feo_prefix _ _ Hs _ _ Hh) j _ _ Ht).
  Qed.

  Definition src_edf_prefix_jobs_come_from_arrival_sequence : Prop :=
    ltac:(body_of (fun s : S.statement_edf_prefix_jobs_come_from_arrival_sequence => s Job dlR jaR)).
  Definition tgt_edf_prefix_jobs_come_from_arrival_sequence : SProp :=
    ltac:(type_of_term
      (@I.Prosa_Analysis_Facts_Transform_EdfOpt_edf_prefix_jobs_come_from_arrival_sequence Job dJ dlL jaL)).

  Theorem edf_prefix_jobs_come_from_arrival_sequence_correspondence :
    PropSPropRel src_edf_prefix_jobs_come_from_arrival_sequence tgt_edf_prefix_jobs_come_from_arrival_sequence.
  Proof.
    unfold src_edf_prefix_jobs_come_from_arrival_sequence, tgt_edf_prefix_jobs_come_from_arrival_sequence.
    apply pa_forall_sched. intros sR sL Hs.
    apply ar_forall_nat_correspondence. intros hR hL Hh.
    apply feo_forall_arr. intros aR aL Ha.
    apply ar_imp_correspondence; [exact (feo_jcf_rel _ _ Hs _ _ Ha)|].
    exact (feo_jcf_rel _ _ (feo_prefix _ _ Hs _ _ Hh) _ _ Ha).
  Qed.

  Definition src_edf_prefix_guarantee : Prop :=
    ltac:(body_of (fun s : S.statement_edf_prefix_guarantee => s Job jcR dlR jaR)).
  Definition tgt_edf_prefix_guarantee : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Transform_EdfOpt_edf_prefix_guarantee Job dJ jcL dlL jaL)).

  Theorem edf_prefix_guarantee_correspondence : PropSPropRel src_edf_prefix_guarantee tgt_edf_prefix_guarantee.
  Proof.
    unfold src_edf_prefix_guarantee, tgt_edf_prefix_guarantee.
    apply pa_forall_sched. intros sR sL Hs. apply (feo_wf _ _ Hs).
    apply ar_forall_nat_correspondence. intros hR hL Hh.
    apply ar_forall_nat_correspondence. intros tR tL Ht.
    apply ar_imp_correspondence; [exact (sub_nat_lt_correspondence _ _ _ _ Ht Hh)|].
    exact (feo_EDF_at_rel _ _ (feo_prefix _ _ Hs _ _ Hh) _ _ Ht).
  Qed.

  (** *** EDFPrefixInclusion *)

  Definition src_edf_prefix_inclusion : Prop :=
    ltac:(body_of (fun s : S.statement_edf_prefix_inclusion => s Job jcR dlR jaR)).
  Definition tgt_edf_prefix_inclusion : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Transform_EdfOpt_edf_prefix_inclusion Job dJ jcL dlL jaL)).

  Theorem edf_prefix_inclusion_correspondence : PropSPropRel src_edf_prefix_inclusion tgt_edf_prefix_inclusion.
  Proof.
    unfold src_edf_prefix_inclusion, tgt_edf_prefix_inclusion.
    apply pa_forall_sched. intros sR sL Hs. apply (feo_wf _ _ Hs).
    apply ar_forall_nat_correspondence. intros h1R h1L Hh1.
    apply ar_forall_nat_correspondence. intros h2R h2L Hh2.
    apply ar_imp_correspondence; [exact (sub_nat_le_correspondence _ _ _ _ Hh1 Hh2)|].
    exact (feo_idp_rel _ _ (feo_prefix _ _ Hs _ _ Hh1) _ _ (feo_prefix _ _ Hs _ _ Hh2) _ _ Hh1).
  Qed.

  (** *** EDFTransformFacts *)

  Definition src_edf_finite_prefix : Prop :=
    ltac:(body_of (fun s : S.statement_edf_finite_prefix => s Job jcR dlR jaR)).
  Definition tgt_edf_finite_prefix : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Transform_EdfOpt_edf_finite_prefix Job dJ jcL dlL jaL)).

  Theorem edf_finite_prefix_correspondence : PropSPropRel src_edf_finite_prefix tgt_edf_finite_prefix.
  Proof.
    unfold src_edf_finite_prefix, tgt_edf_finite_prefix.
    apply pa_forall_sched. intros sR sL Hs. apply (feo_wf _ _ Hs).
    apply ar_forall_nat_correspondence. intros hR hL Hh.
    exact (feo_idp_rel _ _ (feo_transform _ _ Hs) _ _ (feo_prefix _ _ Hs _ _ Hh) _ _ Hh).
  Qed.

  Definition src_edf_transform_ensures_edf : Prop :=
    ltac:(body_of (fun s : S.statement_edf_transform_ensures_edf => s Job jcR dlR jaR)).
  Definition tgt_edf_transform_ensures_edf : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Transform_EdfOpt_edf_transform_ensures_edf Job dJ jcL dlL jaL)).

  Theorem edf_transform_ensures_edf_correspondence :
    PropSPropRel src_edf_transform_ensures_edf tgt_edf_transform_ensures_edf.
  Proof.
    unfold src_edf_transform_ensures_edf, tgt_edf_transform_ensures_edf.
    apply pa_forall_sched. intros sR sL Hs. apply (feo_wf _ _ Hs).
    exact (feo_EDF_schedule_rel _ _ (feo_transform _ _ Hs)).
  Qed.

  Definition src_edf_transform_completed_jobs_dont_execute : Prop :=
    ltac:(body_of (fun s : S.statement_edf_transform_completed_jobs_dont_execute => s Job jcR dlR jaR)).
  Definition tgt_edf_transform_completed_jobs_dont_execute : SProp :=
    ltac:(type_of_term
      (@I.Prosa_Analysis_Facts_Transform_EdfOpt_edf_transform_completed_jobs_dont_execute Job dJ jcL dlL jaL)).

  Theorem edf_transform_completed_jobs_dont_execute_correspondence :
    PropSPropRel src_edf_transform_completed_jobs_dont_execute tgt_edf_transform_completed_jobs_dont_execute.
  Proof.
    unfold src_edf_transform_completed_jobs_dont_execute, tgt_edf_transform_completed_jobs_dont_execute.
    apply pa_forall_sched. intros sR sL Hs. apply (feo_wf _ _ Hs).
    exact (feo_cde_rel _ _ (feo_transform _ _ Hs)).
  Qed.

  Definition src_edf_transform_jobs_must_arrive : Prop :=
    ltac:(body_of (fun s : S.statement_edf_transform_jobs_must_arrive => s Job jcR dlR jaR)).
  Definition tgt_edf_transform_jobs_must_arrive : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Transform_EdfOpt_edf_transform_jobs_must_arrive Job dJ jcL dlL jaL)).

  Theorem edf_transform_jobs_must_arrive_correspondence :
    PropSPropRel src_edf_transform_jobs_must_arrive tgt_edf_transform_jobs_must_arrive.
  Proof.
    unfold src_edf_transform_jobs_must_arrive, tgt_edf_transform_jobs_must_arrive.
    apply pa_forall_sched. intros sR sL Hs. apply (feo_wf _ _ Hs).
    exact (feo_must_rel _ _ (feo_transform _ _ Hs)).
  Qed.

  Definition src_edf_transform_deadlines_met : Prop :=
    ltac:(body_of (fun s : S.statement_edf_transform_deadlines_met => s Job jcR dlR jaR)).
  Definition tgt_edf_transform_deadlines_met : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Transform_EdfOpt_edf_transform_deadlines_met Job dJ jcL dlL jaL)).

  Theorem edf_transform_deadlines_met_correspondence :
    PropSPropRel src_edf_transform_deadlines_met tgt_edf_transform_deadlines_met.
  Proof.
    unfold src_edf_transform_deadlines_met, tgt_edf_transform_deadlines_met.
    apply pa_forall_sched. intros sR sL Hs. apply (feo_wf _ _ Hs).
    exact (feo_dm_rel _ _ (feo_transform _ _ Hs)).
  Qed.

  Definition src_edf_transform_job_scheduled : Prop :=
    ltac:(body_of (fun s : S.statement_edf_transform_job_scheduled => s Job dlR jaR)).
  Definition tgt_edf_transform_job_scheduled : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Transform_EdfOpt_edf_transform_job_scheduled Job dJ dlL jaL)).

  Theorem edf_transform_job_scheduled_correspondence :
    PropSPropRel src_edf_transform_job_scheduled tgt_edf_transform_job_scheduled.
  Proof.
    unfold src_edf_transform_job_scheduled, tgt_edf_transform_job_scheduled.
    apply pa_forall_sched. intros sR sL Hs.
    apply ar_forall_identity_correspondence. intro j.
    apply ar_forall_nat_correspondence. intros tR tL Ht.
    exact (feo_sched_exists _ _ (feo_transform _ _ Hs) _ _ Hs j _ _ Ht).
  Qed.

  Definition src_edf_transform_job_scheduled' : Prop :=
    ltac:(body_of (fun s : S.statement_edf_transform_job_scheduled' => s Job jcR dlR jaR)).
  Definition tgt_edf_transform_job_scheduled' : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Transform_EdfOpt_edf_transform_job_scheduled' Job dJ jcL dlL jaL)).

  Theorem edf_transform_job_scheduled'_correspondence :
    PropSPropRel src_edf_transform_job_scheduled' tgt_edf_transform_job_scheduled'.
  Proof.
    unfold src_edf_transform_job_scheduled', tgt_edf_transform_job_scheduled'.
    apply pa_forall_sched. intros sR sL Hs. apply (feo_wf _ _ Hs).
    apply ar_forall_identity_correspondence. intro j.
    apply ar_forall_nat_correspondence. intros tR tL Ht.
    exact (feo_sched_exists _ _ Hs _ _ (feo_transform _ _ Hs) j _ _ Ht).
  Qed.

  Definition src_edf_transform_jobs_come_from_arrival_sequence : Prop :=
    ltac:(body_of (fun s : S.statement_edf_transform_jobs_come_from_arrival_sequence => s Job dlR jaR)).
  Definition tgt_edf_transform_jobs_come_from_arrival_sequence : SProp :=
    ltac:(type_of_term
      (@I.Prosa_Analysis_Facts_Transform_EdfOpt_edf_transform_jobs_come_from_arrival_sequence Job dJ dlL jaL)).

  Theorem edf_transform_jobs_come_from_arrival_sequence_correspondence :
    PropSPropRel src_edf_transform_jobs_come_from_arrival_sequence
      tgt_edf_transform_jobs_come_from_arrival_sequence.
  Proof.
    unfold src_edf_transform_jobs_come_from_arrival_sequence, tgt_edf_transform_jobs_come_from_arrival_sequence.
    apply pa_forall_sched. intros sR sL Hs.
    apply feo_forall_arr. intros aR aL Ha.
    apply ar_imp_correspondence; [exact (feo_jcf_rel _ _ Hs _ _ Ha)|].
    exact (feo_jcf_rel _ _ (feo_transform _ _ Hs) _ _ Ha).
  Qed.

  (** *** Optimality *)

  Definition src_edf_schedule_is_valid : Prop :=
    ltac:(body_of (fun s : S.statement_edf_schedule_is_valid => s Job jcR dlR jaR)).
  Definition tgt_edf_schedule_is_valid : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Transform_EdfOpt_edf_schedule_is_valid Job dJ jcL dlL jaL)).

  Theorem edf_schedule_is_valid_correspondence : PropSPropRel src_edf_schedule_is_valid tgt_edf_schedule_is_valid.
  Proof.
    unfold src_edf_schedule_is_valid, tgt_edf_schedule_is_valid.
    apply feo_forall_arr. intros aR aL Ha.
    apply pa_forall_sched. intros sR sL Hs.
    apply ar_imp_correspondence; [exact (feo_valid_rel _ _ Hs _ _ Ha)|].
    apply ar_imp_correspondence; [exact (feo_dm_rel _ _ Hs)|].
    exact (feo_valid_rel _ _ (feo_transform _ _ Hs) _ _ Ha).
  Qed.

  Definition src_edf_schedule_meets_all_deadlines : Prop :=
    ltac:(body_of (fun s : S.statement_edf_schedule_meets_all_deadlines => s Job jcR dlR jaR)).
  Definition tgt_edf_schedule_meets_all_deadlines : SProp :=
    ltac:(type_of_term
      (@I.Prosa_Analysis_Facts_Transform_EdfOpt_edf_schedule_meets_all_deadlines Job dJ jcL dlL jaL)).

  Theorem edf_schedule_meets_all_deadlines_correspondence :
    PropSPropRel src_edf_schedule_meets_all_deadlines tgt_edf_schedule_meets_all_deadlines.
  Proof.
    unfold src_edf_schedule_meets_all_deadlines, tgt_edf_schedule_meets_all_deadlines.
    apply feo_forall_arr. intros aR aL Ha.
    apply pa_forall_sched. intros sR sL Hs.
    apply ar_imp_correspondence; [exact (feo_valid_rel _ _ Hs _ _ Ha)|].
    apply ar_imp_correspondence; [exact (feo_dm_rel _ _ Hs)|].
    exact (feo_dm_rel _ _ (feo_transform _ _ Hs)).
  Qed.

  Definition src_edf_schedule_meets_all_deadlines_wrt_arrivals : Prop :=
    ltac:(body_of (fun s : S.statement_edf_schedule_meets_all_deadlines_wrt_arrivals => s Job jcR dlR jaR)).
  Definition tgt_edf_schedule_meets_all_deadlines_wrt_arrivals : SProp :=
    ltac:(type_of_term
      (@I.Prosa_Analysis_Facts_Transform_EdfOpt_edf_schedule_meets_all_deadlines_wrt_arrivals Job dJ jcL dlL jaL)).

  Theorem edf_schedule_meets_all_deadlines_wrt_arrivals_correspondence :
    PropSPropRel src_edf_schedule_meets_all_deadlines_wrt_arrivals
      tgt_edf_schedule_meets_all_deadlines_wrt_arrivals.
  Proof.
    unfold src_edf_schedule_meets_all_deadlines_wrt_arrivals, tgt_edf_schedule_meets_all_deadlines_wrt_arrivals.
    apply feo_forall_arr. intros aR aL Ha.
    apply pa_forall_sched. intros sR sL Hs.
    apply ar_imp_correspondence; [exact (feo_valid_rel _ _ Hs _ _ Ha)|].
    apply ar_imp_correspondence; [exact (feo_doa_rel _ _ Hs _ _ Ha)|].
    exact (feo_doa_rel _ _ (feo_transform _ _ Hs) _ _ Ha).
  Qed.
End EdfOpt.
