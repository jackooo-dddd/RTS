(* Helper-only copy of accepted certificates/analysis_facts_transform_edf_opt/FactsEdfOptCorrespondence.v: the imported
   module name differs and the statement correspondences (whose statements are not exported here) are cut, as are
   the helpers feo_EDF_at_rel, feo_EDF_schedule_rel, feo_doa_rel and feo_idp_rel (their definitions are not exported
   here); the kept blocks are byte-identical. *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From prosa Require Import FactsEdfOptSemanticSource.
From prosa Require Import model.processor.ideal model.schedule.edf model.readiness.basic
  analysis.definitions.schedule_prefix analysis.transform.swap.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedFactsEdfWc ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence
  JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations
  JitterSvcScheduleOperations JitterSvcJobOperations PreemptionParameterCorrespondence
  IdealUniSchedulerCorrespondence EdfDefinitionsHelpers EdfTransCorrespondence.

Module I := ImportedFactsEdfWc.
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

    End Arr.
  End Sched.


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
End EdfOpt.
