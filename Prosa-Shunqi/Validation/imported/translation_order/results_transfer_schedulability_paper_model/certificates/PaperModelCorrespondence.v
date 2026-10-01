From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq fintype bigop.
From prosa Require Import results.transfer_schedulability.paper_model.
From prosa Require Import model.processor.ideal.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedPaperModel ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation SubadditivityNatCorrespondence
  PmArrivalsSeqBaseAdapter PmArrivalsSeqOperations PmArrivalsSeqCorrespondence
  PmJitterSvcBaseAdapter PmJitterSvcNatBoolOperations PmJitterSvcIntervalOperations
  PmJitterSvcScheduleOperations PmJitterSvcJobOperations PmCriterionDefs PmFinishTimeMinBridge.

Module I := ImportedPaperModel.
Module PM := prosa.results.transfer_schedulability.paper_model.
Module FT := prosa.analysis.definitions.finish_time.

(** Correspondences for [results/transfer_schedulability/paper_model.v].

    The source is the official file, compiled on the official proof closure (no statement extraction): its constants
    are the official ones. The accepted criterion definition certificates ([PmCriterionDefs]: the ideal schedule
    relation, [schedulability_transferred], [transfer_schedulability_criterion]) and the accepted finish-time minimum
    bridge ([PmFinishTimeMinBridge]) are replayed at this export over the same official constants.

    Jobs are related by identity (any [eqType], the compiled side at [ar_decidable_eq]); the processor model is the
    ideal uniprocessor on both sides (the accepted [IdScheduleRel]); job arrivals, costs, predecessors and delays
    pointwise; evolutions by identity with their parameters related pointwise; schedulers pointwise; the
    non-starvation witnesses by their bound values (their proofs are irrelevant on the compiled side and only
    transported on the source side). Every inner binder is covered in both directions. *)

Ltac body_of f := let T := type of f in match T with _ -> ?B => exact B end.
Ltac type_of_term t := let T := type of t in exact T.

(** ** Generic combinators *)

Lemma pm_forall_type (PR : Type -> Prop) (PL : Type -> SProp) :
  (forall T, PropSPropRel (PR T) (PL T)) -> PropSPropRel (forall T, PR T) (forall T, PL T).
Proof.
  intro H. apply prop_sprop_rel_intro.
  - intros HR T. exact (prop_to_sprop _ _ (H T) (HR T)).
  - intro HL. apply strictly_inhabits. intro T. exact (sprop_to_prop _ _ (H T) (HL T)).
Qed.

(** A binder over proofs: the source proposition and the compiled one are related; the bodies are related for every
    pair of proofs. *)
Lemma pm_forall_proof (P : Prop) (PL : SProp) (QR : P -> Prop) (QL : PL -> SProp) :
  PropSPropRel P PL -> (forall p q, PropSPropRel (QR p) (QL q)) ->
  PropSPropRel (forall p, QR p) (forall q, QL q).
Proof.
  intros HP HQ. apply prop_sprop_rel_intro.
  - intros HR q. exact (prop_to_sprop _ _ (HQ _ q) (HR (sprop_to_prop _ _ HP q))).
  - intro HL. apply strictly_inhabits. intro p. exact (sprop_to_prop _ _ (HQ p _) (HL (prop_to_sprop _ _ HP p))).
Qed.

(** ** The classes of the model *)

Section Classes.
  Context (Job : eqType).
  Let dJ := ar_decidable_eq Job.

  (** *** Job predecessors (lists of jobs, by the canonical list map) *)

  Definition PmPredRel (pR : PM.JobPredecessors Job)
      (pL : I.Prosa_Results_TransferSchedulability_PaperModel_JobPredecessors Job dJ) : SProp :=
    forall j, ArListRel (@PM.job_predecessors Job pR j)
      (I.Prosa_Results_TransferSchedulability_PaperModel_JobPredecessors_job_predecessors Job dJ pL j).

  Definition pm_pred_to_target (pR : PM.JobPredecessors Job) :
      I.Prosa_Results_TransferSchedulability_PaperModel_JobPredecessors Job dJ :=
    I.Prosa_Results_TransferSchedulability_PaperModel_JobPredecessors_mk Job dJ
      (fun j => ar_list_to_imported (@PM.job_predecessors Job pR j)).

  Definition pm_pred_to_source (pL : I.Prosa_Results_TransferSchedulability_PaperModel_JobPredecessors Job dJ) :
      PM.JobPredecessors Job :=
    PM.Build_JobPredecessors Job
      (fun j => ar_list_to_rocq
        (I.Prosa_Results_TransferSchedulability_PaperModel_JobPredecessors_job_predecessors Job dJ pL j)).

  Lemma JobPredecessors_source_total (pR : PM.JobPredecessors Job) : PmPredRel pR (pm_pred_to_target pR).
  Proof. intro j. exact (@Lean.eq_refl _ _). Qed.

  Lemma JobPredecessors_target_total
      (pL : I.Prosa_Results_TransferSchedulability_PaperModel_JobPredecessors Job dJ) :
    PmPredRel (pm_pred_to_source pL) pL.
  Proof. intro j. exact (ar_list_target_roundtrip _). Qed.

  (** *** Job delays (pointwise, by [SubNatRel]) *)

  Definition PmDelayRel (dR : PM.JobDelay Job)
      (dL : I.Prosa_Results_TransferSchedulability_PaperModel_JobDelay Job dJ) : SProp :=
    forall j j', SubNatRel (@PM.job_delay Job dR j j')
      (I.Prosa_Results_TransferSchedulability_PaperModel_JobDelay_job_delay Job dJ dL j j').

  Definition pm_delay_to_target (dR : PM.JobDelay Job) :
      I.Prosa_Results_TransferSchedulability_PaperModel_JobDelay Job dJ :=
    I.Prosa_Results_TransferSchedulability_PaperModel_JobDelay_mk Job dJ
      (fun j j' => sub_nat_to_imported (@PM.job_delay Job dR j j')).

  Definition pm_delay_to_source (dL : I.Prosa_Results_TransferSchedulability_PaperModel_JobDelay Job dJ) :
      PM.JobDelay Job :=
    PM.Build_JobDelay Job (fun j j' => sub_nat_to_rocq
      (I.Prosa_Results_TransferSchedulability_PaperModel_JobDelay_job_delay Job dJ dL j j')).

  Lemma JobDelay_source_total (dR : PM.JobDelay Job) : PmDelayRel dR (pm_delay_to_target dR).
  Proof. intros j j'. exact (sub_nat_rel_canonical _). Qed.

  Lemma JobDelay_target_total (dL : I.Prosa_Results_TransferSchedulability_PaperModel_JobDelay Job dJ) :
    PmDelayRel (pm_delay_to_source dL) dL.
  Proof. intros j j'. exact (sub_nat_imported_roundtrip _). Qed.

  (** *** System evolutions (evolutions by identity; costs and delays pointwise) *)

  Definition PmEvoRel (Omega : Type) (eR : PM.SystemEvolutions Omega Job)
      (eL : I.Prosa_Results_TransferSchedulability_PaperModel_SystemEvolutions Omega Job dJ) : SProp :=
    forall omega : Omega, Lean.And
      (SvcJobCostRel Job (@PM.evo_costs Omega Job eR omega)
        (I.Prosa_Results_TransferSchedulability_PaperModel_SystemEvolutions_evo_costs Omega Job dJ eL omega))
      (PmDelayRel (@PM.evo_delays Omega Job eR omega)
        (I.Prosa_Results_TransferSchedulability_PaperModel_SystemEvolutions_evo_delays Omega Job dJ eL omega)).

  Definition pm_evo_to_target (Omega : Type) (eR : PM.SystemEvolutions Omega Job) :
      I.Prosa_Results_TransferSchedulability_PaperModel_SystemEvolutions Omega Job dJ :=
    I.Prosa_Results_TransferSchedulability_PaperModel_SystemEvolutions_mk Omega Job dJ
      (fun omega => svc_import_job_cost Job (@PM.evo_costs Omega Job eR omega))
      (fun omega => pm_delay_to_target (@PM.evo_delays Omega Job eR omega)).

  Definition pm_evo_to_source (Omega : Type)
      (eL : I.Prosa_Results_TransferSchedulability_PaperModel_SystemEvolutions Omega Job dJ) :
      PM.SystemEvolutions Omega Job :=
    PM.Build_SystemEvolutions Omega Job
      (fun omega => svc_export_job_cost Job
        (I.Prosa_Results_TransferSchedulability_PaperModel_SystemEvolutions_evo_costs Omega Job dJ eL omega))
      (fun omega => pm_delay_to_source
        (I.Prosa_Results_TransferSchedulability_PaperModel_SystemEvolutions_evo_delays Omega Job dJ eL omega)).

  Lemma SystemEvolutions_source_total (Omega : Type) (eR : PM.SystemEvolutions Omega Job) :
    PmEvoRel Omega eR (pm_evo_to_target Omega eR).
  Proof.
    intro omega. exact (Lean.And_intro _ _ (svc_job_cost_import Job _) (JobDelay_source_total _)).
  Qed.

  Lemma SystemEvolutions_target_total (Omega : Type)
      (eL : I.Prosa_Results_TransferSchedulability_PaperModel_SystemEvolutions Omega Job dJ) :
    PmEvoRel Omega (pm_evo_to_source Omega eL) eL.
  Proof.
    intro omega. exact (Lean.And_intro _ _ (svc_job_cost_export Job _) (JobDelay_target_total _)).
  Qed.

  Lemma pm_forall_pred (PR : PM.JobPredecessors Job -> Prop)
      (PL : I.Prosa_Results_TransferSchedulability_PaperModel_JobPredecessors Job dJ -> SProp) :
    (forall pR pL, PmPredRel pR pL -> PropSPropRel (PR pR) (PL pL)) ->
    PropSPropRel (forall p, PR p) (forall p, PL p).
  Proof.
    exact (id_forall_cover_sprop _ _ PmPredRel pm_pred_to_target pm_pred_to_source
      JobPredecessors_source_total JobPredecessors_target_total PR PL).
  Qed.

  Lemma pm_forall_evo (Omega : Type) (PR : PM.SystemEvolutions Omega Job -> Prop)
      (PL : I.Prosa_Results_TransferSchedulability_PaperModel_SystemEvolutions Omega Job dJ -> SProp) :
    (forall eR eL, PmEvoRel Omega eR eL -> PropSPropRel (PR eR) (PL eL)) ->
    PropSPropRel (forall e, PR e) (forall e, PL e).
  Proof.
    exact (id_forall_cover_sprop _ _ (PmEvoRel Omega) (pm_evo_to_target Omega) (pm_evo_to_source Omega)
      (SystemEvolutions_source_total Omega) (SystemEvolutions_target_total Omega) PR PL).
  Qed.
End Classes.

(** ** The model at the ideal uniprocessor *)

Section IdealModel.
  Context (Job : eqType).
  Let dJ := ar_decidable_eq Job.
  Let PSR := prosa.model.processor.ideal.processor_state Job.
  Let PSL := I.Prosa_Model_Processor_Ideal_processor_state Job dJ.

  Variable jaR : prosa.behavior.job.JobArrival Job.
  Variable jaL : I.Prosa_Behavior_Job_JobArrival Job dJ.
  Hypothesis Hja : ArJobArrivalRel Job jaR jaL.

  (** *** [all] over related job lists *)

  Fixpoint pm_all_canonical (pR : Job -> bool) (pL : Job -> I.Bool)
      (Hp : forall x, SvcBoolRel (pR x) (pL x)) (xs : seq Job) {struct xs} :
      SvcBoolRel (all pR xs) (I.List_all Job (ar_list_to_imported xs) pL) :=
    match xs return SvcBoolRel (all pR xs) (I.List_all Job (ar_list_to_imported xs) pL) with
    | [::] => @Lean.eq_refl _ _
    | x :: tail => svc_bool_and_related _ _ _ _ (Hp x) (pm_all_canonical pR pL Hp tail)
    end.

  Lemma pm_all_related (pR : Job -> bool) (pL : Job -> I.Bool) xsR xsL :
    ArListRel xsR xsL -> (forall x, SvcBoolRel (pR x) (pL x)) ->
    SvcBoolRel (all pR xsR) (I.List_all Job xsL pL).
  Proof.
    intros Hxs Hp.
    refine (id_lean_transport (fun l => SvcBoolRel _ (I.List_all Job l pL)) _ _ Hxs _).
    exact (pm_all_canonical pR pL Hp xsR).
  Qed.

  (** *** Readiness under delayed precedence (the source's local instance and the compiled definition) *)

  Lemma pm_job_ready_related cR cL (Hc : SvcJobCostRel Job cR cL) pR pL (Hp : PmPredRel Job pR pL)
      dR dL (Hd : PmDelayRel Job dR dL) sR sL (Hs : IdScheduleRel Job sR sL) (j : Job) tR tL :
    SubNatRel tR tL ->
    SvcBoolRel
      (@prosa.behavior.ready.job_ready Job PSR cR jaR
        (@PM.delayed_precedence_ready_instance Job PSR jaR cR pR dR) sR j tR)
      (I.Prosa_Behavior_Ready_JobReady_job_ready_inst4 Job dJ PSL cL jaL
        (I.Prosa_Results_TransferSchedulability_PaperModel_delayed_precedence_ready_instance_inst4
          Job dJ PSL jaL cL pL dL) sL j tL).
  Proof.
    intro Ht.
    rewrite /PM.delayed_precedence_ready_instance /=.
    cbn [I.Prosa_Results_TransferSchedulability_PaperModel_delayed_precedence_ready_instance_inst4
      I.Prosa_Behavior_Ready_JobReady_job_ready_inst4].
    apply svc_bool_and_related; [apply svc_bool_and_related|].
    - exact (svc_decide_le_related _ _ _ _ (Hja j) Ht).
    - apply (pm_all_related _ _ _ _ (Hp j)). intro jp.
      apply svc_bool_and_related.
      + exact (svc_decide_le_related _ _ _ _ (Hd j jp) Ht).
      + exact (cr_completed_by_related Job sR sL Hs cR cL Hc jp _ _ (svc_target_sub_related _ _ _ _ Ht (Hd j jp))).
    - exact (svc_bool_not_related _ _ (cr_completed_by_related Job sR sL Hs cR cL Hc j _ _ Ht)).
  Qed.

  Lemma pm_valid_schedule_rel cR cL (Hc : SvcJobCostRel Job cR cL) pR pL (Hp : PmPredRel Job pR pL)
      dR dL (Hd : PmDelayRel Job dR dL) arrR arrL (Harr : ArArrivalSequenceRel Job arrR arrL)
      sR sL (Hs : IdScheduleRel Job sR sL) :
    PropSPropRel
      (@prosa.behavior.ready.valid_schedule Job jaR PSR sR cR
        (@PM.delayed_precedence_ready_instance Job PSR jaR cR pR dR) arrR)
      (I.Prosa_Behavior_Ready_valid_schedule_inst4 Job dJ jaL PSL sL cL
        (I.Prosa_Results_TransferSchedulability_PaperModel_delayed_precedence_ready_instance_inst4
          Job dJ PSL jaL cL pL dL) arrL).
  Proof.
    unfold prosa.behavior.ready.valid_schedule.
    cbn [I.Prosa_Behavior_Ready_valid_schedule_inst4].
    apply ar_and_correspondence.
    - exact (cr_jobs_come_from_rel Job arrR arrL Harr sR sL Hs).
    - unfold prosa.behavior.ready.jobs_must_be_ready_to_execute.
      cbn [I.Prosa_Behavior_Ready_jobs_must_be_ready_to_execute_inst4].
      apply ar_forall_identity_correspondence => j.
      apply ar_forall_nat_correspondence => tR tL Ht.
      apply ar_imp_correspondence.
      + exact (svc_bool_truth_correspondence _ _ (id_scheduled_at_related Job sR sL Hs j tR tL Ht)).
      + exact (svc_bool_truth_correspondence _ _
          (pm_job_ready_related cR cL Hc pR pL Hp dR dL Hd sR sL Hs j tR tL Ht)).
  Qed.

  (** *** Response-time bounds and finish times *)

  Lemma pm_jrtb_related sR sL (Hs : IdScheduleRel Job sR sL) cR cL (Hc : SvcJobCostRel Job cR cL)
      (j : Job) RR RL :
    SubNatRel RR RL ->
    SvcBoolRel (@prosa.behavior.service.job_response_time_bound Job PSR sR cR jaR j RR)
      (I.Prosa_Behavior_Service_job_response_time_bound_inst4 Job dJ PSL sL cL jaL j RL).
  Proof.
    intro HR. unfold prosa.behavior.service.job_response_time_bound.
    cbn [I.Prosa_Behavior_Service_job_response_time_bound_inst4].
    exact (cr_completed_by_related Job sR sL Hs cR cL Hc j _ _ (svc_target_add_related _ _ _ _ (Hja j) HR)).
  Qed.

  Lemma pm_finish_time_rel sR sL (Hs : IdScheduleRel Job sR sL) cR cL (Hc : SvcJobCostRel Job cR cL)
      (j : Job) RR RL
      (HR : @prosa.behavior.service.job_response_time_bound Job PSR sR cR jaR j RR)
      (HL : Lean.eq (I.Prosa_Behavior_Service_job_response_time_bound_inst4 Job dJ PSL sL cL jaL j RL) I.Bool_true) :
    SubNatRel RR RL ->
    SubNatRel (@FT.finish_time Job jaR cR PSR sR j RR HR)
      (I.Prosa_Analysis_Definitions_FinishTime_finish_time_inst4 Job dJ jaL cL PSL sL j RL HL).
  Proof.
    intro HRR. unfold FT.finish_time.
    cbn [I.Prosa_Analysis_Definitions_FinishTime_finish_time_inst4].
    eapply minimum_value_correspondence. intros nR nL Hn.
    apply svc_bool_truth_correspondence.
    exact (cr_completed_by_related Job sR sL Hs cR cL Hc j nR nL Hn).
  Qed.
End IdealModel.

(** ** Schedulers, evolution-indexed definitions and finish times *)

Section Definitions.
  Context (Job : eqType).
  Let dJ := ar_decidable_eq Job.
  Let PSR := prosa.model.processor.ideal.processor_state Job.
  Let PSL := I.Prosa_Model_Processor_Ideal_processor_state Job dJ.

  Variable jaR : prosa.behavior.job.JobArrival Job.
  Variable jaL : I.Prosa_Behavior_Job_JobArrival Job dJ.
  Hypothesis Hja : ArJobArrivalRel Job jaR jaL.
  Variable pR : PM.JobPredecessors Job.
  Variable pL : I.Prosa_Results_TransferSchedulability_PaperModel_JobPredecessors Job dJ.
  Hypothesis Hp : PmPredRel Job pR pL.
  Variable Omega : Type.
  Variable eR : PM.SystemEvolutions Omega Job.
  Variable eL : I.Prosa_Results_TransferSchedulability_PaperModel_SystemEvolutions Omega Job dJ.
  Hypothesis He : PmEvoRel Job Omega eR eL.

  Let Hc (omega : Omega) := Lean.left _ _ (He omega).
  Let Hd (omega : Omega) := Lean.right _ _ (He omega).

  Definition PmSchR := @PM.Scheduler Omega Job PSR jaR Job pR Job eR.
  Definition PmSchL := I.Prosa_Results_TransferSchedulability_PaperModel_Scheduler_inst4 Omega Job dJ PSL jaL
    Job dJ pL Job dJ eL.

  (** Schedulers pointwise, by the accepted ideal schedule relation (covered in both directions). *)
  Definition PmAlgRel (aR : PmSchR) (aL : PmSchL) : SProp :=
    forall omega : Omega, IdScheduleRel Job (aR omega) (aL omega).

  Lemma Scheduler_source_total (aR : PmSchR) :
    PmAlgRel aR (fun omega => id_schedule_to_target Job (aR omega)).
  Proof. intro omega. exact (id_schedule_to_target_rel Job (aR omega)). Qed.

  Lemma Scheduler_target_total (aL : PmSchL) :
    PmAlgRel (fun omega => id_schedule_to_source Job (aL omega)) aL.
  Proof. intro omega. exact (id_schedule_to_source_rel Job (aL omega)). Qed.

  Lemma pm_forall_alg (PR : PmSchR -> Prop) (PL : PmSchL -> SProp) :
    (forall aR aL, PmAlgRel aR aL -> PropSPropRel (PR aR) (PL aL)) ->
    PropSPropRel (forall a, PR a) (forall a, PL a).
  Proof.
    exact (id_forall_cover_sprop _ _ PmAlgRel (fun aR omega => id_schedule_to_target Job (aR omega))
      (fun aL omega => id_schedule_to_source Job (aL omega)) Scheduler_source_total Scheduler_target_total PR PL).
  Qed.

  Theorem schedulability_transferred_AB_correspondence (omega_0 : Omega) aR aL bR bL :
    PmAlgRel aR aL -> PmAlgRel bR bL -> forall omega : Omega,
    PropSPropRel (@PM.schedulability_transferred_AB Job jaR pR Omega eR omega_0 aR bR omega)
      (I.Prosa_Results_TransferSchedulability_PaperModel_schedulability_transferred_AB Job dJ jaL pL Omega eL
        omega_0 aL bL omega).
  Proof.
    intros Ha Hb omega. unfold PM.schedulability_transferred_AB. cbv beta zeta.
    cbn [I.Prosa_Results_TransferSchedulability_PaperModel_schedulability_transferred_AB].
    exact (schedulability_transferred_correspondence Job (aR omega_0) (aL omega_0) (Ha omega_0)
      (bR omega) (bL omega) (Hb omega) _ _ (Hc omega_0) _ _ (Hc omega)).
  Qed.

  Variable arrR : prosa.behavior.arrival_sequence.arrival_sequence Job.
  Variable arrL : I.Prosa_Behavior_Arrival_sequence_arrival_sequence Job dJ.
  Hypothesis Harr : ArArrivalSequenceRel Job arrR arrL.

  Theorem clairvoyant_criterion_correspondence (omega_0 : Omega) aR aL bR bL :
    PmAlgRel aR aL -> PmAlgRel bR bL ->
    PropSPropRel (@PM.clairvoyant_criterion Job jaR pR arrR Omega eR omega_0 aR bR)
      (I.Prosa_Results_TransferSchedulability_PaperModel_clairvoyant_criterion Job dJ jaL pL arrL Omega eL
        omega_0 aL bL).
  Proof.
    intros Ha Hb. unfold PM.clairvoyant_criterion. cbv beta zeta.
    cbn [I.Prosa_Results_TransferSchedulability_PaperModel_clairvoyant_criterion].
    apply ar_forall_identity_correspondence => omega.
    exact (transfer_schedulability_criterion_correspondence Job (aR omega_0) (aL omega_0) (Ha omega_0)
      (bR omega) (bL omega) (Hb omega) _ _ (Hc omega_0) _ _ (Hc omega) arrR arrL Harr _ _ (Hc omega)).
  Qed.

  Theorem nonclairvoyant_criterion_correspondence (omega_0 : Omega) aR aL bR bL :
    PmAlgRel aR aL -> PmAlgRel bR bL ->
    PropSPropRel (@PM.nonclairvoyant_criterion Job jaR pR arrR Omega eR omega_0 aR bR)
      (I.Prosa_Results_TransferSchedulability_PaperModel_nonclairvoyant_criterion Job dJ jaL pL arrL Omega eL
        omega_0 aL bL).
  Proof.
    intros Ha Hb. unfold PM.nonclairvoyant_criterion. cbv beta zeta.
    cbn [I.Prosa_Results_TransferSchedulability_PaperModel_nonclairvoyant_criterion].
    apply ar_forall_identity_correspondence => omega.
    exact (transfer_schedulability_criterion_correspondence Job (aR omega_0) (aL omega_0) (Ha omega_0)
      (bR omega) (bL omega) (Hb omega) _ _ (Hc omega_0) _ _ (Hc omega) arrR arrL Harr _ _ (Hc omega_0)).
  Qed.
End Definitions.

(** ** Non-starvation witnesses and finish times *)

Section NonStarvation.
  Context (Job : eqType).
  Let dJ := ar_decidable_eq Job.
  Let PSR := prosa.model.processor.ideal.processor_state Job.
  Let PSL := I.Prosa_Model_Processor_Ideal_processor_state Job dJ.

  Variable jaR : prosa.behavior.job.JobArrival Job.
  Variable jaL : I.Prosa_Behavior_Job_JobArrival Job dJ.
  Hypothesis Hja : ArJobArrivalRel Job jaR jaL.
  Variable arrR : prosa.behavior.arrival_sequence.arrival_sequence Job.
  Variable arrL : I.Prosa_Behavior_Arrival_sequence_arrival_sequence Job dJ.
  Hypothesis Harr : ArArrivalSequenceRel Job arrR arrL.

  Let AIN (j : Job) := arrives_in_correspondence_certificate Job arrR arrL j Harr.

  Variable sR : @prosa.behavior.schedule.schedule Job PSR.
  Variable sL : I.Prosa_Behavior_Schedule_schedule_inst4 Job dJ PSL.
  Hypothesis Hs : IdScheduleRel Job sR sL.
  Variable cR : prosa.behavior.job.JobCost Job.
  Variable cL : I.Prosa_Behavior_Job_JobCost Job dJ.
  Hypothesis Hc : SvcJobCostRel Job cR cL.

  Definition PmBoundR (j : Job) := {R : duration | @prosa.behavior.service.job_response_time_bound Job PSR sR cR jaR j R}.
  Definition PmBoundL (j : Job) := I.Subtype I.Prosa_Behavior_Time_duration
    (fun R => Lean.eq (I.Prosa_Behavior_Service_job_response_time_bound_inst4 Job dJ PSL sL cL jaL j R) I.Bool_true).

  (** The response-time bound of a job, by the value of the bound (the proofs travel along). *)
  Definition PmBoundRel (j : Job) (xR : PmBoundR j) (xL : PmBoundL j) : SProp :=
    SubNatRel (sval xR) (I.Subtype_val _ _ xL).

  Let JR (j : Job) RR RL (H : SubNatRel RR RL) :=
    svc_bool_truth_correspondence _ _ (pm_jrtb_related Job jaR jaL Hja sR sL Hs cR cL Hc j RR RL H).

  Definition pm_bound_to_target (j : Job) (xR : PmBoundR j) : PmBoundL j :=
    I.Subtype_mk _ _ (sub_nat_to_imported (sval xR))
      (prop_to_sprop _ _ (JR j _ _ (sub_nat_rel_canonical (sval xR))) (proj2_sig xR)).

  Definition pm_bound_to_source (j : Job) (xL : PmBoundL j) : PmBoundR j :=
    exist _ (sub_nat_to_rocq (I.Subtype_val _ _ xL))
      (sprop_to_prop _ _ (JR j _ _ (sub_nat_rel_surjective (I.Subtype_val _ _ xL))) (I.Subtype_property _ _ xL)).

  Lemma pm_bound_source_total (j : Job) (xR : PmBoundR j) : PmBoundRel j xR (pm_bound_to_target j xR).
  Proof. exact (sub_nat_rel_canonical _). Qed.

  Lemma pm_bound_target_total (j : Job) (xL : PmBoundL j) : PmBoundRel j (pm_bound_to_source j xL) xL.
  Proof. exact (sub_nat_rel_surjective _). Qed.

  (** Witness functions. The compiled function cannot depend on the (irrelevant) proof of [arrives_in]; witnesses
      are related when their bound values are related for all proofs. *)
  Definition PmNSR := forall j, prosa.behavior.arrival_sequence.arrives_in arrR j -> PmBoundR j.
  Definition PmNSL := forall j, I.Prosa_Behavior_Arrival_sequence_arrives_in Job dJ arrL j -> PmBoundL j.

  Definition PmNSRel (nR : PmNSR) (nL : PmNSL) : SProp :=
    forall j pR pL, PmBoundRel j (nR j pR) (nL j pL).

  (** Every compiled witness has a related source witness. *)
  Definition pm_ns_to_source (nL : PmNSL) : PmNSR :=
    fun j p => pm_bound_to_source j (nL j (prop_to_sprop _ _ (AIN j) p)).

  Lemma pm_ns_target_total (nL : PmNSL) : PmNSRel (pm_ns_to_source nL) nL.
  Proof. intros j pR pL. exact (pm_bound_target_total j _). Qed.

  (** A source witness, read at one job [jf] with one arrival proof [HA], has a compiled witness that agrees with it
      there (elsewhere it reads the source witness at the proof interpreted from the compiled one). *)
  Definition pm_ns_pick (nR : PmNSR) (jf : Job) (HA : prosa.behavior.arrival_sequence.arrives_in arrR jf)
      (j : Job) (p : prosa.behavior.arrival_sequence.arrives_in arrR j) : PmBoundR j :=
    match @eqP Job j jf with
    | ReflectT E => eq_rect_r PmBoundR (nR jf HA) E
    | ReflectF _ => nR j p
    end.

  Lemma pm_ns_pick_at (nR : PmNSR) jf HA p : Logic.eq (pm_ns_pick nR jf HA jf p) (nR jf HA).
  Proof.
    rewrite /pm_ns_pick. case: eqP => [E|]; last by [].
    by rewrite (eq_irrelevance E (Logic.eq_refl jf)).
  Qed.

  Definition pm_ns_to_target_at (nR : PmNSR) jf HA : PmNSL :=
    fun j q => pm_bound_to_target j (pm_ns_pick nR jf HA j (sprop_to_prop _ _ (AIN j) q)).

  Lemma pm_ns_to_target_at_jf (nR : PmNSR) jf HA q :
    PmBoundRel jf (nR jf HA) (pm_ns_to_target_at nR jf HA jf q).
  Proof.
    unfold PmBoundRel, pm_ns_to_target_at, pm_bound_to_target. cbn.
    rewrite pm_ns_pick_at. exact (sub_nat_rel_canonical _).
  Qed.
End NonStarvation.

(** ** Declarations *)

Section Declarations.
  Context (Job : eqType).
  Let dJ := ar_decidable_eq Job.
  Let PSR := prosa.model.processor.ideal.processor_state Job.
  Let PSL := I.Prosa_Model_Processor_Ideal_processor_state Job dJ.

  Variable jaR : prosa.behavior.job.JobArrival Job.
  Variable jaL : I.Prosa_Behavior_Job_JobArrival Job dJ.
  Hypothesis Hja : ArJobArrivalRel Job jaR jaL.
  Variable pR : PM.JobPredecessors Job.
  Variable pL : I.Prosa_Results_TransferSchedulability_PaperModel_JobPredecessors Job dJ.
  Hypothesis Hp : PmPredRel Job pR pL.
  Variable arrR : prosa.behavior.arrival_sequence.arrival_sequence Job.
  Variable arrL : I.Prosa_Behavior_Arrival_sequence_arrival_sequence Job dJ.
  Hypothesis Harr : ArArrivalSequenceRel Job arrR arrL.

  Let AIN (j : Job) := arrives_in_correspondence_certificate Job arrR arrL j Harr.
  Let VALID := valid_arrival_sequence_correspondence_certificate Job jaR jaL arrR arrL Hja Harr.

  (** *** Finish-time definitions (for related inputs; the proof arguments are arbitrary on both sides) *)

  Section EvolutionInputs.
    Variable Omega : Type.
    Variable eR : PM.SystemEvolutions Omega Job.
    Variable eL : I.Prosa_Results_TransferSchedulability_PaperModel_SystemEvolutions Omega Job dJ.
    Hypothesis He : PmEvoRel Job Omega eR eL.
    Let Hc (omega : Omega) := Lean.left _ _ (He omega).
    Variable omega_0 : Omega.
    Variable aR bR : PmSchR Job jaR pR Omega eR.
    Variable aL bL : PmSchL Job jaL pL Omega eL.
    Hypothesis Ha : PmAlgRel Job jaR jaL pR pL Omega eR eL aR aL.
    Hypothesis Hb : PmAlgRel Job jaR jaL pR pL Omega eR eL bR bL.

    Theorem ref_finish_time_correspondence
        (nR : PmNSR Job jaR arrR (aR omega_0) (@PM.evo_costs Omega Job eR omega_0))
        (nL : PmNSL Job jaL arrL (aL omega_0)
          (I.Prosa_Results_TransferSchedulability_PaperModel_SystemEvolutions_evo_costs Omega Job dJ eL omega_0))
        (jf : Job) pjR pjL :
      PmBoundRel Job jaR jaL (aR omega_0) (aL omega_0) _ _ jf (nR jf pjR) (nL jf pjL) ->
      SubNatRel (@PM.ref_finish_time Job jaR pR arrR Omega eR omega_0 aR nR jf pjR)
        (I.Prosa_Results_TransferSchedulability_PaperModel_ref_finish_time Job dJ jaL pL arrL Omega eL omega_0 aL nL
          jf pjL).
    Proof.
      intro Hn. unfold PM.ref_finish_time. cbv beta zeta.
      cbn [I.Prosa_Results_TransferSchedulability_PaperModel_ref_finish_time].
      exact (pm_finish_time_rel Job jaR jaL _ _ (Ha omega_0) _ _ (Hc omega_0) jf _ _ _ _ Hn).
    Qed.

    Theorem online_finish_time_correspondence
        (nR : PmNSR Job jaR arrR (aR omega_0) (@PM.evo_costs Omega Job eR omega_0))
        (nL : PmNSL Job jaL arrL (aL omega_0)
          (I.Prosa_Results_TransferSchedulability_PaperModel_SystemEvolutions_evo_costs Omega Job dJ eL omega_0))
        (omega : Omega) (jf : Job) pjR pjL tR tL :
      PmBoundRel Job jaR jaL (aR omega_0) (aL omega_0) _ _ jf (nR jf pjR) (nL jf pjL) ->
      SubNatRel (@PM.online_finish_time Job jaR pR arrR Omega eR omega_0 aR bR nR omega jf pjR tR)
        (I.Prosa_Results_TransferSchedulability_PaperModel_online_finish_time Job dJ jaL pL arrL Omega eL omega_0 aL
          bL nL omega jf pjL tL).
    Proof.
      intro Hn. unfold PM.online_finish_time. cbv beta zeta.
      cbn [I.Prosa_Results_TransferSchedulability_PaperModel_online_finish_time].
      exact (pm_finish_time_rel Job jaR jaL _ _ (Hb omega) _ _ (Hc omega) jf _ _ _ _ Hn).
    Qed.

    Theorem online_finish_time_bounded_correspondence
        (nR : PmNSR Job jaR arrR (aR omega_0) (@PM.evo_costs Omega Job eR omega_0))
        (nL : PmNSL Job jaL arrL (aL omega_0)
          (I.Prosa_Results_TransferSchedulability_PaperModel_SystemEvolutions_evo_costs Omega Job dJ eL omega_0))
        (omega : Omega) (jf : Job) pjR pjL tR tL :
      PmBoundRel Job jaR jaL (aR omega_0) (aL omega_0) _ _ jf (nR jf pjR) (nL jf pjL) ->
      SvcBoolRel (@PM.online_finish_time_bounded Job jaR pR arrR Omega eR omega_0 aR bR nR omega jf pjR tR)
        (I.Prosa_Results_TransferSchedulability_PaperModel_online_finish_time_bounded Job dJ jaL pL arrL Omega eL
          omega_0 aL bL nL omega jf pjL tL).
    Proof.
      intro Hn. unfold PM.online_finish_time_bounded. cbv beta zeta.
      cbn [I.Prosa_Results_TransferSchedulability_PaperModel_online_finish_time_bounded].
      exact (svc_decide_le_related _ _ _ _ (online_finish_time_correspondence nR nL omega jf pjR pjL tR tL Hn)
        (ref_finish_time_correspondence nR nL jf pjR pjL Hn)).
    Qed.

    (** The strengthened witnesses are indexed by the evolution after the arrival proof. *)
    Definition PmNS'R := forall j, prosa.behavior.arrival_sequence.arrives_in arrR j -> forall omega : Omega,
      PmBoundR Job jaR (bR omega) (@PM.evo_costs Omega Job eR omega) j.
    Definition PmNS'L := forall j, I.Prosa_Behavior_Arrival_sequence_arrives_in Job dJ arrL j -> forall omega : Omega,
      PmBoundL Job jaL (bL omega)
        (I.Prosa_Results_TransferSchedulability_PaperModel_SystemEvolutions_evo_costs Omega Job dJ eL omega) j.

    Theorem online_finish_time'_correspondence (nR' : PmNS'R) (nL' : PmNS'L) (omega : Omega) (jf : Job) pjR pjL :
      PmBoundRel Job jaR jaL (bR omega) (bL omega) _ _ jf (nR' jf pjR omega) (nL' jf pjL omega) ->
      SubNatRel (@PM.online_finish_time' Job jaR pR arrR Omega eR bR nR' omega jf pjR)
        (I.Prosa_Results_TransferSchedulability_PaperModel_online_finish_time' Job dJ jaL pL arrL Omega eL bL nL'
          omega jf pjL).
    Proof.
      intro Hn. unfold PM.online_finish_time'. cbv beta zeta.
      cbn [I.Prosa_Results_TransferSchedulability_PaperModel_online_finish_time'].
      exact (pm_finish_time_rel Job jaR jaL _ _ (Hb omega) _ _ (Hc omega) jf _ _ _ _ Hn).
    Qed.

    Theorem online_finish_time_bounded'_correspondence
        (nR : PmNSR Job jaR arrR (aR omega_0) (@PM.evo_costs Omega Job eR omega_0))
        (nL : PmNSL Job jaL arrL (aL omega_0)
          (I.Prosa_Results_TransferSchedulability_PaperModel_SystemEvolutions_evo_costs Omega Job dJ eL omega_0))
        (nR' : PmNS'R) (nL' : PmNS'L) (omega : Omega) (jf : Job) pjR pjL :
      PmBoundRel Job jaR jaL (aR omega_0) (aL omega_0) _ _ jf (nR jf pjR) (nL jf pjL) ->
      PmBoundRel Job jaR jaL (bR omega) (bL omega) _ _ jf (nR' jf pjR omega) (nL' jf pjL omega) ->
      SvcBoolRel (@PM.online_finish_time_bounded' Job jaR pR arrR Omega eR omega_0 aR bR nR nR' omega jf pjR)
        (I.Prosa_Results_TransferSchedulability_PaperModel_online_finish_time_bounded' Job dJ jaL pL arrL Omega eL
          omega_0 aL bL nL nL' omega jf pjL).
    Proof.
      intros Hn Hn'. unfold PM.online_finish_time_bounded'. cbv beta zeta.
      cbn [I.Prosa_Results_TransferSchedulability_PaperModel_online_finish_time_bounded'].
      exact (svc_decide_le_related _ _ _ _ (online_finish_time'_correspondence nR' nL' omega jf pjR pjL Hn')
        (ref_finish_time_correspondence nR nL jf pjR pjL Hn)).
    Qed.
  End EvolutionInputs.
End Declarations.

(** ** Statement correspondences *)

Section Statements.
  Context (Job : eqType).
  Let dJ := ar_decidable_eq Job.
  Let PSR := prosa.model.processor.ideal.processor_state Job.
  Let PSL := I.Prosa_Model_Processor_Ideal_processor_state Job dJ.

  Variable jaR : prosa.behavior.job.JobArrival Job.
  Variable jaL : I.Prosa_Behavior_Job_JobArrival Job dJ.
  Hypothesis Hja : ArJobArrivalRel Job jaR jaL.
  Variable pR : PM.JobPredecessors Job.
  Variable pL : I.Prosa_Results_TransferSchedulability_PaperModel_JobPredecessors Job dJ.
  Hypothesis Hp : PmPredRel Job pR pL.
  Variable arrR : prosa.behavior.arrival_sequence.arrival_sequence Job.
  Variable arrL : I.Prosa_Behavior_Arrival_sequence_arrival_sequence Job dJ.
  Hypothesis Harr : ArArrivalSequenceRel Job arrR arrL.

  Let AIN (j : Job) := arrives_in_correspondence_certificate Job arrR arrL j Harr.
  Let VALID := valid_arrival_sequence_correspondence_certificate Job jaR jaL arrR arrL Hja Harr.

  Local Ltac imp H := apply ar_imp_correspondence; [exact H|].

  (** *** Shared pieces *)

  Lemma pm_max_cost_rel (Omega : Type) eR eL (He : PmEvoRel Job Omega eR eL) (omega_0 : Omega) :
    PropSPropRel
      (forall (omega : Omega) (j : Job),
        is_true (leq (@prosa.behavior.job.job_cost Job (@PM.evo_costs Omega Job eR omega) j)
          (@prosa.behavior.job.job_cost Job (@PM.evo_costs Omega Job eR omega_0) j)))
      (forall (omega : Omega) (j : Job),
        I.LE_le_inst1 Lean.Nat I.instLENat
          (I.Prosa_Behavior_Job_JobCost_job_cost Job dJ
            (I.Prosa_Results_TransferSchedulability_PaperModel_SystemEvolutions_evo_costs Omega Job dJ eL omega) j)
          (I.Prosa_Behavior_Job_JobCost_job_cost Job dJ
            (I.Prosa_Results_TransferSchedulability_PaperModel_SystemEvolutions_evo_costs Omega Job dJ eL omega_0) j)).
  Proof.
    apply ar_forall_identity_correspondence => omega.
    apply ar_forall_identity_correspondence => j.
    exact (sub_nat_le_correspondence _ _ _ _ (Lean.left _ _ (He omega) j) (Lean.left _ _ (He omega_0) j)).
  Qed.

  Lemma pm_vs (Omega : Type) eR eL (He : PmEvoRel Job Omega eR eL) (omega : Omega) sR sL (Hs : IdScheduleRel Job sR sL) :
    PropSPropRel
      (@prosa.behavior.ready.valid_schedule Job jaR PSR sR (@PM.evo_costs Omega Job eR omega)
        (@PM.delayed_precedence_ready_instance Job PSR jaR (@PM.evo_costs Omega Job eR omega) pR
          (@PM.evo_delays Omega Job eR omega)) arrR)
      (I.Prosa_Behavior_Ready_valid_schedule_inst4 Job dJ jaL PSL sL
        (I.Prosa_Results_TransferSchedulability_PaperModel_SystemEvolutions_evo_costs Omega Job dJ eL omega)
        (I.Prosa_Results_TransferSchedulability_PaperModel_delayed_precedence_ready_instance_inst4 Job dJ PSL jaL
          (I.Prosa_Results_TransferSchedulability_PaperModel_SystemEvolutions_evo_costs Omega Job dJ eL omega) pL
          (I.Prosa_Results_TransferSchedulability_PaperModel_SystemEvolutions_evo_delays Omega Job dJ eL omega))
        arrL).
  Proof.
    exact (pm_valid_schedule_rel Job jaR jaL Hja _ _ (Lean.left _ _ (He omega)) pR pL Hp _ _ (Lean.right _ _ (He omega))
      arrR arrL Harr sR sL Hs).
  Qed.

  (** *** clairvoyant_sufficiency *)

  Definition src_clairvoyant_sufficiency : Prop :=
    ltac:(type_of_term (@PM.clairvoyant_sufficiency Job jaR pR arrR)).
  Definition tgt_clairvoyant_sufficiency : SProp :=
    ltac:(type_of_term (I.Prosa_Results_TransferSchedulability_PaperModel_clairvoyant_sufficiency Job dJ jaL pL arrL)).

  Theorem clairvoyant_sufficiency_correspondence :
    PropSPropRel src_clairvoyant_sufficiency tgt_clairvoyant_sufficiency.
  Proof.
    unfold src_clairvoyant_sufficiency, tgt_clairvoyant_sufficiency.
    imp VALID.
    apply pm_forall_type => Omega.
    apply (pm_forall_evo Job Omega) => eR eL He.
    apply ar_forall_identity_correspondence => omega_0.
    imp (pm_max_cost_rel Omega eR eL He omega_0).
    apply (pm_forall_alg Job jaR jaL pR pL Omega eR eL) => aR aL Ha.
    apply (pm_forall_alg Job jaR jaL pR pL Omega eR eL) => bR bL Hb.
    imp (pm_vs Omega eR eL He omega_0 _ _ (Ha omega_0)).
    apply ar_imp_correspondence.
    { apply ar_forall_identity_correspondence => omega. exact (pm_vs Omega eR eL He omega _ _ (Hb omega)). }
    imp (clairvoyant_criterion_correspondence Job jaR jaL pR pL Omega eR eL He arrR arrL Harr omega_0 aR aL bR bL Ha Hb).
    apply ar_forall_identity_correspondence => omega.
    exact (schedulability_transferred_AB_correspondence Job jaR jaL pR pL Omega eR eL He omega_0 aR aL bR bL Ha Hb omega).
  Qed.

  (** *** clairvoyant_necessity *)

  Definition src_clairvoyant_necessity : Prop :=
    ltac:(type_of_term (@PM.clairvoyant_necessity Job jaR pR arrR)).
  Definition tgt_clairvoyant_necessity : SProp :=
    ltac:(type_of_term (I.Prosa_Results_TransferSchedulability_PaperModel_clairvoyant_necessity Job dJ jaL pL arrL)).

  Theorem clairvoyant_necessity_correspondence :
    PropSPropRel src_clairvoyant_necessity tgt_clairvoyant_necessity.
  Proof.
    unfold src_clairvoyant_necessity, tgt_clairvoyant_necessity.
    imp VALID.
    apply pm_forall_type => Omega.
    apply (pm_forall_evo Job Omega) => eR eL He.
    apply ar_forall_identity_correspondence => omega_0.
    apply (pm_forall_alg Job jaR jaL pR pL Omega eR eL) => aR aL Ha.
    apply (pm_forall_alg Job jaR jaL pR pL Omega eR eL) => bR bL Hb.
    apply ar_imp_correspondence.
    { apply ar_forall_identity_correspondence => omega. exact (pm_vs Omega eR eL He omega _ _ (Hb omega)). }
    apply ar_imp_correspondence.
    { apply ar_forall_identity_correspondence => omega.
      exact (schedulability_transferred_AB_correspondence Job jaR jaL pR pL Omega eR eL He omega_0 aR aL bR bL Ha Hb
        omega). }
    exact (clairvoyant_criterion_correspondence Job jaR jaL pR pL Omega eR eL He arrR arrL Harr omega_0 aR aL bR bL Ha Hb).
  Qed.

  (** *** nonclairvoyant_sufficiency *)

  Definition src_nonclairvoyant_sufficiency : Prop :=
    ltac:(type_of_term (@PM.nonclairvoyant_sufficiency Job jaR pR arrR)).
  Definition tgt_nonclairvoyant_sufficiency : SProp :=
    ltac:(type_of_term (I.Prosa_Results_TransferSchedulability_PaperModel_nonclairvoyant_sufficiency Job dJ jaL pL arrL)).

  Theorem nonclairvoyant_sufficiency_correspondence :
    PropSPropRel src_nonclairvoyant_sufficiency tgt_nonclairvoyant_sufficiency.
  Proof.
    unfold src_nonclairvoyant_sufficiency, tgt_nonclairvoyant_sufficiency.
    imp VALID.
    apply pm_forall_type => Omega.
    apply (pm_forall_evo Job Omega) => eR eL He.
    apply ar_forall_identity_correspondence => omega_0.
    imp (pm_max_cost_rel Omega eR eL He omega_0).
    apply (pm_forall_alg Job jaR jaL pR pL Omega eR eL) => aR aL Ha.
    apply (pm_forall_alg Job jaR jaL pR pL Omega eR eL) => bR bL Hb.
    imp (pm_vs Omega eR eL He omega_0 _ _ (Ha omega_0)).
    apply ar_imp_correspondence.
    { apply ar_forall_identity_correspondence => omega. exact (pm_vs Omega eR eL He omega _ _ (Hb omega)). }
    imp (nonclairvoyant_criterion_correspondence Job jaR jaL pR pL Omega eR eL He arrR arrL Harr omega_0 aR aL bR bL Ha Hb).
    apply ar_forall_identity_correspondence => omega.
    exact (schedulability_transferred_AB_correspondence Job jaR jaL pR pL Omega eR eL He omega_0 aR aL bR bL Ha Hb omega).
  Qed.
End Statements.

(** ** Statement correspondences over non-starvation witnesses *)

Section WitnessStatements.
  Context (Job : eqType).
  Let dJ := ar_decidable_eq Job.
  Let PSR := prosa.model.processor.ideal.processor_state Job.
  Let PSL := I.Prosa_Model_Processor_Ideal_processor_state Job dJ.

  Variable jaR : prosa.behavior.job.JobArrival Job.
  Variable jaL : I.Prosa_Behavior_Job_JobArrival Job dJ.
  Hypothesis Hja : ArJobArrivalRel Job jaR jaL.
  Variable pR : PM.JobPredecessors Job.
  Variable pL : I.Prosa_Results_TransferSchedulability_PaperModel_JobPredecessors Job dJ.
  Hypothesis Hp : PmPredRel Job pR pL.
  Variable arrR : prosa.behavior.arrival_sequence.arrival_sequence Job.
  Variable arrL : I.Prosa_Behavior_Arrival_sequence_arrival_sequence Job dJ.
  Hypothesis Harr : ArArrivalSequenceRel Job arrR arrL.

  Let AIN (j : Job) := arrives_in_correspondence_certificate Job arrR arrL j Harr.

  (** *** online_response_time_bound

      Source witnesses may depend on the proof of [arrives_in]; compiled ones cannot. From source to compiled, each
      compiled witness is read back as a proof-independent source witness; from compiled to source, the given source
      witness is matched, at the job and arrival proof the statement uses, by [pm_ns_to_target_at]. *)

  Definition src_online_response_time_bound : Prop :=
    ltac:(type_of_term (@PM.online_response_time_bound Job jaR pR arrR)).
  Definition tgt_online_response_time_bound : SProp :=
    ltac:(type_of_term (I.Prosa_Results_TransferSchedulability_PaperModel_online_response_time_bound Job dJ jaL pL arrL)).

  Theorem online_response_time_bound_correspondence :
    PropSPropRel src_online_response_time_bound tgt_online_response_time_bound.
  Proof.
    unfold src_online_response_time_bound, tgt_online_response_time_bound.
    apply pm_forall_type => Omega.
    apply (pm_forall_evo Job Omega) => eR eL He.
    apply ar_forall_identity_correspondence => omega_0.
    apply (pm_forall_alg Job jaR jaL pR pL Omega eR eL) => aR aL Ha.
    apply (pm_forall_alg Job jaR jaL pR pL Omega eR eL) => bR bL Hb.
    pose Hc := fun omega : Omega => Lean.left _ _ (He omega).
    pose ST := schedulability_transferred_AB_correspondence Job jaR jaL pR pL Omega eR eL He omega_0 aR aL bR bL Ha Hb.
    apply prop_sprop_rel_intro.
    - intros HR nL omega jf q HtL.
      pose nR := pm_ns_to_source Job jaR jaL Hja arrR arrL Harr _ _ (Ha omega_0) _ _ (Hc omega_0) nL.
      pose pA := sprop_to_prop _ _ (AIN jf) q.
      have H := HR nR omega jf pA (sprop_to_prop _ _ (ST omega) HtL).
      exact (prop_to_sprop _ _ (svc_bool_truth_correspondence _ _
        (pm_jrtb_related Job jaR jaL Hja _ _ (Hb omega) _ _ (Hc omega) jf _ _
          (pm_ns_target_total Job jaR jaL Hja arrR arrL Harr _ _ (Ha omega_0) _ _ (Hc omega_0) nL jf pA q))) H).
    - intro HL. apply strictly_inhabits. intros nR omega jf pA HtR.
      pose nL := pm_ns_to_target_at Job jaR jaL Hja arrR arrL Harr _ _ (Ha omega_0) _ _ (Hc omega_0) nR jf pA.
      pose q := prop_to_sprop _ _ (AIN jf) pA.
      have H := HL nL omega jf q (prop_to_sprop _ _ (ST omega) HtR).
      exact (sprop_to_prop _ _ (svc_bool_truth_correspondence _ _
        (pm_jrtb_related Job jaR jaL Hja _ _ (Hb omega) _ _ (Hc omega) jf _ _
          (pm_ns_to_target_at_jf Job jaR jaL Hja arrR arrL Harr _ _ (Ha omega_0) _ _ (Hc omega_0) nR jf pA q))) H).
  Qed.
End WitnessStatements.

(** ** The finish-time sufficiency statements

    Their compiled statements contain, as an argument of [online_finish_time_bounded], a proof term of the compiled
    sufficiency theorem ([I.…clairvoyant_sufficiency …]), which the export carries statement-only. The certificate's
    target replaces that proof term by a proof of the same SProp type built from the official source theorem through
    the sufficiency correspondence above (no compiled theorem is used). Proofs of an SProp are definitionally equal,
    so this target is definitionally the compiled statement; [conv_tgt_*] below checks that in the kernel. *)

Section FinishTimeStatements.
  Context (Job : eqType).
  Let dJ := ar_decidable_eq Job.
  Let PSR := prosa.model.processor.ideal.processor_state Job.
  Let PSL := I.Prosa_Model_Processor_Ideal_processor_state Job dJ.

  Variable jaR : prosa.behavior.job.JobArrival Job.
  Variable jaL : I.Prosa_Behavior_Job_JobArrival Job dJ.
  Hypothesis Hja : ArJobArrivalRel Job jaR jaL.
  Variable pR : PM.JobPredecessors Job.
  Variable pL : I.Prosa_Results_TransferSchedulability_PaperModel_JobPredecessors Job dJ.
  Hypothesis Hp : PmPredRel Job pR pL.
  Variable arrR : prosa.behavior.arrival_sequence.arrival_sequence Job.
  Variable arrL : I.Prosa_Behavior_Arrival_sequence_arrival_sequence Job dJ.
  Hypothesis Harr : ArArrivalSequenceRel Job arrR arrL.

  Definition pm_transported_cs :=
    prop_to_sprop _ _ (clairvoyant_sufficiency_correspondence Job jaR jaL Hja pR pL Hp arrR arrL Harr)
      (@PM.clairvoyant_sufficiency Job jaR pR arrR).

  Definition tgt_clairvoyant_sufficiency'_import : SProp :=
    ltac:(type_of_term (I.Prosa_Results_TransferSchedulability_PaperModel_clairvoyant_sufficiency' Job dJ jaL pL arrL)).

  Definition tgt_clairvoyant_sufficiency' : SProp :=
    ltac:(let T := type of (I.Prosa_Results_TransferSchedulability_PaperModel_clairvoyant_sufficiency' Job dJ jaL pL arrL)
          in let F := eval pattern (I.Prosa_Results_TransferSchedulability_PaperModel_clairvoyant_sufficiency Job dJ jaL pL
                                     arrL) in T
          in match F with ?G _ => let T' := eval cbv beta in (G pm_transported_cs) in exact T' end).

  Definition conv_tgt_clairvoyant_sufficiency' :
    tgt_clairvoyant_sufficiency'_import -> tgt_clairvoyant_sufficiency' := fun x => x.
  Definition src_clairvoyant_sufficiency' : Prop :=
    ltac:(type_of_term (@PM.clairvoyant_sufficiency' Job jaR pR arrR)).

  Theorem clairvoyant_sufficiency'_correspondence :
    PropSPropRel src_clairvoyant_sufficiency' tgt_clairvoyant_sufficiency'.
  Proof.
    unfold src_clairvoyant_sufficiency', tgt_clairvoyant_sufficiency'.
    pose AIN := fun j : Job => arrives_in_correspondence_certificate Job arrR arrL j Harr.
    pose VALID := valid_arrival_sequence_correspondence_certificate Job jaR jaL arrR arrL Hja Harr.
    apply prop_sprop_rel_intro.
    - intros HR hvL Omega eL omega_0 hmL aL bL wfAL wfBL nL critL omega j q.
      pose eR := pm_evo_to_source Job Omega eL.
      pose He := SystemEvolutions_target_total Job Omega eL.
      pose Hc := fun o : Omega => Lean.left _ _ (He o).
      pose aR := fun o : Omega => id_schedule_to_source Job (aL o).
      pose bR := fun o : Omega => id_schedule_to_source Job (bL o).
      pose Ha := Scheduler_target_total Job jaR jaL pR pL Omega eR eL aL.
      pose Hb := Scheduler_target_total Job jaR jaL pR pL Omega eR eL bL.
      pose nR := pm_ns_to_source Job jaR jaL Hja arrR arrL Harr _ _ (Ha omega_0) _ _ (Hc omega_0) nL.
      pose pA := sprop_to_prop _ _ (AIN j) q.
      have H := HR (sprop_to_prop _ _ VALID hvL) Omega eR omega_0
        (sprop_to_prop _ _ (pm_max_cost_rel Job Omega eR eL He omega_0) hmL) aR bR
        (sprop_to_prop _ _ (pm_vs Job jaR jaL Hja pR pL Hp arrR arrL Harr Omega eR eL He omega_0 _ _ (Ha omega_0)) wfAL)
        (fun o => sprop_to_prop _ _ (pm_vs Job jaR jaL Hja pR pL Hp arrR arrL Harr Omega eR eL He o _ _ (Hb o)) (wfBL o))
        nR
        (sprop_to_prop _ _ (clairvoyant_criterion_correspondence Job jaR jaL pR pL Omega eR eL He arrR arrL Harr omega_0 aR aL bR bL Ha Hb) critL)
        omega j pA.
      exact (prop_to_sprop _ _ (svc_bool_truth_correspondence _ _
        (online_finish_time_bounded_correspondence Job jaR jaL pR pL arrR arrL Omega eR eL He omega_0 aR bR aL bL Ha Hb
          nR nL omega j pA q _ _
          (pm_ns_target_total Job jaR jaL Hja arrR arrL Harr _ _ (Ha omega_0) _ _ (Hc omega_0) nL j pA q))) H).
    - intro HL. apply strictly_inhabits.
      intros hvR Omega eR omega_0 hmR aR bR wfAR wfBR nR critR omega j pA.
      pose eL := pm_evo_to_target Job Omega eR.
      pose He := SystemEvolutions_source_total Job Omega eR.
      pose Hc := fun o : Omega => Lean.left _ _ (He o).
      pose aL := fun o : Omega => id_schedule_to_target Job (aR o).
      pose bL := fun o : Omega => id_schedule_to_target Job (bR o).
      pose Ha := Scheduler_source_total Job jaR jaL pR pL Omega eR eL aR.
      pose Hb := Scheduler_source_total Job jaR jaL pR pL Omega eR eL bR.
      pose nL := pm_ns_to_target_at Job jaR jaL Hja arrR arrL Harr _ _ (Ha omega_0) _ _ (Hc omega_0) nR j pA.
      pose q := prop_to_sprop _ _ (AIN j) pA.
      have H := HL (prop_to_sprop _ _ VALID hvR) Omega eL omega_0
        (prop_to_sprop _ _ (pm_max_cost_rel Job Omega eR eL He omega_0) hmR) aL bL
        (prop_to_sprop _ _ (pm_vs Job jaR jaL Hja pR pL Hp arrR arrL Harr Omega eR eL He omega_0 _ _ (Ha omega_0)) wfAR)
        (fun o => prop_to_sprop _ _ (pm_vs Job jaR jaL Hja pR pL Hp arrR arrL Harr Omega eR eL He o _ _ (Hb o)) (wfBR o))
        nL
        (prop_to_sprop _ _ (clairvoyant_criterion_correspondence Job jaR jaL pR pL Omega eR eL He arrR arrL Harr omega_0 aR aL bR bL Ha Hb) critR)
        omega j q.
      exact (sprop_to_prop _ _ (svc_bool_truth_correspondence _ _
        (online_finish_time_bounded_correspondence Job jaR jaL pR pL arrR arrL Omega eR eL He omega_0 aR bR aL bL Ha Hb
          nR nL omega j pA q _ _
          (pm_ns_to_target_at_jf Job jaR jaL Hja arrR arrL Harr _ _ (Ha omega_0) _ _ (Hc omega_0) nR j pA q))) H).
  Qed.

  Definition pm_transported_ncs :=
    prop_to_sprop _ _ (nonclairvoyant_sufficiency_correspondence Job jaR jaL Hja pR pL Hp arrR arrL Harr)
      (@PM.nonclairvoyant_sufficiency Job jaR pR arrR).

  Definition tgt_nonclairvoyant_sufficiency'_import : SProp :=
    ltac:(type_of_term (I.Prosa_Results_TransferSchedulability_PaperModel_nonclairvoyant_sufficiency' Job dJ jaL pL arrL)).

  Definition tgt_nonclairvoyant_sufficiency' : SProp :=
    ltac:(let T := type of (I.Prosa_Results_TransferSchedulability_PaperModel_nonclairvoyant_sufficiency' Job dJ jaL pL
                              arrL)
          in let F := eval pattern (I.Prosa_Results_TransferSchedulability_PaperModel_nonclairvoyant_sufficiency Job dJ jaL
                                     pL arrL) in T
          in match F with ?G _ => let T' := eval cbv beta in (G pm_transported_ncs) in exact T' end).

  Definition conv_tgt_nonclairvoyant_sufficiency' :
    tgt_nonclairvoyant_sufficiency'_import -> tgt_nonclairvoyant_sufficiency' := fun x => x.

  Definition src_nonclairvoyant_sufficiency' : Prop :=
    ltac:(type_of_term (@PM.nonclairvoyant_sufficiency' Job jaR pR arrR)).

  Theorem nonclairvoyant_sufficiency'_correspondence :
    PropSPropRel src_nonclairvoyant_sufficiency' tgt_nonclairvoyant_sufficiency'.
  Proof.
    unfold src_nonclairvoyant_sufficiency', tgt_nonclairvoyant_sufficiency'.
    pose AIN := fun j : Job => arrives_in_correspondence_certificate Job arrR arrL j Harr.
    pose VALID := valid_arrival_sequence_correspondence_certificate Job jaR jaL arrR arrL Hja Harr.
    apply prop_sprop_rel_intro.
    - intros HR hvL Omega eL omega_0 hmL aL bL wfAL wfBL nL critL omega j q.
      pose eR := pm_evo_to_source Job Omega eL.
      pose He := SystemEvolutions_target_total Job Omega eL.
      pose Hc := fun o : Omega => Lean.left _ _ (He o).
      pose aR := fun o : Omega => id_schedule_to_source Job (aL o).
      pose bR := fun o : Omega => id_schedule_to_source Job (bL o).
      pose Ha := Scheduler_target_total Job jaR jaL pR pL Omega eR eL aL.
      pose Hb := Scheduler_target_total Job jaR jaL pR pL Omega eR eL bL.
      pose nR := pm_ns_to_source Job jaR jaL Hja arrR arrL Harr _ _ (Ha omega_0) _ _ (Hc omega_0) nL.
      pose pA := sprop_to_prop _ _ (AIN j) q.
      have H := HR (sprop_to_prop _ _ VALID hvL) Omega eR omega_0
        (sprop_to_prop _ _ (pm_max_cost_rel Job Omega eR eL He omega_0) hmL) aR bR
        (sprop_to_prop _ _ (pm_vs Job jaR jaL Hja pR pL Hp arrR arrL Harr Omega eR eL He omega_0 _ _ (Ha omega_0)) wfAL)
        (fun o => sprop_to_prop _ _ (pm_vs Job jaR jaL Hja pR pL Hp arrR arrL Harr Omega eR eL He o _ _ (Hb o)) (wfBL o))
        nR
        (sprop_to_prop _ _ (nonclairvoyant_criterion_correspondence Job jaR jaL pR pL Omega eR eL He arrR arrL Harr omega_0 aR aL bR bL Ha Hb) critL)
        omega j pA.
      exact (prop_to_sprop _ _ (svc_bool_truth_correspondence _ _
        (online_finish_time_bounded_correspondence Job jaR jaL pR pL arrR arrL Omega eR eL He omega_0 aR bR aL bL Ha Hb
          nR nL omega j pA q _ _
          (pm_ns_target_total Job jaR jaL Hja arrR arrL Harr _ _ (Ha omega_0) _ _ (Hc omega_0) nL j pA q))) H).
    - intro HL. apply strictly_inhabits.
      intros hvR Omega eR omega_0 hmR aR bR wfAR wfBR nR critR omega j pA.
      pose eL := pm_evo_to_target Job Omega eR.
      pose He := SystemEvolutions_source_total Job Omega eR.
      pose Hc := fun o : Omega => Lean.left _ _ (He o).
      pose aL := fun o : Omega => id_schedule_to_target Job (aR o).
      pose bL := fun o : Omega => id_schedule_to_target Job (bR o).
      pose Ha := Scheduler_source_total Job jaR jaL pR pL Omega eR eL aR.
      pose Hb := Scheduler_source_total Job jaR jaL pR pL Omega eR eL bR.
      pose nL := pm_ns_to_target_at Job jaR jaL Hja arrR arrL Harr _ _ (Ha omega_0) _ _ (Hc omega_0) nR j pA.
      pose q := prop_to_sprop _ _ (AIN j) pA.
      have H := HL (prop_to_sprop _ _ VALID hvR) Omega eL omega_0
        (prop_to_sprop _ _ (pm_max_cost_rel Job Omega eR eL He omega_0) hmR) aL bL
        (prop_to_sprop _ _ (pm_vs Job jaR jaL Hja pR pL Hp arrR arrL Harr Omega eR eL He omega_0 _ _ (Ha omega_0)) wfAR)
        (fun o => prop_to_sprop _ _ (pm_vs Job jaR jaL Hja pR pL Hp arrR arrL Harr Omega eR eL He o _ _ (Hb o)) (wfBR o))
        nL
        (prop_to_sprop _ _ (nonclairvoyant_criterion_correspondence Job jaR jaL pR pL Omega eR eL He arrR arrL Harr omega_0 aR aL bR bL Ha Hb) critR)
        omega j q.
      exact (sprop_to_prop _ _ (svc_bool_truth_correspondence _ _
        (online_finish_time_bounded_correspondence Job jaR jaL pR pL arrR arrL Omega eR eL He omega_0 aR bR aL bL Ha Hb
          nR nL omega j pA q _ _
          (pm_ns_to_target_at_jf Job jaR jaL Hja arrR arrL Harr _ _ (Ha omega_0) _ _ (Hc omega_0) nR j pA q))) H).
  Qed.

  (** *** clairvoyant_necessity'

      The witnesses occur in a hypothesis quantified over all arrival proofs. From compiled to source the compiled
      witnesses are read back proof-independently; from source to compiled each source witness is read at the source
      proof interpreted from the compiled one, where the hypothesis is used. *)

  Definition src_clairvoyant_necessity' : Prop :=
    ltac:(type_of_term (@PM.clairvoyant_necessity' Job jaR pR arrR)).
  Definition tgt_clairvoyant_necessity' : SProp :=
    ltac:(type_of_term (I.Prosa_Results_TransferSchedulability_PaperModel_clairvoyant_necessity' Job dJ jaL pL arrL)).

  Theorem clairvoyant_necessity'_correspondence :
    PropSPropRel src_clairvoyant_necessity' tgt_clairvoyant_necessity'.
  Proof.
    unfold src_clairvoyant_necessity', tgt_clairvoyant_necessity'.
    pose AIN := fun j : Job => arrives_in_correspondence_certificate Job arrR arrL j Harr.
    pose VALID := valid_arrival_sequence_correspondence_certificate Job jaR jaL arrR arrL Hja Harr.
    apply prop_sprop_rel_intro.
    - intros HR hvL Omega eL omega_0 hmL aL bL wfAL wfBL nL nL' hbL.
      pose eR := pm_evo_to_source Job Omega eL.
      pose He := SystemEvolutions_target_total Job Omega eL.
      pose Hc := fun o : Omega => Lean.left _ _ (He o).
      pose aR := fun o : Omega => id_schedule_to_source Job (aL o).
      pose bR := fun o : Omega => id_schedule_to_source Job (bL o).
      pose Ha := Scheduler_target_total Job jaR jaL pR pL Omega eR eL aL.
      pose Hb := Scheduler_target_total Job jaR jaL pR pL Omega eR eL bL.
      pose nR := pm_ns_to_source Job jaR jaL Hja arrR arrL Harr _ _ (Ha omega_0) _ _ (Hc omega_0) nL.
      pose nR' := fun j p o => pm_bound_to_source Job jaR jaL Hja (bR o) (bL o) (Hb o) _ _ (Hc o) j
        (nL' j (prop_to_sprop _ _ (AIN j) p) o).
      have hbR : forall o j p, PM.online_finish_time_bounded' arrR Omega omega_0 aR bR nR nR' o j p.
      { intros o j p.
        exact (sprop_to_prop _ _ (svc_bool_truth_correspondence _ _
          (online_finish_time_bounded'_correspondence Job jaR jaL pR pL arrR arrL Omega eR eL He omega_0 aR bR aL bL Ha
            Hb nR nL nR' nL' o j p (prop_to_sprop _ _ (AIN j) p)
            (pm_ns_target_total Job jaR jaL Hja arrR arrL Harr _ _ (Ha omega_0) _ _ (Hc omega_0) nL j p _)
            (pm_bound_target_total Job jaR jaL Hja (bR o) (bL o) (Hb o) _ _ (Hc o) j _)))
          (hbL o j (prop_to_sprop _ _ (AIN j) p))). }
      have H := HR (sprop_to_prop _ _ VALID hvL) Omega eR omega_0
        (sprop_to_prop _ _ (pm_max_cost_rel Job Omega eR eL He omega_0) hmL) aR bR
        (sprop_to_prop _ _ (pm_vs Job jaR jaL Hja pR pL Hp arrR arrL Harr Omega eR eL He omega_0 _ _ (Ha omega_0)) wfAL)
        (fun o => sprop_to_prop _ _ (pm_vs Job jaR jaL Hja pR pL Hp arrR arrL Harr Omega eR eL He o _ _ (Hb o)) (wfBL o))
        nR nR' hbR.
      exact (prop_to_sprop _ _
        (clairvoyant_criterion_correspondence Job jaR jaL pR pL Omega eR eL He arrR arrL Harr omega_0 aR aL bR bL Ha Hb) H).
    - intro HL. apply strictly_inhabits.
      intros hvR Omega eR omega_0 hmR aR bR wfAR wfBR nR nR' hbR.
      pose eL := pm_evo_to_target Job Omega eR.
      pose He := SystemEvolutions_source_total Job Omega eR.
      pose Hc := fun o : Omega => Lean.left _ _ (He o).
      pose aL := fun o : Omega => id_schedule_to_target Job (aR o).
      pose bL := fun o : Omega => id_schedule_to_target Job (bR o).
      pose Ha := Scheduler_source_total Job jaR jaL pR pL Omega eR eL aR.
      pose Hb := Scheduler_source_total Job jaR jaL pR pL Omega eR eL bR.
      pose nL := fun j q => pm_bound_to_target Job jaR jaL Hja (aR omega_0) (aL omega_0) (Ha omega_0) _ _ (Hc omega_0) j
        (nR j (sprop_to_prop _ _ (AIN j) q)).
      pose nL' := fun j q o => pm_bound_to_target Job jaR jaL Hja (bR o) (bL o) (Hb o) _ _ (Hc o) j
        (nR' j (sprop_to_prop _ _ (AIN j) q) o).
      have hbL := fun o j q => prop_to_sprop _ _ (svc_bool_truth_correspondence _ _
        (online_finish_time_bounded'_correspondence Job jaR jaL pR pL arrR arrL Omega eR eL He omega_0 aR bR aL bL Ha Hb
          nR nL nR' nL' o j (sprop_to_prop _ _ (AIN j) q) q
          (pm_bound_source_total Job jaR jaL Hja (aR omega_0) (aL omega_0) (Ha omega_0) _ _ (Hc omega_0) j _)
          (pm_bound_source_total Job jaR jaL Hja (bR o) (bL o) (Hb o) _ _ (Hc o) j _)))
        (hbR o j (sprop_to_prop _ _ (AIN j) q)).
      have H := HL (prop_to_sprop _ _ VALID hvR) Omega eL omega_0
        (prop_to_sprop _ _ (pm_max_cost_rel Job Omega eR eL He omega_0) hmR) aL bL
        (prop_to_sprop _ _ (pm_vs Job jaR jaL Hja pR pL Hp arrR arrL Harr Omega eR eL He omega_0 _ _ (Ha omega_0)) wfAR)
        (fun o => prop_to_sprop _ _ (pm_vs Job jaR jaL Hja pR pL Hp arrR arrL Harr Omega eR eL He o _ _ (Hb o)) (wfBR o))
        nL nL' hbL.
      exact (sprop_to_prop _ _
        (clairvoyant_criterion_correspondence Job jaR jaL pR pL Omega eR eL He arrR arrL Harr omega_0 aR aL bR bL Ha Hb) H).
  Qed.

End FinishTimeStatements.

(** ** The [Scheduler] type at any processor model

    [Scheduler Omega Job] is [Omega -> schedule PState] for every processor model; for any processor models related
    by the accepted [SvcProcessorStateRel] (here generic, not only the ideal one used by the statements), schedulers
    are related pointwise by the accepted [SvcScheduleRel], with covers in both directions. The other job types
    [Job0], [Job1] of the source's elaborated signature carry only the instance arguments. *)

Section GenericScheduler.
  Context (Job : eqType).
  Let dJ := ar_decidable_eq Job.
  Variable PSR : prosa.behavior.schedule.ProcessorState Job.
  Variable PSL : I.Prosa_Behavior_Schedule_ProcessorState Job dJ.
  Variable Rst : SvcProcessorStateRel Job PSR PSL.
  Variable jaR : prosa.behavior.job.JobArrival Job.
  Variable jaL : I.Prosa_Behavior_Job_JobArrival Job dJ.
  Variable pR : PM.JobPredecessors Job.
  Variable pL : I.Prosa_Results_TransferSchedulability_PaperModel_JobPredecessors Job dJ.
  Variable Omega : Type.
  Variable eR : PM.SystemEvolutions Omega Job.
  Variable eL : I.Prosa_Results_TransferSchedulability_PaperModel_SystemEvolutions Omega Job dJ.

  Definition PmGenSchR := @PM.Scheduler Omega Job PSR jaR Job pR Job eR.
  Definition PmGenSchL := I.Prosa_Results_TransferSchedulability_PaperModel_Scheduler Omega Job dJ PSL jaL Job dJ pL Job
    dJ eL.

  Definition PmGenAlgRel (aR : PmGenSchR) (aL : PmGenSchL) : SProp :=
    forall omega : Omega, SvcScheduleRel Job PSR PSL Rst (aR omega) (aL omega).

  Definition pm_gen_alg_to_target (aR : PmGenSchR) : PmGenSchL :=
    fun omega tL => svc_ps_state_to_target Job PSR PSL Rst (aR omega (sub_nat_to_rocq tL)).

  Definition pm_gen_alg_to_source (aL : PmGenSchL) : PmGenSchR :=
    fun omega tR => svc_ps_state_to_source Job PSR PSL Rst (aL omega (sub_nat_to_imported tR)).

  Lemma Scheduler_generic_source_total (aR : PmGenSchR) : PmGenAlgRel aR (pm_gen_alg_to_target aR).
  Proof.
    intros omega tR tL Ht. unfold pm_gen_alg_to_target.
    rewrite (id_nat_input tR tL Ht).
    exact (svc_ps_state_rel_canonical Job PSR PSL Rst (aR omega tR)).
  Qed.

  Lemma Scheduler_generic_target_total (aL : PmGenSchL) : PmGenAlgRel (pm_gen_alg_to_source aL) aL.
  Proof.
    intros omega tR tL Ht. unfold pm_gen_alg_to_source.
    refine (id_lean_transport (fun x => svc_ps_state_rel Job PSR PSL Rst
      (svc_ps_state_to_source Job PSR PSL Rst (aL omega (sub_nat_to_imported tR))) (aL omega x)) _ _ Ht _).
    exact (svc_ps_state_rel_surjective Job PSR PSL Rst _).
  Qed.
End GenericScheduler.
