(* Helper-only copy of accepted certificates/analysis_facts_edf_definitions/EdfDefinitionsHelpers.v: the imported
   module name differs, and the lemma pa_preemption_time_related (whose preemption-time constant is not exported
   here) is removed; all other blocks are byte-identical. *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From prosa Require Import PreemptionAwareSemanticSource.
From prosa Require Import model.processor.ideal model.schedule.work_conserving
  implementation.definitions.generic_scheduler.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedFactsEdfOpt ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence
  JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations
  JitterSvcScheduleOperations JitterSvcJobOperations PreemptionParameterCorrespondence
  IdealUniSchedulerCorrespondence.

Module I := ImportedFactsEdfOpt.
Module S := PreemptionAwareSemanticSource.PreemptionAwareSemanticSource.
Module U := IdealUniSchedulerSemanticSource.IdealUniSchedulerSemanticSource.
Module PP := PreemptionParameterSemanticSource.PreemptionParameterSemanticSource.
Module RS := ReadinessSemanticSource.ReadinessSemanticSource.
Module LP := ScheduleLimitedPreemptiveSemanticSource.ScheduleLimitedPreemptiveSemanticSource.
Module PT := PreemptionTimeSemanticSource.PreemptionTimeSemanticSource.

(** Helper certificates of [implementation/facts/ideal_uni/preemption_aware.v] restricted to
    the ideal-state schedule covers, the [pending] relation, [preemption_time] and
    [jobs_come_from_arrival_sequence] (its accepted PreemptionAwareCorrespondence without the
    readiness covers and statement correspondences, whose readiness and prefix targets are not
    instantiated at the ideal processor in this export), re-bound to this export.

    Source side: the extracted statements [S.statement_X] specialised at
    their leading inputs; target side: the imported Lean theorem types.  The
    processor model is fixed to the ideal uniprocessor on both sides: states
    are related by the constructor-preserving Option map and schedules
    pointwise ([IdScheduleRel] of the accepted scheduler certificate);
    [job_cost] by [SvcJobCostRel], [job_arrival] by [ArJobArrivalRel], arrival
    sequences by [ArArrivalSequenceRel]; the readiness model by its
    [job_ready] on related schedules and instants, the preemption model
    pointwise ([PpJobPreemptableRel]), [choose_job] on related instants and
    job lists.  Inputs quantified inside a statement are covered in both
    directions: schedules, job lists, preemption models and [choose_job]
    functions by explicit conversions; readiness models (always quantified
    together with the [nonclairvoyant_readiness] hypothesis) among
    nonclairvoyant models, whose [job_ready] respects pointwise-equal
    schedules, by readiness models built from the other side's [job_ready]
    with the pending obligation transported through the related [pending]
    (so no functional extensionality is needed).  The scheduler definitions
    are related by the accepted scheduler certificate; [preemption_time] and
    [scheduled_job_at] through the accepted filter and [arrivals_up_to]
    certificates.  No source or target theorem is used. *)

Ltac body_of f := let T := type of f in match T with _ -> ?B => exact B end.
Ltac type_of_term t := let T := type of t in exact T.

(** ** Generic combinators *)

Lemma pa_forall_cover (A B : Type) (Rel : A -> B -> SProp)
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

(** A cover restricted to the inputs satisfying a related side condition. *)
Lemma pa_forall_cond_cover (A B : Type) (Rel : A -> B -> SProp)
    (PA : A -> Prop) (PB : B -> SProp) (toB : A -> B) (toA : B -> A)
    (HtoB : forall a, PA a -> Rel a (toB a)) (HtoA : forall b, PB b -> Rel (toA b) b)
    (QA : A -> Prop) (QB : B -> SProp) :
  (forall a b, Rel a b -> PropSPropRel (PA a) (PB b)) ->
  (forall a b, Rel a b -> PropSPropRel (QA a) (QB b)) ->
  PropSPropRel (forall a, PA a -> QA a) (forall b, PB b -> QB b).
Proof.
  intros HP HQ. apply prop_sprop_rel_intro.
  - intros HR b pb.
    have Hr := HtoA b pb.
    exact (prop_to_sprop _ _ (HQ _ _ Hr) (HR (toA b) (sprop_to_prop _ _ (HP _ _ Hr) pb))).
  - intro HL. apply strictly_inhabits. intros a pa.
    have Hr := HtoB a pa.
    exact (sprop_to_prop _ _ (HQ _ _ Hr) (HL (toB a) (prop_to_sprop _ _ (HP _ _ Hr) pa))).
Qed.

Lemma pa_exists_identity_correspondence (T : Type) (PR : T -> Prop) (PL : T -> SProp) :
  (forall x, PropSPropRel (PR x) (PL x)) ->
  PropSPropRel (exists x, PR x) (I.Exists T PL).
Proof.
  intro HP. apply prop_sprop_rel_intro.
  - intros [x Hx]. exact (I.Exists_intro T PL x (prop_to_sprop _ _ (HP x) Hx)).
  - intros [x Hx]. apply strictly_inhabits. exists x.
    exact (sprop_to_prop _ _ (HP x) Hx).
Qed.

Lemma pa_bool_eq_correspondence (bR cR : bool) (bL cL : I.Bool) :
  SvcBoolRel bR bL -> SvcBoolRel cR cL -> PropSPropRel (bR = cR) (Lean.eq bL cL).
Proof.
  intros Hb Hc. apply prop_sprop_rel_intro.
  - intro E. destruct E.
    exact (sub_imported_eq_trans _ _ _ (sub_imported_eq_sym _ _ Hb) Hc).
  - intro E. apply strictly_inhabits.
    have EL := imported_eq_to_coq_eq _ _
      (sub_imported_eq_trans _ _ _ Hb (sub_imported_eq_trans _ _ _ E (sub_imported_eq_sym _ _ Hc))).
    destruct bR, cR; cbn in EL; solve [reflexivity | discriminate EL].
Qed.

Lemma pa_bool_true_elim (b : bool) (G : SProp) :
  Lean.eq (svc_bool_to_imported b) I.Bool_true -> (b = true -> G) -> G.
Proof.
  destruct b; intros H K; first exact (K (erefl true)).
  exact (id_lean_transport
    (fun x => match x with
              | I.Bool_true => G
              | I.Bool_false => Lean.eq I.Bool_false I.Bool_false
              end) _ _ H (@Lean.eq_refl _ _)).
Qed.

Lemma pa_true_of_rocq (bL : I.Bool) : svc_bool_to_rocq bL = true -> Lean.eq bL I.Bool_true.
Proof. destruct bL; cbn; intro H; solve [discriminate H | exact (@Lean.eq_refl _ _)]. Qed.

Lemma pa_list_input {T : Type} (xsR : seq T) (xsL : I.List T) :
  ArListRel xsR xsL -> Logic.eq (ar_list_to_rocq xsL) xsR.
Proof.
  intro H. have E := f_equal ar_list_to_rocq (imported_eq_to_coq_eq _ _ H).
  rewrite ar_list_source_roundtrip in E. exact (Logic.eq_sym E).
Qed.

Lemma pa_forall_list (T : Type) (PR : seq T -> Prop) (PL : I.List T -> SProp) :
  (forall xsR xsL, ArListRel xsR xsL -> PropSPropRel (PR xsR) (PL xsL)) ->
  PropSPropRel (forall xs, PR xs) (forall xs, PL xs).
Proof.
  exact (pa_forall_cover _ _ ArListRel ar_list_to_imported ar_list_to_rocq
    (fun xs => @Lean.eq_refl _ _) ar_list_target_roundtrip PR PL).
Qed.

(** ** The ideal uniprocessor *)

Section PreemptionAware.
  Context (Job : eqType).
  Let dJ := ar_decidable_eq Job.
  Let PSR := prosa.model.processor.ideal.processor_state Job.
  Let PSL := I.Prosa_Model_Processor_Ideal_processor_state Job dJ.
  Let SchedR := @prosa.behavior.schedule.schedule Job PSR.
  Let SchedL := I.Prosa_Behavior_Schedule_schedule_inst4 Job dJ PSL.

  (** *** Schedule covers *)

  Definition pa_sched_to_target (sR : SchedR) : SchedL :=
    fun tL => id_opt_to_imported (sR (sub_nat_to_rocq tL)).

  Definition pa_sched_to_source (sL : SchedL) : SchedR :=
    fun tR => id_opt_to_rocq (sL (sub_nat_to_imported tR)).

  Lemma pa_sched_to_target_rel sR : IdScheduleRel Job sR (pa_sched_to_target sR).
  Proof.
    intros tR tL Ht. unfold IdOptRel, pa_sched_to_target.
    rewrite (id_nat_input _ _ Ht). exact (@Lean.eq_refl _ _).
  Qed.

  Lemma pa_sched_to_source_rel sL : IdScheduleRel Job (pa_sched_to_source sL) sL.
  Proof.
    intros tR tL Ht.
    exact (sub_imported_eq_trans _ _ _ (id_opt_target_roundtrip _) (sub_imported_eq_congr sL _ _ Ht)).
  Qed.

  Lemma pa_forall_sched (PR : SchedR -> Prop) (PL : SchedL -> SProp) :
    (forall sR sL, IdScheduleRel Job sR sL -> PropSPropRel (PR sR) (PL sL)) ->
    PropSPropRel (forall s, PR s) (forall s, PL s).
  Proof.
    exact (pa_forall_cover _ _ (IdScheduleRel Job) pa_sched_to_target pa_sched_to_source
      pa_sched_to_target_rel pa_sched_to_source_rel PR PL).
  Qed.

  Lemma pa_pointwise (sR : SchedR) (sL : SchedL) (Hs : IdScheduleRel Job sR sL) (t : nat) :
    sR t = pa_sched_to_source sL t.
  Proof.
    have E := f_equal id_opt_to_rocq (imported_eq_to_coq_eq _ _ (Hs t _ (sub_nat_rel_canonical t))).
    rewrite id_opt_source_roundtrip in E. exact E.
  Qed.

  Variable jcR : prosa.behavior.job.JobCost Job.
  Variable jcL : I.Prosa_Behavior_Job_JobCost Job dJ.
  Hypothesis Hjc : SvcJobCostRel Job jcR jcL.
  Variable jaR : prosa.behavior.job.JobArrival Job.
  Variable jaL : I.Prosa_Behavior_Job_JobArrival Job dJ.
  Hypothesis Hja : ArJobArrivalRel Job jaR jaL.
  Variable arrR : prosa.behavior.arrival_sequence.arrival_sequence Job.
  Variable arrL : I.Prosa_Behavior_Arrival_sequence_arrival_sequence Job dJ.
  Hypothesis Harr : ArArrivalSequenceRel Job arrR arrL.

  Let RMR := @prosa.behavior.ready.JobReady Job PSR jcR jaR.
  Let RML := I.Prosa_Behavior_Ready_JobReady_inst4 Job dJ PSL jcL jaL.

  Definition PaReadyRel (rmR : RMR) (rmL : RML) : SProp :=
    forall sR sL, IdScheduleRel Job sR sL -> forall (j : Job) tR tL, SubNatRel tR tL ->
      SvcBoolRel (@prosa.behavior.ready.job_ready Job PSR jcR jaR rmR sR j tR)
        (I.Prosa_Behavior_Ready_JobReady_job_ready_inst4 Job dJ PSL jcL jaL rmL sL j tL).

  Definition PaChooseRel (cjR : nat -> seq Job -> option Job)
      (cjL : I.Prosa_Behavior_Time_instant -> I.List Job -> I.Option Job) : SProp :=
    forall tR tL, SubNatRel tR tL -> forall xsR xsL, ArListRel xsR xsL ->
      IdOptRel (cjR tR xsR) (cjL tL xsL).

  Lemma pa_pending_related (sR : SchedR) (sL : SchedL) (Hs : IdScheduleRel Job sR sL)
      (j : Job) (tR : nat) (tL : Lean.Nat) (Ht : SubNatRel tR tL) :
    SvcBoolRel (@prosa.behavior.service.pending Job PSR sR jcR jaR j tR)
      (I.Prosa_Behavior_Service_pending_inst4 Job dJ PSL sL jcL jaL j tL).
  Proof.
    unfold prosa.behavior.service.pending, prosa.behavior.service.completed_by.
    cbn [I.Prosa_Behavior_Service_pending_inst4
      I.Prosa_Validation_ServiceInterface_completedByProjection_inst4].
    exact (ar_bool_and_related _ _ _ _ (has_arrived_correspondence_certificate Job jaR jaL j Hja tR tL Ht)
      (svc_bool_not_related _ _ (svc_decide_le_related _ _ _ _ (Hjc j)
        (iu_service_related Job sR sL Hs j tR tL Ht)))).
  Qed.

  (** *** Preemption times and validity on related schedules *)

  Section Scheduler.
    Variable jpR : PP.JobPreemptable Job.
    Variable jpL : I.Prosa_Model_Preemption_Parameter_JobPreemptable Job dJ.
    Hypothesis Hjp : PpJobPreemptableRel Job jpR jpL.

    Lemma pa_jobs_come_from_rel sR sL (Hs : IdScheduleRel Job sR sL) :
      PropSPropRel (prosa.behavior.ready.jobs_come_from_arrival_sequence sR arrR)
        (I.Prosa_Behavior_Ready_jobs_come_from_arrival_sequence_inst4 Job dJ PSL sL arrL).
    Proof.
      unfold prosa.behavior.ready.jobs_come_from_arrival_sequence.
      cbn [I.Prosa_Behavior_Ready_jobs_come_from_arrival_sequence_inst4].
      apply ar_forall_identity_correspondence. intro j.
      apply ar_forall_nat_correspondence. intros tR tL Ht.
      apply ar_imp_correspondence;
        [exact (svc_bool_truth_correspondence _ _ (iu_scheduled_at_related Job sR sL Hs j tR tL Ht))|].
      exact (arrives_in_correspondence_certificate Job arrR arrL j Harr).
    Qed.

  End Scheduler.

End PreemptionAware.
