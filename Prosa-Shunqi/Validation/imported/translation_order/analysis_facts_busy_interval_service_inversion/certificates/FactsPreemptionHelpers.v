(* Re-bound copy of the accepted certificates/analysis_facts_priority_sequential/FactsPreemptionHelpers.v
   (only the imported module name differs), itself a helper-only copy of the accepted
   certificates/analysis_facts_model_preemption/
   FactsPreemptionCorrespondence.v, re-bound to this export, without its fourteen statement
   correspondences (whose target statements are not part of this export) and the tactic
   abbreviations used only by them; every helper definition and proof is unchanged. *)
From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq fintype bigop.
From prosa Require Import FactsPreemptionSemanticSource.
From prosa Require Import behavior.all model.processor.platform_properties model.schedule.scheduled
  model.priority.classes.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedBusyIntervalServiceInversion ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence
  JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations
  JitterSvcScheduleOperations JitterSvcJobOperations PreemptionParameterCorrespondence
  PreemptionTimeCorrespondence PriorityDrivenCorrespondence PStateCoverHelpers.

Module I := ImportedBusyIntervalServiceInversion.
Module S := FactsPreemptionSemanticSource.FactsPreemptionSemanticSource.
Module PP := PreemptionParameterSemanticSource.PreemptionParameterSemanticSource.
Module PTS := PreemptionTimeSemanticSource.PreemptionTimeSemanticSource.
Module PDS := PriorityDrivenSemanticSource.PriorityDrivenSemanticSource.

(** Statement correspondences for [analysis/facts/model/preemption.v].

    Source side: the extracted statements [S.statement_X] specialised at
    their leading inputs; target side: the imported Lean theorem types.
    Inputs: processor models by the accepted two-sided processor-model
    relation [IsjPSRel] of [PStateCover] (state and core conversions with the
    scheduled/service/supply observations), schedules functionally through it
    ([IsjPSchedRel]); [job_arrival] by [ArJobArrivalRel]; [job_cost] by the
    accepted [SvcJobCostRel]; [JobPreemptable] by the accepted
    [PpJobPreemptableRel]; arrival sequences by [ArArrivalSequenceRel]; JLFP
    policies pointwise on Booleans; jobs identity, instants by [SubNatRel].

    Inputs quantified inside a statement are covered in both directions by
    explicit conversions: processor models (the accepted [isj_cover_pstate]),
    arrival sequences, schedules, [JobPreemptable] instances (the accepted
    total conversions), JLFP policies, jobs (identity) and instants.
    A [JobReady] instance quantified inside a statement is used only at the
    statement's schedule: it is related on that schedule pair only
    ([FpreJrAt]), and covered by conversions whose readiness at any schedule is
    the other side's readiness at the fixed schedule conjoined with pendency
    (so the class law holds); at the fixed pair the conjunction collapses
    because ready jobs are pending.  Where the readiness binder precedes the
    arrival sequence and the schedule, the two sides are first rearranged by a
    proved equivalence ([fpre_reorder_jr]) so that the schedule pair is fixed
    before the readiness instance.  The scheduled/service observations over
    related schedules are the accepted [PStateCover] operations; service,
    completion, pendency, preemption times, preemption-model validity and the
    JLFP-at-preemption-point policy are related here by replaying the accepted
    [PreemptionParameter]/[PreemptionTime]/[PriorityDriven] certificate proofs
    over those observations.  No source or target theorem is used. *)

Ltac body_of f := let T := type of f in match T with _ -> ?B => exact B end.
Ltac type_of_term t := let T := type of t in exact T.

(** ** Generic combinators *)

Lemma fpre_or_correspondence (P Q : Prop) (PL QL : SProp) :
  PropSPropRel P PL -> PropSPropRel Q QL -> PropSPropRel (P \/ Q) (Lean.Or PL QL).
Proof.
  intros HP HQ. apply prop_sprop_rel_intro.
  - intros [p | q].
    + exact (Lean.Or_inl PL QL (prop_to_sprop _ _ HP p)).
    + exact (Lean.Or_inr PL QL (prop_to_sprop _ _ HQ q)).
  - intros [p | q]; apply strictly_inhabits.
    + left. exact (sprop_to_prop _ _ HP p).
    + right. exact (sprop_to_prop _ _ HQ q).
Qed.

Lemma fpre_exists2_correspondence (PR QR : nat -> Prop) (PL QL : Lean.Nat -> SProp) :
  (forall xR xL, SubNatRel xR xL -> PropSPropRel (PR xR) (PL xL)) ->
  (forall xR xL, SubNatRel xR xL -> PropSPropRel (QR xR) (QL xL)) ->
  PropSPropRel (exists2 x, PR x & QR x) (I.Exists Lean.Nat (fun x => And (PL x) (QL x))).
Proof.
  intros HP HQ. apply prop_sprop_rel_intro.
  - intros [x Hx Hy].
    exact (I.Exists_intro Lean.Nat _ (sub_nat_to_imported x) (And_intro _ _
      (prop_to_sprop _ _ (HP x _ (sub_nat_rel_canonical x)) Hx)
      (prop_to_sprop _ _ (HQ x _ (sub_nat_rel_canonical x)) Hy))).
  - intros [x Hxy]. destruct Hxy as [Ha Hb]. apply strictly_inhabits.
    exists (sub_nat_to_rocq x).
    + exact (sprop_to_prop _ _ (HP _ x (sub_nat_rel_surjective x)) Ha).
    + exact (sprop_to_prop _ _ (HQ _ x (sub_nat_rel_surjective x)) Hb).
Qed.

Lemma fpre_and_true_right (a b : I.Bool) :
  Lean.eq (I.Bool_and a b) I.Bool_true -> Lean.eq b I.Bool_true.
Proof.
  destruct a; cbn; intro H.
  - exact (ar_false_elim _ (ar_false_ne_true H)).
  - exact H.
Qed.

Lemma fpre_neq_related (Job : eqType) (x y : Job) :
  ArBoolRel (x != y)
    (I.Decidable_decide (I.Not (Lean.eq x y)) (I.instDecidableNot (Lean.eq x y) (ar_decidable_eq Job x y))).
Proof.
  unfold ArBoolRel. apply coq_eq_to_imported_eq.
  unfold ar_decidable_eq. case: eqP => H; reflexivity.
Qed.

Lemma fpre_and_absorb_target (bR : bool) (pL : I.Bool) :
  (bR = true -> Lean.eq pL I.Bool_true) ->
  Lean.eq (ar_bool_to_imported bR) (I.Bool_and (ar_bool_to_imported bR) pL).
Proof.
  destruct bR; cbn; intro H.
  - exact (sub_imported_eq_sym _ _ (H (Logic.eq_refl _))).
  - exact (@Lean.eq_refl _ _).
Qed.

Lemma fpre_and_absorb_source (rL : I.Bool) (pR : bool) :
  (Lean.eq rL I.Bool_true -> pR = true) ->
  Lean.eq (ar_bool_to_imported (ar_bool_to_rocq rL && pR)) rL.
Proof.
  destruct rL; cbn; intro H.
  - exact (@Lean.eq_refl _ _).
  - rewrite (H (@Lean.eq_refl _ _)). exact (@Lean.eq_refl _ _).
Qed.

Lemma fpre_bool_true_of_rel (bR : bool) (bL : I.Bool) :
  ArBoolRel bR bL -> Lean.eq bL I.Bool_true -> bR = true.
Proof.
  intros Hb HL.
  have E := imported_eq_to_coq_eq _ _ (sub_imported_eq_trans _ _ _ Hb HL).
  have E' := f_equal ar_bool_to_rocq E.
  rewrite ar_bool_source_roundtrip in E'. exact E'.
Qed.

(** Rearranging [forall jr a, A a -> forall s, B jr a s] so that the arrival
    sequence and schedule are fixed before the readiness instance. *)
Lemma fpre_reorder_jr (JR AR SR JL AL SL : Type) (AR' : AR -> Prop) (AL' : AL -> SProp)
    (BR : JR -> AR -> SR -> Prop) (BL : JL -> AL -> SL -> SProp) :
  PropSPropRel (forall a, AR' a -> forall s jr, BR jr a s) (forall a, AL' a -> forall s jr, BL jr a s) ->
  PropSPropRel (forall jr a, AR' a -> forall s, BR jr a s) (forall jr a, AL' a -> forall s, BL jr a s).
Proof.
  intro H. apply prop_sprop_rel_intro.
  - intros HR jr a Ha s.
    exact (prop_to_sprop _ _ H (fun a' Ha' s' jr' => HR jr' a' Ha' s') a Ha s jr).
  - intro HL. apply strictly_inhabits. intros jr a Ha s.
    exact (sprop_to_prop _ _ H (fun a' Ha' s' jr' => HL jr' a' Ha' s') a Ha s jr).
Qed.

Section FactsPreemption.
  Context (Job : eqType).
  Let dJ := ar_decidable_eq Job.
  Let PSL := I.Prosa_Behavior_Schedule_ProcessorState Job dJ.

  Variable jaR : prosa.behavior.job.JobArrival Job.
  Variable jaL : I.Prosa_Behavior_Job_JobArrival Job dJ.
  Hypothesis Hja : ArJobArrivalRel Job jaR jaL.
  Variable costR : prosa.behavior.job.JobCost Job.
  Variable costL : I.Prosa_Behavior_Job_JobCost Job dJ.
  Hypothesis Hcost : SvcJobCostRel Job costR costL.

  (** *** Covers not depending on the processor model *)

  Lemma fpre_forall_arr (PR : prosa.behavior.arrival_sequence.arrival_sequence Job -> Prop)
      (PL : I.Prosa_Behavior_Arrival_sequence_arrival_sequence Job dJ -> SProp) :
    (forall aR aL, ArArrivalSequenceRel Job aR aL -> PropSPropRel (PR aR) (PL aL)) ->
    PropSPropRel (forall a, PR a) (forall a, PL a).
  Proof.
    exact (isj_forall_cover_sprop _ _ (ArArrivalSequenceRel Job) (ar_arrival_sequence_to_imported Job)
      (isj_arrival_sequence_to_source Job) (ar_arrival_sequence_canonical Job)
      (isj_arrival_sequence_to_source_rel Job) PR PL).
  Qed.

  Lemma fpre_forall_jp (PR : PP.JobPreemptable Job -> Prop)
      (PL : I.Prosa_Model_Preemption_Parameter_JobPreemptable Job dJ -> SProp) :
    (forall jpR jpL, PpJobPreemptableRel Job jpR jpL -> PropSPropRel (PR jpR) (PL jpL)) ->
    PropSPropRel (forall jp, PR jp) (forall jp, PL jp).
  Proof.
    exact (isj_forall_cover_sprop _ _ (PpJobPreemptableRel Job)
      (fun jpR => I.Prosa_Model_Preemption_Parameter_JobPreemptable_mk Job dJ
        (fun j nL => ar_bool_to_imported (jpR j (sub_nat_to_rocq nL))))
      (fun jpL => ((fun j n => ar_bool_to_rocq
        (I.Prosa_Model_Preemption_Parameter_JobPreemptable_job_preemptable Job dJ jpL j
          (sub_nat_to_imported n))) : PP.JobPreemptable Job))
      (JobPreemptable_source_total Job) (JobPreemptable_target_total Job) PR PL).
  Qed.

  Definition FpreJLFPRel (pR : prosa.model.priority.definitions.JLFP_policy Job)
      (pL : I.Prosa_Model_Priority_Definitions_JLFP_policy Job dJ) : SProp :=
    forall x y : Job, ArBoolRel (@prosa.model.priority.definitions.hep_job Job pR x y)
      (I.Prosa_Model_Priority_Definitions_JLFP_policy_hep_job Job dJ pL x y).

  Lemma fpre_forall_jlfp (PR : prosa.model.priority.definitions.JLFP_policy Job -> Prop)
      (PL : I.Prosa_Model_Priority_Definitions_JLFP_policy Job dJ -> SProp) :
    (forall pR pL, FpreJLFPRel pR pL -> PropSPropRel (PR pR) (PL pL)) ->
    PropSPropRel (forall p, PR p) (forall p, PL p).
  Proof.
    apply (isj_forall_cover_sprop _ _ FpreJLFPRel
      (fun pR => I.Prosa_Model_Priority_Definitions_JLFP_policy_mk Job dJ
        (fun x y => ar_bool_to_imported (@prosa.model.priority.definitions.hep_job Job pR x y)))
      (fun pL => ((fun x y => ar_bool_to_rocq
        (I.Prosa_Model_Priority_Definitions_JLFP_policy_hep_job Job dJ pL x y))
        : prosa.model.priority.definitions.JLFP_policy Job))).
    - intros pR x y. exact (@Lean.eq_refl _ _).
    - intros pL x y. exact (ar_bool_target_roundtrip _).
  Qed.

  Lemma fpre_reflexive_rel pR pL (Hp : FpreJLFPRel pR pL) :
    PropSPropRel (@prosa.model.priority.definitions.reflexive_job_priorities Job pR)
      (I.Prosa_Model_Priority_Definitions_reflexive_job_priorities Job dJ pL).
  Proof.
    unfold prosa.model.priority.definitions.reflexive_job_priorities.
    cbn [I.Prosa_Model_Priority_Definitions_reflexive_job_priorities].
    apply ar_forall_identity_correspondence. intro j.
    exact (ar_bool_truth_correspondence _ _ (Hp j j)).
  Qed.

  (** *** A fixed processor-model pair *)

  Section Pair.
    Variable PR : prosa.behavior.schedule.ProcessorState Job.
    Variable PL : PSL.
    Variable X : IsjPSRel Job PR PL.
    Let SchedR := @prosa.behavior.schedule.schedule Job PR.
    Let SchedL := I.Prosa_Behavior_Schedule_schedule Job dJ PL.

    Lemma fpre_forall_sched (PRs : SchedR -> Prop) (PLs : SchedL -> SProp) :
      (forall sR sL, IsjPSchedRel Job PR PL X sR sL -> PropSPropRel (PRs sR) (PLs sL)) ->
      PropSPropRel (forall s, PRs s) (forall s, PLs s).
    Proof.
      exact (isj_forall_cover_sprop _ _ (IsjPSchedRel Job PR PL X) (isj_psr_sched_to_target Job PR PL X)
        (isj_psr_sched_to_source Job PR PL X) (isj_psr_sched_to_target_rel Job PR PL X)
        (isj_psr_sched_to_source_rel Job PR PL X) PRs PLs).
    Qed.

    Section Sched.
      Variable sR : SchedR.
      Variable sL : SchedL.
      Hypothesis Hs : IsjPSchedRel Job PR PL X sR sL.

      Let Hsa := isj_psr_scheduled_at_related Job PR PL X sR sL Hs.
      Let Hse := isj_psr_service_at_related Job PR PL X sR sL Hs.

      Lemma fpre_scheduled_at_related (j : Job) tR tL (Ht : SubNatRel tR tL) :
        ArBoolRel (@prosa.behavior.service.scheduled_at Job PR sR j tR)
          (I.Prosa_Behavior_Service_scheduled_at Job dJ PL sL j tL).
      Proof. exact (Hsa j tR tL Ht). Qed.

      Lemma fpre_service_related (j : Job) tR tL (Ht : SubNatRel tR tL) :
        SubNatRel (@prosa.behavior.service.service Job PR sR j tR)
          (I.Prosa_Behavior_Service_service Job dJ PL sL j tL).
      Proof.
        unfold prosa.behavior.service.service.
        cbn [I.Prosa_Behavior_Service_service].
        exact (isj_service_during_related Job PR PL sR sL Hse j O tR Lean.Nat_zero tL
          (sub_nat_rel_canonical O) Ht).
      Qed.

      Lemma fpre_completed_by_related (j : Job) tR tL (Ht : SubNatRel tR tL) :
        ArBoolRel (@prosa.behavior.service.completed_by Job PR sR costR j tR)
          (I.Prosa_Behavior_Service_completed_by Job dJ PL sL costL j tL).
      Proof.
        unfold prosa.behavior.service.completed_by.
        cbn [I.Prosa_Behavior_Service_completed_by].
        exact (svc_decide_le_related _ _ _ _ (Hcost j) (fpre_service_related j tR tL Ht)).
      Qed.

      Lemma fpre_pending_related (j : Job) tR tL (Ht : SubNatRel tR tL) :
        ArBoolRel (@prosa.behavior.service.pending Job PR sR costR jaR j tR)
          (I.Prosa_Behavior_Service_pending Job dJ PL sL costL jaL j tL).
      Proof.
        unfold prosa.behavior.service.pending.
        cbn [I.Prosa_Behavior_Service_pending].
        exact (ar_bool_and_related _ _ _ _ (has_arrived_correspondence_certificate Job jaR jaL j Hja tR tL Ht)
          (svc_bool_not_related _ _ (fpre_completed_by_related j tR tL Ht))).
      Qed.

      Variable arrR : prosa.behavior.arrival_sequence.arrival_sequence Job.
      Variable arrL : I.Prosa_Behavior_Arrival_sequence_arrival_sequence Job dJ.
      Hypothesis Harr : ArArrivalSequenceRel Job arrR arrL.

      Lemma fpre_come_from_rel :
        PropSPropRel (@prosa.behavior.ready.jobs_come_from_arrival_sequence Job PR sR arrR)
          (I.Prosa_Behavior_Ready_jobs_come_from_arrival_sequence Job dJ PL sL arrL).
      Proof. exact (isj_jobs_come_from_related Job PR PL sR sL Hsa arrR arrL Harr). Qed.

      Lemma fpre_must_arrive_rel :
        PropSPropRel (@prosa.behavior.ready.jobs_must_arrive_to_execute Job jaR PR sR)
          (I.Prosa_Behavior_Ready_jobs_must_arrive_to_execute Job dJ jaL PL sL).
      Proof.
        unfold prosa.behavior.ready.jobs_must_arrive_to_execute.
        cbn [I.Prosa_Behavior_Ready_jobs_must_arrive_to_execute].
        apply ar_forall_identity_correspondence. intro j.
        apply ar_forall_nat_correspondence. intros tR tL Ht.
        apply ar_imp_correspondence; [exact (ar_bool_truth_correspondence _ _ (Hsa j _ _ Ht))|].
        exact (ar_bool_truth_correspondence _ _ (has_arrived_correspondence_certificate Job jaR jaL j Hja tR tL Ht)).
      Qed.

      Lemma fpre_is_idle_related tR tL (Ht : SubNatRel tR tL) :
        ArBoolRel (@prosa.model.schedule.scheduled.is_idle Job PR arrR sR tR)
          (I.Prosa_Model_Schedule_Scheduled_is_idle Job dJ PL arrL sL tL).
      Proof. exact (isj_is_idle_related Job PR PL sR sL Hsa arrR arrL Harr tR tL Ht). Qed.

      Section Preemptable.
        Variable jpR : PP.JobPreemptable Job.
        Variable jpL : I.Prosa_Model_Preemption_Parameter_JobPreemptable Job dJ.
        Hypothesis Hjp : PpJobPreemptableRel Job jpR jpL.

        Lemma fpre_pt_case (tR : nat) (tL : Lean.Nat) (l : seq Job) :
          SubNatRel tR tL ->
          ArListRel l (I.Prosa_Model_Schedule_Scheduled_scheduled_jobs_at Job dJ PL arrL sL tL) ->
          ArBoolRel
            (if ohead l is Some j then @PP.job_preemptable Job jpR j (@prosa.behavior.service.service Job PR sR j tR)
             else true)
            (I.Prosa_Model_Schedule_PreemptionTime_preemption_time Job dJ jpL arrL PL sL tL).
        Proof.
          have Hsj := I.Prosa_Validation_PreemptionTimeInterface_production_scheduled_job_at_eq
            Job dJ arrL PL sL tL.
          destruct l as [|j js]; intros Ht Hl; cbn [ohead].
          - refine (sub_imported_eq_sym _ _
              (I.Prosa_Validation_PreemptionTimeInterface_production_preemption_time_none
                Job dJ jpL arrL PL sL tL _)).
            refine (sub_imported_eq_trans _ _ _ Hsj _).
            refine (sub_imported_eq_trans _ _ _
              (sub_imported_eq_congr (I.List_head__q Job) _ _ (sub_imported_eq_sym _ _ Hl)) _).
            exact (@Lean.eq_refl _ _).
          - refine (sub_imported_eq_trans _ _ _ _ (sub_imported_eq_sym _ _
              (I.Prosa_Validation_PreemptionTimeInterface_production_preemption_time_some
                Job dJ jpL arrL PL sL tL j _))).
            + exact (Hjp j _ _ (fpre_service_related j tR tL Ht)).
            + refine (sub_imported_eq_trans _ _ _ Hsj _).
              refine (sub_imported_eq_trans _ _ _
                (sub_imported_eq_congr (I.List_head__q Job) _ _ (sub_imported_eq_sym _ _ Hl)) _).
              exact (@Lean.eq_refl _ _).
        Qed.

        Lemma fpre_preemption_time_related tR tL (Ht : SubNatRel tR tL) :
          ArBoolRel (@PTS.preemption_time Job jpR arrR PR sR tR)
            (I.Prosa_Model_Schedule_PreemptionTime_preemption_time Job dJ jpL arrL PL sL tL).
        Proof.
          unfold PTS.preemption_time, prosa.model.schedule.scheduled.scheduled_job_at.
          exact (fpre_pt_case tR tL _ Ht (isj_scheduled_jobs_at_related Job PR PL sR sL Hsa arrR arrL Harr tR tL Ht)).
        Qed.

        Lemma fpre_valid_preemption_model_rel :
          PropSPropRel (@PP.valid_preemption_model Job costR jpR PR arrR sR)
            (I.Prosa_Model_Preemption_Parameter_valid_preemption_model Job dJ costL jpL PL arrL sL).
        Proof.
          unfold PP.valid_preemption_model.
          cbn [I.Prosa_Model_Preemption_Parameter_valid_preemption_model].
          apply ar_forall_identity_correspondence. intro j.
          apply ar_imp_correspondence; [exact (arrives_in_correspondence_certificate Job arrR arrL j Harr)|].
          apply ar_and_correspondence.
          { exact (ar_bool_truth_correspondence _ _
              (job_cannot_become_nonpreemptive_before_execution_correspondence Job jpR jpL Hjp j)). }
          apply ar_and_correspondence.
          { exact (ar_bool_truth_correspondence _ _
              (job_cannot_be_nonpreemptive_after_completion_correspondence Job costR costL Hcost jpR jpL Hjp j)). }
          apply ar_and_correspondence.
          - unfold PP.not_preemptive_implies_scheduled.
            cbn [I.Prosa_Model_Preemption_Parameter_not_preemptive_implies_scheduled].
            apply ar_forall_nat_correspondence. intros tR tL Ht.
            apply ar_imp_correspondence.
            + exact (ar_bool_truth_correspondence _ _
                (svc_bool_not_related _ _ (Hjp j _ _ (fpre_service_related j tR tL Ht)))).
            + exact (ar_bool_truth_correspondence _ _ (Hsa j tR tL Ht)).
          - unfold PP.execution_starts_with_preemption_point.
            cbn [I.Prosa_Model_Preemption_Parameter_execution_starts_with_preemption_point].
            apply ar_forall_nat_correspondence. intros tR tL Ht.
            have Ht1 := pp_succ_related tR tL Ht.
            apply ar_imp_correspondence.
            + exact (ar_bool_truth_correspondence _ _ (svc_bool_not_related _ _ (Hsa j tR tL Ht))).
            + apply ar_imp_correspondence.
              * exact (ar_bool_truth_correspondence _ _ (Hsa j _ _ Ht1)).
              * exact (ar_bool_truth_correspondence _ _ (Hjp j _ _ (fpre_service_related j _ _ Ht1))).
        Qed.
      End Preemptable.

      (** *** Readiness at this schedule pair *)

      Definition FpreJrAt (jrR : @prosa.behavior.ready.JobReady Job PR costR jaR)
          (jrL : I.Prosa_Behavior_Ready_JobReady Job dJ PL costL jaL) : SProp :=
        forall j tR tL, SubNatRel tR tL ->
          ArBoolRel (@prosa.behavior.ready.job_ready Job PR costR jaR jrR sR j tR)
            (I.Prosa_Behavior_Ready_JobReady_job_ready Job dJ PL costL jaL jrL sL j tL).

      Definition fpre_jr_to_target (jrR : @prosa.behavior.ready.JobReady Job PR costR jaR) :
          I.Prosa_Behavior_Ready_JobReady Job dJ PL costL jaL :=
        I.Prosa_Behavior_Ready_JobReady_mk Job dJ PL costL jaL
          (fun s j tL => I.Bool_and
            (ar_bool_to_imported (@prosa.behavior.ready.job_ready Job PR costR jaR jrR sR j (sub_nat_to_rocq tL)))
            (I.Prosa_Behavior_Service_pending Job dJ PL s costL jaL j tL))
          (fun s j t H => fpre_and_true_right _ _ H).

      Definition fpre_jr_to_source (jrL : I.Prosa_Behavior_Ready_JobReady Job dJ PL costL jaL) :
          @prosa.behavior.ready.JobReady Job PR costR jaR :=
        @prosa.behavior.ready.Build_JobReady Job PR costR jaR
          (fun s j t => ar_bool_to_rocq
            (I.Prosa_Behavior_Ready_JobReady_job_ready Job dJ PL costL jaL jrL sL j (sub_nat_to_imported t))
            && @prosa.behavior.service.pending Job PR s costR jaR j t)
          (fun s j t H => proj2 (andP H)).

      Lemma fpre_jr_to_target_rel jrR : FpreJrAt jrR (fpre_jr_to_target jrR).
      Proof.
        intros j tR tL Ht. unfold ArBoolRel, fpre_jr_to_target. cbn.
        have Hp := fpre_pending_related j tR tL Ht.
        destruct Ht. rewrite sub_nat_rocq_roundtrip.
        destruct jrR as [f Hf]. cbn.
        apply fpre_and_absorb_target. intro Hr.
        have Hpr : @prosa.behavior.service.pending Job PR sR costR jaR j tR = true := Hf sR j tR Hr.
        rewrite Hpr in Hp. exact (sub_imported_eq_sym _ _ Hp).
      Qed.

      Lemma fpre_jr_to_source_rel jrL : FpreJrAt (fpre_jr_to_source jrL) jrL.
      Proof.
        intros j tR tL Ht. unfold ArBoolRel, fpre_jr_to_source. cbn.
        have Hp := fpre_pending_related j tR tL Ht.
        have Hlaw := I.Prosa_Behavior_Ready_JobReady_ready_implies_pending Job dJ PL costL jaL jrL sL j tL.
        destruct Ht.
        apply fpre_and_absorb_source. intro Hr.
        exact (fpre_bool_true_of_rel _ _ Hp (Hlaw Hr)).
      Qed.

      Lemma fpre_forall_jr (PRr : @prosa.behavior.ready.JobReady Job PR costR jaR -> Prop)
          (PLr : I.Prosa_Behavior_Ready_JobReady Job dJ PL costL jaL -> SProp) :
        (forall jrR jrL, FpreJrAt jrR jrL -> PropSPropRel (PRr jrR) (PLr jrL)) ->
        PropSPropRel (forall jr, PRr jr) (forall jr, PLr jr).
      Proof.
        exact (isj_forall_cover_sprop _ _ FpreJrAt fpre_jr_to_target fpre_jr_to_source
          fpre_jr_to_target_rel fpre_jr_to_source_rel PRr PLr).
      Qed.

      Section Ready.
        Variable jrR : @prosa.behavior.ready.JobReady Job PR costR jaR.
        Variable jrL : I.Prosa_Behavior_Ready_JobReady Job dJ PL costL jaL.
        Hypothesis Hjr : FpreJrAt jrR jrL.

        Lemma fpre_valid_schedule_rel :
          PropSPropRel (@prosa.behavior.ready.valid_schedule Job jaR PR sR costR jrR arrR)
            (I.Prosa_Behavior_Ready_valid_schedule Job dJ jaL PL sL costL jrL arrL).
        Proof.
          unfold prosa.behavior.ready.valid_schedule, prosa.behavior.ready.jobs_must_be_ready_to_execute.
          cbn [I.Prosa_Behavior_Ready_valid_schedule I.Prosa_Behavior_Ready_jobs_must_be_ready_to_execute].
          apply ar_and_correspondence; [exact fpre_come_from_rel|].
          apply ar_forall_identity_correspondence. intro j.
          apply ar_forall_nat_correspondence. intros tR tL Ht.
          apply ar_imp_correspondence; [exact (ar_bool_truth_correspondence _ _ (Hsa j _ _ Ht))|].
          exact (ar_bool_truth_correspondence _ _ (Hjr j tR tL Ht)).
        Qed.

        Lemma fpre_backlogged_related (j : Job) tR tL (Ht : SubNatRel tR tL) :
          ArBoolRel (@prosa.behavior.ready.backlogged Job PR costR jaR jrR sR j tR)
            (I.Prosa_Behavior_Ready_backlogged Job dJ PL costL jaL jrL sL j tL).
        Proof.
          unfold prosa.behavior.ready.backlogged. cbn [I.Prosa_Behavior_Ready_backlogged].
          exact (ar_bool_and_related _ _ _ _ (Hjr j tR tL Ht) (svc_bool_not_related _ _ (Hsa j tR tL Ht))).
        Qed.

        Lemma fpre_respects_jlfp_rel jpR jpL (Hjp : PpJobPreemptableRel Job jpR jpL) pR pL
            (Hp : FpreJLFPRel pR pL) :
          PropSPropRel (@PDS.respects_JLFP_policy_at_preemption_point Job jaR costR PR jpR jrR arrR sR pR)
            (I.Prosa_Model_Schedule_PriorityDriven_respects_JLFP_policy_at_preemption_point
              Job dJ jaL costL PL jpL jrL arrL sL pL).
        Proof.
          unfold PDS.respects_JLFP_policy_at_preemption_point, PDS.respects_JLDP_policy_at_preemption_point.
          cbn [I.Prosa_Model_Schedule_PriorityDriven_respects_JLFP_policy_at_preemption_point
            I.Prosa_Model_Schedule_PriorityDriven_respects_JLDP_policy_at_preemption_point].
          apply ar_forall_identity_correspondence. intro j.
          apply ar_forall_identity_correspondence. intro j_hp.
          apply ar_forall_nat_correspondence. intros tR tL Ht.
          apply ar_imp_correspondence; [exact (arrives_in_correspondence_certificate Job arrR arrL j Harr)|].
          apply ar_imp_correspondence;
            [exact (ar_bool_truth_correspondence _ _ (fpre_preemption_time_related jpR jpL Hjp tR tL Ht))|].
          apply ar_imp_correspondence;
            [exact (ar_bool_truth_correspondence _ _ (fpre_backlogged_related j tR tL Ht))|].
          apply ar_imp_correspondence; [exact (ar_bool_truth_correspondence _ _ (Hsa j_hp tR tL Ht))|].
          exact (ar_bool_truth_correspondence _ _ (Hp j_hp j)).
        Qed.
      End Ready.
    End Sched.
  End Pair.

End FactsPreemption.
