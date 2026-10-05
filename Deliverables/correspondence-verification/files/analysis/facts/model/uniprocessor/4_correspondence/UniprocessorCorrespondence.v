From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq
  fintype bigop.
From prosa Require Import analysis.facts.model.uniprocessor.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedUniprocessor ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation
  LogicalRelation SubadditivityNatCorrespondence
  UniPlatformScheduleBaseAdapter UniPlatformScheduleFiniteOperations
  UniPlatformScheduleCorrespondence UniPlatformProcessorStateCorrespondence
  UniPlatformPropertiesCorrespondence.

Module I := ImportedUniprocessor.

(** Statement correspondence for [scheduled_job_at_neq].  The processor state,
    schedule and [uniprocessor_model] relations are the accepted two-sided
    platform certificates re-bound to this artifact; neither the source nor the
    imported theorem is used. *)

(** [j != j'] on an [eqType] versus Lean's [decide (j ≠ j')] under the
    certified [DecidableEq] encoding. *)
Lemma uni_logic_eq_to_lean_eq {A : Type} (x y : A) :
  Logic.eq x y -> Lean.eq x y.
Proof. intros []. exact (@Lean.eq_refl _ _). Qed.

Lemma uni_neq_related (Job : eqType) (j j' : Job) :
  SchBoolRel (j != j')
    (I.Decidable_decide (I.Ne Job j j')
      (I.instDecidableNot (Lean.eq j j') (sch_decidable_eq Job j j'))).
Proof.
  apply uni_logic_eq_to_lean_eq.
  unfold sch_decidable_eq. case: eqP => H; reflexivity.
Qed.

Lemma uni_bool_not_related (bR : bool) (bL : I.Bool) :
  SchBoolRel bR bL -> SchBoolRel (~~ bR) (I.Bool_not bL).
Proof.
  unfold SchBoolRel. intro H. destruct H.
  destruct bR; exact (@Lean.eq_refl _ _).
Qed.

(** Propositional shape of the conclusion under related Boolean observations. *)
Lemma uni_body_related (aR bR cR : bool) (aL bL cL : I.Bool) :
  SchBoolRel aR aL -> SchBoolRel bR bL -> SchBoolRel cR cL ->
  PropSPropRel (is_true aR -> is_true bR -> is_true (~~ cR))
    (Lean.eq aL I.Bool_true -> Lean.eq bL I.Bool_true ->
     Lean.eq (I.Bool_not cL) I.Bool_true).
Proof.
  intros Ha Hb Hc.
  have Hnc := uni_bool_not_related cR cL Hc.
  destruct (sch_bool_truth_correspondence _ _ Ha) as [HaF HaB].
  destruct (sch_bool_truth_correspondence _ _ Hb) as [HbF HbB].
  destruct (sch_bool_truth_correspondence _ _ Hnc) as [HcF HcB].
  apply prop_sprop_rel_intro.
  - intros Himp HaL HbL. exact (HcF (Himp (HaB HaL) (HbB HbL))).
  - intro HimpL. apply strictly_inhabits.
    intros HaR HbR. exact (HcB (HimpL (HaF HaR) (HbF HbR))).
Qed.

Section UniprocessorStatement.
  Context (Job : eqType).
  Context (PStateR : prosa.behavior.schedule.ProcessorState Job).
  Variable PStateL :
    I.Prosa_Behavior_Schedule_ProcessorState Job (sch_decidable_eq Job).
  Variable R : SchProcessorStateRel Job PStateR PStateL.

  Let stateToR := sch_ps_state_to_source Job PStateR PStateL R.
  Let stateToL := sch_ps_state_to_target Job PStateR PStateL R.

  Lemma uni_scheduled_at_related schedR schedL (j : Job) tR tL :
    SchScheduleRel Job PStateR PStateL (sch_ps_state_rel Job PStateR PStateL R) schedR schedL ->
    SubNatRel tR tL ->
    SchBoolRel (@prosa.behavior.service.scheduled_at Job PStateR schedR j tR)
      (I.Prosa_Behavior_Service_scheduled_at Job (sch_decidable_eq Job)
        PStateL schedL j tL).
  Proof.
    intros Hsched Ht.
    exact (scheduled_in_certificate Job PStateR PStateL R j
      (schedR tR) (schedL tL) (Hsched tR tL Ht)).
  Qed.

  Theorem scheduled_job_at_neq_statement_correspondence :
    PropSPropRel
      (@prosa.model.processor.platform_properties.uniprocessor_model Job PStateR ->
       forall (sched : prosa.behavior.schedule.schedule PStateR) (j j' : Job)
         (t : nat),
         is_true (j != j') ->
         is_true (@prosa.behavior.service.scheduled_at Job PStateR sched j t) ->
         is_true (~~ @prosa.behavior.service.scheduled_at Job PStateR sched j' t))
      (I.Prosa_Model_Processor_PlatformProperties_uniprocessor_model
         Job (sch_decidable_eq Job) PStateL ->
       forall (sched : I.Prosa_Behavior_Schedule_schedule Job
                 (sch_decidable_eq Job) PStateL) (j j' : Job)
         (t : I.Prosa_Behavior_Time_instant),
         Lean.eq (I.Decidable_decide (I.Ne Job j j')
           (I.instDecidableNot (Lean.eq j j') (sch_decidable_eq Job j j')))
           I.Bool_true ->
         Lean.eq (I.Prosa_Behavior_Service_scheduled_at Job
           (sch_decidable_eq Job) PStateL sched j t) I.Bool_true ->
         Lean.eq (I.Bool_not (I.Prosa_Behavior_Service_scheduled_at Job
           (sch_decidable_eq Job) PStateL sched j' t)) I.Bool_true).
  Proof.
    have Huni := uniprocessor_model_correspondence Job PStateR PStateL R.
    apply prop_sprop_rel_intro.
    - intros Hsource HuniL schedL j j' tL.
      pose (schedR := export_schedule Job PStateR PStateL stateToR schedL).
      pose (tR := sub_nat_to_rocq tL).
      have Hsched := schedule_export_certificate Job PStateR PStateL R schedL.
      have Ht := sub_nat_rel_surjective tL.
      exact (prop_to_sprop _ _
        (uni_body_related _ _ _ _ _ _ (uni_neq_related Job j j')
          (uni_scheduled_at_related schedR schedL j tR tL Hsched Ht)
          (uni_scheduled_at_related schedR schedL j' tR tL Hsched Ht))
        (Hsource (sprop_to_prop _ _ Huni HuniL) schedR j j' tR)).
    - intro Htarget. apply strictly_inhabits.
      intros HuniR schedR j j' tR.
      pose (schedL := import_schedule Job PStateR PStateL stateToL schedR).
      pose (tL := sub_nat_to_imported tR).
      have Hsched := schedule_import_certificate Job PStateR PStateL R schedR.
      have Ht := sub_nat_rel_canonical tR.
      exact (sprop_to_prop _ _
        (uni_body_related _ _ _ _ _ _ (uni_neq_related Job j j')
          (uni_scheduled_at_related schedR schedL j tR tL Hsched Ht)
          (uni_scheduled_at_related schedR schedL j' tR tL Hsched Ht))
        (Htarget (prop_to_sprop _ _ Huni HuniR) schedL j j' tL)).
  Qed.
End UniprocessorStatement.

(** Exact-type guards: the two sides of the certificate are literally the
    elaborated source theorem type and the imported theorem type. *)
Definition uni_source_type_guard (Job : eqType)
    (PStateR : prosa.behavior.schedule.ProcessorState Job) :
  @prosa.model.processor.platform_properties.uniprocessor_model Job PStateR ->
  forall (sched : prosa.behavior.schedule.schedule PStateR) (j j' : Job)
    (t : nat),
    is_true (j != j') ->
    is_true (@prosa.behavior.service.scheduled_at Job PStateR sched j t) ->
    is_true (~~ @prosa.behavior.service.scheduled_at Job PStateR sched j' t) :=
  @prosa.analysis.facts.model.uniprocessor.scheduled_job_at_neq Job PStateR.

Definition uni_target_type_guard (Job : eqType)
    (PStateL : I.Prosa_Behavior_Schedule_ProcessorState Job (sch_decidable_eq Job)) :
  I.Prosa_Model_Processor_PlatformProperties_uniprocessor_model
     Job (sch_decidable_eq Job) PStateL ->
  forall (sched : I.Prosa_Behavior_Schedule_schedule Job
            (sch_decidable_eq Job) PStateL) (j j' : Job)
    (t : I.Prosa_Behavior_Time_instant),
    Lean.eq (I.Decidable_decide (I.Ne Job j j')
      (I.instDecidableNot (Lean.eq j j') (sch_decidable_eq Job j j')))
      I.Bool_true ->
    Lean.eq (I.Prosa_Behavior_Service_scheduled_at Job
      (sch_decidable_eq Job) PStateL sched j t) I.Bool_true ->
    Lean.eq (I.Bool_not (I.Prosa_Behavior_Service_scheduled_at Job
      (sch_decidable_eq Job) PStateL sched j' t)) I.Bool_true :=
  @I.Prosa_Analysis_Facts_Model_Uniprocessor_scheduled_job_at_neq
    Job (sch_decidable_eq Job) PStateL.

Print Assumptions uni_neq_related.
Print Assumptions scheduled_job_at_neq_statement_correspondence.
