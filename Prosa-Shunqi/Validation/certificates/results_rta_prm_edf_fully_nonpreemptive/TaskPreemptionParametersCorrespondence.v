From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From prosa Require Import TaskPreemptionParametersSemanticSource.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedRtaPrmEdfFullyNonpreemptive ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence
  JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations
  JitterSvcScheduleOperations JitterSvcJobOperations PreemptionParameterCorrespondence.

Module I := ImportedRtaPrmEdfFullyNonpreemptive.
Module S := TaskPreemptionParametersSemanticSource.TaskPreemptionParametersSemanticSource.
Module P := prosa.PreemptionParameterSemanticSource.PreemptionParameterSemanticSource.

(** Definition certificates for [model/task/preemption/parameters.v].

    Source side: the extracted byte-identical class, instance and definition
    blocks [S.X] (over the accepted extracted parameter source [P] and the
    accepted utility sources); target side: the compiled Lean declarations.
    Inputs: the task classes pointwise ([SubNatRel] for the two work-valued
    classes, [SvcNatListRel] for the preemption points; two-way totals below),
    [TaskCost] pointwise by [SubNatRel], [job_task] by [Lean.eq], [job_cost]
    by the accepted [SvcJobCostRel], [JobPreemptable] by the accepted
    [PpJobPreemptableRel], processor states and schedules by the accepted
    two-sided [SvcProcessorStateRel]/[SvcScheduleRel], arrival sequences by
    [ArArrivalSequenceRel].  Job-level segment lengths and run-to-completion
    thresholds, [max0]/[last0]/[distances] and the preemption-model validity
    are closed by the accepted [PreemptionParameterCorrespondence]. *)

Lemma tpp_lean_transport {A : Type} (P : A -> SProp) (x y : A) :
  Lean.eq x y -> P x -> P y.
Proof. intros H. destruct H. exact (fun p => p). Qed.

Lemma tpp_logic_eq_to_lean_eq {A : Type} (x y : A) :
  Logic.eq x y -> Lean.eq x y.
Proof. intros []. exact (@Lean.eq_refl _ _). Qed.

Lemma tpp_decide_eq_related (T : eqType) (x y : T) :
  ArBoolRel (x == y) (I.Decidable_decide (Lean.eq x y) (ar_decidable_eq T x y)).
Proof.
  apply tpp_logic_eq_to_lean_eq.
  unfold ar_decidable_eq. case: eqP => H; reflexivity.
Qed.

Fixpoint tpp_nat_list_to_rocq (xs : I.List_inst1 Lean.Nat) : seq nat :=
  match xs with
  | I.List_nil_inst1 => [::]
  | I.List_cons_inst1 x tail => sub_nat_to_rocq x :: tpp_nat_list_to_rocq tail
  end.

Lemma tpp_nat_list_target_roundtrip (xs : I.List_inst1 Lean.Nat) :
  Lean.eq (svc_nat_list_to_imported (tpp_nat_list_to_rocq xs)) xs.
Proof.
  induction xs as [|x xs IH].
  - exact (@Lean.eq_refl _ _).
  - cbn [tpp_nat_list_to_rocq svc_nat_list_to_imported].
    exact (sub_imported_eq_congr2 (I.List_cons_inst1 Lean.Nat) _ _ _ _
      (sub_nat_rel_surjective x) IH).
Qed.

(** ** Task-level classes (input relations with two-way totals) *)

Section Classes.
  Context (Task : eqType).
  Let dT := ar_decidable_eq Task.

  Definition TppMaxSegmentRel (cR : S.TaskMaxNonpreemptiveSegment Task)
      (cL : I.Prosa_Model_Task_Preemption_Parameters_TaskMaxNonpreemptiveSegment Task dT) : SProp :=
    forall tsk : Task, SubNatRel (@S.task_max_nonpreemptive_segment Task cR tsk)
      (I.Prosa_Model_Task_Preemption_Parameters_TaskMaxNonpreemptiveSegment_task_max_nonpreemptive_segment
        Task dT cL tsk).

  Lemma TaskMaxNonpreemptiveSegment_source_total (cR : S.TaskMaxNonpreemptiveSegment Task) :
    TppMaxSegmentRel cR
      (I.Prosa_Model_Task_Preemption_Parameters_TaskMaxNonpreemptiveSegment_mk Task dT
        (fun tsk => sub_nat_to_imported (@S.task_max_nonpreemptive_segment Task cR tsk))).
  Proof. intro tsk. exact (@Lean.eq_refl _ _). Qed.

  Lemma TaskMaxNonpreemptiveSegment_target_total
      (cL : I.Prosa_Model_Task_Preemption_Parameters_TaskMaxNonpreemptiveSegment Task dT) :
    TppMaxSegmentRel
      ((fun tsk => sub_nat_to_rocq
        (I.Prosa_Model_Task_Preemption_Parameters_TaskMaxNonpreemptiveSegment_task_max_nonpreemptive_segment
          Task dT cL tsk)) : S.TaskMaxNonpreemptiveSegment Task) cL.
  Proof. intro tsk. exact (sub_nat_rel_surjective _). Qed.

  Definition TppRtctRel (cR : S.TaskRunToCompletionThreshold Task)
      (cL : I.Prosa_Model_Task_Preemption_Parameters_TaskRunToCompletionThreshold Task dT) : SProp :=
    forall tsk : Task, SubNatRel (@S.task_rtct Task cR tsk)
      (I.Prosa_Model_Task_Preemption_Parameters_TaskRunToCompletionThreshold_task_rtct
        Task dT cL tsk).

  Lemma TaskRunToCompletionThreshold_source_total (cR : S.TaskRunToCompletionThreshold Task) :
    TppRtctRel cR
      (I.Prosa_Model_Task_Preemption_Parameters_TaskRunToCompletionThreshold_mk Task dT
        (fun tsk => sub_nat_to_imported (@S.task_rtct Task cR tsk))).
  Proof. intro tsk. exact (@Lean.eq_refl _ _). Qed.

  Lemma TaskRunToCompletionThreshold_target_total
      (cL : I.Prosa_Model_Task_Preemption_Parameters_TaskRunToCompletionThreshold Task dT) :
    TppRtctRel
      ((fun tsk => sub_nat_to_rocq
        (I.Prosa_Model_Task_Preemption_Parameters_TaskRunToCompletionThreshold_task_rtct
          Task dT cL tsk)) : S.TaskRunToCompletionThreshold Task) cL.
  Proof. intro tsk. exact (sub_nat_rel_surjective _). Qed.

  Definition TppPointsRel (cR : S.TaskPreemptionPoints Task)
      (cL : I.Prosa_Model_Task_Preemption_Parameters_TaskPreemptionPoints Task dT) : SProp :=
    forall tsk : Task, SvcNatListRel (@S.task_preemption_points Task cR tsk)
      (I.Prosa_Model_Task_Preemption_Parameters_TaskPreemptionPoints_task_preemption_points
        Task dT cL tsk).

  Lemma TaskPreemptionPoints_source_total (cR : S.TaskPreemptionPoints Task) :
    TppPointsRel cR
      (I.Prosa_Model_Task_Preemption_Parameters_TaskPreemptionPoints_mk Task dT
        (fun tsk => svc_nat_list_to_imported (@S.task_preemption_points Task cR tsk))).
  Proof. intro tsk. exact (@Lean.eq_refl _ _). Qed.

  Lemma TaskPreemptionPoints_target_total
      (cL : I.Prosa_Model_Task_Preemption_Parameters_TaskPreemptionPoints Task dT) :
    TppPointsRel
      ((fun tsk => tpp_nat_list_to_rocq
        (I.Prosa_Model_Task_Preemption_Parameters_TaskPreemptionPoints_task_preemption_points
          Task dT cL tsk)) : S.TaskPreemptionPoints Task) cL.
  Proof. intro tsk. exact (tpp_nat_list_target_roundtrip _). Qed.

  (** ** Task-level segments and the conversion instance *)

  Variable ppR : S.TaskPreemptionPoints Task.
  Variable ppL : I.Prosa_Model_Task_Preemption_Parameters_TaskPreemptionPoints Task dT.
  Hypothesis Hpp : TppPointsRel ppR ppL.

  Theorem task_max_nonpr_segment_correspondence (tsk : Task) :
    SubNatRel (@S.task_max_nonpr_segment Task ppR tsk)
      (I.Prosa_Model_Task_Preemption_Parameters_task_max_nonpr_segment Task dT ppL tsk).
  Proof.
    unfold S.task_max_nonpr_segment.
    cbn [I.Prosa_Model_Task_Preemption_Parameters_task_max_nonpr_segment].
    exact (pp_max0_related _ _ (pp_distances_related _ _ (Hpp tsk))).
  Qed.

  Theorem task_last_nonpr_segment_correspondence (tsk : Task) :
    SubNatRel (@S.task_last_nonpr_segment Task ppR tsk)
      (I.Prosa_Model_Task_Preemption_Parameters_task_last_nonpr_segment Task dT ppL tsk).
  Proof.
    unfold S.task_last_nonpr_segment.
    cbn [I.Prosa_Model_Task_Preemption_Parameters_task_last_nonpr_segment].
    exact (pp_last0_related _ _ (pp_distances_related _ _ (Hpp tsk))).
  Qed.

  Theorem TaskPreemptionPoints_to_TaskMaxNonpreemptiveSegment_conversion_correspondence :
    TppMaxSegmentRel (@S.TaskPreemptionPoints_to_TaskMaxNonpreemptiveSegment_conversion Task ppR)
      (I.Prosa_Model_Task_Preemption_Parameters_TaskPreemptionPoints_to_TaskMaxNonpreemptiveSegment_conversion
        Task dT ppL).
  Proof. intro tsk. exact (task_max_nonpr_segment_correspondence tsk). Qed.
End Classes.

(** ** Job-level definitions *)

Section Model.
  Context (Task Job : eqType).
  Let dT := ar_decidable_eq Task.
  Let dJ := ar_decidable_eq Job.
  Variable jtR : prosa.model.task.concept.JobTask Job Task.
  Variable jtL : I.Prosa_Model_Task_Concept_JobTask Job dJ Task dT.
  Hypothesis Hjt : forall j : Job,
    Lean.eq (@prosa.model.task.concept.job_task Job Task jtR j)
      (I.Prosa_Model_Task_Concept_JobTask_job_task Job dJ Task dT jtL j).
  Variable costR : prosa.behavior.job.JobCost Job.
  Variable costL : I.Prosa_Behavior_Job_JobCost Job dJ.
  Hypothesis Hcost : SvcJobCostRel Job costR costL.
  Variable mR : S.TaskMaxNonpreemptiveSegment Task.
  Variable mL : I.Prosa_Model_Task_Preemption_Parameters_TaskMaxNonpreemptiveSegment Task dT.
  Hypothesis Hm : TppMaxSegmentRel Task mR mL.
  Variable jpR : P.JobPreemptable Job.
  Variable jpL : I.Prosa_Model_Preemption_Parameter_JobPreemptable Job dJ.
  Hypothesis Hjp : PpJobPreemptableRel Job jpR jpL.

  Let MAXNPS (j : Job) :=
    job_max_nonpreemptive_segment_correspondence Job costR costL Hcost jpR jpL Hjp j.

  Theorem job_respects_max_nonpreemptive_segment_correspondence (j : Job) :
    ArBoolRel (@S.job_respects_max_nonpreemptive_segment Task Job jtR costR mR jpR j)
      (I.Prosa_Model_Task_Preemption_Parameters_job_respects_max_nonpreemptive_segment
        Task dT Job dJ jtL costL mL jpL j).
  Proof.
    unfold S.job_respects_max_nonpreemptive_segment.
    cbn [I.Prosa_Model_Task_Preemption_Parameters_job_respects_max_nonpreemptive_segment].
    apply svc_decide_le_related; [exact (MAXNPS j)|].
    exact (sub_imported_eq_trans _ _ _ (Hm _)
      (sub_imported_eq_congr
        (I.Prosa_Model_Task_Preemption_Parameters_TaskMaxNonpreemptiveSegment_task_max_nonpreemptive_segment
          Task dT mL) _ _ (Hjt j))).
  Qed.

  Theorem nonpreemptive_regions_have_bounded_length_correspondence (j : Job) :
    PropSPropRel (@S.nonpreemptive_regions_have_bounded_length Job costR jpR j)
      (I.Prosa_Model_Task_Preemption_Parameters_nonpreemptive_regions_have_bounded_length
        Job dJ costL jpL j).
  Proof.
    unfold S.nonpreemptive_regions_have_bounded_length.
    cbn [I.Prosa_Model_Task_Preemption_Parameters_nonpreemptive_regions_have_bounded_length].
    apply ar_forall_nat_correspondence. intros rR rL Hr.
    apply ar_imp_correspondence.
    { apply ar_bool_truth_correspondence. apply ar_bool_and_related.
      - exact (svc_decide_le_related _ _ _ _ (sub_nat_rel_canonical O) Hr).
      - exact (svc_decide_le_related _ _ _ _ Hr (Hcost j)). }
    apply ar_exists_nat_correspondence. intros pR pL Hp.
    apply ar_and_correspondence.
    - apply ar_bool_truth_correspondence. apply ar_bool_and_related.
      + exact (svc_decide_le_related _ _ _ _ Hr Hp).
      + exact (svc_decide_le_related _ _ _ _ Hp
          (svc_target_add_related _ _ _ _ Hr
            (svc_target_sub_related _ _ _ _ (MAXNPS j) (sub_nat_rel_canonical 1)))).
    - exact (ar_bool_truth_correspondence _ _ (Hjp j _ _ Hp)).
  Qed.

  Variable arrR : prosa.behavior.arrival_sequence.arrival_sequence Job.
  Variable arrL : I.Prosa_Behavior_Arrival_sequence_arrival_sequence Job dJ.
  Hypothesis Harr : ArArrivalSequenceRel Job arrR arrL.

  Theorem model_with_bounded_nonpreemptive_segments_correspondence :
    PropSPropRel (@S.model_with_bounded_nonpreemptive_segments Task Job jtR costR mR jpR arrR)
      (I.Prosa_Model_Task_Preemption_Parameters_model_with_bounded_nonpreemptive_segments
        Task dT Job dJ jtL costL mL jpL arrL).
  Proof.
    unfold S.model_with_bounded_nonpreemptive_segments.
    cbn [I.Prosa_Model_Task_Preemption_Parameters_model_with_bounded_nonpreemptive_segments].
    apply ar_forall_identity_correspondence. intro j.
    apply ar_imp_correspondence; [exact (arrives_in_correspondence_certificate Job arrR arrL j Harr)|].
    apply ar_and_correspondence.
    - exact (ar_bool_truth_correspondence _ _
        (job_respects_max_nonpreemptive_segment_correspondence j)).
    - exact (nonpreemptive_regions_have_bounded_length_correspondence j).
  Qed.

  Context (PStateR : prosa.behavior.schedule.ProcessorState Job).
  Variable PStateL : I.Prosa_Behavior_Schedule_ProcessorState Job dJ.
  Variable R : SvcProcessorStateRel Job PStateR PStateL.
  Variable schedR : @prosa.behavior.schedule.schedule Job PStateR.
  Variable schedL : I.Prosa_Behavior_Schedule_schedule Job dJ PStateL.
  Hypothesis Hsched : SvcScheduleRel Job PStateR PStateL R schedR schedL.

  Theorem valid_model_with_bounded_nonpreemptive_segments_correspondence :
    PropSPropRel
      (@S.valid_model_with_bounded_nonpreemptive_segments Task Job jtR costR mR jpR PStateR arrR schedR)
      (I.Prosa_Model_Task_Preemption_Parameters_valid_model_with_bounded_nonpreemptive_segments
        Task dT Job dJ jtL costL mL jpL PStateL arrL schedL).
  Proof.
    unfold S.valid_model_with_bounded_nonpreemptive_segments.
    cbn [I.Prosa_Model_Task_Preemption_Parameters_valid_model_with_bounded_nonpreemptive_segments].
    apply ar_and_correspondence.
    - exact (valid_preemption_model_correspondence Job costR costL Hcost jpR jpL Hjp
        PStateR PStateL R schedR schedL Hsched arrR arrL Harr).
    - exact model_with_bounded_nonpreemptive_segments_correspondence.
  Qed.
End Model.

(** ** Task run-to-completion threshold *)

Section Rtct.
  Context (Task Job : eqType).
  Let dT := ar_decidable_eq Task.
  Let dJ := ar_decidable_eq Job.
  Variable tcR : prosa.model.task.concept.TaskCost Task.
  Variable tcL : I.Prosa_Model_Task_Concept_TaskCost Task dT.
  Hypothesis Htc : forall tsk : Task,
    SubNatRel (@prosa.model.task.concept.task_cost Task tcR tsk)
      (I.Prosa_Model_Task_Concept_TaskCost_task_cost Task dT tcL tsk).
  Variable rR : S.TaskRunToCompletionThreshold Task.
  Variable rL : I.Prosa_Model_Task_Preemption_Parameters_TaskRunToCompletionThreshold Task dT.
  Hypothesis Hr : TppRtctRel Task rR rL.

  Theorem task_rtc_bounded_by_cost_correspondence (tsk : Task) :
    ArBoolRel (@S.task_rtc_bounded_by_cost Task tcR rR tsk)
      (I.Prosa_Model_Task_Preemption_Parameters_task_rtc_bounded_by_cost Task dT tcL rL tsk).
  Proof.
    unfold S.task_rtc_bounded_by_cost.
    cbn [I.Prosa_Model_Task_Preemption_Parameters_task_rtc_bounded_by_cost].
    exact (svc_decide_le_related _ _ _ _ (Hr tsk) (Htc tsk)).
  Qed.

  Variable jtR : prosa.model.task.concept.JobTask Job Task.
  Variable jtL : I.Prosa_Model_Task_Concept_JobTask Job dJ Task dT.
  Hypothesis Hjt : forall j : Job,
    Lean.eq (@prosa.model.task.concept.job_task Job Task jtR j)
      (I.Prosa_Model_Task_Concept_JobTask_job_task Job dJ Task dT jtL j).
  Variable costR : prosa.behavior.job.JobCost Job.
  Variable costL : I.Prosa_Behavior_Job_JobCost Job dJ.
  Hypothesis Hcost : SvcJobCostRel Job costR costL.
  Variable jpR : P.JobPreemptable Job.
  Variable jpL : I.Prosa_Model_Preemption_Parameter_JobPreemptable Job dJ.
  Hypothesis Hjp : PpJobPreemptableRel Job jpR jpL.
  Variable arrR : prosa.behavior.arrival_sequence.arrival_sequence Job.
  Variable arrL : I.Prosa_Behavior_Arrival_sequence_arrival_sequence Job dJ.
  Hypothesis Harr : ArArrivalSequenceRel Job arrR arrL.

  Lemma tpp_job_of_task_related (tsk : Task) (j : Job) :
    ArBoolRel (@prosa.model.task.concept.job_of_task Job Task jtR tsk j)
      (I.Prosa_Model_Task_Concept_job_of_task Job dJ Task dT jtL tsk j).
  Proof.
    unfold prosa.model.task.concept.job_of_task.
    cbn [I.Prosa_Model_Task_Concept_job_of_task].
    refine (tpp_lean_transport
      (fun v => ArBoolRel (@prosa.model.task.concept.job_task Job Task jtR j == tsk)
        (I.Decidable_decide (Lean.eq v tsk) (dT v tsk))) _ _ (Hjt j) _).
    exact (tpp_decide_eq_related Task _ tsk).
  Qed.

  Theorem job_respects_task_rtc_correspondence (tsk : Task) :
    PropSPropRel (@S.job_respects_task_rtc Task Job jtR costR jpR rR arrR tsk)
      (I.Prosa_Model_Task_Preemption_Parameters_job_respects_task_rtc
        Task dT Job dJ jtL costL jpL rL arrL tsk).
  Proof.
    unfold S.job_respects_task_rtc.
    cbn [I.Prosa_Model_Task_Preemption_Parameters_job_respects_task_rtc].
    apply ar_forall_identity_correspondence. intro j.
    apply ar_imp_correspondence; [exact (arrives_in_correspondence_certificate Job arrR arrL j Harr)|].
    apply ar_imp_correspondence;
      [exact (ar_bool_truth_correspondence _ _ (tpp_job_of_task_related tsk j))|].
    exact (sub_nat_le_correspondence _ _ _ _
      (job_rtct_correspondence Job costR costL Hcost jpR jpL Hjp j) (Hr tsk)).
  Qed.

  Theorem valid_task_run_to_completion_threshold_correspondence (tsk : Task) :
    PropSPropRel
      (@S.valid_task_run_to_completion_threshold Task tcR Job jtR costR jpR rR arrR tsk)
      (I.Prosa_Model_Task_Preemption_Parameters_valid_task_run_to_completion_threshold
        Task dT tcL Job dJ jtL costL jpL rL arrL tsk).
  Proof.
    unfold S.valid_task_run_to_completion_threshold.
    cbn [I.Prosa_Model_Task_Preemption_Parameters_valid_task_run_to_completion_threshold].
    apply ar_and_correspondence.
    - exact (ar_bool_truth_correspondence _ _ (task_rtc_bounded_by_cost_correspondence tsk)).
    - exact (job_respects_task_rtc_correspondence tsk).
  Qed.
End Rtct.
