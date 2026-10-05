From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq bigop.
From prosa Require Import FactsDynamicSuspensionSemanticSource.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedFactsDynamicSuspension ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence ArrivalsCorrespondence
  CurvesCorrespondence DsPStateCover
  JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations
  JitterSvcScheduleOperations JitterSvcJobOperations ProgressHelpers SuspensionCorrespondence
  DynamicSuspensionCorrespondence.

Module I := ImportedFactsDynamicSuspension.
Module S := FactsDynamicSuspensionSemanticSource.FactsDynamicSuspensionSemanticSource.
Module SS := SuspensionSemanticSource.SuspensionSemanticSource.
Module DS := DynamicSuspensionSemanticSource.DynamicSuspensionSemanticSource.

(** Statement certificates for [analysis/facts/model/dynamic_suspension.v].
    For related processor states and schedules (the accepted two-sided
    Service relations), job-task, job-arrival, job-cost, job-suspension,
    max-arrivals and task-total-suspension instances and arrival sequences
    (the accepted relations, each with two-way totals), each extracted source
    statement (the authoritative elaborated type, specialised at these inputs)
    and the imported Lean theorem type are related; tasks and jobs are
    identity carriers, instants and durations are covered in both directions
    by [SubNatRel].  The interval sums of the suspension indicator go through
    the accepted interval-sum relation, the sums over the task's arrivals
    through the accepted sequence-sum and task-arrivals relations. *)

Ltac body_of f := let T := type of f in match T with _ -> ?B => exact B end.
Ltac type_of_term t := let T := type of t in exact T.

Lemma fds_nat_of_bool_related (bR : bool) (bL : I.Bool) :
  SvcBoolRel bR bL -> SubNatRel (nat_of_bool bR) (I.Bool_toNat bL).
Proof. intro Hb. destruct Hb. destruct bR; exact (@Lean.eq_refl _ _). Qed.

Section FactsDynamicSuspension.
  Context (Task Job : eqType).
  Let dT := svc_decidable_eq Task.
  Let dJ := svc_decidable_eq Job.

  Variable ttsR : DS.TaskTotalSuspension Task.
  Variable ttsL : I.Prosa_Model_Task_Suspension_Dynamic_TaskTotalSuspension Task dT.
  Hypothesis Htts : DsuspTaskTotalSuspensionRel Task ttsR ttsL.
  Variable jtR : prosa.model.task.concept.JobTask Job Task.
  Variable jtL : I.Prosa_Model_Task_Concept_JobTask Job dJ Task dT.
  Hypothesis Hjt : DsuspJobTaskRel Task Job jtR jtL.
  Variable jaR : prosa.behavior.job.JobArrival Job.
  Variable jaL : I.Prosa_Behavior_Job_JobArrival Job dJ.
  Hypothesis Hja : SvcJobArrivalRel Job jaR jaL.
  Variable costR : prosa.behavior.job.JobCost Job.
  Variable costL : I.Prosa_Behavior_Job_JobCost Job dJ.
  Hypothesis Hcost : SvcJobCostRel Job costR costL.
  Variable sR : SS.JobSuspension Job.
  Variable sL : I.Prosa_Model_Readiness_Suspension_JobSuspension Job dJ.
  Hypothesis Hs : SuspJobSuspensionRel Job sR sL.

  Lemma fds_valid_related :
    PropSPropRel (@DS.valid_dynamic_suspensions Job costR sR Task jtR ttsR)
      (I.Prosa_Model_Task_Suspension_Dynamic_valid_dynamic_suspensions Job dJ costL sL Task dT jtL ttsL).
  Proof.
    exact (valid_dynamic_suspensions_correspondence Task Job costR costL Hcost sR sL Hs jtR jtL Hjt ttsR ttsL Htts).
  Qed.

  Section Sched.
    Context (PStateR : prosa.behavior.schedule.ProcessorState Job).
    Variable PStateL : I.Prosa_Behavior_Schedule_ProcessorState Job dJ.
    Variable R : SvcProcessorStateRel Job PStateR PStateL.
    Variable schedR : @prosa.behavior.schedule.schedule Job PStateR.
    Variable schedL : I.Prosa_Behavior_Schedule_schedule Job dJ PStateL.
    Hypothesis Hsched : SvcScheduleRel Job PStateR PStateL R schedR schedL.

    Lemma fds_suspended_related (j : Job) tR tL : SubNatRel tR tL ->
      SvcBoolRel (@SS.suspended Job PStateR jaR costR sR schedR j tR)
        (I.Prosa_Model_Readiness_Suspension_suspended Job dJ PStateL jaL costL sL schedL j tL).
    Proof.
      exact (suspended_correspondence Job PStateR PStateL R schedR schedL Hsched jaR jaL Hja
        costR costL Hcost sR sL Hs j tR tL).
    Qed.

    Lemma fds_job_sum_related (j : Job) aR aL bR bL :
      SubNatRel aR aL -> SubNatRel bR bL ->
      SubNatRel (\sum_(aR <= t < bR) nat_of_bool (@SS.suspended Job PStateR jaR costR sR schedR j t))
        (svc_target_interval_value aL bL (fun t =>
          I.Bool_toNat (I.Prosa_Model_Readiness_Suspension_suspended Job dJ PStateL jaL costL sL schedL j t))).
    Proof.
      intros Ha Hb.
      apply svc_interval_sum_related; [exact Ha | exact Hb |].
      intros tR tL Ht. exact (fds_nat_of_bool_related _ _ (fds_suspended_related j tR tL Ht)).
    Qed.
  End Sched.

  (** ** Covers for the quantifiers inside the statements *)

  Lemma fds_forall_cover (A B : Type) (Rel : A -> B -> SProp) (toB : A -> B) (toA : B -> A)
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

  Lemma fds_nat_input (nR : nat) (nL : Lean.Nat) : SubNatRel nR nL -> Logic.eq (sub_nat_to_rocq nL) nR.
  Proof.
    intro H. have E := f_equal sub_nat_to_rocq (imported_eq_to_coq_eq _ _ H).
    rewrite sub_nat_rocq_roundtrip in E. exact (Logic.eq_sym E).
  Qed.

  Lemma fds_forall_sched (PStateR : prosa.behavior.schedule.ProcessorState Job)
      (PStateL : I.Prosa_Behavior_Schedule_ProcessorState Job dJ) (R : SvcProcessorStateRel Job PStateR PStateL)
      (PR : @prosa.behavior.schedule.schedule Job PStateR -> Prop)
      (PL : I.Prosa_Behavior_Schedule_schedule Job dJ PStateL -> SProp) :
    (forall schR schL, SvcScheduleRel Job PStateR PStateL R schR schL -> PropSPropRel (PR schR) (PL schL)) ->
    PropSPropRel (forall schR, PR schR) (forall schL, PL schL).
  Proof.
    apply (fds_forall_cover _ _ (SvcScheduleRel Job PStateR PStateL R)
      (fun schR tL => svc_ps_state_to_target Job PStateR PStateL R (schR (sub_nat_to_rocq tL)))
      (fun schL tR => svc_ps_state_to_source Job PStateR PStateL R (schL (sub_nat_to_imported tR)))).
    - intros schR tR tL Ht. cbn. rewrite (fds_nat_input _ _ Ht).
      exact (svc_ps_state_rel_canonical Job PStateR PStateL R (schR tR)).
    - intros schL tR tL Ht. cbn.
      exact (dsusp_lean_transport (fun v => svc_ps_state_rel Job PStateR PStateL R
          (svc_ps_state_to_source Job PStateR PStateL R (schL (sub_nat_to_imported tR))) (schL v)) _ _ Ht
        (svc_ps_state_rel_surjective Job PStateR PStateL R (schL (sub_nat_to_imported tR)))).
  Qed.

  Definition fds_arr_to_source (arrL : I.Prosa_Behavior_Arrival_sequence_arrival_sequence Job dJ) :
      prosa.behavior.arrival_sequence.arrival_sequence Job :=
    fun t => ar_list_to_rocq (arrL (sub_nat_to_imported t)).

  Lemma fds_forall_arr (PR : prosa.behavior.arrival_sequence.arrival_sequence Job -> Prop)
      (PL : I.Prosa_Behavior_Arrival_sequence_arrival_sequence Job dJ -> SProp) :
    (forall aR aL, ArArrivalSequenceRel Job aR aL -> PropSPropRel (PR aR) (PL aL)) ->
    PropSPropRel (forall aR, PR aR) (forall aL, PL aL).
  Proof.
    apply (fds_forall_cover _ _ (ArArrivalSequenceRel Job) (ar_arrival_sequence_to_imported Job) fds_arr_to_source).
    - exact (ar_arrival_sequence_canonical Job).
    - intros aL tR tL Ht. unfold fds_arr_to_source.
      exact (dsusp_lean_transport (fun v => ArListRel (ar_list_to_rocq (aL (sub_nat_to_imported tR))) (aL v)) _ _ Ht
        (ar_list_target_roundtrip _)).
  Qed.

  (** ** Statement correspondences *)

  Definition src_job_suspension_bounded : Prop :=
    ltac:(body_of (fun s : S.statement_job_suspension_bounded => s Task ttsR Job jtR jaR costR sR)).
  Definition tgt_job_suspension_bounded : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Model_DynamicSuspension_job_suspension_bounded
      Task dT Job dJ ttsL jtL jaL costL sL)).
  Theorem job_suspension_bounded_correspondence :
    PropSPropRel src_job_suspension_bounded tgt_job_suspension_bounded.
  Proof.
    unfold src_job_suspension_bounded, tgt_job_suspension_bounded.
    apply pg_imp_correspondence; [exact fds_valid_related|].
    apply (rs_forall_pstate Job); intros PStateR PStateL [R].
    apply (fds_forall_sched PStateR PStateL R); intros schR schL Hsch.
    apply pg_forall_identity_correspondence; intro tsk.
    apply pg_forall_nat_correspondence; intros t1R t1L H1.
    apply pg_forall_nat_correspondence; intros dR dL Hd.
    apply pg_forall_identity_correspondence; intro j.
    apply pg_imp_correspondence.
    - exact (ar_bool_truth_correspondence _ _
        (job_of_task_related Job Task jtR jtL Hjt tsk tsk (@Lean.eq_refl _ tsk) j)).
    - exact (sub_nat_le_correspondence _ _ _ _
        (fds_job_sum_related PStateR PStateL R schR schL Hsch j _ _ _ _ H1 (sub_add_correspondence _ _ _ _ H1 Hd))
        (Htts tsk)).
  Qed.

  Section Curve.
    Variable maR : prosa.model.task.arrival.curves.MaxArrivals Task.
    Variable maL : I.Prosa_Model_Task_Arrival_Curves_MaxArrivals Task dT.
    Hypothesis Hma : CvMaxArrivalsRel Task maR maL.

    Definition src_suspension_of_task_bounded : Prop :=
      ltac:(body_of (fun s : S.statement_suspension_of_task_bounded => s Task maR ttsR Job jtR jaR costR sR)).
    Definition tgt_suspension_of_task_bounded : SProp :=
      ltac:(type_of_term (@I.Prosa_Analysis_Facts_Model_DynamicSuspension_suspension_of_task_bounded
        Task dT Job dJ maL ttsL jtL jaL costL sL)).
    Theorem suspension_of_task_bounded_correspondence :
      PropSPropRel src_suspension_of_task_bounded tgt_suspension_of_task_bounded.
    Proof.
      unfold src_suspension_of_task_bounded, tgt_suspension_of_task_bounded.
      apply pg_imp_correspondence; [exact fds_valid_related|].
      apply fds_forall_arr; intros aR aL Ha.
      apply (rs_forall_pstate Job); intros PStateR PStateL [R].
      apply (fds_forall_sched PStateR PStateL R); intros schR schL Hsch.
      apply pg_forall_identity_correspondence; intro tsk.
      apply pg_forall_nat_correspondence; intros t1R t1L H1.
      apply pg_forall_nat_correspondence; intros dR dL Hd.
      apply pg_imp_correspondence.
      - exact (respects_max_arrivals_correspondence Task Job jtR jtL Hjt aR aL Ha tsk _ _ (Hma tsk)).
      - apply sub_nat_le_correspondence; [|exact (sub_mul_correspondence _ _ _ _ (Hma tsk _ _ Hd) (Htts tsk))].
        have H2 := sub_add_correspondence _ _ _ _ H1 Hd.
        apply svc_interval_sum_related; [exact H1 | exact H2 |].
        intros tR tL Ht.
        apply ari_sum_related.
        + intro x. exact (fds_nat_of_bool_related _ _
            (fds_suspended_related PStateR PStateL R schR schL Hsch x tR tL Ht)).
        + exact (task_arrivals_between_correspondence Job Task jtR jtL Hjt aR aL Ha tsk tsk _ _ _ _
            (@Lean.eq_refl _ tsk) H1 H2).
    Qed.
  End Curve.
End FactsDynamicSuspension.
