From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From prosa Require Import model.schedule.tdma.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedTdmaProjectedFull.
From FoundationCertificates Require Import
  PropSPropFoundation LogicalRelation SubadditivityNatCorrespondence
  TdmaBaseAdapter TdmaSeqsetAdapter TdmaPolicyAdapter
  TdmaValidityCorrespondence TdmaNumericCorrespondence
  TdmaArithmeticAdapter TdmaJobTaskAdapter TdmaProcessorOperations.

Lemma tdma_imp_correspondence (P Q : Prop) (PL QL : SProp) :
  PropSPropRel P PL -> PropSPropRel Q QL ->
  PropSPropRel (P -> Q) (PL -> QL).
Proof.
  intros HP HQ. apply prop_sprop_rel_intro.
  - intros H p. apply (prop_to_sprop _ _ HQ).
    exact (H (sprop_to_prop _ _ HP p)).
  - intro H. apply strictly_inhabits. intro p.
    apply (sprop_to_prop _ _ HQ).
    exact (H (prop_to_sprop _ _ HP p)).
Qed.

Lemma tdma_false_correspondence :
  PropSPropRel Logic.False ImportedTdmaProjectedFull.False.
Proof.
  apply prop_sprop_rel_intro.
  - exact ar_coq_false_to_target.
  - intro H. exact (match H with end).
Qed.

Lemma tdma_not_correspondence (P : Prop) (PL : SProp) :
  PropSPropRel P PL ->
  PropSPropRel (~ P) (ImportedTdmaProjectedFull.Not PL).
Proof.
  intro HP. change (PropSPropRel (P -> Logic.False)
    (PL -> ImportedTdmaProjectedFull.False)).
  exact (tdma_imp_correspondence P Logic.False PL
    ImportedTdmaProjectedFull.False HP tdma_false_correspondence).
Qed.

Lemma tdma_or_correspondence (P Q : Prop) (PL QL : SProp) :
  PropSPropRel P PL -> PropSPropRel Q QL ->
  PropSPropRel (P \/ Q) (Lean.Or PL QL).
Proof.
  intros HP HQ. apply prop_sprop_rel_intro.
  - intros [p | q].
    + exact (Lean.Or_inl PL QL (prop_to_sprop _ _ HP p)).
    + exact (Lean.Or_inr PL QL (prop_to_sprop _ _ HQ q)).
  - intro H.
    destruct H as [p | q].
    + exact (strictly_inhabits (or_introl _ (sprop_to_prop _ _ HP p))).
    + exact (strictly_inhabits (or_intror _ (sprop_to_prop _ _ HQ q))).
Qed.

Lemma tdma_exists_correspondence (T : Type)
    (PR : T -> Prop) (PL : T -> SProp) :
  (forall x, PropSPropRel (PR x) (PL x)) ->
  PropSPropRel (exists x, PR x) (ImportedTdmaProjectedFull.Exists T PL).
Proof.
  intro HP. apply prop_sprop_rel_intro.
  - intros [x Hx]. exact (ImportedTdmaProjectedFull.Exists_intro T PL x
      (prop_to_sprop _ _ (HP x) Hx)).
  - intros [x Hx]. apply strictly_inhabits.
    exists x. exact (sprop_to_prop _ _ (HP x) Hx).
Qed.

Lemma tdma_forall_identity_correspondence (T : Type)
    (PR : T -> Prop) (PL : T -> SProp) :
  (forall x, PropSPropRel (PR x) (PL x)) ->
  PropSPropRel (forall x, PR x) (forall x, PL x).
Proof.
  intro HP. apply prop_sprop_rel_intro.
  - intros HR x. exact (prop_to_sprop _ _ (HP x) (HR x)).
  - intro HL. apply strictly_inhabits. intro x.
    exact (sprop_to_prop _ _ (HP x) (HL x)).
Qed.

Lemma tdma_forall_nat_correspondence
    (PR : nat -> Prop) (PL : Lean.Nat -> SProp) :
  (forall nR nL, SubNatRel nR nL ->
    PropSPropRel (PR nR) (PL nL)) ->
  PropSPropRel (forall nR, PR nR) (forall nL, PL nL).
Proof.
  intro HP. apply prop_sprop_rel_intro.
  - intros HR nL. exact (prop_to_sprop _ _
      (HP (sub_nat_to_rocq nL) nL (sub_nat_rel_surjective nL))
      (HR (sub_nat_to_rocq nL))).
  - intro HL. apply strictly_inhabits. intro nR.
    exact (sprop_to_prop _ _
      (HP nR (sub_nat_to_imported nR) (sub_nat_rel_canonical nR))
      (HL (sub_nat_to_imported nR))).
Qed.

Lemma tdma_bool_of_truth (bR : bool)
    (bL : ImportedTdmaProjectedFull.Bool) :
  PropSPropRel (is_true bR)
    (Lean.eq bL ImportedTdmaProjectedFull.Bool_true) ->
  ArBoolRel bR bL.
Proof.
  intro Htruth. destruct bR, bL; cbn [ArBoolRel ar_bool_to_imported].
  - exact (ar_false_elim _ (ar_false_ne_true
      (prop_to_sprop _ _ Htruth (Logic.eq_refl true)))).
  - exact (@Lean.eq_refl _ _).
  - exact (@Lean.eq_refl _ _).
  - have Hfalse := sprop_to_prop _ _ Htruth (@Lean.eq_refl _ _).
    discriminate Hfalse.
Qed.

Lemma tdma_bool_not_related bR bL :
  ArBoolRel bR bL ->
  ArBoolRel (~~ bR) (ImportedTdmaProjectedFull.Bool_not bL).
Proof.
  intro Hb. destruct bR, bL; cbn in *;
    try exact (@Lean.eq_refl _ _);
    try exact (ar_false_elim _ (ar_false_ne_true Hb));
    try exact (ar_false_elim _
      (ar_false_ne_true (sub_imported_eq_sym _ _ Hb))).
Qed.

Section TdmaJobSlot.
  Context (Task Job : eqType).
  Context (policyR : prosa.model.schedule.tdma.TDMAPolicy Task).
  Context (policyL : ImportedTdmaProjectedFull.Prosa_Model_Schedule_Tdma_TDMAPolicy
    Task (ar_decidable_eq Task)).
  Context (Hpolicy : TdmaPolicyRel Task policyR policyL).
  Context (jobTaskR : prosa.model.task.concept.JobTask Job Task).
  Context (jobTaskL : ImportedTdmaProjectedFull.Prosa_Model_Task_Concept_JobTask
    Job (ar_decidable_eq Job) Task (ar_decidable_eq Task)).
  Context (HjobTask : TdmaJobTaskRel Job Task jobTaskR jobTaskL).
  Context (tsR : @prosa.util.seqset.set Task).
  Context (tsL : ImportedTdmaProjectedFull.Prosa_Util_Seqset_set Task
    (ar_decidable_eq Task)).
  Context (Hts : RocqSeqSetRel Task tsR tsL).

  Theorem job_in_time_slot_correspondence (j : Job) tR tL :
    SubNatRel tR tL ->
    ArBoolRel
      (@prosa.model.schedule.tdma.job_in_time_slot
        Task Job jobTaskR tsR policyR j tR)
      (ImportedTdmaProjectedFull.Prosa_Model_Schedule_Tdma_job_in_time_slot
        Task (ar_decidable_eq Task) policyL
        Job (ar_decidable_eq Job) jobTaskL tsL j tL).
  Proof.
    intro Ht.
    change (ArBoolRel
      (@prosa.model.schedule.tdma.task_in_time_slot Task tsR policyR
        (@prosa.model.task.concept.job_task Job Task jobTaskR j) tR)
      (ImportedTdmaProjectedFull.Prosa_Model_Schedule_Tdma_task_in_time_slot
        Task (ar_decidable_eq Task) policyL tsL
        (ImportedTdmaProjectedFull.Prosa_Model_Task_Concept_JobTask_job_task
          Job (ar_decidable_eq Job) Task (ar_decidable_eq Task) jobTaskL j)
        tL)).
    unfold ArBoolRel.
    exact (sub_imported_eq_trans _ _ _
      (task_in_time_slot_correspondence Task policyR policyL Hpolicy
        tsR tsL Hts
        (@prosa.model.task.concept.job_task Job Task jobTaskR j) tR tL Ht)
      (sub_imported_eq_congr
        (fun tsk =>
          ImportedTdmaProjectedFull.Prosa_Model_Schedule_Tdma_task_in_time_slot
            Task (ar_decidable_eq Task) policyL tsL tsk tL)
        _ _ (HjobTask j))).
  Qed.
End TdmaJobSlot.

Section TdmaSchedule.
  Context (Task Job : eqType).
  Context (policyR : prosa.model.schedule.tdma.TDMAPolicy Task).
  Context (policyL : ImportedTdmaProjectedFull.Prosa_Model_Schedule_Tdma_TDMAPolicy
    Task (ar_decidable_eq Task)).
  Context (Hpolicy : TdmaPolicyRel Task policyR policyL).
  Context (jobTaskR : prosa.model.task.concept.JobTask Job Task).
  Context (jobTaskL : ImportedTdmaProjectedFull.Prosa_Model_Task_Concept_JobTask
    Job (ar_decidable_eq Job) Task (ar_decidable_eq Task)).
  Context (HjobTask : TdmaJobTaskRel Job Task jobTaskR jobTaskL).
  Context (tsR : @prosa.util.seqset.set Task).
  Context (tsL : ImportedTdmaProjectedFull.Prosa_Util_Seqset_set Task
    (ar_decidable_eq Task)).
  Context (Hts : RocqSeqSetRel Task tsR tsL).
  Context (PStateR : prosa.behavior.schedule.ProcessorState Job).
  Context (PStateL : ImportedTdmaProjectedFull.Prosa_Behavior_Schedule_ProcessorState
    Job (ar_decidable_eq Job)).
  Context (schedR : @prosa.behavior.schedule.schedule Job PStateR).
  Context (schedL : ImportedTdmaProjectedFull.Prosa_Behavior_Schedule_schedule
    Job (ar_decidable_eq Job) PStateL).

  Context (R : EdfProcessorRel Job PStateR PStateL).
  Context (Hsched : EdfScheduleRel Job PStateR PStateL R schedR schedL).

  Definition TdmaScheduledAtRel : SProp :=
    forall j tR tL, SubNatRel tR tL ->
      ArBoolRel
        (@prosa.behavior.service.scheduled_at Job PStateR schedR j tR)
        (ImportedTdmaProjectedFull.Prosa_Behavior_Service_scheduled_at
          Job (ar_decidable_eq Job) PStateL schedL j tL).

  Lemma tdma_scheduled_at_bool_related : TdmaScheduledAtRel.
  Proof.
    intros j tR tL Ht. apply tdma_bool_of_truth.
    exact (edf_scheduled_at_truth Job PStateR PStateL R
      schedR schedL j tR tL Hsched Ht).
  Qed.

  Theorem sched_implies_in_slot_correspondence (j : Job) tR tL :
    SubNatRel tR tL ->
    PropSPropRel
      (@prosa.model.schedule.tdma.sched_implies_in_slot
        Task Job PStateR jobTaskR schedR tsR policyR j tR)
      (ImportedTdmaProjectedFull.Prosa_Model_Schedule_Tdma_sched_implies_in_slot
        Task (ar_decidable_eq Task) policyL
        Job (ar_decidable_eq Job) jobTaskL PStateL schedL tsL j tL).
  Proof.
    intro Ht.
    change (PropSPropRel
      (is_true (@prosa.behavior.service.scheduled_at
        Job PStateR schedR j tR) ->
       is_true (@prosa.model.schedule.tdma.job_in_time_slot
         Task Job jobTaskR tsR policyR j tR))
      (Lean.eq
         (ImportedTdmaProjectedFull.Prosa_Behavior_Service_scheduled_at
           Job (ar_decidable_eq Job) PStateL schedL j tL)
         ImportedTdmaProjectedFull.Bool_true ->
       Lean.eq
         (ImportedTdmaProjectedFull.Prosa_Model_Schedule_Tdma_job_in_time_slot
           Task (ar_decidable_eq Task) policyL
           Job (ar_decidable_eq Job) jobTaskL tsL j tL)
         ImportedTdmaProjectedFull.Bool_true)).
    apply tdma_imp_correspondence.
    - exact (ar_bool_truth_correspondence _ _
        (tdma_scheduled_at_bool_related j tR tL Ht)).
    - exact (ar_bool_truth_correspondence _ _
        (job_in_time_slot_correspondence Task Job policyR policyL Hpolicy
          jobTaskR jobTaskL HjobTask tsR tsL Hts j tR tL Ht)).
  Qed.

  Context (arrivalR : prosa.behavior.job.JobArrival Job).
  Context (arrivalL : ImportedTdmaProjectedFull.Prosa_Behavior_Job_JobArrival
    Job (ar_decidable_eq Job)).
  Context (Harrival : TdmaJobArrivalRel Job arrivalR arrivalL).
  Context (costR : prosa.behavior.job.JobCost Job).
  Context (costL : ImportedTdmaProjectedFull.Prosa_Behavior_Job_JobCost
    Job (ar_decidable_eq Job)).
  Context (readyR : @prosa.behavior.ready.JobReady
    Job PStateR costR arrivalR).
  Context (readyL : ImportedTdmaProjectedFull.Prosa_Behavior_Ready_JobReady
    Job (ar_decidable_eq Job) PStateL costL arrivalL).
  Context (arrR : prosa.behavior.arrival_sequence.arrival_sequence Job).
  Context (arrL : ImportedTdmaProjectedFull.Prosa_Behavior_Arrival_sequence_arrival_sequence
    Job (ar_decidable_eq Job)).

  Definition TdmaArrivesInRel : Prop :=
    forall j : Job,
      PropSPropRel
        (@prosa.behavior.arrival_sequence.arrives_in Job arrR j)
        (ImportedTdmaProjectedFull.Prosa_Behavior_Arrival_sequence_arrives_in
          Job (ar_decidable_eq Job) arrL j).

  Definition TdmaBackloggedRel : SProp :=
    forall j tR tL, SubNatRel tR tL ->
      ArBoolRel
        (@prosa.behavior.ready.backlogged Job PStateR costR arrivalR
          readyR schedR j tR)
        (ImportedTdmaProjectedFull.Prosa_Behavior_Ready_backlogged
          Job (ar_decidable_eq Job) PStateL costL arrivalL readyL
          schedL j tL).

  Definition TdmaJobReadyRel : SProp :=
    forall j tR tL, SubNatRel tR tL ->
      ArBoolRel
        (@prosa.behavior.ready.job_ready Job PStateR costR arrivalR
          readyR schedR j tR)
        (ImportedTdmaProjectedFull.Prosa_Behavior_Ready_JobReady_job_ready
          Job (ar_decidable_eq Job) PStateL costL arrivalL readyL
          schedL j tL).

  Context (Harrives : TdmaArrivesInRel).
  Context (Hready : TdmaJobReadyRel).

  Lemma tdma_backlogged_related : TdmaBackloggedRel.
  Proof.
    intros j tR tL Ht.
    change (ArBoolRel
      ((@prosa.behavior.ready.job_ready Job PStateR costR arrivalR
        readyR schedR j tR) &&
       ~~ (@prosa.behavior.service.scheduled_at
         Job PStateR schedR j tR))
      (ImportedTdmaProjectedFull.Bool_and
        (ImportedTdmaProjectedFull.Prosa_Behavior_Ready_JobReady_job_ready
          Job (ar_decidable_eq Job) PStateL costL arrivalL readyL
          schedL j tL)
        (ImportedTdmaProjectedFull.Bool_not
          (ImportedTdmaProjectedFull.Prosa_Behavior_Service_scheduled_at
            Job (ar_decidable_eq Job) PStateL schedL j tL)))).
    apply tdma_bool_and_related.
    - exact (Hready j tR tL Ht).
    - exact (tdma_bool_not_related _ _
        (tdma_scheduled_at_bool_related j tR tL Ht)).
  Qed.

  Lemma tdma_job_task_eq_related j jOther :
    PropSPropRel
      (Logic.eq (@prosa.model.task.concept.job_task
        Job Task jobTaskR j)
        (@prosa.model.task.concept.job_task
          Job Task jobTaskR jOther))
      (Lean.eq
        (ImportedTdmaProjectedFull.Prosa_Model_Task_Concept_JobTask_job_task
          Job (ar_decidable_eq Job) Task (ar_decidable_eq Task) jobTaskL j)
        (ImportedTdmaProjectedFull.Prosa_Model_Task_Concept_JobTask_job_task
          Job (ar_decidable_eq Job) Task (ar_decidable_eq Task) jobTaskL jOther)).
  Proof.
    apply prop_sprop_rel_intro.
    - intro H.
      exact (sub_imported_eq_trans _ _ _
        (sub_imported_eq_sym _ _ (HjobTask j))
        (sub_imported_eq_trans _ _ _
          (coq_eq_to_imported_eq _ _ H) (HjobTask jOther))).
    - intro H. apply strictly_inhabits. apply imported_eq_to_coq_eq.
      exact (sub_imported_eq_trans _ _ _
        (HjobTask j)
        (sub_imported_eq_trans _ _ _ H
          (sub_imported_eq_sym _ _ (HjobTask jOther)))).
  Qed.

  Lemma tdma_arrival_lt_related jOther j :
    PropSPropRel
      (is_true (ltn (@prosa.behavior.job.job_arrival Job arrivalR jOther)
        (@prosa.behavior.job.job_arrival Job arrivalR j)))
      (tdma_nat_lt
        (ImportedTdmaProjectedFull.Prosa_Behavior_Job_JobArrival_job_arrival
          Job (ar_decidable_eq Job) arrivalL jOther)
        (ImportedTdmaProjectedFull.Prosa_Behavior_Job_JobArrival_job_arrival
          Job (ar_decidable_eq Job) arrivalL j)).
  Proof.
    exact (tdma_nat_lt_related _ _ _ _ (Harrival jOther) (Harrival j)).
  Qed.

  Lemma tdma_other_job_related (j jOther : Job) tR tL :
    SubNatRel tR tL ->
    PropSPropRel
      (@prosa.behavior.arrival_sequence.arrives_in Job arrR jOther /\
       is_true (ltn (@prosa.behavior.job.job_arrival Job arrivalR jOther)
         (@prosa.behavior.job.job_arrival Job arrivalR j)) /\
       Logic.eq (@prosa.model.task.concept.job_task Job Task jobTaskR j)
         (@prosa.model.task.concept.job_task Job Task jobTaskR jOther) /\
       is_true (@prosa.behavior.service.scheduled_at
         Job PStateR schedR jOther tR))
      (Lean.And
        (ImportedTdmaProjectedFull.Prosa_Behavior_Arrival_sequence_arrives_in
          Job (ar_decidable_eq Job) arrL jOther)
        (Lean.And
          (tdma_nat_lt
            (ImportedTdmaProjectedFull.Prosa_Behavior_Job_JobArrival_job_arrival
              Job (ar_decidable_eq Job) arrivalL jOther)
            (ImportedTdmaProjectedFull.Prosa_Behavior_Job_JobArrival_job_arrival
              Job (ar_decidable_eq Job) arrivalL j))
          (Lean.And
            (Lean.eq
              (ImportedTdmaProjectedFull.Prosa_Model_Task_Concept_JobTask_job_task
                Job (ar_decidable_eq Job) Task (ar_decidable_eq Task)
                jobTaskL j)
              (ImportedTdmaProjectedFull.Prosa_Model_Task_Concept_JobTask_job_task
                Job (ar_decidable_eq Job) Task (ar_decidable_eq Task)
                jobTaskL jOther))
            (Lean.eq
              (ImportedTdmaProjectedFull.Prosa_Behavior_Service_scheduled_at
                Job (ar_decidable_eq Job) PStateL schedL jOther tL)
              ImportedTdmaProjectedFull.Bool_true)))).
  Proof.
    intro Ht. apply tdma_and_correspondence.
    - exact (Harrives jOther).
    - apply tdma_and_correspondence.
      + exact (tdma_arrival_lt_related jOther j).
      + apply tdma_and_correspondence.
        * exact (tdma_job_task_eq_related j jOther).
        * exact (ar_bool_truth_correspondence _ _
            (tdma_scheduled_at_bool_related jOther tR tL Ht)).
  Qed.

  Theorem backlogged_implies_not_in_slot_or_other_job_sched_correspondence
      (j : Job) tR tL :
    SubNatRel tR tL ->
    PropSPropRel
      (@prosa.model.schedule.tdma.backlogged_implies_not_in_slot_or_other_job_sched
        Task Job PStateR arrivalR costR readyR jobTaskR
        arrR schedR tsR policyR j tR)
      (ImportedTdmaProjectedFull.Prosa_Model_Schedule_Tdma_backlogged_implies_not_in_slot_or_other_job_sched
        Task (ar_decidable_eq Task) policyL
        Job (ar_decidable_eq Job) jobTaskL
        PStateL arrivalL costL readyL arrL schedL tsL j tL).
  Proof.
    intro Ht.
    unfold prosa.model.schedule.tdma.backlogged_implies_not_in_slot_or_other_job_sched.
    cbn [ImportedTdmaProjectedFull.Prosa_Model_Schedule_Tdma_backlogged_implies_not_in_slot_or_other_job_sched].
    apply tdma_imp_correspondence.
    - exact (ar_bool_truth_correspondence _ _
        (tdma_backlogged_related j tR tL Ht)).
    - apply tdma_or_correspondence.
      + apply tdma_not_correspondence.
        exact (ar_bool_truth_correspondence _ _
          (job_in_time_slot_correspondence Task Job policyR policyL Hpolicy
            jobTaskR jobTaskL HjobTask tsR tsL Hts j tR tL Ht)).
      + apply tdma_exists_correspondence. intro jOther.
        exact (tdma_other_job_related j jOther tR tL Ht).
  Qed.

  Theorem respects_TDMA_policy_correspondence :
    PropSPropRel
      (@prosa.model.schedule.tdma.respects_TDMA_policy
        Task Job PStateR arrivalR costR readyR jobTaskR
        arrR schedR tsR policyR)
      (ImportedTdmaProjectedFull.Prosa_Model_Schedule_Tdma_respects_TDMA_policy
        Task (ar_decidable_eq Task) policyL
        Job (ar_decidable_eq Job) jobTaskL
        PStateL arrivalL costL readyL arrL schedL tsL).
  Proof.
    unfold prosa.model.schedule.tdma.respects_TDMA_policy.
    cbn [ImportedTdmaProjectedFull.Prosa_Model_Schedule_Tdma_respects_TDMA_policy].
    apply tdma_forall_identity_correspondence. intro j.
    apply tdma_forall_nat_correspondence. intros tR tL Ht.
    apply tdma_imp_correspondence.
    - exact (Harrives j).
    - apply tdma_and_correspondence.
      + exact (sched_implies_in_slot_correspondence j tR tL Ht).
      + exact (backlogged_implies_not_in_slot_or_other_job_sched_correspondence
          j tR tL Ht).
  Qed.
End TdmaSchedule.

Print Assumptions tdma_imp_correspondence.
Print Assumptions job_in_time_slot_correspondence.
Print Assumptions sched_implies_in_slot_correspondence.
Print Assumptions backlogged_implies_not_in_slot_or_other_job_sched_correspondence.
Print Assumptions respects_TDMA_policy_correspondence.
