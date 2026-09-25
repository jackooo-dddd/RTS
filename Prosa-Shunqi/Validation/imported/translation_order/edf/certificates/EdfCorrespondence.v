From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq fintype.
From prosa Require Import model.schedule.edf.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedEdfFull.
From FoundationCertificates Require Import PropSPropFoundation
  LogicalRelation SubadditivityNatCorrespondence EdfBaseAdapter EdfOperations.

(** Field observations required by the source classes and their actual
    imported Lean counterparts.  They are explicit inputs, not axioms. *)
Definition EdfDeadlineRel (Job : eqType)
    (deadlineR : prosa.behavior.job.JobDeadline Job)
    (deadlineL : ImportedEdfFull.Prosa_Behavior_Job_JobDeadline
      Job (edf_decidable_eq Job)) : SProp :=
  forall j : Job,
    SubNatRel (@prosa.behavior.job.job_deadline Job deadlineR j)
      (ImportedEdfFull.Prosa_Behavior_Job_JobDeadline_job_deadline
        Job (edf_decidable_eq Job) deadlineL j).

Definition EdfArrivalRel (Job : eqType)
    (arrivalR : prosa.behavior.job.JobArrival Job)
    (arrivalL : ImportedEdfFull.Prosa_Behavior_Job_JobArrival
      Job (edf_decidable_eq Job)) : SProp :=
  forall j : Job,
    SubNatRel (@prosa.behavior.job.job_arrival Job arrivalR j)
      (ImportedEdfFull.Prosa_Behavior_Job_JobArrival_job_arrival
        Job (edf_decidable_eq Job) arrivalL j).

Lemma edf_imp_correspondence (P Q : Prop) (PL QL : SProp) :
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

Lemma edf_forall_identity_correspondence (T : Type)
    (PR : T -> Prop) (PL : T -> SProp) :
  (forall x, PropSPropRel (PR x) (PL x)) ->
  PropSPropRel (forall x, PR x) (forall x, PL x).
Proof.
  intro HP. apply prop_sprop_rel_intro.
  - intros HR x. exact (prop_to_sprop _ _ (HP x) (HR x)).
  - intro HL. apply strictly_inhabits. intro x.
    exact (sprop_to_prop _ _ (HP x) (HL x)).
Qed.

Lemma edf_forall_nat_correspondence
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

Section EdfCorrespondence.
  Context (Job : eqType).
  Context (deadlineR : prosa.behavior.job.JobDeadline Job).
  Context (arrivalR : prosa.behavior.job.JobArrival Job).
  Context (PStateR : prosa.behavior.schedule.ProcessorState Job).
  Context (deadlineL : ImportedEdfFull.Prosa_Behavior_Job_JobDeadline
    Job (edf_decidable_eq Job)).
  Context (arrivalL : ImportedEdfFull.Prosa_Behavior_Job_JobArrival
    Job (edf_decidable_eq Job)).
  Context (PStateL : ImportedEdfFull.Prosa_Behavior_Schedule_ProcessorState
    Job (edf_decidable_eq Job)).
  Context (R : EdfProcessorRel Job PStateR PStateL).
  Context (schedR : @prosa.behavior.schedule.schedule Job PStateR).
  Context (schedL : ImportedEdfFull.Prosa_Behavior_Schedule_schedule
    Job (edf_decidable_eq Job) PStateL).
  Context (Hsched : EdfScheduleRel Job PStateR PStateL R schedR schedL).
  Context (Hdeadline : EdfDeadlineRel Job deadlineR deadlineL).
  Context (Harrival : EdfArrivalRel Job arrivalR arrivalL).

  Lemma EDF_at_correspondence (tR : nat) (tL : Lean.Nat) :
    SubNatRel tR tL ->
    PropSPropRel
      (@prosa.model.schedule.edf.EDF_at Job deadlineR arrivalR
        PStateR schedR tR)
      (ImportedEdfFull.Prosa_Model_Schedule_Edf_EDF_at
        Job (edf_decidable_eq Job) deadlineL arrivalL
        PStateL schedL tL).
  Proof.
    intro Ht.
    unfold prosa.model.schedule.edf.EDF_at.
    cbn [ImportedEdfFull.Prosa_Model_Schedule_Edf_EDF_at].
    apply edf_forall_identity_correspondence; intro j.
    apply edf_imp_correspondence.
    - exact (edf_scheduled_at_truth Job PStateR PStateL R
        schedR schedL j tR tL Hsched Ht).
    - apply edf_forall_nat_correspondence; intros tR' tL' Ht'.
      apply edf_forall_identity_correspondence; intro j'.
      apply edf_imp_correspondence.
      + exact (sub_nat_le_correspondence tR tL tR' tL' Ht Ht').
      + apply edf_imp_correspondence.
        * exact (edf_scheduled_at_truth Job PStateR PStateL R
            schedR schedL j' tR' tL' Hsched Ht').
        * apply edf_imp_correspondence.
          -- exact (sub_nat_le_correspondence
               (@prosa.behavior.job.job_arrival Job arrivalR j')
               (ImportedEdfFull.Prosa_Behavior_Job_JobArrival_job_arrival
                 Job (edf_decidable_eq Job) arrivalL j')
               tR tL (Harrival j') Ht).
          -- exact (sub_nat_le_correspondence
               (@prosa.behavior.job.job_deadline Job deadlineR j)
               (ImportedEdfFull.Prosa_Behavior_Job_JobDeadline_job_deadline
                 Job (edf_decidable_eq Job) deadlineL j)
               (@prosa.behavior.job.job_deadline Job deadlineR j')
               (ImportedEdfFull.Prosa_Behavior_Job_JobDeadline_job_deadline
                 Job (edf_decidable_eq Job) deadlineL j')
               (Hdeadline j) (Hdeadline j')).
  Qed.

  Lemma EDF_schedule_correspondence :
    PropSPropRel
      (@prosa.model.schedule.edf.EDF_schedule Job deadlineR arrivalR
        PStateR schedR)
      (ImportedEdfFull.Prosa_Model_Schedule_Edf_EDF_schedule
        Job (edf_decidable_eq Job) deadlineL arrivalL
        PStateL schedL).
  Proof.
    unfold prosa.model.schedule.edf.EDF_schedule.
    cbn [ImportedEdfFull.Prosa_Model_Schedule_Edf_EDF_schedule].
    apply edf_forall_nat_correspondence; intros tR tL Ht.
    exact (EDF_at_correspondence tR tL Ht).
  Qed.
End EdfCorrespondence.
