From mathcomp Require Import ssreflect ssrbool ssrnat eqtype.
From prosa Require Import model.schedule.nonpreemptive.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedNonpreemptive ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation
  LogicalRelation SubadditivityNatCorrespondence NonpreemptiveBaseAdapter
  NonpreemptiveNatBoolOperations NonpreemptiveScheduleOperations
  NonpreemptiveJobOperations NonpreemptiveCorrespondence.

(** The only public v0.6 Nonpreemptive definition.  All observation
    relations below are instantiated from the separately kernel-checked
    Service correspondence for this exact imported Lean artifact. *)
Section NonpreemptiveScheduleCorrespondence.

  Context (Job : eqType).
  Context (PStateR : prosa.behavior.schedule.ProcessorState Job).
  Variable PStateL :
    ImportedNonpreemptive.Prosa_Behavior_Schedule_ProcessorState Job
      (svc_decidable_eq Job).
  Variable R : SvcProcessorStateRel Job PStateR PStateL.

  Variable schedR : @prosa.behavior.schedule.schedule Job PStateR.
  Variable schedL : ImportedNonpreemptive.Prosa_Behavior_Schedule_schedule
    Job (svc_decidable_eq Job) PStateL.
  Hypothesis Hsched : SvcScheduleRel Job PStateR PStateL R schedR schedL.

  Variable costR : prosa.behavior.job.JobCost Job.
  Variable costL : ImportedNonpreemptive.Prosa_Behavior_Job_JobCost Job
    (svc_decidable_eq Job).
  Hypothesis Hcost : SvcJobCostRel Job costR costL.

  Lemma nonpreemptive_schedule_correspondence :
    PropSPropRel
      (@prosa.model.schedule.nonpreemptive.nonpreemptive_schedule
        Job costR PStateR schedR)
      (ImportedNonpreemptive.Prosa_Model_Schedule_Nonpreemptive_nonpreemptive_schedule
        Job (svc_decidable_eq Job) costL PStateL schedL).
  Proof.
    unfold prosa.model.schedule.nonpreemptive.nonpreemptive_schedule.
    cbn [ImportedNonpreemptive.Prosa_Model_Schedule_Nonpreemptive_nonpreemptive_schedule].
    apply prop_sprop_rel_intro.
    - intros Hsource j tL tL' HleL HscheduledL HnotCompletedL.
      pose (tR := sub_nat_to_rocq tL).
      pose (tR' := sub_nat_to_rocq tL').
      have Ht : SubNatRel tR tL := sub_nat_rel_surjective tL.
      have Ht' : SubNatRel tR' tL' := sub_nat_rel_surjective tL'.
      have Hle := sub_nat_le_correspondence tR tL tR' tL' Ht Ht'.
      have Hscheduled := svc_bool_truth_correspondence _ _
        (scheduled_at_correspondence Job PStateR PStateL R
          schedR schedL Hsched j tR tL Ht).
      have Hcompleted := completed_by_correspondence
        Job PStateR PStateL R schedR schedL Hsched
        costR costL Hcost j tR' tL' Ht'.
      have Hnot := svc_bool_truth_correspondence _ _
        (svc_bool_not_related _ _ Hcompleted).
      have Hscheduled' := svc_bool_truth_correspondence _ _
        (scheduled_at_correspondence Job PStateR PStateL R
          schedR schedL Hsched j tR' tL' Ht').
      apply (prop_to_sprop _ _ Hscheduled').
      apply (Hsource j tR tR').
      + exact (sprop_to_prop _ _ Hle HleL).
      + exact (sprop_to_prop _ _ Hscheduled HscheduledL).
      + exact (sprop_to_prop _ _ Hnot HnotCompletedL).
    - intro Htarget. apply strictly_inhabits.
      intros j tR tR' HleR HscheduledR HnotCompletedR.
      pose (tL := sub_nat_to_imported tR).
      pose (tL' := sub_nat_to_imported tR').
      have Ht : SubNatRel tR tL := sub_nat_rel_canonical tR.
      have Ht' : SubNatRel tR' tL' := sub_nat_rel_canonical tR'.
      have Hle := sub_nat_le_correspondence tR tL tR' tL' Ht Ht'.
      have Hscheduled := svc_bool_truth_correspondence _ _
        (scheduled_at_correspondence Job PStateR PStateL R
          schedR schedL Hsched j tR tL Ht).
      have Hcompleted := completed_by_correspondence
        Job PStateR PStateL R schedR schedL Hsched
        costR costL Hcost j tR' tL' Ht'.
      have Hnot := svc_bool_truth_correspondence _ _
        (svc_bool_not_related _ _ Hcompleted).
      have Hscheduled' := svc_bool_truth_correspondence _ _
        (scheduled_at_correspondence Job PStateR PStateL R
          schedR schedL Hsched j tR' tL' Ht').
      apply (sprop_to_prop _ _ Hscheduled').
      apply (Htarget j tL tL').
      + exact (prop_to_sprop _ _ Hle HleR).
      + exact (prop_to_sprop _ _ Hscheduled HscheduledR).
      + exact (prop_to_sprop _ _ Hnot HnotCompletedR).
  Qed.

End NonpreemptiveScheduleCorrespondence.

Print Assumptions nonpreemptive_schedule_correspondence.
