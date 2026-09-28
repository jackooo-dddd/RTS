(* Helper-only copy of the accepted certificates/analysis_facts_busy_interval_hep_at_pt/
   HepAtPtCorrespondence.v, re-bound to this export, truncated before its eight statement
   correspondences (whose target statements are not part of this export); every helper
   definition and proof is unchanged. *)
From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq fintype bigop.
From prosa Require Import behavior.all model.processor.platform_properties model.schedule.scheduled
  model.priority.classes model.schedule.work_conserving model.job.properties
  analysis.definitions.work_bearing_readiness.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedBlockingBoundFpFacts ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence ArrivalsCorrespondence
  JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations
  JitterSvcScheduleOperations JitterSvcJobOperations PreemptionParameterCorrespondence
  PreemptionTimeCorrespondence PriorityDrivenCorrespondence PStateCoverHelpers FactsPreemptionHelpers
  WorkloadCorrespondence PriorityInversionCorrespondence ExistenceHelpers.

Module I := ImportedBlockingBoundFpFacts.

(** Statement correspondence for [analysis/facts/busy_interval/hep_at_pt.v].

    Source side: the extracted statements [S.statement_X] specialised at
    their leading inputs (job type, arrival and cost classes, arrival
    sequence); target side: the imported Lean theorem types.  Inputs:
    [job_arrival] by [ArJobArrivalRel], [job_cost] by the accepted
    [SvcJobCostRel], arrival sequences by [ArArrivalSequenceRel].  Inputs
    quantified inside a statement are covered in both directions by the
    accepted conversions: processor models ([isj_cover_pstate]), schedules
    through the processor-model relation ([fpre_forall_sched]), JLFP policies
    ([fpre_forall_jlfp]), [JobPreemptable] instances ([fpre_forall_jp]), the
    readiness instance on the statement's schedule pair ([fpre_forall_jr]),
    jobs (identity) and instants.  The busy-interval prefix, quiet times,
    work conservation, work-bearing readiness and unit service are the
    accepted busy-interval-existence helpers; schedule validity, preemption
    times, preemption-model validity and the JLFP-at-preemption-point policy
    are the accepted preemption-facts helpers; priority transitivity is
    related by unfolding, and [t.-1] by the accepted subtraction relation
    ([subn1]).  No source or target theorem is used. *)

Ltac body_of f := let T := type of f in match T with _ -> ?B => exact B end.
Ltac type_of_term t := let T := type of t in exact T.

Lemma hap_pred_related (nR : nat) (nL : Lean.Nat) :
  SubNatRel nR nL ->
  SubNatRel nR.-1 (I.HSub_hSub_inst7 Lean.Nat Lean.Nat Lean.Nat (I.instHSub_inst1 Lean.Nat I.instSubNat)
    nL (sub_nat_to_imported 1)).
Proof.
  intro Hn. have H := svc_target_sub_related nR nL 1 (sub_nat_to_imported 1) Hn (sub_nat_rel_canonical 1).
  rewrite subn1 in H. exact H.
Qed.

Section HepAtPt.
  Context (Job : eqType).
  Let dJ := ar_decidable_eq Job.

  Variable jaR : prosa.behavior.job.JobArrival Job.
  Variable jaL : I.Prosa_Behavior_Job_JobArrival Job dJ.
  Hypothesis Hja : ArJobArrivalRel Job jaR jaL.
  Variable costR : prosa.behavior.job.JobCost Job.
  Variable costL : I.Prosa_Behavior_Job_JobCost Job dJ.
  Hypothesis Hcost : SvcJobCostRel Job costR costL.
  Variable arrR : prosa.behavior.arrival_sequence.arrival_sequence Job.
  Variable arrL : I.Prosa_Behavior_Arrival_sequence_arrival_sequence Job dJ.
  Hypothesis Harr : ArArrivalSequenceRel Job arrR arrL.

  Lemma hap_transitive_rel pR pL (Hp : FpreJLFPRel Job pR pL) :
    PropSPropRel (@prosa.model.priority.definitions.transitive_job_priorities Job pR)
      (I.Prosa_Model_Priority_Definitions_transitive_job_priorities Job dJ pL).
  Proof.
    unfold prosa.model.priority.definitions.transitive_job_priorities.
    cbn [I.Prosa_Model_Priority_Definitions_transitive_job_priorities].
    apply ar_forall_identity_correspondence. intro y.
    apply ar_forall_identity_correspondence. intro x.
    apply ar_forall_identity_correspondence. intro z.
    apply ar_imp_correspondence; [exact (ar_bool_truth_correspondence _ _ (Hp x y))|].
    apply ar_imp_correspondence; [exact (ar_bool_truth_correspondence _ _ (Hp y z))|].
    exact (ar_bool_truth_correspondence _ _ (Hp x z)).
  Qed.
End HepAtPt.
