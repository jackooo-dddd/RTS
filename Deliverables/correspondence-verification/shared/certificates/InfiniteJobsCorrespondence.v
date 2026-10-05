From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq
  fintype bigop.
From prosa Require Import analysis.definitions.infinite_jobs.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedInfiniteJobs ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence ArrivalsSeqBaseAdapter ArrivalsSeqOperations
  ArrivalsSeqCorrespondence ArrivalsCorrespondence.

Module I := ImportedInfiniteJobs.

(** Correspondence for [analysis/definitions/infinite_jobs.v], composed from
    the accepted Arrivals certificates re-bound to this artifact
    ([arrives_in], [job_index]) and logical combinators. *)

Lemma inf_exists_identity_correspondence (T : Type) (PR : T -> Prop) (PL : T -> SProp) :
  (forall x, PropSPropRel (PR x) (PL x)) ->
  PropSPropRel (exists x, PR x) (I.Exists T PL).
Proof.
  intro HP. apply prop_sprop_rel_intro.
  - intros [x Hx]. exact (I.Exists_intro T PL x (prop_to_sprop _ _ (HP x) Hx)).
  - intros [x Hx]. apply strictly_inhabits. exists x. exact (sprop_to_prop _ _ (HP x) Hx).
Qed.

Lemma inf_eq_identity_correspondence (T : Type) (xR xL y : T) :
  Lean.eq xR xL -> PropSPropRel (Logic.eq xR y) (Lean.eq xL y).
Proof.
  intro Hx. apply prop_sprop_rel_intro.
  - intro Heq. destruct Heq. exact (sub_imported_eq_sym _ _ Hx).
  - intro Heq. apply strictly_inhabits.
    exact (imported_eq_to_coq_eq _ _ (sub_imported_eq_trans _ _ _ Hx Heq)).
Qed.

Section InfiniteJobs.
  Context (Task Job : eqType).
  Variable jtR : prosa.model.task.concept.JobTask Job Task.
  Variable jtL : I.Prosa_Model_Task_Concept_JobTask Job (ar_decidable_eq Job)
    Task (ar_decidable_eq Task).
  Hypothesis Hjt : forall j : Job,
    Lean.eq (@prosa.model.task.concept.job_task Job Task jtR j)
      (I.Prosa_Model_Task_Concept_JobTask_job_task Job (ar_decidable_eq Job)
        Task (ar_decidable_eq Task) jtL j).
  Variable jaR : prosa.behavior.job.JobArrival Job.
  Variable jaL : I.Prosa_Behavior_Job_JobArrival Job (ar_decidable_eq Job).
  Hypothesis Hja : ArJobArrivalRel Job jaR jaL.
  Variable arrR : prosa.behavior.arrival_sequence.arrival_sequence Job.
  Variable arrL : I.Prosa_Behavior_Arrival_sequence_arrival_sequence Job (ar_decidable_eq Job).
  Hypothesis Harr : ArArrivalSequenceRel Job arrR arrL.

  Theorem infinite_jobs_correspondence :
    PropSPropRel
      (@prosa.analysis.definitions.infinite_jobs.infinite_jobs Task Job jtR jaR arrR)
      (I.Prosa_Analysis_Definitions_InfiniteJobs_infinite_jobs
        Task (ar_decidable_eq Task) Job (ar_decidable_eq Job) jtL jaL arrL).
  Proof.
    unfold prosa.analysis.definitions.infinite_jobs.infinite_jobs.
    cbn [I.Prosa_Analysis_Definitions_InfiniteJobs_infinite_jobs].
    apply ar_forall_identity_correspondence. intro tsk.
    apply ar_forall_nat_correspondence. intros nR nL Hn.
    apply inf_exists_identity_correspondence. intro j.
    apply ar_and_correspondence.
    - exact (arrives_in_correspondence_certificate Job arrR arrL j Harr).
    - apply ar_and_correspondence.
      + exact (inf_eq_identity_correspondence Task _ _ tsk (Hjt j)).
      + exact (sub_nat_eq_correspondence _ _ _ _
          (job_index_correspondence Job Task jtR jtL Hjt arrR arrL Harr jaR jaL Hja j) Hn).
  Qed.
End InfiniteJobs.

Definition inf_target_type_guard := @I.Prosa_Analysis_Definitions_InfiniteJobs_infinite_jobs.

Print Assumptions infinite_jobs_correspondence.
