From mathcomp Require Import ssreflect ssrbool ssrnat eqtype.
From prosa Require Import model.readiness.jitter.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedJitterPublic.
From FoundationCertificates Require Import JitterBaseAdapter
  JitterCorrespondence JitterHelperSourceGuard
  SubadditivityNatCorrespondence.

(** The auxiliary target combinator is an actual compiled/exported Lean
    definition. Its inputs are the two Boolean observations of the helper. *)
Lemma ji_ready_bool_correspondence rR rL cR cL :
  JiBoolRel rR rL -> JiBoolRel cR cL ->
  JiBoolRel (rR && ~~ cR)
    (ImportedJitterPublic.Prosa_Model_Readiness_Jitter_jitter_ready_bool
      rL cL).
Proof.
  intros Hr Hc. unfold JiBoolRel in *.
  destruct Hr. destruct Hc.
  destruct rR, cR; exact (@Lean.eq_refl _ _).
Qed.

Section HelperField.
  Context {Job : eqType} {PState : ProcessorState Job}.
  Context `{JobArrival Job} `{JobCost Job} `{JobJitter Job}.
  Variable (d : ImportedJitterPublic.DecidableEq Job).
  Variable (al : ImportedJitterPublic.Prosa_Behavior_Job_JobArrival Job d).
  Variable (jl : ImportedJitterPublic.Prosa_Model_Readiness_Jitter_JobJitter
    Job d).

  Let sourceReady : JobReady Job PState :=
    @prosa.model.readiness.jitter.jitter_ready_instance
      Job PState H H0 H1.

  Lemma ji_helper_ready_field_correspondence
      (sched : schedule PState) (j : Job) (tR : nat) (tL : Lean.Nat)
      (completedL : ImportedJitterPublic.Bool) :
    JiArrivalRel Job d H al -> JiJitterRel Job d H1 jl ->
    SubNatRel tR tL ->
    JiBoolRel (completed_by sched j tR) completedL ->
    JiBoolRel
      (@prosa.behavior.ready.job_ready Job PState H0 H sourceReady
        sched j tR)
      (ImportedJitterPublic.Prosa_Model_Readiness_Jitter_jitter_ready_bool
        (ImportedJitterPublic.Prosa_Model_Readiness_Jitter_is_released
          Job d al jl j tL) completedL).
  Proof.
    intros Harr Hjit Ht Hcompleted.
    change (JiBoolRel (is_released j tR && ~~ completed_by sched j tR)
      (ImportedJitterPublic.Prosa_Model_Readiness_Jitter_jitter_ready_bool
        (ImportedJitterPublic.Prosa_Model_Readiness_Jitter_is_released
          Job d al jl j tL) completedL)).
    apply ji_ready_bool_correspondence.
    - exact (ji_is_released_correspondence Job d H al H1 jl
        j tR tL Harr Hjit Ht).
    - exact Hcompleted.
  Qed.
End HelperField.

Print Assumptions ji_ready_bool_correspondence.
Print Assumptions ji_helper_ready_field_correspondence.
