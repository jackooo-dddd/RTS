From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq fintype.
From prosa Require Import analysis.facts.model.ideal_uni_exceed.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedIdealUniExceedFacts ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation
  LogicalRelation SubadditivityNatCorrespondence
  IdealUniExceedFactsBaseAdapter IdealUniExceedFactsStateCorrespondence
  IdealUniExceedFactsSourceComputation.

(** Every statement below refers to the official v0.6 source constant and
    the actual imported production Lean artifact.  No target theorem proof is
    used in a correspondence derivation. *)

Section IdealUniExceedFactsCorrespondence.
  Context (Job : eqType).

  Let stateR : prosa.behavior.schedule.ProcessorState Job :=
    @prosa.model.processor.ideal_uni_exceed.exceedance_proc_state Job.
  Let stateL :=
    ImportedIdealUniExceedFacts.Prosa_Model_Processor_IdealUniExceed_exceedance_proc_state
      Job (iue_decidable_eq Job).

  Lemma facts_is_exceedance_exec_correspondence
      (sR : IueSource Job) :
    IueBoolRel
      (@prosa.analysis.facts.model.ideal_uni_exceed.is_exceedance_exec Job sR)
      (ImportedIdealUniExceedFacts.Prosa_Analysis_Facts_Model_IdealUniExceed_is_exceedance_exec
        Job (iue_decidable_eq Job) (iue_to_target Job sR)).
  Proof.
    destruct sR; cbn; exact (@Lean.eq_refl _ _).
  Qed.
End IdealUniExceedFactsCorrespondence.

Print Assumptions facts_is_exceedance_exec_correspondence.
