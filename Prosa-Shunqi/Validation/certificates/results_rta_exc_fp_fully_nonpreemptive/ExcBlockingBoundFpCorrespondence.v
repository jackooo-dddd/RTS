(* Helper copy of the accepted BlockingBoundFpCorrespondence.v of the FP search-space certificate chain, re-bound to this export and
   to the replayed arrivals modules of this chain. *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq bigop.
From prosa Require Import BlockingBoundFpSemanticSource.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedRtaExcFpFullyNonpreemptive ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence
  ExcArrivalsSeqBaseAdapter ExcArrivalsSeqOperations ExcArrivalsSeqCorrespondence
  ExcJitterSvcBaseAdapter ExcJitterSvcNatBoolOperations ExcJitterSvcIntervalOperations
  ExcJitterSvcScheduleOperations ExcJitterSvcJobOperations ExcPreemptionParameterCorrespondence
  ExcTaskPreemptionParametersCorrespondence.

Module I := ImportedRtaExcFpFullyNonpreemptive.
Module S := BlockingBoundFpSemanticSource.BlockingBoundFpSemanticSource.
Module T := prosa.TaskPreemptionParametersSemanticSource.TaskPreemptionParametersSemanticSource.

(** Definition certificate for [analysis/definitions/blocking_bound/fp.v].

    Source side: the extracted byte-identical definition block; target side:
    the compiled Lean declaration.  Inputs: the FP policy pointwise on
    Booleans, [TaskMaxNonpreemptiveSegment] by the accepted
    [TppMaxSegmentRel], task sets by [ArListRel].  MathComp's conditional
    [\max] big operator is related to [bigMaxListCond] through kernel-checked
    Lean constructor equations exported with the artifact (replayed from the
    accepted EDF blocking-bound certificate). *)

(** ** Conditional maximum over a sequence *)

Section BigMax.
  Context (X : Type).
  Variable PR : X -> bool.
  Variable PL : X -> I.Bool.
  Hypothesis HP : forall x, ArBoolRel (PR x) (PL x).
  Variable FR : X -> nat.
  Variable FL : X -> Lean.Nat.
  Hypothesis HF : forall x, SubNatRel (FR x) (FL x).

  Lemma bbf_bigmax_canonical (xs : seq X) :
    SubNatRel (\max_(x <- xs | PR x) FR x)
      (I.Prosa_Util_Minmax_bigMaxListCond X (ar_list_to_imported xs) PL FL).
  Proof.
    induction xs as [|x xs IH].
    - rewrite big_nil.
      exact (sub_imported_eq_sym _ _
        (I.Prosa_Validation_BlockingBoundInterface_production_bigMaxListCond_nil X PL FL)).
    - rewrite big_cons. cbn [ar_list_to_imported].
      have Hx := HP x. unfold ArBoolRel in Hx.
      destruct (PR x).
      + refine (sub_imported_eq_trans _ _ _ _ (sub_imported_eq_sym _ _
          (I.Prosa_Validation_BlockingBoundInterface_production_bigMaxListCond_cons_true
            X PL FL x (ar_list_to_imported xs) (sub_imported_eq_sym _ _ Hx)))).
        refine (sub_imported_eq_trans _ _ _
          (sub_imported_eq_sym _ _ (pp_max_canonical (FR x) (\max_(y <- xs | PR y) FR y))) _).
        exact (sub_imported_eq_congr2 I.Nat_max _ _ _ _ (HF x) IH).
      + refine (sub_imported_eq_trans _ _ _ IH (sub_imported_eq_sym _ _
          (I.Prosa_Validation_BlockingBoundInterface_production_bigMaxListCond_cons_false
            X PL FL x (ar_list_to_imported xs) (sub_imported_eq_sym _ _ Hx)))).
  Qed.

  Lemma bbf_bigmax_related (xsR : seq X) (xsL : I.List X) :
    ArListRel xsR xsL ->
    SubNatRel (\max_(x <- xsR | PR x) FR x) (I.Prosa_Util_Minmax_bigMaxListCond X xsL PL FL).
  Proof.
    intro Hxs.
    exact (sub_imported_eq_trans _ _ _ (bbf_bigmax_canonical xsR)
      (sub_imported_eq_congr (fun l => I.Prosa_Util_Minmax_bigMaxListCond X l PL FL) _ _ Hxs)).
  Qed.
End BigMax.

(** ** Definition *)

Section Blocking.
  Context (Task : eqType).
  Let dT := ar_decidable_eq Task.
  Variable mR : T.TaskMaxNonpreemptiveSegment Task.
  Variable mL : I.Prosa_Model_Task_Preemption_Parameters_TaskMaxNonpreemptiveSegment Task dT.
  Hypothesis Hm : TppMaxSegmentRel Task mR mL.
  Variable fpR : prosa.model.priority.definitions.FP_policy Task.
  Variable fpL : I.Prosa_Model_Priority_Definitions_FP_policy Task dT.
  Hypothesis Hfp : forall x y : Task,
    ArBoolRel (@prosa.model.priority.definitions.hep_task Task fpR x y)
      (I.Prosa_Model_Priority_Definitions_FP_policy_hep_task Task dT fpL x y).
  Variable tsR : seq Task.
  Variable tsL : I.List Task.
  Hypothesis Hts : ArListRel tsR tsL.

  Theorem blocking_bound_correspondence (tsk : Task) :
    SubNatRel (@S.blocking_bound Task mR fpR tsR tsk)
      (I.Prosa_Analysis_Definitions_BlockingBound_Fp_blocking_bound Task dT mL fpL tsL tsk).
  Proof.
    unfold S.blocking_bound.
    cbn [I.Prosa_Analysis_Definitions_BlockingBound_Fp_blocking_bound].
    apply bbf_bigmax_related; [| |exact Hts].
    - intro tsk_o. exact (svc_bool_not_related _ _ (Hfp tsk_o tsk)).
    - intro tsk_o.
      exact (svc_target_sub_related _ _ _ _ (Hm tsk_o) (sub_nat_rel_canonical 1)).
  Qed.
End Blocking.
