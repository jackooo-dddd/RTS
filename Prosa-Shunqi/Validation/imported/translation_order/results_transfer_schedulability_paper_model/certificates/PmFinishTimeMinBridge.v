(* The accepted certificates/analysis/FinishTimeMinBridge.v (the minimum-witness bridge between the source ex_minn
   and the compiled Nat.find), re-bound to this export: ImportedFinishTime is this export's ImportedPaperModel and its
   two adapter imports ServiceBaseAdapter / ServiceNatBoolOperations are the replayed PmJitterSvcBaseAdapter /
   PmJitterSvcNatBoolOperations (the same adapter, re-bound for the criterion run). No block was dropped; all
   definitions and proofs are unchanged. *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedPaperModel ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation
  LogicalRelation SubadditivityNatCorrespondence PmJitterSvcBaseAdapter
  PmJitterSvcNatBoolOperations.

(** Reusable minimum-witness correspondence.  The target is the actual
    imported Lean [Nat.find], with its compiled proof-bodied specification and
    minimum lemma.  No target application theorem is used here. *)
Section MinimumWitness.

  Variable pR : pred nat.
  Variable pL : Lean.Nat -> SProp.
  Variable dp : ImportedPaperModel.DecidablePred Lean.Nat pL.
  Variable exR : exists n : nat, pR n.
  Variable exL : ImportedPaperModel.Exists Lean.Nat pL.
  Hypothesis Hp : forall nR nL,
    SubNatRel nR nL -> PropSPropRel (is_true (pR nR)) (pL nL).

  Let mR := ex_minn exR.
  Let mL := ImportedPaperModel.Nat_find pL dp exL.

  Lemma source_minimum_spec : pR mR /\
      forall n, pR n -> (mR <= n)%N.
  Proof.
    unfold mR, ex_minn.
    destruct (find_ex_minn exR) as [m Hsat Hmin].
    split; first exact Hsat.
    exact Hmin.
  Qed.

  Lemma imported_minimum_spec : pL mL.
  Proof. exact (ImportedPaperModel.Nat_find_spec pL dp exL). Qed.

  Lemma minimum_value_correspondence : SubNatRel mR mL.
  Proof.
    pose nR := sub_nat_to_rocq mL.
    have Hn : SubNatRel nR mL := sub_nat_rel_surjective mL.
    have Hpn : pR nR :=
      sprop_to_prop _ _ (Hp nR mL Hn) imported_minimum_spec.
    have Hleft : (mR <= nR)%N :=
      (proj2 source_minimum_spec) nR Hpn.
    have Hpm : pL (sub_nat_to_imported mR) :=
      prop_to_sprop _ _ (Hp mR (sub_nat_to_imported mR)
        (sub_nat_rel_canonical mR)) (proj1 source_minimum_spec).
    have HrightL : svc_target_le mL (sub_nat_to_imported mR) :=
      ImportedPaperModel.Nat_find_min' pL dp exL
        (sub_nat_to_imported mR) Hpm.
    have Hright : (nR <= mR)%N :=
      sprop_to_prop _ _
        (svc_target_le_related nR mL mR (sub_nat_to_imported mR)
          Hn (sub_nat_rel_canonical mR)) HrightL.
    have Heq : mR = nR by apply/eqP; rewrite eqn_leq Hleft Hright.
    rewrite Heq. exact Hn.
  Qed.

End MinimumWitness.
