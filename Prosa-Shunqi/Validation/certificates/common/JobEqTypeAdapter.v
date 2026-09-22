From mathcomp Require Import ssreflect ssrbool eqtype.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedJob.
From FoundationCertificates Require Import PropSPropFoundation.

(** Artifact-local realization of the approved representation boundary
    [eqType] -> carrier [Type] plus Lean [DecidableEq].  The proof pattern is
    shared with [EqTypeCorrespondence], but the imported [Decidable] datatype
    is generated separately for each lean4export artifact, so this small
    adapter must be tied to the actual [ImportedJob] artifact. *)

Inductive JobEqObservationTrue : SProp := job_eq_observation_I.
Inductive JobEqObservationFalse : SProp := .

Definition job_false_from_coq_false
    (H : Logic.False) : ImportedJob.False :=
  match H return ImportedJob.False with end.

Definition eqtype_to_job_decidable_eq (T : eqType) :
    ImportedJob.DecidableEq T :=
  fun x y =>
    match @eqP T x y with
    | ReflectT H =>
        ImportedJob.Decidable_isTrue (Lean.eq x y)
          (coq_eq_to_imported_eq x y H)
    | ReflectF H =>
        ImportedJob.Decidable_isFalse (Lean.eq x y)
          (fun HL => job_false_from_coq_false
            (H (imported_eq_to_coq_eq x y HL)))
    end.

Definition JobEqDecisionRel (T : eqType) (x y : T)
    (d : ImportedJob.Decidable (Lean.eq x y)) : SProp :=
  match x == y, d with
  | true, ImportedJob.Decidable_isTrue _ => JobEqObservationTrue
  | false, ImportedJob.Decidable_isFalse _ => JobEqObservationTrue
  | _, _ => JobEqObservationFalse
  end.

Definition JobTypeRepresentationRel (T : eqType)
    (d : ImportedJob.DecidableEq T) : SProp :=
  forall x y : T, JobEqDecisionRel T x y (d x y).

Lemma job_type_equality_evidence_certificate (T : eqType) :
  JobTypeRepresentationRel T (eqtype_to_job_decidable_eq T).
Proof.
  intros x y. unfold JobEqDecisionRel, eqtype_to_job_decidable_eq.
  destruct (@eqP T x y); cbn; exact job_eq_observation_I.
Qed.

Print Assumptions job_type_equality_evidence_certificate.
