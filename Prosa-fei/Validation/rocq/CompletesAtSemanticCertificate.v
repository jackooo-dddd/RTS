From mathcomp Require Import ssreflect ssrbool ssrnat bigop eqtype fintype.
From prosa Require Import behavior.service.
From LeanImport Require Import Lean.
Require Import ImportedCompletesAt93 PropSPropFoundation.

(** The source-side witness fixes the job cost to zero.  At time zero the
    half-open service interval is empty, so this is independent of all
    processor-state representation details. *)
Definition completes_at_zero_cost (Job : eqType) :
    prosa.behavior.job.JobCost Job := fun _ => Datatypes.O.

Definition completes_at_zero_deadline (Job : eqType) :
    prosa.behavior.job.JobDeadline Job := fun _ => Datatypes.O.

Definition completes_at_zero_arrival (Job : eqType) :
    prosa.behavior.job.JobArrival Job := fun _ => Datatypes.O.

Section SourceWitness.
  Context (Job : eqType).
  Context (PState : prosa.behavior.schedule.ProcessorState Job).
  Variable sched : prosa.behavior.schedule.schedule PState.
  Variable j : Job.

  Definition source_completes_at_zero_statement : Prop :=
    @prosa.behavior.service.completes_at
      Job PState sched
      (completes_at_zero_cost Job)
      j Datatypes.O.

  Lemma source_completes_at_zero_true :
    source_completes_at_zero_statement.
  Proof.
    rewrite /source_completes_at_zero_statement
            /prosa.behavior.service.completes_at
            /prosa.behavior.service.completed_by
            /prosa.behavior.service.service
            /prosa.behavior.service.service_during
            /completes_at_zero_cost.
    by rewrite big_geq.
  Qed.
End SourceWitness.

Definition imported_completes_at_current_false :
    Not Prosa_Validation_CompletesAt_production_completes_at_zero :=
  fun H =>
    match H with
    | Lean.And_intro Hnot Hle => Hnot Hle
    end.

Definition imported_completes_at_corrected_true :
    Prosa_Validation_CompletesAt_corrected_completes_at_zero :=
  Lean.And_intro _ _
    (Lean.Or_inr _ _ (eq_refl Lean.Nat_zero))
    (Lean.Nat_le_refl Lean.Nat_zero).

(** A direct, kernel-inhabited counterexample package: the official source
    proposition holds while the frozen production target proposition does
    not. *)
Definition completes_at_current_counterexample
    (Job : eqType)
    (PState : prosa.behavior.schedule.ProcessorState Job)
    (sched : prosa.behavior.schedule.schedule PState)
    (j : Job) : SProp :=
  Lean.And
    (StrictlyInhabited
      (source_completes_at_zero_statement Job PState sched j))
    (Not Prosa_Validation_CompletesAt_production_completes_at_zero).

Definition completes_at_current_counterexample_witness
    (Job : eqType)
    (PState : prosa.behavior.schedule.ProcessorState Job)
    (sched : prosa.behavior.schedule.schedule PState)
    (j : Job) :
    completes_at_current_counterexample Job PState sched j :=
  Lean.And_intro _ _
    (strictly_inhabits
      (source_completes_at_zero_true Job PState sched j))
    imported_completes_at_current_false.

Theorem completes_at_corrected_certificate
    (Job : eqType)
    (PState : prosa.behavior.schedule.ProcessorState Job)
    (sched : prosa.behavior.schedule.schedule PState)
    (j : Job) :
  PropSPropRel
    (source_completes_at_zero_statement Job PState sched j)
    Prosa_Validation_CompletesAt_corrected_completes_at_zero.
Proof.
  constructor.
  - exact (fun _ => imported_completes_at_corrected_true).
  - exact (fun _ => source_completes_at_zero_true Job PState sched j).
Qed.

Print Assumptions source_completes_at_zero_true.
Print Assumptions imported_completes_at_current_false.
Print Assumptions imported_completes_at_corrected_true.
Print Assumptions completes_at_current_counterexample_witness.
Print Assumptions completes_at_corrected_certificate.
