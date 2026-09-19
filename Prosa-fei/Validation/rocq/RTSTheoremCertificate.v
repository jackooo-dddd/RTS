From mathcomp Require Import ssreflect ssrbool eqtype fintype.
From prosa Require Import behavior.service model.processor.ideal.
From LeanImport Require Import Lean.
Require Import ImportedEasy93 PropSPropBridge ProcessorStateBridge.
Require Import EqTypeBridge TimeJobCertificates IdealScheduledInCertificate.
Require Import ScheduledAtCertificate OriginalIdealScheduleSlice.

Definition imported_scheduled_at_def_statement (Job : eqType)
    (schedR : prosa.behavior.schedule.schedule
      (prosa.model.processor.ideal.processor_state Job))
    (j : Job) (t : prosa.behavior.time.instant) : SProp :=
  eq
    (Prosa_Behavior_Service_scheduled_at_inst1
       Job (Prosa_Model_Processor_Ideal_processor_state Job)
       (Prosa_Model_Processor_Ideal_pstate_instance
          Job (imported_classical_decidable_eq Job))
       (import_ideal_schedule Job schedR) j (instant_to_imported t))
    (Decidable_decide
       (eq
          (import_ideal_schedule Job schedR (instant_to_imported t))
          (Option_some_inst1 Job j))
       (Option_instDecidableEq_inst1
          Job (imported_classical_decidable_eq Job)
          (import_ideal_schedule Job schedR (instant_to_imported t))
          (Option_some_inst1 Job j))).

(** Kernel type check tying the name exported from the actual compiled Lean
    theorem to the proposition used by the semantic certificate.  This
    witness is audited separately; the correspondence proof below does not
    use the imported theorem proof/axiom. *)
Definition imported_scheduled_at_def_has_expected_statement (Job : eqType)
    (arrivalR : prosa.behavior.job.JobArrival Job)
    (costR : prosa.behavior.job.JobCost Job)
    (schedR : prosa.behavior.schedule.schedule
      (prosa.model.processor.ideal.processor_state Job))
    (j : Job) (t : prosa.behavior.time.instant) :
    imported_scheduled_at_def_statement Job schedR j t :=
  Prosa_Analysis_Facts_Model_Ideal_schedule_scheduled_at_def
    Job (imported_classical_decidable_eq Job)
    (import_job_arrival Job arrivalR) (import_job_cost Job costR)
    (import_ideal_schedule Job schedR) j (instant_to_imported t).

Definition original_scheduled_at_def_statement (Job : eqType)
    (schedR : prosa.behavior.schedule.schedule
      (prosa.model.processor.ideal.processor_state Job))
    (j : Job) (t : prosa.behavior.time.instant) : Prop :=
  Logic.eq
    (@prosa.behavior.service.scheduled_at
       Job (prosa.model.processor.ideal.processor_state Job) schedR j t)
    (schedR t == Some j).

Definition original_scheduled_at_def_has_expected_statement (Job : eqType)
    (arrivalR : prosa.behavior.job.JobArrival Job)
    (costR : prosa.behavior.job.JobCost Job)
    (schedR : prosa.behavior.schedule.schedule
      (prosa.model.processor.ideal.processor_state Job))
    (j : Job) (t : prosa.behavior.time.instant) :
    original_scheduled_at_def_statement Job schedR j t :=
  @OriginalProsa06IdealSchedule.scheduled_at_def
    Job schedR j t.

Lemma ideal_schedule_state_eq_certificate (Job : eqType)
    (schedR : prosa.behavior.schedule.schedule
      (prosa.model.processor.ideal.processor_state Job))
    (j : Job) (t : prosa.behavior.time.instant) :
  ImportedBoolRel
    (schedR t == Some j)
    (Decidable_decide
       (eq
          (import_ideal_schedule Job schedR (instant_to_imported t))
          (Option_some_inst1 Job j))
       (Option_instDecidableEq_inst1
          Job (imported_classical_decidable_eq Job)
          (import_ideal_schedule Job schedR (instant_to_imported t))
          (Option_some_inst1 Job j))).
Proof.
  have H := ideal_scheduled_on_rel Job j j (schedR t)
    (import_ideal_schedule Job schedR (instant_to_imported t)) tt
    (eq_refl j) (imported_ideal_schedule_at_rel Job schedR t).
  cbv [prosa.behavior.schedule.scheduled_on
       prosa.model.processor.ideal.processor_state
       Prosa_Behavior_Schedule_ProcessorState_scheduled_on_inst1
       Prosa_Model_Processor_Ideal_pstate_instance
       ideal_core_toL] in H.
  exact H.
Qed.

Theorem scheduled_at_def_statement_certificate (Job : eqType)
    (arrivalR : prosa.behavior.job.JobArrival Job)
    (costR : prosa.behavior.job.JobCost Job)
    (schedR : prosa.behavior.schedule.schedule
      (prosa.model.processor.ideal.processor_state Job))
    (j : Job) (t : prosa.behavior.time.instant) :
  PropSPropRel
    (original_scheduled_at_def_statement Job schedR j t)
    (imported_scheduled_at_def_statement Job schedR j t).
Proof.
  unfold original_scheduled_at_def_statement,
    imported_scheduled_at_def_statement.
  apply prop_sprop_rel_intro.
  - intro Hsource.
    eapply imported_bool_equality_forward.
    + have H := ideal_scheduled_at_certificate Job schedR j j t (eq_refl j).
      cbv [Prosa_Validation_ideal_scheduled_at] in H.
      exact H.
    + exact (ideal_schedule_state_eq_certificate Job schedR j t).
    + exact Hsource.
  - intro Htarget.
    eapply imported_bool_equality_backward_strict.
    + have H := ideal_scheduled_at_certificate Job schedR j j t (eq_refl j).
      cbv [Prosa_Validation_ideal_scheduled_at] in H.
      exact H.
    + exact (ideal_schedule_state_eq_certificate Job schedR j t).
    + exact Htarget.
Qed.

Print Assumptions scheduled_at_def_statement_certificate.
Print Assumptions imported_scheduled_at_def_has_expected_statement.
Print Assumptions original_scheduled_at_def_has_expected_statement.
