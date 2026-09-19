From mathcomp Require Import ssreflect ssrbool eqtype fintype.
From prosa Require Import behavior.service model.processor.ideal.
From LeanImport Require Import Lean.
Require Import ImportedEasy93 PropSPropFoundation ProcessorStateBridge.
Require Import EqTypeBridge TimeJobCertificates IdealScheduledInCertificate.
Require Import ScheduledAtCertificate GeneratedOfficialProsa06.

Definition imported_scheduled_in_def_statement (Job : eqType)
    (j : Job) (sR : prosa.model.processor.ideal.processor_state Job) : SProp :=
  eq
    (Prosa_Behavior_Schedule_ProcessorState_scheduled_in_inst1
       Job (Prosa_Model_Processor_Ideal_processor_state Job)
       (Prosa_Model_Processor_Ideal_pstate_instance
          Job (imported_classical_decidable_eq Job))
       j (ideal_state_to_imported sR))
    (Decidable_decide
       (eq (ideal_state_to_imported sR) (Option_some_inst1 Job j))
       (Option_instDecidableEq_inst1
          Job (imported_classical_decidable_eq Job)
          (ideal_state_to_imported sR) (Option_some_inst1 Job j))).

Definition imported_scheduled_in_def_has_expected_statement (Job : eqType)
    (arrivalR : prosa.behavior.job.JobArrival Job)
    (costR : prosa.behavior.job.JobCost Job)
    (j : Job) (sR : prosa.model.processor.ideal.processor_state Job) :
    imported_scheduled_in_def_statement Job j sR :=
  Prosa_Analysis_Facts_Model_Ideal_schedule_scheduled_in_def
    Job (imported_classical_decidable_eq Job)
    (import_job_arrival Job arrivalR) (import_job_cost Job costR)
    j (ideal_state_to_imported sR).

Definition original_scheduled_in_def_statement (Job : eqType)
    (j : Job) (sR : prosa.model.processor.ideal.processor_state Job) : Prop :=
  Logic.eq (@prosa.behavior.schedule.scheduled_in
    Job (prosa.model.processor.ideal.processor_state Job) j sR)
    (sR == Some j).

Definition original_scheduled_in_def_has_expected_statement (Job : eqType)
    (j : Job) (sR : prosa.model.processor.ideal.processor_state Job) :
    original_scheduled_in_def_statement Job j sR :=
  @GeneratedOfficialProsa06.scheduled_in_def Job j sR.

Lemma ideal_state_eq_certificate (Job : eqType)
    (j : Job) (sR : prosa.model.processor.ideal.processor_state Job) :
  ImportedBoolRel (sR == Some j)
    (Decidable_decide
       (eq (ideal_state_to_imported sR) (Option_some_inst1 Job j))
       (Option_instDecidableEq_inst1 Job (imported_classical_decidable_eq Job)
          (ideal_state_to_imported sR) (Option_some_inst1 Job j))).
Proof.
  have H := ideal_scheduled_on_rel Job j j sR
    (ideal_state_to_imported sR) tt (eq_refl j)
    (ideal_state_to_imported_rel Job sR).
  cbv [prosa.behavior.schedule.scheduled_on
       prosa.model.processor.ideal.processor_state
       Prosa_Behavior_Schedule_ProcessorState_scheduled_on_inst1
       Prosa_Model_Processor_Ideal_pstate_instance
       ideal_core_toL] in H.
  exact H.
Qed.

Theorem scheduled_in_def_statement_certificate (Job : eqType)
    (arrivalR : prosa.behavior.job.JobArrival Job)
    (costR : prosa.behavior.job.JobCost Job)
    (j : Job) (sR : prosa.model.processor.ideal.processor_state Job) :
  PropSPropRel
    (original_scheduled_in_def_statement Job j sR)
    (imported_scheduled_in_def_statement Job j sR).
Proof.
  unfold original_scheduled_in_def_statement,
    imported_scheduled_in_def_statement.
  apply prop_sprop_rel_intro.
  - intro Hsource.
    eapply imported_bool_equality_forward.
    + have H := ideal_scheduled_in_certificate Job j j sR
        (ideal_state_to_imported sR) (eq_refl j)
        (ideal_state_to_imported_rel Job sR).
      cbv [Prosa_Validation_ideal_scheduled_in] in H.
      exact H.
    + exact (ideal_state_eq_certificate Job j sR).
    + exact Hsource.
  - intro Htarget.
    eapply imported_bool_equality_backward_strict.
    + have H := ideal_scheduled_in_certificate Job j j sR
        (ideal_state_to_imported sR) (eq_refl j)
        (ideal_state_to_imported_rel Job sR).
      cbv [Prosa_Validation_ideal_scheduled_in] in H.
      exact H.
    + exact (ideal_state_eq_certificate Job j sR).
    + exact Htarget.
Qed.

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
  @GeneratedOfficialProsa06.scheduled_at_def
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
Print Assumptions scheduled_in_def_statement_certificate.
Print Assumptions imported_scheduled_at_def_has_expected_statement.
Print Assumptions original_scheduled_at_def_has_expected_statement.
Print Assumptions imported_scheduled_in_def_has_expected_statement.
Print Assumptions original_scheduled_in_def_has_expected_statement.
