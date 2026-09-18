From mathcomp Require Import ssreflect ssrbool eqtype.
From prosa Require Import model.processor.ideal behavior.service.
From LeanImport Require Import Lean.
Require Import ImportedEasy93 ImportedNatBridge TimeJobCertificates.
Require Import IdealScheduledInCertificate.

Definition import_ideal_schedule (Job : eqType)
    (schedR : prosa.behavior.schedule.schedule
      (prosa.model.processor.ideal.processor_state Job)) :
    Prosa_Behavior_Schedule_schedule_inst1
      (Prosa_Model_Processor_Ideal_processor_state Job) :=
  fun tL => ideal_state_to_imported (schedR (imported_nat_to_rocq tL)).

Lemma imported_ideal_schedule_at_rel (Job : eqType)
    (schedR : prosa.behavior.schedule.schedule
      (prosa.model.processor.ideal.processor_state Job))
    (t : prosa.behavior.time.instant) :
  IdealStateRel Job (schedR t)
    (import_ideal_schedule Job schedR (instant_to_imported t)).
Proof.
  unfold import_ideal_schedule, instant_to_imported.
  have Htime := Logic.eq_sym (rocq_nat_roundtrip t).
  destruct Htime.
  exact (ideal_state_to_imported_rel Job (schedR t)).
Qed.

Theorem ideal_scheduled_at_certificate (Job : eqType)
    (schedR : prosa.behavior.schedule.schedule
      (prosa.model.processor.ideal.processor_state Job))
    (jR jL : Job) (t : prosa.behavior.time.instant) :
  eq jR jL ->
  ImportedBoolRel
    (@prosa.behavior.service.scheduled_at
       Job (prosa.model.processor.ideal.processor_state Job) schedR jR t)
    (Prosa_Validation_ideal_scheduled_at
       Job (imported_classical_decidable_eq Job)
       (import_ideal_schedule Job schedR) jL (instant_to_imported t)).
Proof.
  intro Hjob.
  unfold prosa.behavior.service.scheduled_at.
  unfold Prosa_Validation_ideal_scheduled_at.
  unfold Prosa_Behavior_Service_scheduled_at_inst1.
  exact (ideal_scheduled_in_certificate Job jR jL
    (schedR t)
    (import_ideal_schedule Job schedR (instant_to_imported t))
    Hjob (imported_ideal_schedule_at_rel Job schedR t)).
Qed.

Print Assumptions ideal_scheduled_at_certificate.
