From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq fintype.
From prosa Require Import model.schedule.edf.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedEdfFull.

Check (@prosa.model.schedule.edf.EDF_at :
  forall (Job : prosa.behavior.job.JobType)
    (deadline : prosa.behavior.job.JobDeadline Job)
    (arrival : prosa.behavior.job.JobArrival Job)
    (PState : prosa.behavior.schedule.ProcessorState Job),
    @prosa.behavior.schedule.schedule Job PState ->
    prosa.behavior.time.instant -> Prop).
Check (ImportedEdfFull.Prosa_Model_Schedule_Edf_EDF_at :
  forall (Job : ImportedEdfFull.Prosa_Behavior_Job_JobType)
    (deq : ImportedEdfFull.DecidableEq Job)
    (deadline : ImportedEdfFull.Prosa_Behavior_Job_JobDeadline Job deq)
    (arrival : ImportedEdfFull.Prosa_Behavior_Job_JobArrival Job deq)
    (PState : ImportedEdfFull.Prosa_Behavior_Schedule_ProcessorState
      Job deq),
    ImportedEdfFull.Prosa_Behavior_Schedule_schedule Job deq PState ->
    ImportedEdfFull.Prosa_Behavior_Time_instant -> SProp).

Check (@prosa.model.schedule.edf.EDF_schedule :
  forall (Job : prosa.behavior.job.JobType)
    (deadline : prosa.behavior.job.JobDeadline Job)
    (arrival : prosa.behavior.job.JobArrival Job)
    (PState : prosa.behavior.schedule.ProcessorState Job),
    @prosa.behavior.schedule.schedule Job PState -> Prop).
Check (ImportedEdfFull.Prosa_Model_Schedule_Edf_EDF_schedule :
  forall (Job : ImportedEdfFull.Prosa_Behavior_Job_JobType)
    (deq : ImportedEdfFull.DecidableEq Job)
    (deadline : ImportedEdfFull.Prosa_Behavior_Job_JobDeadline Job deq)
    (arrival : ImportedEdfFull.Prosa_Behavior_Job_JobArrival Job deq)
    (PState : ImportedEdfFull.Prosa_Behavior_Schedule_ProcessorState
      Job deq),
    ImportedEdfFull.Prosa_Behavior_Schedule_schedule Job deq PState ->
    SProp).
