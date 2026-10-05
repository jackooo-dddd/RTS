From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedGenericScheduler.

Check ImportedGenericScheduler.Prosa_Implementation_Definitions_GenericScheduler_PointwisePolicy.
Check ImportedGenericScheduler.Prosa_Implementation_Definitions_GenericScheduler_empty_schedule.
Check ImportedGenericScheduler.Prosa_Implementation_Definitions_GenericScheduler_schedule_up_to.
Check ImportedGenericScheduler.Prosa_Implementation_Definitions_GenericScheduler_generic_schedule.

Definition gs_pointwise_policy_exact_type :
  forall (Job : ImportedGenericScheduler.Prosa_Behavior_Job_JobType)
    (dec : ImportedGenericScheduler.DecidableEq Job),
    ImportedGenericScheduler.Prosa_Behavior_Schedule_ProcessorState Job dec ->
    Type :=
  ImportedGenericScheduler.Prosa_Implementation_Definitions_GenericScheduler_PointwisePolicy.

Definition gs_empty_schedule_exact_type :
  forall (Job : ImportedGenericScheduler.Prosa_Behavior_Job_JobType)
    (dec : ImportedGenericScheduler.DecidableEq Job)
    (PState : ImportedGenericScheduler.Prosa_Behavior_Schedule_ProcessorState Job dec),
    ImportedGenericScheduler.Prosa_Behavior_Schedule_ProcessorState_State
      Job dec PState ->
    ImportedGenericScheduler.Prosa_Behavior_Schedule_schedule Job dec PState :=
  ImportedGenericScheduler.Prosa_Implementation_Definitions_GenericScheduler_empty_schedule.

Definition gs_schedule_up_to_exact_type :
  forall (Job : ImportedGenericScheduler.Prosa_Behavior_Job_JobType)
    (dec : ImportedGenericScheduler.DecidableEq Job)
    (PState : ImportedGenericScheduler.Prosa_Behavior_Schedule_ProcessorState Job dec),
    ImportedGenericScheduler.Prosa_Implementation_Definitions_GenericScheduler_PointwisePolicy
      Job dec PState ->
    ImportedGenericScheduler.Prosa_Behavior_Schedule_ProcessorState_State
      Job dec PState ->
    ImportedGenericScheduler.Prosa_Behavior_Time_instant ->
    ImportedGenericScheduler.Prosa_Behavior_Schedule_schedule Job dec PState :=
  ImportedGenericScheduler.Prosa_Implementation_Definitions_GenericScheduler_schedule_up_to.

Definition gs_generic_schedule_exact_type :
  forall (Job : ImportedGenericScheduler.Prosa_Behavior_Job_JobType)
    (dec : ImportedGenericScheduler.DecidableEq Job)
    (PState : ImportedGenericScheduler.Prosa_Behavior_Schedule_ProcessorState Job dec),
    ImportedGenericScheduler.Prosa_Implementation_Definitions_GenericScheduler_PointwisePolicy
      Job dec PState ->
    ImportedGenericScheduler.Prosa_Behavior_Schedule_ProcessorState_State
      Job dec PState ->
    ImportedGenericScheduler.Prosa_Behavior_Time_instant ->
    ImportedGenericScheduler.Prosa_Behavior_Schedule_ProcessorState_State
      Job dec PState :=
  ImportedGenericScheduler.Prosa_Implementation_Definitions_GenericScheduler_generic_schedule.

Print Assumptions ImportedGenericScheduler.Prosa_Implementation_Definitions_GenericScheduler_PointwisePolicy.
Print Assumptions ImportedGenericScheduler.Prosa_Implementation_Definitions_GenericScheduler_empty_schedule.
Print Assumptions ImportedGenericScheduler.Prosa_Implementation_Definitions_GenericScheduler_schedule_up_to.
Print Assumptions ImportedGenericScheduler.Prosa_Implementation_Definitions_GenericScheduler_generic_schedule.
