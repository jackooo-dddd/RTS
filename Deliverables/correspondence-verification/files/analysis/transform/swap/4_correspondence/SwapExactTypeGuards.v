From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat.
From prosa Require Import analysis.transform.swap.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedSwap.

Check (@prosa.analysis.transform.swap.replace_at :
  forall (Job : prosa.behavior.job.JobType)
    (PState : prosa.behavior.schedule.ProcessorState Job),
    prosa.behavior.schedule.schedule PState ->
    prosa.behavior.time.instant -> PState ->
    prosa.behavior.schedule.schedule PState).
Check (ImportedSwap.Prosa_Analysis_Transform_Swap_replace_at :
  forall (Job : ImportedSwap.Prosa_Behavior_Job_JobType)
    (deq : ImportedSwap.DecidableEq Job)
    (PState : ImportedSwap.Prosa_Behavior_Schedule_ProcessorState Job deq),
    ImportedSwap.Prosa_Behavior_Schedule_schedule Job deq PState ->
    ImportedSwap.Prosa_Behavior_Time_instant ->
    ImportedSwap.Prosa_Behavior_Schedule_ProcessorState_State Job deq PState ->
    ImportedSwap.Prosa_Behavior_Schedule_schedule Job deq PState).

Check (@prosa.analysis.transform.swap.swapped :
  forall (Job : prosa.behavior.job.JobType)
    (PState : prosa.behavior.schedule.ProcessorState Job),
    prosa.behavior.schedule.schedule PState ->
    prosa.behavior.time.instant -> prosa.behavior.time.instant ->
    prosa.behavior.schedule.schedule PState).
Check (ImportedSwap.Prosa_Analysis_Transform_Swap_swapped :
  forall (Job : ImportedSwap.Prosa_Behavior_Job_JobType)
    (deq : ImportedSwap.DecidableEq Job)
    (PState : ImportedSwap.Prosa_Behavior_Schedule_ProcessorState Job deq),
    ImportedSwap.Prosa_Behavior_Schedule_schedule Job deq PState ->
    ImportedSwap.Prosa_Behavior_Time_instant ->
    ImportedSwap.Prosa_Behavior_Time_instant ->
    ImportedSwap.Prosa_Behavior_Schedule_schedule Job deq PState).
