# `hep_interference_another_task_split`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.interference.hep_interference_another_task_split`
- Lean: `Prosa.Analysis.Facts.Interference.hep_interference_another_task_split`
- Certificate: `hep_interference_another_task_split_correspondence`

## Official Rocq

```coq
hep_interference_another_task_split :
forall {Task : TaskType} {Job : JobType} {jt : JobTask Job Task} {PState : ProcessorState Job}
  (arr_seq : arrival_sequence Job) (sched : @schedule Job PState) {FP : FP_policy Task}
  {JLFP : JLFP_policy Job},
@JLFP_FP_compatible Task Job jt JLFP FP ->
forall (j : Equality.sort Job) (t : instant),
@another_task_hep_job_interference Task Job jt PState arr_seq sched JLFP j t =
@hep_job_from_hp_task_interference Task Job jt PState arr_seq sched FP JLFP j t
|| @hep_job_from_other_ep_task_interference Task Job jt PState arr_seq sched FP JLFP j t

hep_interference_another_task_split is not universe polymorphic
Arguments hep_interference_another_task_split {Task Job jt PState} arr_seq sched {FP JLFP} H_compatible j t
hep_interference_another_task_split is opaque
Expands to: Constant prosa.analysis.facts.interference.hep_interference_another_task_split
Declared in library prosa.analysis.facts.interference, line 58, characters 8-43
@hep_interference_another_task_split
     : forall (Task : TaskType) (Job : JobType) (jt : JobTask Job Task) (PState : ProcessorState Job)
         (arr_seq : arrival_sequence Job) (sched : @schedule Job PState) (FP : FP_policy Task)
         (JLFP : JLFP_policy Job),
       @JLFP_FP_compatible Task Job jt JLFP FP ->
       forall (j : Equality.sort Job) (t : instant),
       @another_task_hep_job_interference Task Job jt PState arr_seq sched JLFP j t =
       @hep_job_from_hp_task_interference Task Job jt PState arr_seq sched FP JLFP j t
       || @hep_job_from_other_ep_task_interference Task Job jt PState arr_seq sched FP JLFP j t
```

## Lean

```lean
@Prosa.Analysis.Facts.Interference.hep_interference_another_task_split : ∀ {Task : Prosa.Model.Task.Concept.TaskType}
  [inst : DecidableEq Task] {Job : Prosa.Behavior.Job.JobType} [inst_1 : DecidableEq Job]
  [inst_2 : Prosa.Model.Task.Concept.JobTask Job Task] {PState : Prosa.Behavior.Schedule.ProcessorState Job}
  (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job) (sched : Prosa.Behavior.Schedule.schedule PState)
  (FP : Prosa.Model.Priority.Definitions.FP_policy Task) (JLFP : Prosa.Model.Priority.Definitions.JLFP_policy Job),
  Prosa.Analysis.Definitions.Priority.Classes.JLFP_FP_compatible JLFP FP →
    ∀ (j : Job) (t : Prosa.Behavior.Time.instant),
      Prosa.Analysis.Definitions.Interference.another_task_hep_job_interference arr_seq sched j t =
        (Prosa.Analysis.Definitions.Interference.hep_job_from_hp_task_interference arr_seq sched j t ||
          Prosa.Analysis.Definitions.Interference.hep_job_from_other_ep_task_interference arr_seq sched j t)
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Interference_hep_interference_another_task_split
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task)
         (Job : Prosa_Behavior_Job_JobType)
         (inst_7 : DecidableEq Job)
         (inst_10 : 
          Prosa_Model_Task_Concept_JobTask Job
            inst_7 Task
            inst_3)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_7)
         (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                      inst_7)
         (sched : Prosa_Behavior_Schedule_schedule Job
                    inst_7 PState)
         (FP : Prosa_Model_Priority_Definitions_FP_policy Task
                 inst_3)
         (JLFP : Prosa_Model_Priority_Definitions_JLFP_policy Job
                   inst_7),
       Prosa_Analysis_Definitions_Priority_Classes_JLFP_FP_compatible Task
         inst_3 Job
         inst_7
         inst_10 JLFP FP ->
       forall (j : Job) (t : Prosa_Behavior_Time_instant),
       @eq Bool
         (Prosa_Analysis_Definitions_Interference_another_task_hep_job_interference Task
            inst_3 Job
            inst_7
            inst_10 PState arr_seq sched JLFP
            j t)
         (Bool_or
            (Prosa_Analysis_Definitions_Interference_hep_job_from_hp_task_interference Task
               inst_3 Job
               inst_7
               inst_10 PState arr_seq sched
               FP JLFP j t)
            (Prosa_Analysis_Definitions_Interference_hep_job_from_other_ep_task_interference Task
               inst_3 Job
               inst_7
               inst_10 PState arr_seq sched
               FP JLFP j t))
```
