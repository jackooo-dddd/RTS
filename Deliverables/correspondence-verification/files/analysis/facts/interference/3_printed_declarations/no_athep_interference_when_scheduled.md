# `no_athep_interference_when_scheduled`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.interference.no_athep_interference_when_scheduled`
- Lean: `Prosa.Analysis.Facts.Interference.no_athep_interference_when_scheduled`
- Certificate: `no_athep_interference_when_scheduled_correspondence`

## Official Rocq

```coq
no_athep_interference_when_scheduled :
forall {Task : TaskType} {Job : JobType} {H0 : JobTask Job Task} {PState : ProcessorState Job},
@uniprocessor_model Job PState ->
forall (arr_seq : arrival_sequence Job) (sched : @schedule Job PState) (tsk : Equality.sort Task)
  {JLFP : JLFP_policy Job} (j : Equality.sort Job),
is_true (@job_of_task Job Task H0 tsk j) ->
forall (t : instant) (j' : Equality.sort Job),
is_true (@job_of_task Job Task H0 tsk j') ->
is_true (@scheduled_at Job PState sched j' t) ->
is_true (~~ @another_task_hep_job_interference Task Job H0 PState arr_seq sched JLFP j t)

no_athep_interference_when_scheduled is not universe polymorphic
Arguments no_athep_interference_when_scheduled {Task Job H0 PState} H_uniprocessor_proc_model 
  arr_seq sched tsk {JLFP} j H_j_tsk t j' H_j'_tsk H_j'_sched
no_athep_interference_when_scheduled is opaque
Expands to: Constant prosa.analysis.facts.interference.no_athep_interference_when_scheduled
Declared in library prosa.analysis.facts.interference, line 313, characters 12-48
@no_athep_interference_when_scheduled
     : forall (Task : TaskType) (Job : JobType) (H0 : JobTask Job Task) (PState : ProcessorState Job),
       @uniprocessor_model Job PState ->
       forall (arr_seq : arrival_sequence Job) (sched : @schedule Job PState) (tsk : Equality.sort Task)
         (JLFP : JLFP_policy Job) (j : Equality.sort Job),
       is_true (@job_of_task Job Task H0 tsk j) ->
       forall (t : instant) (j' : Equality.sort Job),
       is_true (@job_of_task Job Task H0 tsk j') ->
       is_true (@scheduled_at Job PState sched j' t) ->
       is_true (~~ @another_task_hep_job_interference Task Job H0 PState arr_seq sched JLFP j t)
```

## Lean

```lean
@Prosa.Analysis.Facts.Interference.no_athep_interference_when_scheduled : ∀ {Task : Prosa.Model.Task.Concept.TaskType}
  [inst : DecidableEq Task] {Job : Prosa.Behavior.Job.JobType} [inst_1 : DecidableEq Job]
  [inst_2 : Prosa.Model.Task.Concept.JobTask Job Task] {PState : Prosa.Behavior.Schedule.ProcessorState Job},
  Prosa.Model.Processor.PlatformProperties.uniprocessor_model PState →
    ∀ (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job) (sched : Prosa.Behavior.Schedule.schedule PState)
      (tsk : Task) (JLFP : Prosa.Model.Priority.Definitions.JLFP_policy Job) (j : Job),
      Prosa.Model.Task.Concept.job_of_task tsk j = true →
        ∀ (t : Prosa.Behavior.Time.instant) (j' : Job),
          Prosa.Model.Task.Concept.job_of_task tsk j' = true →
            Prosa.Behavior.Service.scheduled_at sched j' t = true →
              (!Prosa.Analysis.Definitions.Interference.another_task_hep_job_interference arr_seq sched j t) = true
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Interference_no_athep_interference_when_scheduled
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task)
         (Job : Prosa_Behavior_Job_JobType)
         (inst_7 : DecidableEq Job)
         (inst_10 : 
          Prosa_Model_Task_Concept_JobTask Job
            inst_7 Task
            inst_3)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_7),
       Prosa_Model_Processor_PlatformProperties_uniprocessor_model Job
         inst_7 PState ->
       forall
         (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                      inst_7)
         (sched : Prosa_Behavior_Schedule_schedule Job
                    inst_7 PState)
         (tsk : Task)
         (JLFP : Prosa_Model_Priority_Definitions_JLFP_policy Job
                   inst_7)
         (j : Job),
       @eq Bool
         (Prosa_Model_Task_Concept_job_of_task Job
            inst_7 Task
            inst_3
            inst_10 tsk j)
         Bool_true ->
       forall (t : Prosa_Behavior_Time_instant) (j' : Job),
       @eq Bool
         (Prosa_Model_Task_Concept_job_of_task Job
            inst_7 Task
            inst_3
            inst_10 tsk j')
         Bool_true ->
       @eq Bool
         (Prosa_Behavior_Service_scheduled_at Job
            inst_7 PState sched j' t)
         Bool_true ->
       @eq Bool
         (Bool_not
            (Prosa_Analysis_Definitions_Interference_another_task_hep_job_interference Task
               inst_3 Job
               inst_7
               inst_10 PState arr_seq sched
               JLFP j t))
         Bool_true
```
