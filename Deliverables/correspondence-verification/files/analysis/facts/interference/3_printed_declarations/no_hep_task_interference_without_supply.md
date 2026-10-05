# `no_hep_task_interference_without_supply`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.interference.no_hep_task_interference_without_supply`
- Lean: `Prosa.Analysis.Facts.Interference.no_hep_task_interference_without_supply`
- Certificate: `no_hep_task_interference_without_supply_correspondence`

## Official Rocq

```coq
no_hep_task_interference_without_supply :
forall {Task : TaskType} {Job : JobType} {H0 : JobTask Job Task} {PState : ProcessorState Job}
  (arr_seq : arrival_sequence Job) (sched : @schedule Job PState) {JLFP : JLFP_policy Job} 
  (t : instant),
is_true (~~ @has_supply Job PState sched t) ->
forall j : Equality.sort Job,
is_true (~~ @another_task_hep_job_interference Task Job H0 PState arr_seq sched JLFP j t)

no_hep_task_interference_without_supply is not universe polymorphic
Arguments no_hep_task_interference_without_supply {Task Job H0 PState} arr_seq sched {JLFP} t H_no_supply j
no_hep_task_interference_without_supply is opaque
Expands to: Constant prosa.analysis.facts.interference.no_hep_task_interference_without_supply
Declared in library prosa.analysis.facts.interference, line 160, characters 10-49
@no_hep_task_interference_without_supply
     : forall (Task : TaskType) (Job : JobType) (H0 : JobTask Job Task) (PState : ProcessorState Job)
         (arr_seq : arrival_sequence Job) (sched : @schedule Job PState) (JLFP : JLFP_policy Job)
         (t : instant),
       is_true (~~ @has_supply Job PState sched t) ->
       forall j : Equality.sort Job,
       is_true (~~ @another_task_hep_job_interference Task Job H0 PState arr_seq sched JLFP j t)
```

## Lean

```lean
@Prosa.Analysis.Facts.Interference.no_hep_task_interference_without_supply : ∀
  {Task : Prosa.Model.Task.Concept.TaskType} [inst : DecidableEq Task] {Job : Prosa.Behavior.Job.JobType}
  [inst_1 : DecidableEq Job] [inst_2 : Prosa.Model.Task.Concept.JobTask Job Task]
  {PState : Prosa.Behavior.Schedule.ProcessorState Job} (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job)
  (sched : Prosa.Behavior.Schedule.schedule PState) (JLFP : Prosa.Model.Priority.Definitions.JLFP_policy Job)
  (t : Prosa.Behavior.Time.instant),
  (!Prosa.Model.Processor.Supply.has_supply sched t) = true →
    ∀ (j : Job), (!Prosa.Analysis.Definitions.Interference.another_task_hep_job_interference arr_seq sched j t) = true
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Interference_no_hep_task_interference_without_supply
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
         (JLFP : Prosa_Model_Priority_Definitions_JLFP_policy Job
                   inst_7)
         (t : Prosa_Behavior_Time_instant),
       @eq Bool
         (Bool_not
            (Prosa_Model_Processor_Supply_has_supply Job
               inst_7 PState sched t))
         Bool_true ->
       forall j : Job,
       @eq Bool
         (Bool_not
            (Prosa_Analysis_Definitions_Interference_another_task_hep_job_interference Task
               inst_3 Job
               inst_7
               inst_10 PState arr_seq sched
               JLFP j t))
         Bool_true
```
