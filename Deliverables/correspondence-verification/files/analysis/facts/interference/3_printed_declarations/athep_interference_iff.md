# `athep_interference_iff`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.interference.athep_interference_iff`
- Lean: `Prosa.Analysis.Facts.Interference.athep_interference_iff`
- Certificate: `athep_interference_iff_correspondence`

## Official Rocq

```coq
athep_interference_iff :
forall {Task : TaskType} {Job : JobType} {H0 : JobTask Job Task} {H1 : JobArrival Job}
  {PState : ProcessorState Job},
@uniprocessor_model Job PState ->
@fully_consuming_proc_model Job PState ->
forall arr_seq : arrival_sequence Job,
@valid_arrival_sequence Job H1 arr_seq ->
forall sched : @schedule Job PState,
@jobs_come_from_arrival_sequence Job PState sched arr_seq ->
@jobs_must_arrive_to_execute Job H1 PState sched ->
forall (tsk : Equality.sort Task) {JLFP : JLFP_policy Job} (j : Equality.sort Job),
is_true (@job_of_task Job Task H0 tsk j) ->
forall t : instant,
is_true (@has_supply Job PState sched t) ->
forall j' : Equality.sort Job,
is_true (~~ @job_of_task Job Task H0 tsk j') ->
is_true (@scheduled_at Job PState sched j' t) ->
@another_task_hep_job_interference Task Job H0 PState arr_seq sched JLFP j t = @hep_job Job JLFP j' j

athep_interference_iff is not universe polymorphic
Arguments athep_interference_iff {Task Job H0 H1 PState} H_uniprocessor_proc_model
  H_consumed_supply_proc_model arr_seq H_valid_arrival_sequence sched H_jobs_come_from_arrival_sequence
  H_jobs_must_arrive_to_execute tsk {JLFP} j H_j_tsk t H_supply j' H_j'_not_tsk H_j'_sched
athep_interference_iff is opaque
Expands to: Constant prosa.analysis.facts.interference.athep_interference_iff
Declared in library prosa.analysis.facts.interference, line 337, characters 12-34
@athep_interference_iff
     : forall (Task : TaskType) (Job : JobType) (H0 : JobTask Job Task) (H1 : JobArrival Job)
         (PState : ProcessorState Job),
       @uniprocessor_model Job PState ->
       @fully_consuming_proc_model Job PState ->
       forall arr_seq : arrival_sequence Job,
       @valid_arrival_sequence Job H1 arr_seq ->
       forall sched : @schedule Job PState,
       @jobs_come_from_arrival_sequence Job PState sched arr_seq ->
       @jobs_must_arrive_to_execute Job H1 PState sched ->
       forall (tsk : Equality.sort Task) (JLFP : JLFP_policy Job) (j : Equality.sort Job),
       is_true (@job_of_task Job Task H0 tsk j) ->
       forall t : instant,
       is_true (@has_supply Job PState sched t) ->
       forall j' : Equality.sort Job,
       is_true (~~ @job_of_task Job Task H0 tsk j') ->
       is_true (@scheduled_at Job PState sched j' t) ->
       @another_task_hep_job_interference Task Job H0 PState arr_seq sched JLFP j t = @hep_job Job JLFP j' j
```

## Lean

```lean
@Prosa.Analysis.Facts.Interference.athep_interference_iff : ∀ {Task : Prosa.Model.Task.Concept.TaskType}
  [inst : DecidableEq Task] {Job : Prosa.Behavior.Job.JobType} [inst_1 : DecidableEq Job]
  [inst_2 : Prosa.Model.Task.Concept.JobTask Job Task] [inst_3 : Prosa.Behavior.Job.JobArrival Job]
  {PState : Prosa.Behavior.Schedule.ProcessorState Job},
  Prosa.Model.Processor.PlatformProperties.uniprocessor_model PState →
    Prosa.Model.Processor.PlatformProperties.fully_consuming_proc_model PState →
      ∀ (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
        Prosa.Behavior.Arrival_sequence.valid_arrival_sequence arr_seq →
          ∀ (sched : Prosa.Behavior.Schedule.schedule PState),
            Prosa.Behavior.Ready.jobs_come_from_arrival_sequence sched arr_seq →
              Prosa.Behavior.Ready.jobs_must_arrive_to_execute sched →
                ∀ (tsk : Task) (JLFP : Prosa.Model.Priority.Definitions.JLFP_policy Job) (j : Job),
                  Prosa.Model.Task.Concept.job_of_task tsk j = true →
                    ∀ (t : Prosa.Behavior.Time.instant),
                      Prosa.Model.Processor.Supply.has_supply sched t = true →
                        ∀ (j' : Job),
                          (!Prosa.Model.Task.Concept.job_of_task tsk j') = true →
                            Prosa.Behavior.Service.scheduled_at sched j' t = true →
                              Prosa.Analysis.Definitions.Interference.another_task_hep_job_interference arr_seq sched j
                                  t =
                                Prosa.Model.Priority.Definitions.hep_job j' j
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Interference_athep_interference_iff
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task)
         (Job : Prosa_Behavior_Job_JobType)
         (inst_7 : DecidableEq Job)
         (inst_10 : 
          Prosa_Model_Task_Concept_JobTask Job
            inst_7 Task
            inst_3)
         (inst_14 : 
          Prosa_Behavior_Job_JobArrival Job
            inst_7)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_7),
       Prosa_Model_Processor_PlatformProperties_uniprocessor_model Job
         inst_7 PState ->
       Prosa_Model_Processor_PlatformProperties_fully_consuming_proc_model Job
         inst_7 PState ->
       forall
         arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                     inst_7,
       Prosa_Behavior_Arrival_sequence_valid_arrival_sequence Job
         inst_7
         inst_14 arr_seq ->
       forall
         sched : Prosa_Behavior_Schedule_schedule Job
                   inst_7 PState,
       Prosa_Behavior_Ready_jobs_come_from_arrival_sequence Job
         inst_7 PState sched arr_seq ->
       Prosa_Behavior_Ready_jobs_must_arrive_to_execute Job
         inst_7
         inst_14 PState sched ->
       forall (tsk : Task)
         (JLFP : Prosa_Model_Priority_Definitions_JLFP_policy Job
                   inst_7)
         (j : Job),
       @eq Bool
         (Prosa_Model_Task_Concept_job_of_task Job
            inst_7 Task
            inst_3
            inst_10 tsk j)
         Bool_true ->
       forall t : Prosa_Behavior_Time_instant,
       @eq Bool
         (Prosa_Model_Processor_Supply_has_supply Job
            inst_7 PState sched t)
         Bool_true ->
       forall j' : Job,
       @eq Bool
         (Bool_not
            (Prosa_Model_Task_Concept_job_of_task Job
               inst_7 Task
               inst_3
               inst_10 tsk j'))
         Bool_true ->
       @eq Bool
         (Prosa_Behavior_Service_scheduled_at Job
            inst_7 PState sched j' t)
         Bool_true ->
       @eq Bool
         (Prosa_Analysis_Definitions_Interference_another_task_hep_job_interference Task
            inst_3 Job
            inst_7
            inst_10 PState arr_seq sched JLFP
            j t)
         (Prosa_Model_Priority_Definitions_JLFP_policy_hep_job Job
            inst_7 JLFP j' j)
```
