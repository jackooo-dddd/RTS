# `task_interference_eq_false`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.abstract.ideal.iw_instantiation.task_interference_eq_false`
- Lean: `Prosa.Analysis.Abstract.Ideal.IwInstantiation.task_interference_eq_false`
- Certificate: `task_interference_eq_false_correspondence`

## Official Rocq

```coq
task_interference_eq_false :
forall {Task : TaskType} {Job : JobType} {H0 : JobTask Job Task} {H1 : JobArrival Job}
  (arr_seq : arrival_sequence Job),
@valid_arrival_sequence Job H1 arr_seq ->
forall sched : @schedule Job (ideal.processor_state Job),
@jobs_come_from_arrival_sequence Job (ideal.processor_state Job) sched arr_seq ->
@jobs_must_arrive_to_execute Job H1 (ideal.processor_state Job) sched ->
forall {JLFP : JLFP_policy Job} (tsk : Equality.sort Task) (j : Equality.sort Job),
is_true (@job_of_task Job Task H0 tsk j) ->
forall (t : instant) (j' : Equality.sort Job),
is_true (@job_of_task Job Task H0 tsk j') ->
is_true (@scheduled_at Job (ideal.processor_state Job) sched j' t) ->
is_true
  (~~
   @task_interference Job Task H0 (ideal.processor_state Job) arr_seq sched
     (@ideal_jlfp_interference Job arr_seq sched JLFP) j t)

task_interference_eq_false is not universe polymorphic
Arguments task_interference_eq_false {Task Job H0 H1} arr_seq H_valid_arrival_sequence 
  sched H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute {JLFP} tsk 
  j H_j_tsk t j' H_j'_tsk H_j'_sched
task_interference_eq_false is opaque
Expands to: Constant prosa.analysis.abstract.ideal.iw_instantiation.task_interference_eq_false
Declared in library prosa.analysis.abstract.ideal.iw_instantiation, line 173, characters 12-38
@task_interference_eq_false
     : forall (Task : TaskType) (Job : JobType) (H0 : JobTask Job Task) (H1 : JobArrival Job)
         (arr_seq : arrival_sequence Job),
       @valid_arrival_sequence Job H1 arr_seq ->
       forall sched : @schedule Job (ideal.processor_state Job),
       @jobs_come_from_arrival_sequence Job (ideal.processor_state Job) sched arr_seq ->
       @jobs_must_arrive_to_execute Job H1 (ideal.processor_state Job) sched ->
       forall (JLFP : JLFP_policy Job) (tsk : Equality.sort Task) (j : Equality.sort Job),
       is_true (@job_of_task Job Task H0 tsk j) ->
       forall (t : instant) (j' : Equality.sort Job),
       is_true (@job_of_task Job Task H0 tsk j') ->
       is_true (@scheduled_at Job (ideal.processor_state Job) sched j' t) ->
       is_true
         (~~
          @task_interference Job Task H0 (ideal.processor_state Job) arr_seq sched
            (@ideal_jlfp_interference Job arr_seq sched JLFP) j t)
```

## Lean

```lean
@Prosa.Analysis.Abstract.Ideal.IwInstantiation.task_interference_eq_false : ∀ {Task : Prosa.Model.Task.Concept.TaskType}
  [inst : DecidableEq Task] {Job : Prosa.Behavior.Job.JobType} [inst_1 : DecidableEq Job]
  [inst_2 : Prosa.Model.Task.Concept.JobTask Job Task] [inst_3 : Prosa.Behavior.Job.JobArrival Job]
  (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
  Prosa.Behavior.Arrival_sequence.valid_arrival_sequence arr_seq →
    ∀ (sched : Prosa.Behavior.Schedule.schedule (Prosa.Model.Processor.Ideal.processor_state Job)),
      Prosa.Behavior.Ready.jobs_come_from_arrival_sequence sched arr_seq →
        Prosa.Behavior.Ready.jobs_must_arrive_to_execute sched →
          ∀ [JLFP : Prosa.Model.Priority.Definitions.JLFP_policy Job] (tsk : Task) (j : Job),
            Prosa.Model.Task.Concept.job_of_task tsk j = true →
              ∀ (t : Prosa.Behavior.Time.instant) (j' : Job),
                Prosa.Model.Task.Concept.job_of_task tsk j' = true →
                  Prosa.Behavior.Service.scheduled_at sched j' t = true →
                    (!Prosa.Analysis.Abstract.IBF.Task.task_interference arr_seq sched j t) = true
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Abstract_Ideal_IwInstantiation_task_interference_eq_false
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : 
          DecidableEq Task)
         (Job : Prosa_Behavior_Job_JobType)
         (inst_7 : 
          DecidableEq Job)
         (inst_10 : 
          Prosa_Model_Task_Concept_JobTask Job
            inst_7 Task
            inst_3)
         (inst_14 : 
          Prosa_Behavior_Job_JobArrival Job
            inst_7)
         (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                      inst_7),
       Prosa_Behavior_Arrival_sequence_valid_arrival_sequence Job
         inst_7
         inst_14 arr_seq ->
       forall
         sched : Prosa_Behavior_Schedule_schedule_inst4 Job
                   inst_7
                   (Prosa_Model_Processor_Ideal_processor_state Job
                      inst_7),
       Prosa_Behavior_Ready_jobs_come_from_arrival_sequence_inst4 Job
         inst_7
         (Prosa_Model_Processor_Ideal_processor_state Job
            inst_7)
         sched arr_seq ->
       Prosa_Behavior_Ready_jobs_must_arrive_to_execute_inst4 Job
         inst_7
         inst_14
         (Prosa_Model_Processor_Ideal_processor_state Job
            inst_7)
         sched ->
       forall
         (JLFP : Prosa_Model_Priority_Definitions_JLFP_policy Job
                   inst_7)
         (tsk : Task) (j : Job),
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
         (Prosa_Behavior_Service_scheduled_at_inst4 Job
            inst_7
            (Prosa_Model_Processor_Ideal_processor_state Job
               inst_7)
            sched j' t)
         Bool_true ->
       @eq Bool
         (Bool_not
            (Prosa_Analysis_Abstract_IBF_Task_task_interference_inst8 Job
               inst_7 Task
               inst_3
               inst_10
               (Prosa_Model_Processor_Ideal_processor_state Job
                  inst_7)
               arr_seq sched
               (Prosa_Analysis_Abstract_Ideal_IwInstantiation_ideal_jlfp_interference Job
                  inst_7 arr_seq
                  sched JLFP)
               j t))
         Bool_true
```
