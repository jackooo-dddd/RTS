# `cumulative_task_interference_split`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.abstract.ideal.iw_instantiation.cumulative_task_interference_split`
- Lean: `Prosa.Analysis.Abstract.Ideal.IwInstantiation.cumulative_task_interference_split`
- Certificate: `cumulative_task_interference_split_correspondence`

## Official Rocq

```coq
cumulative_task_interference_split :
forall {Task : TaskType} {Job : JobType} {H0 : JobTask Job Task} {H1 : JobArrival Job} 
  {H2 : JobCost Job} (arr_seq : arrival_sequence Job),
@valid_arrival_sequence Job H1 arr_seq ->
forall sched : @schedule Job (ideal.processor_state Job),
@jobs_come_from_arrival_sequence Job (ideal.processor_state Job) sched arr_seq ->
@jobs_must_arrive_to_execute Job H1 (ideal.processor_state Job) sched ->
forall {JLFP : JLFP_policy Job},
@reflexive_job_priorities Job JLFP ->
forall (tsk : Equality.sort Task) (j : Equality.sort Job) (t1 : nat) (t2 : instant),
@arrives_in Job arr_seq j ->
is_true (@job_of_task Job Task H0 tsk j) ->
is_true (~~ @completed_by Job (ideal.processor_state Job) sched H2 j t2) ->
is_true
  (@cumul_task_interference Job Task H0 (ideal.processor_state Job) arr_seq sched
     (@ideal_jlfp_interference Job arr_seq sched JLFP) j t1 t2 <=
   @cumulative_priority_inversion Job (ideal.processor_state Job) arr_seq sched JLFP j t1 t2 +
   @cumulative_another_task_hep_job_interference Task Job H0 (ideal.processor_state Job) arr_seq sched JLFP j
     t1 t2)

cumulative_task_interference_split is not universe polymorphic
Arguments cumulative_task_interference_split {Task Job H0 H1 H2} arr_seq H_valid_arrival_sequence 
  sched H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute {JLFP} H_priority_is_reflexive 
  tsk j t1%nat_scope t2 _ _ _
cumulative_task_interference_split is opaque
Expands to: Constant prosa.analysis.abstract.ideal.iw_instantiation.cumulative_task_interference_split
Declared in library prosa.analysis.abstract.ideal.iw_instantiation, line 265, characters 8-42
@cumulative_task_interference_split
     : forall (Task : TaskType) (Job : JobType) (H0 : JobTask Job Task) (H1 : JobArrival Job)
         (H2 : JobCost Job) (arr_seq : arrival_sequence Job),
       @valid_arrival_sequence Job H1 arr_seq ->
       forall sched : @schedule Job (ideal.processor_state Job),
       @jobs_come_from_arrival_sequence Job (ideal.processor_state Job) sched arr_seq ->
       @jobs_must_arrive_to_execute Job H1 (ideal.processor_state Job) sched ->
       forall JLFP : JLFP_policy Job,
       @reflexive_job_priorities Job JLFP ->
       forall (tsk : Equality.sort Task) (j : Equality.sort Job) (t1 : nat) (t2 : instant),
       @arrives_in Job arr_seq j ->
       is_true (@job_of_task Job Task H0 tsk j) ->
       is_true (~~ @completed_by Job (ideal.processor_state Job) sched H2 j t2) ->
       is_true
         (@cumul_task_interference Job Task H0 (ideal.processor_state Job) arr_seq sched
            (@ideal_jlfp_interference Job arr_seq sched JLFP) j t1 t2 <=
          @cumulative_priority_inversion Job (ideal.processor_state Job) arr_seq sched JLFP j t1 t2 +
          @cumulative_another_task_hep_job_interference Task Job H0 (ideal.processor_state Job) arr_seq sched
            JLFP j t1 t2)
```

## Lean

```lean
@Prosa.Analysis.Abstract.Ideal.IwInstantiation.cumulative_task_interference_split : ∀
  {Task : Prosa.Model.Task.Concept.TaskType} [inst : DecidableEq Task] {Job : Prosa.Behavior.Job.JobType}
  [inst_1 : DecidableEq Job] [inst_2 : Prosa.Model.Task.Concept.JobTask Job Task]
  [inst_3 : Prosa.Behavior.Job.JobArrival Job] [inst_4 : Prosa.Behavior.Job.JobCost Job]
  (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
  Prosa.Behavior.Arrival_sequence.valid_arrival_sequence arr_seq →
    ∀ (sched : Prosa.Behavior.Schedule.schedule (Prosa.Model.Processor.Ideal.processor_state Job)),
      Prosa.Behavior.Ready.jobs_come_from_arrival_sequence sched arr_seq →
        Prosa.Behavior.Ready.jobs_must_arrive_to_execute sched →
          ∀ [JLFP : Prosa.Model.Priority.Definitions.JLFP_policy Job],
            Prosa.Model.Priority.Definitions.reflexive_job_priorities JLFP →
              ∀ (tsk : Task) (j : Job) (t1 : ℕ) (t2 : Prosa.Behavior.Time.instant),
                Prosa.Behavior.Arrival_sequence.arrives_in arr_seq j →
                  Prosa.Model.Task.Concept.job_of_task tsk j = true →
                    (!Prosa.Behavior.Service.completed_by sched j t2) = true →
                      Prosa.Analysis.Abstract.IBF.Task.cumul_task_interference arr_seq sched j t1 t2 ≤
                        Prosa.Analysis.Definitions.PriorityInversion.cumulative_priority_inversion arr_seq sched j t1
                            t2 +
                          Prosa.Analysis.Definitions.Interference.cumulative_another_task_hep_job_interference arr_seq
                            sched j t1 t2
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Abstract_Ideal_IwInstantiation_cumulative_task_interference_split
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
         (inst_17 : 
          Prosa_Behavior_Job_JobCost Job
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
         JLFP : Prosa_Model_Priority_Definitions_JLFP_policy Job
                  inst_7,
       Prosa_Model_Priority_Definitions_reflexive_job_priorities Job
         inst_7 JLFP ->
       forall (tsk : Task) (j : Job) (t1 : Nat) (t2 : Prosa_Behavior_Time_instant),
       Prosa_Behavior_Arrival_sequence_arrives_in Job
         inst_7 arr_seq j ->
       @eq Bool
         (Prosa_Model_Task_Concept_job_of_task Job
            inst_7 Task
            inst_3
            inst_10 tsk j)
         Bool_true ->
       @eq Bool
         (Bool_not
            (Prosa_Behavior_Service_completed_by_inst4 Job
               inst_7
               (Prosa_Model_Processor_Ideal_processor_state Job
                  inst_7)
               sched inst_17 j t2))
         Bool_true ->
       LE_le_inst1 Nat instLENat
         (Prosa_Analysis_Abstract_IBF_Task_cumul_task_interference_inst8 Job
            inst_7 Task
            inst_3
            inst_10
            (Prosa_Model_Processor_Ideal_processor_state Job
               inst_7)
            arr_seq sched
            (Prosa_Analysis_Abstract_Ideal_IwInstantiation_ideal_jlfp_interference Job
               inst_7 arr_seq
               sched JLFP)
            j t1 t2)
         (HAdd_hAdd_inst7 Nat Nat Nat (instHAdd_inst1 Nat instAddNat)
            (Prosa_Analysis_Definitions_PriorityInversion_cumulative_priority_inversion_inst4 Job
               inst_7
               (Prosa_Model_Processor_Ideal_processor_state Job
                  inst_7)
               arr_seq sched JLFP j t1 t2)
            (Prosa_Analysis_Definitions_Interference_cumulative_another_task_hep_job_interference_inst8 Task
               inst_3 Job
               inst_7
               inst_10
               (Prosa_Model_Processor_Ideal_processor_state Job
                  inst_7)
               arr_seq sched JLFP j t1 t2))
```
