# `jitter_response_time_bound`

- Kind (Rocq): Theorem
- Rocq: `prosa.analysis.facts.jitter.jitter_response_time_bound`
- Lean: `Prosa.Analysis.Facts.Jitter.jitter_response_time_bound`
- Certificate: `jitter_response_time_bound_correspondence`

## Official Rocq

```coq
jitter_response_time_bound :
forall {Task : TaskType} {Job : JobType} {H : JobTask Job Task} {original_arrival : JobArrival Job}
  {H0 : TaskJitter Task} {H1 : JobJitter Job} (arr_seq : arrival_sequence Job),
@valid_arrival_sequence Job original_arrival arr_seq ->
forall ts : seq (Equality.sort Task),
@valid_jitter_bounds Task H0 Job H H1 ts ->
forall {PState : ProcessorState Job} (sched : @schedule Job PState) {H2 : JobCost Job}
  (tsk : Equality.sort Task) (R : duration),
is_true (tsk \in ts) ->
@task_response_time_bound Task Job (@release_as_arrival Job original_arrival H1) H2 H PState
  (@release_sequence Job original_arrival H1 arr_seq) sched tsk R ->
@task_response_time_bound Task Job original_arrival H2 H PState arr_seq sched tsk
  (@task_jitter Task H0 tsk + R)

jitter_response_time_bound is not universe polymorphic
Arguments jitter_response_time_bound {Task Job H original_arrival H0 H1} arr_seq 
  H_valid_arrival_sequence ts%seq_scope H_valid_jitter {PState} sched {H2} tsk R 
  _ _ j _ _
jitter_response_time_bound is opaque
Expands to: Constant prosa.analysis.facts.jitter.jitter_response_time_bound
Declared in library prosa.analysis.facts.jitter, line 263, characters 10-36
@jitter_response_time_bound
     : forall (Task : TaskType) (Job : JobType) (H : JobTask Job Task) (original_arrival : JobArrival Job)
         (H0 : TaskJitter Task) (H1 : JobJitter Job) (arr_seq : arrival_sequence Job),
       @valid_arrival_sequence Job original_arrival arr_seq ->
       forall ts : seq (Equality.sort Task),
       @valid_jitter_bounds Task H0 Job H H1 ts ->
       forall (PState : ProcessorState Job) (sched : @schedule Job PState) (H2 : JobCost Job)
         (tsk : Equality.sort Task) (R : duration),
       is_true (tsk \in ts) ->
       @task_response_time_bound Task Job (@release_as_arrival Job original_arrival H1) H2 H PState
         (@release_sequence Job original_arrival H1 arr_seq) sched tsk R ->
       @task_response_time_bound Task Job original_arrival H2 H PState arr_seq sched tsk
         (@task_jitter Task H0 tsk + R)
```

## Lean

```lean
@Prosa.Analysis.Facts.Jitter.jitter_response_time_bound : ∀ {Task : Prosa.Model.Task.Concept.TaskType}
  [inst : DecidableEq Task] {Job : Prosa.Behavior.Job.JobType} [inst_1 : DecidableEq Job]
  [inst_2 : Prosa.Model.Task.Concept.JobTask Job Task] (original_arrival : Prosa.Behavior.Job.JobArrival Job)
  [inst_3 : Prosa.Model.Task.Jitter.TaskJitter Task] [inst_4 : Prosa.Model.Readiness.Jitter.JobJitter Job]
  (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
  Prosa.Behavior.Arrival_sequence.valid_arrival_sequence arr_seq →
    ∀ (ts : Prosa.Model.Task.Concept.TaskSet Task),
      Prosa.Model.Task.Jitter.valid_jitter_bounds ts →
        ∀ (PState : Prosa.Behavior.Schedule.ProcessorState Job) (sched : Prosa.Behavior.Schedule.schedule PState)
          [inst_5 : Prosa.Behavior.Job.JobCost Job] (tsk : Task) (R : Prosa.Behavior.Time.duration),
          decide (tsk ∈ ts) = true →
            Prosa.Analysis.Definitions.Schedulability.task_response_time_bound
                (Prosa.Analysis.Definitions.DelayPropagation.release_sequence original_arrival arr_seq) sched tsk R →
              Prosa.Analysis.Definitions.Schedulability.task_response_time_bound arr_seq sched tsk
                (Prosa.Model.Task.Jitter.task_jitter tsk + R)
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Jitter_jitter_response_time_bound
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task)
         (Job : Prosa_Behavior_Job_JobType)
         (inst_7 : DecidableEq Job)
         (inst_10 : Prosa_Model_Task_Concept_JobTask
                                                                                Job
                                                                                inst_7
                                                                                Task
                                                                                inst_3)
         (original_arrival : Prosa_Behavior_Job_JobArrival Job
                               inst_7)
         (inst_16 : Prosa_Model_Task_Jitter_TaskJitter
                                                                                Task
                                                                                inst_3)
         (inst_19 : Prosa_Model_Readiness_Jitter_JobJitter
                                                                                Job
                                                                                inst_7)
         (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                      inst_7),
       Prosa_Behavior_Arrival_sequence_valid_arrival_sequence Job
         inst_7 original_arrival arr_seq ->
       forall ts : Prosa_Model_Task_Concept_TaskSet Task,
       Prosa_Model_Task_Jitter_valid_jitter_bounds Task
         inst_3
         inst_16 Job
         inst_7
         inst_10
         inst_19 ts ->
       forall
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_7)
         (sched : Prosa_Behavior_Schedule_schedule Job
                    inst_7 PState)
         (inst_43 : Prosa_Behavior_Job_JobCost Job
                                                                                inst_7)
         (tsk : Task) (R : Prosa_Behavior_Time_duration),
       @eq Bool
         (Decidable_decide
            (Membership_mem Task (Prosa_Model_Task_Concept_TaskSet Task) (List_instMembership Task) ts tsk)
            (List_instDecidableMemOfLawfulBEq Task
               (instBEqOfDecidableEq Task inst_3)
               (instLawfulBEq Task inst_3) tsk ts))
         Bool_true ->
       Prosa_Analysis_Definitions_Schedulability_task_response_time_bound Task
         inst_3 Job
         inst_7
         (Prosa_Analysis_Facts_Jitter_release_as_arrival Job
            inst_7 original_arrival
            inst_19)
         inst_43
         inst_10 PState
         (Prosa_Analysis_Definitions_DelayPropagation_release_sequence Job
            inst_7 original_arrival
            inst_19 arr_seq)
         sched tsk R ->
       Prosa_Analysis_Definitions_Schedulability_task_response_time_bound Task
         inst_3 Job
         inst_7 original_arrival
         inst_43
         inst_10 PState arr_seq sched tsk
         (HAdd_hAdd_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration
            Prosa_Behavior_Time_duration (instHAdd_inst1 Prosa_Behavior_Time_duration instAddNat)
            (Prosa_Model_Task_Jitter_TaskJitter_task_jitter Task
               inst_3
               inst_16 tsk)
            R)
```
