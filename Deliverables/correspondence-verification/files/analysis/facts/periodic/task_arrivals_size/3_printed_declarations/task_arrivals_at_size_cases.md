# `task_arrivals_at_size_cases`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.periodic.task_arrivals_size.task_arrivals_at_size_cases`
- Lean: `Prosa.Analysis.Facts.Periodic.TaskArrivalsSize.task_arrivals_at_size_cases`
- Certificate: `task_arrivals_at_size_cases_correspondence`

## Official Rocq

```coq
task_arrivals_at_size_cases :
forall {Task : TaskType} {H0 : PeriodicModel Task} {Job : JobType} {H1 : JobTask Job Task}
  {H2 : JobArrival Job} (arr_seq : arrival_sequence Job),
@valid_arrival_sequence Job H2 arr_seq ->
forall tsk : Equality.sort Task,
is_true (@valid_period Task H0 tsk) ->
@respects_periodic_task_model Task H0 Job H1 H2 arr_seq tsk ->
forall t : instant,
@size (Equality.sort Job) (@task_arrivals_at Job Task H1 arr_seq tsk t) = 0 \/
@size (Equality.sort Job) (@task_arrivals_at Job Task H1 arr_seq tsk t) = 1

task_arrivals_at_size_cases is not universe polymorphic
Arguments task_arrivals_at_size_cases {Task H0 Job H1 H2} arr_seq H_valid_arrival_sequence 
  tsk H_valid_period H_task_respects_periodic_model t
task_arrivals_at_size_cases is opaque
Expands to: Constant prosa.analysis.facts.periodic.task_arrivals_size.task_arrivals_at_size_cases
Declared in library prosa.analysis.facts.periodic.task_arrivals_size, line 56, characters 8-35
@task_arrivals_at_size_cases
     : forall (Task : TaskType) (H0 : PeriodicModel Task) (Job : JobType) (H1 : JobTask Job Task)
         (H2 : JobArrival Job) (arr_seq : arrival_sequence Job),
       @valid_arrival_sequence Job H2 arr_seq ->
       forall tsk : Equality.sort Task,
       is_true (@valid_period Task H0 tsk) ->
       @respects_periodic_task_model Task H0 Job H1 H2 arr_seq tsk ->
       forall t : instant,
       @size (Equality.sort Job) (@task_arrivals_at Job Task H1 arr_seq tsk t) = 0 \/
       @size (Equality.sort Job) (@task_arrivals_at Job Task H1 arr_seq tsk t) = 1
```

## Lean

```lean
@Prosa.Analysis.Facts.Periodic.TaskArrivalsSize.task_arrivals_at_size_cases : ∀
  {Task : Prosa.Model.Task.Concept.TaskType} [inst : DecidableEq Task]
  [inst_1 : Prosa.Model.Task.Arrival.Periodic.PeriodicModel Task] {Job : Prosa.Behavior.Job.JobType}
  [inst_2 : DecidableEq Job] [inst_3 : Prosa.Model.Task.Concept.JobTask Job Task]
  [inst_4 : Prosa.Behavior.Job.JobArrival Job] (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
  Prosa.Behavior.Arrival_sequence.valid_arrival_sequence arr_seq →
    ∀ (tsk : Task),
      Prosa.Model.Task.Arrival.Periodic.valid_period tsk = true →
        Prosa.Model.Task.Arrival.Periodic.respects_periodic_task_model arr_seq tsk →
          ∀ (t : Prosa.Behavior.Time.instant),
            (Prosa.Model.Task.Arrivals.task_arrivals_at arr_seq tsk t).length = 0 ∨
              (Prosa.Model.Task.Arrivals.task_arrivals_at arr_seq tsk t).length = 1
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Periodic_TaskArrivalsSize_task_arrivals_at_size_cases
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : 
          DecidableEq Task)
         (inst_6 : 
          Prosa_Model_Task_Arrival_Periodic_PeriodicModel Task
            inst_3)
         (Job : Prosa_Behavior_Job_JobType)
         (inst_10 : 
          DecidableEq Job)
         (inst_13 : 
          Prosa_Model_Task_Concept_JobTask Job
            inst_10 Task
            inst_3)
         (inst_17 : 
          Prosa_Behavior_Job_JobArrival Job
            inst_10)
         (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                      inst_10),
       Prosa_Behavior_Arrival_sequence_valid_arrival_sequence Job
         inst_10
         inst_17 arr_seq ->
       forall tsk : Task,
       @eq Bool
         (Prosa_Model_Task_Arrival_Periodic_valid_period Task
            inst_3
            inst_6 tsk)
         Bool_true ->
       Prosa_Model_Task_Arrival_Periodic_respects_periodic_task_model Task
         inst_3
         inst_6 Job
         inst_10
         inst_13
         inst_17 arr_seq tsk ->
       forall t : Prosa_Behavior_Time_instant,
       Or
         (@eq Nat
            (List_length Job
               (Prosa_Model_Task_Arrivals_task_arrivals_at Job
                  inst_10 Task
                  inst_3
                  inst_13
                  arr_seq tsk t))
            (OfNat_ofNat_inst1 Nat 0 (instOfNatNat 0)))
         (@eq Nat
            (List_length Job
               (Prosa_Model_Task_Arrivals_task_arrivals_at Job
                  inst_10 Task
                  inst_3
                  inst_13
                  arr_seq tsk t))
            (OfNat_ofNat_inst1 Nat 1 (instOfNatNat 1)))
```
