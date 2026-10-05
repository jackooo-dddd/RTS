# `size_task_arrivals_at_leq_one`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.sporadic.arrival_sequence.size_task_arrivals_at_leq_one`
- Lean: `Prosa.Analysis.Facts.Sporadic.ArrivalSequence.size_task_arrivals_at_leq_one`
- Certificate: `size_task_arrivals_at_leq_one_correspondence`

## Official Rocq

```coq
size_task_arrivals_at_leq_one :
forall {Task : TaskType} {H : SporadicModel Task} {Job : JobType} {H0 : JobTask Job Task}
  {H1 : JobArrival Job} (arr_seq : arrival_sequence Job),
@valid_arrival_sequence Job H1 arr_seq ->
~
(exists j : Equality.sort Job,
   is_true (1 < @size (Equality.sort Job) (@task_arrivals_at_job_arrival Job Task H0 H1 arr_seq j)) /\
   @respects_sporadic_task_model Task H Job H0 H1 arr_seq (@job_task Job Task H0 j) /\
   is_true (@valid_task_min_inter_arrival_time Task H (@job_task Job Task H0 j)))

size_task_arrivals_at_leq_one is not universe polymorphic
Arguments size_task_arrivals_at_leq_one {Task H Job H0 H1} arr_seq H_valid_arrival_sequence _
size_task_arrivals_at_leq_one is opaque
Expands to: Constant prosa.analysis.facts.sporadic.arrival_sequence.size_task_arrivals_at_leq_one
Declared in library prosa.analysis.facts.sporadic.arrival_sequence, line 37, characters 8-37
@size_task_arrivals_at_leq_one
     : forall (Task : TaskType) (H : SporadicModel Task) (Job : JobType) (H0 : JobTask Job Task)
         (H1 : JobArrival Job) (arr_seq : arrival_sequence Job),
       @valid_arrival_sequence Job H1 arr_seq ->
       ~
       (exists j : Equality.sort Job,
          is_true (1 < @size (Equality.sort Job) (@task_arrivals_at_job_arrival Job Task H0 H1 arr_seq j)) /\
          @respects_sporadic_task_model Task H Job H0 H1 arr_seq (@job_task Job Task H0 j) /\
          is_true (@valid_task_min_inter_arrival_time Task H (@job_task Job Task H0 j)))
```

## Lean

```lean
@Prosa.Analysis.Facts.Sporadic.ArrivalSequence.size_task_arrivals_at_leq_one : ∀
  {Task : Prosa.Model.Task.Concept.TaskType} [inst : DecidableEq Task]
  [inst_1 : Prosa.Model.Task.Arrival.Sporadic.SporadicModel Task] {Job : Prosa.Behavior.Job.JobType}
  [inst_2 : DecidableEq Job] [inst_3 : Prosa.Model.Task.Concept.JobTask Job Task]
  [inst_4 : Prosa.Behavior.Job.JobArrival Job] (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
  Prosa.Behavior.Arrival_sequence.valid_arrival_sequence arr_seq →
    ¬∃ j,
        1 < (Prosa.Model.Task.Arrivals.task_arrivals_at_job_arrival arr_seq j).length ∧
          Prosa.Model.Task.Arrival.Sporadic.respects_sporadic_task_model arr_seq (Prosa.Model.Task.Concept.job_task j) ∧
            Prosa.Model.Task.Arrival.Sporadic.valid_task_min_inter_arrival_time (Prosa.Model.Task.Concept.job_task j) =
              true
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Sporadic_ArrivalSequence_size_task_arrivals_at_leq_one
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : 
          DecidableEq Task)
         (inst_6 : 
          Prosa_Model_Task_Arrival_Sporadic_SporadicModel Task
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
       Not
         (Exists Job
            (fun j : Job =>
             And
               (LT_lt_inst1 Nat instLTNat (OfNat_ofNat_inst1 Nat 1 (instOfNatNat 1))
                  (List_length Job
                     (Prosa_Model_Task_Arrivals_task_arrivals_at_job_arrival Job
                        inst_10
                        Task inst_3
                        inst_13
                        inst_17
                        arr_seq j)))
               (And
                  (Prosa_Model_Task_Arrival_Sporadic_respects_sporadic_task_model Task
                     inst_3
                     inst_6 Job
                     inst_10
                     inst_13
                     inst_17
                     arr_seq
                     (Prosa_Model_Task_Concept_JobTask_job_task Job
                        inst_10
                        Task inst_3
                        inst_13 j))
                  (@eq Bool
                     (Prosa_Model_Task_Arrival_Sporadic_valid_task_min_inter_arrival_time Task
                        inst_3
                        inst_6
                        (Prosa_Model_Task_Concept_JobTask_job_task Job
                           inst_10
                           Task
                           inst_3
                           inst_13
                           j))
                     Bool_true))))
```
