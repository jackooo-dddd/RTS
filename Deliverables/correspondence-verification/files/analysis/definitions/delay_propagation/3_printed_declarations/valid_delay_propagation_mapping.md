# `valid_delay_propagation_mapping`

- Kind (Rocq): Definition
- Rocq: `prosa.analysis.definitions.delay_propagation.valid_delay_propagation_mapping`
- Lean: `Prosa.Analysis.Definitions.DelayPropagation.valid_delay_propagation_mapping`
- Certificate: `valid_delay_propagation_mapping_correspondence`

## Official Rocq

```coq
valid_delay_propagation_mapping :
forall {Task1 Task2 : TaskType} {Job1 Job2 : JobType},
JobTask Job1 Task1 ->
JobTask Job2 Task2 ->
JobArrival Job1 ->
JobArrival Job2 ->
(Equality.sort Job2 -> Equality.sort Job1) ->
(Equality.sort Task2 -> Equality.sort Task1) ->
(Equality.sort Task2 -> duration) -> seq (Equality.sort Task2) -> Prop

valid_delay_propagation_mapping is not universe polymorphic
Arguments valid_delay_propagation_mapping {Task1 Task2 Job1 Job2 H H0} H1 H2
  (job1_of task1_of delay_bound)%function_scope ts%seq_scope
valid_delay_propagation_mapping is transparent
Expands to: Constant prosa.analysis.definitions.delay_propagation.valid_delay_propagation_mapping
Declared in library prosa.analysis.definitions.delay_propagation, line 51, characters 13-44
@valid_delay_propagation_mapping
     : forall (Task1 Task2 : TaskType) (Job1 Job2 : JobType),
       JobTask Job1 Task1 ->
       JobTask Job2 Task2 ->
       JobArrival Job1 ->
       JobArrival Job2 ->
       (Equality.sort Job2 -> Equality.sort Job1) ->
       (Equality.sort Task2 -> Equality.sort Task1) ->
       (Equality.sort Task2 -> duration) -> seq (Equality.sort Task2) -> Prop
```

Body:

```coq
valid_delay_propagation_mapping =
fun (Task1 Task2 : TaskType) (Job1 Job2 : JobType) (H : JobTask Job1 Task1) (H0 : JobTask Job2 Task2)
  (H1 : JobArrival Job1) (H2 : JobArrival Job2) (job1_of : Equality.sort Job2 -> Equality.sort Job1)
  (task1_of : Equality.sort Task2 -> Equality.sort Task1) (delay_bound : Equality.sort Task2 -> duration) =>
let consistent_task_job_mapping :=
  forall j2 : Equality.sort Job2, @job_task Job1 Task1 H (job1_of j2) = task1_of (@job_task Job2 Task2 H0 j2)
  in
let bounded_arrival_delay :=
  fun ts : seq (Equality.sort Task2) =>
  forall j2 : Equality.sort Job2,
  is_true (@job_task Job2 Task2 H0 j2 \in ts) ->
  is_true
    (@job_arrival Job2 H2 j2 <= @job_arrival Job1 H1 (job1_of j2) + delay_bound (@job_task Job2 Task2 H0 j2))
  in
fun ts : seq (Equality.sort Task2) => consistent_task_job_mapping /\ bounded_arrival_delay ts
     : forall {Task1 Task2 : TaskType} {Job1 Job2 : JobType},
       JobTask Job1 Task1 ->
       JobTask Job2 Task2 ->
       JobArrival Job1 ->
       JobArrival Job2 ->
       (Equality.sort Job2 -> Equality.sort Job1) ->
       (Equality.sort Task2 -> Equality.sort Task1) ->
       (Equality.sort Task2 -> duration) -> seq (Equality.sort Task2) -> Prop

Arguments valid_delay_propagation_mapping {Task1 Task2 Job1 Job2 H H0} H1 H2
  (job1_of task1_of delay_bound)%function_scope ts%seq_scope
```

## Lean

```lean
@Prosa.Analysis.Definitions.DelayPropagation.valid_delay_propagation_mapping : {Task1 :
    Prosa.Model.Task.Concept.TaskType} →
  {Task2 : Prosa.Model.Task.Concept.TaskType} →
    [inst : DecidableEq Task1] →
      [inst_1 : DecidableEq Task2] →
        {Job1 : Prosa.Behavior.Job.JobType} →
          {Job2 : Prosa.Behavior.Job.JobType} →
            [inst_2 : DecidableEq Job1] →
              [inst_3 : DecidableEq Job2] →
                [Prosa.Model.Task.Concept.JobTask Job1 Task1] →
                  [Prosa.Model.Task.Concept.JobTask Job2 Task2] →
                    Prosa.Behavior.Job.JobArrival Job1 →
                      Prosa.Behavior.Job.JobArrival Job2 →
                        (Job2 → Job1) → (Task2 → Task1) → (Task2 → Prosa.Behavior.Time.duration) → List Task2 → Prop
def Prosa.Analysis.Definitions.DelayPropagation.valid_delay_propagation_mapping.{u_1, u_2, u_3, u_4} : {Task1 :
    Prosa.Model.Task.Concept.TaskType} →
  {Task2 : Prosa.Model.Task.Concept.TaskType} →
    [inst : DecidableEq Task1] →
      [inst_1 : DecidableEq Task2] →
        {Job1 : Prosa.Behavior.Job.JobType} →
          {Job2 : Prosa.Behavior.Job.JobType} →
            [inst_2 : DecidableEq Job1] →
              [inst_3 : DecidableEq Job2] →
                [Prosa.Model.Task.Concept.JobTask Job1 Task1] →
                  [Prosa.Model.Task.Concept.JobTask Job2 Task2] →
                    Prosa.Behavior.Job.JobArrival Job1 →
                      Prosa.Behavior.Job.JobArrival Job2 →
                        (Job2 → Job1) → (Task2 → Task1) → (Task2 → Prosa.Behavior.Time.duration) → List Task2 → Prop :=
fun {Task1} {Task2} [DecidableEq Task1] [DecidableEq Task2] {Job1} {Job2} [DecidableEq Job1] [DecidableEq Job2]
    [Prosa.Model.Task.Concept.JobTask Job1 Task1] [Prosa.Model.Task.Concept.JobTask Job2 Task2] ja1 ja2 job1_of task1_of
    delay_bound ts =>
  (∀ (j2 : Job2), Prosa.Model.Task.Concept.job_task (job1_of j2) = task1_of (Prosa.Model.Task.Concept.job_task j2)) ∧
    ∀ (j2 : Job2),
      decide (Prosa.Model.Task.Concept.job_task j2 ∈ ts) = true →
        Prosa.Behavior.Job.job_arrival j2 ≤
          Prosa.Behavior.Job.job_arrival (job1_of j2) + delay_bound (Prosa.Model.Task.Concept.job_task j2)
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Definitions_DelayPropagation_valid_delay_propagation_mapping
     : forall (Task1 Task2 : Prosa_Model_Task_Concept_TaskType)
         (inst_4 : 
          DecidableEq Task1)
         (inst_7 : 
          DecidableEq Task2)
         (Job1 Job2 : Prosa_Behavior_Job_JobType)
         (inst_12 : 
          DecidableEq Job1)
         (inst_15 : 
          DecidableEq Job2),
       Prosa_Model_Task_Concept_JobTask Job1
         inst_12 Task1
         inst_4 ->
       Prosa_Model_Task_Concept_JobTask Job2
         inst_15 Task2
         inst_7 ->
       Prosa_Behavior_Job_JobArrival Job1
         inst_12 ->
       Prosa_Behavior_Job_JobArrival Job2
         inst_15 ->
       (Job2 -> Job1) -> (Task2 -> Task1) -> (Task2 -> Prosa_Behavior_Time_duration) -> List Task2 -> SProp
```

Body:

```coq
Prosa_Analysis_Definitions_DelayPropagation_valid_delay_propagation_mapping@{u_1 u_2 u_3 u_4 Lean.u_1+1.0
Lean.max__u_1+1_u_3+1.0 Lean.u_2+1.0 Lean.max__u_2+1_u_4+1.0 Lean.u_3+1.0 Lean.u_4+1.0 Lean.u_1+2.0
Lean.u_2+2.0 Lean.u_3+2.0 Lean.u_4+2.0} =
fun (Task1 Task2 : Prosa_Model_Task_Concept_TaskType)
  (inst_4 : DecidableEq Task1)
  (inst_7 : DecidableEq Task2)
  (Job1 Job2 : Prosa_Behavior_Job_JobType)
  (inst_12 : DecidableEq Job1)
  (inst_15 : DecidableEq Job2)
  (inst_18 : 
   Prosa_Model_Task_Concept_JobTask Job1
     inst_12 Task1
     inst_4)
  (inst_22 : 
   Prosa_Model_Task_Concept_JobTask Job2
     inst_15 Task2
     inst_7)
  (ja1 : Prosa_Behavior_Job_JobArrival Job1
           inst_12)
  (ja2 : Prosa_Behavior_Job_JobArrival Job2
           inst_15)
  (job1_of : Job2 -> Job1) (task1_of : Task2 -> Task1) (delay_bound : Task2 -> Prosa_Behavior_Time_duration)
  (ts : List Task2) =>
And
  (forall j2 : Job2,
   @eq Task1
     (Prosa_Model_Task_Concept_JobTask_job_task Job1
        inst_12 Task1
        inst_4
        inst_18 
        (job1_of j2))
     (task1_of
        (Prosa_Model_Task_Concept_JobTask_job_task Job2
           inst_15 Task2
           inst_7
           inst_22 j2)))
  (forall j2 : Job2,
   @eq Bool
     (Decidable_decide
        (Membership_mem Task2 (List Task2) (List_instMembership Task2) ts
           (Prosa_Model_Task_Concept_JobTask_job_task Job2
              inst_15 Task2
              inst_7
              inst_22 j2))
        (List_instDecidableMemOfLawfulBEq Task2
           (instBEqOfDecidableEq Task2
              inst_7)
           (instLawfulBEq Task2
              inst_7)
           (Prosa_Model_Task_Concept_JobTask_job_task Job2
              inst_15 Task2
              inst_7
              inst_22 j2)
           ts))
     Bool_true ->
   LE_le_inst1 Prosa_Behavior_Time_instant instLENat
     (Prosa_Behavior_Job_JobArrival_job_arrival Job2
        inst_15 ja2 j2)
     (HAdd_hAdd_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_duration Prosa_Behavior_Time_instant
        (instHAdd_inst1 Prosa_Behavior_Time_instant instAddNat)
        (Prosa_Behavior_Job_JobArrival_job_arrival Job1
           inst_12 ja1 
           (job1_of j2))
        (delay_bound
           (Prosa_Model_Task_Concept_JobTask_job_task Job2
              inst_15 Task2
              inst_7
              inst_22 j2))))
     : forall (Task1 Task2 : Prosa_Model_Task_Concept_TaskType)
         (inst_4 : 
          DecidableEq Task1)
         (inst_7 : 
          DecidableEq Task2)
         (Job1 Job2 : Prosa_Behavior_Job_JobType)
         (inst_12 : 
          DecidableEq Job1)
         (inst_15 : 
          DecidableEq Job2),
       Prosa_Model_Task_Concept_JobTask Job1
         inst_12 Task1
         inst_4 ->
       Prosa_Model_Task_Concept_JobTask Job2
         inst_15 Task2
         inst_7 ->
       Prosa_Behavior_Job_JobArrival Job1
         inst_12 ->
       Prosa_Behavior_Job_JobArrival Job2
         inst_15 ->
       (Job2 -> Job1) -> (Task2 -> Task1) -> (Task2 -> Prosa_Behavior_Time_duration) -> List Task2 -> SProp

Arguments Prosa_Analysis_Definitions_DelayPropagation_valid_delay_propagation_mapping 
  Task1 Task2 inst_4
  inst_7 
  Job1 Job2 inst_12
  inst_15
  inst_18
  inst_22 
  ja1 ja2 (job1_of task1_of delay_bound)%_function_scope ts
```
