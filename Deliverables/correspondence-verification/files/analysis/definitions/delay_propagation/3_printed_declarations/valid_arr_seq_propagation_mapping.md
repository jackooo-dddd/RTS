# `valid_arr_seq_propagation_mapping`

- Kind (Rocq): Definition
- Rocq: `prosa.analysis.definitions.delay_propagation.valid_arr_seq_propagation_mapping`
- Lean: `Prosa.Analysis.Definitions.DelayPropagation.valid_arr_seq_propagation_mapping`
- Certificate: `valid_arr_seq_propagation_mapping_correspondence`

## Official Rocq

```coq
valid_arr_seq_propagation_mapping :
forall {Task2 : TaskType} {Job1 Job2 : JobType},
JobTask Job2 Task2 ->
JobArrival Job1 ->
JobArrival Job2 ->
(Equality.sort Job2 -> Equality.sort Job1) ->
(Equality.sort Task2 -> duration) ->
arrival_sequence Job1 ->
(Equality.sort Job1 -> seq (Equality.sort Job2)) ->
(Equality.sort Job2 -> duration) -> seq (Equality.sort Task2) -> Prop

valid_arr_seq_propagation_mapping is not universe polymorphic
Arguments valid_arr_seq_propagation_mapping {Task2 Job1 Job2 H0} H1 H2 (job1_of delay_bound)%function_scope
  arr_seq1 (job2_of arrival_delay)%function_scope ts%seq_scope
valid_arr_seq_propagation_mapping is transparent
Expands to: Constant prosa.analysis.definitions.delay_propagation.valid_arr_seq_propagation_mapping
Declared in library prosa.analysis.definitions.delay_propagation, line 123, characters 13-46
@valid_arr_seq_propagation_mapping
     : forall (Task2 : TaskType) (Job1 Job2 : JobType),
       JobTask Job2 Task2 ->
       JobArrival Job1 ->
       JobArrival Job2 ->
       (Equality.sort Job2 -> Equality.sort Job1) ->
       (Equality.sort Task2 -> duration) ->
       arrival_sequence Job1 ->
       (Equality.sort Job1 -> seq (Equality.sort Job2)) ->
       (Equality.sort Job2 -> duration) -> seq (Equality.sort Task2) -> Prop
```

Body:

```coq
valid_arr_seq_propagation_mapping =
fun (Task2 : TaskType) (Job1 Job2 : JobType) (H0 : JobTask Job2 Task2) (H1 : JobArrival Job1)
  (H2 : JobArrival Job2) (job1_of : Equality.sort Job2 -> Equality.sort Job1)
  (delay_bound : Equality.sort Task2 -> duration) (arr_seq1 : arrival_sequence Job1)
  (job2_of : Equality.sort Job1 -> seq (Equality.sort Job2)) (arrival_delay : Equality.sort Job2 -> duration) =>
let consistent_job_mapping :=
  forall (j1 : Equality.sort Job1) (j2 : Equality.sort Job2), is_true (j2 \in job2_of j1) <-> job1_of j2 = j1
  in
let valid_arrival_delay :=
  fun ts : seq (Equality.sort Task2) =>
  forall j2 : Equality.sort Job2,
  is_true (@job_task Job2 Task2 H0 j2 \in ts) ->
  @arrives_in Job1 arr_seq1 (job1_of j2) ->
  is_true (arrival_delay j2 <= delay_bound (@job_task Job2 Task2 H0 j2)) in
let valid_job_arrival_def :=
  forall j2 : Equality.sort Job2,
  @job_arrival Job2 H2 j2 = @job_arrival Job1 H1 (job1_of j2) + arrival_delay j2 in
fun ts : seq (Equality.sort Task2) =>
  & valid_job_arrival_def]
     : forall {Task2 : TaskType} {Job1 Job2 : JobType},
       JobTask Job2 Task2 ->
       JobArrival Job1 ->
       JobArrival Job2 ->
       (Equality.sort Job2 -> Equality.sort Job1) ->
       (Equality.sort Task2 -> duration) ->
       arrival_sequence Job1 ->
       (Equality.sort Job1 -> seq (Equality.sort Job2)) ->
       (Equality.sort Job2 -> duration) -> seq (Equality.sort Task2) -> Prop

Arguments valid_arr_seq_propagation_mapping {Task2 Job1 Job2 H0} H1 H2 (job1_of delay_bound)%function_scope
  arr_seq1 (job2_of arrival_delay)%function_scope ts%seq_scope
```

## Lean

```lean
@Prosa.Analysis.Definitions.DelayPropagation.valid_arr_seq_propagation_mapping : {Task2 :
    Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task2] →
    {Job1 : Prosa.Behavior.Job.JobType} →
      {Job2 : Prosa.Behavior.Job.JobType} →
        [inst_1 : DecidableEq Job1] →
          [inst_2 : DecidableEq Job2] →
            [Prosa.Model.Task.Concept.JobTask Job2 Task2] →
              Prosa.Behavior.Job.JobArrival Job1 →
                Prosa.Behavior.Job.JobArrival Job2 →
                  (Job2 → Job1) →
                    (Task2 → Prosa.Behavior.Time.duration) →
                      Prosa.Behavior.Arrival_sequence.arrival_sequence Job1 →
                        (Job1 → List Job2) → (Job2 → Prosa.Behavior.Time.duration) → List Task2 → Prop
def Prosa.Analysis.Definitions.DelayPropagation.valid_arr_seq_propagation_mapping.{u_1, u_2, u_3} : {Task2 :
    Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task2] →
    {Job1 : Prosa.Behavior.Job.JobType} →
      {Job2 : Prosa.Behavior.Job.JobType} →
        [inst_1 : DecidableEq Job1] →
          [inst_2 : DecidableEq Job2] →
            [Prosa.Model.Task.Concept.JobTask Job2 Task2] →
              Prosa.Behavior.Job.JobArrival Job1 →
                Prosa.Behavior.Job.JobArrival Job2 →
                  (Job2 → Job1) →
                    (Task2 → Prosa.Behavior.Time.duration) →
                      Prosa.Behavior.Arrival_sequence.arrival_sequence Job1 →
                        (Job1 → List Job2) → (Job2 → Prosa.Behavior.Time.duration) → List Task2 → Prop :=
fun {Task2} [DecidableEq Task2] {Job1} {Job2} [DecidableEq Job1] [DecidableEq Job2]
    [Prosa.Model.Task.Concept.JobTask Job2 Task2] ja1 ja2 job1_of delay_bound arr_seq1 job2_of arrival_delay ts =>
  (∀ (j1 : Job1) (j2 : Job2), decide (j2 ∈ job2_of j1) = true ↔ job1_of j2 = j1) ∧
    Prosa.Analysis.Definitions.DelayPropagation.job_mapping_uniq arr_seq1 job2_of ∧
      (∀ (j2 : Job2),
          decide (Prosa.Model.Task.Concept.job_task j2 ∈ ts) = true →
            Prosa.Behavior.Arrival_sequence.arrives_in arr_seq1 (job1_of j2) →
              arrival_delay j2 ≤ delay_bound (Prosa.Model.Task.Concept.job_task j2)) ∧
        ∀ (j2 : Job2),
          Prosa.Behavior.Job.job_arrival j2 = Prosa.Behavior.Job.job_arrival (job1_of j2) + arrival_delay j2
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Definitions_DelayPropagation_valid_arr_seq_propagation_mapping
     : forall (Task2 : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : 
          DecidableEq Task2)
         (Job1 Job2 : Prosa_Behavior_Job_JobType)
         (inst_8 : 
          DecidableEq Job1)
         (inst_11 : 
          DecidableEq Job2),
       Prosa_Model_Task_Concept_JobTask Job2
         inst_11 Task2
         inst_3 ->
       Prosa_Behavior_Job_JobArrival Job1
         inst_8 ->
       Prosa_Behavior_Job_JobArrival Job2
         inst_11 ->
       (Job2 -> Job1) ->
       (Task2 -> Prosa_Behavior_Time_duration) ->
       Prosa_Behavior_Arrival_sequence_arrival_sequence Job1
         inst_8 ->
       (Job1 -> List Job2) -> (Job2 -> Prosa_Behavior_Time_duration) -> List Task2 -> SProp
```

Body:

```coq
Prosa_Analysis_Definitions_DelayPropagation_valid_arr_seq_propagation_mapping@{u_1 u_2 u_3 Lean.u_1+1.0
Lean.max__u_1+1_u_3+1.0 Lean.u_2+1.0 Lean.u_3+1.0 Lean.u_1+2.0 Lean.u_2+2.0 Lean.u_3+2.0} =
fun (Task2 : Prosa_Model_Task_Concept_TaskType)
  (inst_3 : DecidableEq Task2)
  (Job1 Job2 : Prosa_Behavior_Job_JobType)
  (inst_8 : DecidableEq Job1)
  (inst_11 : DecidableEq Job2)
  (inst_14 : 
   Prosa_Model_Task_Concept_JobTask Job2
     inst_11 Task2
     inst_3)
  (ja1 : Prosa_Behavior_Job_JobArrival Job1
           inst_8)
  (ja2 : Prosa_Behavior_Job_JobArrival Job2
           inst_11)
  (job1_of : Job2 -> Job1) (delay_bound : Task2 -> Prosa_Behavior_Time_duration)
  (arr_seq1 : Prosa_Behavior_Arrival_sequence_arrival_sequence Job1
                inst_8)
  (job2_of : Job1 -> List Job2) (arrival_delay : Job2 -> Prosa_Behavior_Time_duration) 
  (ts : List Task2) =>
And
  (forall (j1 : Job1) (j2 : Job2),
   Iff
     (@eq Bool
        (Decidable_decide (Membership_mem Job2 (List Job2) (List_instMembership Job2) (job2_of j1) j2)
           (List_instDecidableMemOfLawfulBEq Job2
              (instBEqOfDecidableEq Job2
                 inst_11)
              (instLawfulBEq Job2
                 inst_11)
              j2 (job2_of j1)))
        Bool_true)
     (@eq Job1 (job1_of j2) j1))
  (And
     (Prosa_Analysis_Definitions_DelayPropagation_job_mapping_uniq Job1 Job2
        inst_8
        inst_11 arr_seq1 job2_of)
     (And
        (forall j2 : Job2,
         @eq Bool
           (Decidable_decide
              (Membership_mem Task2 (List Task2) (List_instMembership Task2) ts
                 (Prosa_Model_Task_Concept_JobTask_job_task Job2
                    inst_11 Task2
                    inst_3
                    inst_14 j2))
              (List_instDecidableMemOfLawfulBEq Task2
                 (instBEqOfDecidableEq Task2
                    inst_3)
                 (instLawfulBEq Task2
                    inst_3)
                 (Prosa_Model_Task_Concept_JobTask_job_task Job2
                    inst_11 Task2
                    inst_3
                    inst_14 j2)
                 ts))
           Bool_true ->
         Prosa_Behavior_Arrival_sequence_arrives_in Job1
           inst_8 arr_seq1
           (job1_of j2) ->
         LE_le_inst1 Prosa_Behavior_Time_duration instLENat (arrival_delay j2)
           (delay_bound
              (Prosa_Model_Task_Concept_JobTask_job_task Job2
                 inst_11 Task2
                 inst_3
                 inst_14 j2)))
        (forall j2 : Job2,
         @eq Prosa_Behavior_Time_instant
           (Prosa_Behavior_Job_JobArrival_job_arrival Job2
              inst_11 ja2 j2)
           (HAdd_hAdd_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_duration
              Prosa_Behavior_Time_instant (instHAdd_inst1 Prosa_Behavior_Time_instant instAddNat)
              (Prosa_Behavior_Job_JobArrival_job_arrival Job1
                 inst_8 ja1
                 (job1_of j2))
              (arrival_delay j2)))))
     : forall (Task2 : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : 
          DecidableEq Task2)
         (Job1 Job2 : Prosa_Behavior_Job_JobType)
         (inst_8 : 
          DecidableEq Job1)
         (inst_11 : 
          DecidableEq Job2),
       Prosa_Model_Task_Concept_JobTask Job2
         inst_11 Task2
         inst_3 ->
       Prosa_Behavior_Job_JobArrival Job1
         inst_8 ->
       Prosa_Behavior_Job_JobArrival Job2
         inst_11 ->
       (Job2 -> Job1) ->
       (Task2 -> Prosa_Behavior_Time_duration) ->
       Prosa_Behavior_Arrival_sequence_arrival_sequence Job1
         inst_8 ->
       (Job1 -> List Job2) -> (Job2 -> Prosa_Behavior_Time_duration) -> List Task2 -> SProp

Arguments Prosa_Analysis_Definitions_DelayPropagation_valid_arr_seq_propagation_mapping 
  Task2 inst_3 
  Job1 Job2 inst_8
  inst_11
  inst_14 
  ja1 ja2 (job1_of delay_bound)%_function_scope arr_seq1 (job2_of arrival_delay)%_function_scope 
  ts
```
