# `job_mapping_uniq`

- Kind (Rocq): Definition
- Rocq: `prosa.analysis.definitions.delay_propagation.job_mapping_uniq`
- Lean: `Prosa.Analysis.Definitions.DelayPropagation.job_mapping_uniq`
- Certificate: `job_mapping_uniq_correspondence`

## Official Rocq

```coq
job_mapping_uniq :
forall {Job1 Job2 : JobType},
arrival_sequence Job1 -> (Equality.sort Job1 -> seq (Equality.sort Job2)) -> Prop

job_mapping_uniq is not universe polymorphic
Arguments job_mapping_uniq {Job1 Job2} arr_seq1 job2_of%function_scope
job_mapping_uniq is transparent
Expands to: Constant prosa.analysis.definitions.delay_propagation.job_mapping_uniq
Declared in library prosa.analysis.definitions.delay_propagation, line 103, characters 13-29
@job_mapping_uniq
     : forall Job1 Job2 : JobType,
       arrival_sequence Job1 -> (Equality.sort Job1 -> seq (Equality.sort Job2)) -> Prop
```

Body:

```coq
job_mapping_uniq =
fun (Job1 Job2 : JobType) (arr_seq1 : arrival_sequence Job1)
  (job2_of : Equality.sort Job1 -> seq (Equality.sort Job2)) =>
forall j1 : Equality.sort Job1, @arrives_in Job1 arr_seq1 j1 -> is_true (@uniq Job2 (job2_of j1))
     : forall {Job1 Job2 : JobType},
       arrival_sequence Job1 -> (Equality.sort Job1 -> seq (Equality.sort Job2)) -> Prop

Arguments job_mapping_uniq {Job1 Job2} arr_seq1 job2_of%function_scope
```

## Lean

```lean
@Prosa.Analysis.Definitions.DelayPropagation.job_mapping_uniq : {Job1 : Prosa.Behavior.Job.JobType} →
  {Job2 : Prosa.Behavior.Job.JobType} →
    [inst : DecidableEq Job1] →
      [DecidableEq Job2] → Prosa.Behavior.Arrival_sequence.arrival_sequence Job1 → (Job1 → List Job2) → Prop
def Prosa.Analysis.Definitions.DelayPropagation.job_mapping_uniq.{u_1, u_2} : {Job1 : Prosa.Behavior.Job.JobType} →
  {Job2 : Prosa.Behavior.Job.JobType} →
    [inst : DecidableEq Job1] →
      [DecidableEq Job2] → Prosa.Behavior.Arrival_sequence.arrival_sequence Job1 → (Job1 → List Job2) → Prop :=
fun {Job1} {Job2} [DecidableEq Job1] [DecidableEq Job2] arr_seq1 job2_of =>
  ∀ (j1 : Job1), Prosa.Behavior.Arrival_sequence.arrives_in arr_seq1 j1 → (job2_of j1).Nodup
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Definitions_DelayPropagation_job_mapping_uniq
     : forall (Job1 Job2 : Prosa_Behavior_Job_JobType)
         (inst_4 : 
          DecidableEq Job1),
       DecidableEq Job2 ->
       Prosa_Behavior_Arrival_sequence_arrival_sequence Job1
         inst_4 ->
       (Job1 -> List Job2) -> SProp
```

Body:

```coq
Prosa_Analysis_Definitions_DelayPropagation_job_mapping_uniq@{u_1 u_2 Lean.u_1+1.0 Lean.u_2+1.0 Lean.u_1+2.0
Lean.u_2+2.0} =
fun (Job1 Job2 : Prosa_Behavior_Job_JobType)
  (inst_4 : DecidableEq Job1)
  (_ : DecidableEq Job2)
  (arr_seq1 : Prosa_Behavior_Arrival_sequence_arrival_sequence Job1
                inst_4)
  (job2_of : Job1 -> List Job2) =>
forall j1 : Job1,
Prosa_Behavior_Arrival_sequence_arrives_in Job1
  inst_4 arr_seq1 j1 ->
List_Nodup Job2 (job2_of j1)
     : forall (Job1 Job2 : Prosa_Behavior_Job_JobType)
         (inst_4 : 
          DecidableEq Job1),
       DecidableEq Job2 ->
       Prosa_Behavior_Arrival_sequence_arrival_sequence Job1
         inst_4 ->
       (Job1 -> List Job2) -> SProp

Arguments Prosa_Analysis_Definitions_DelayPropagation_job_mapping_uniq Job1 Job2
  inst_4
  inst_7 
  arr_seq1 job2_of%_function_scope
```
