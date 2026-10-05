# `release_sequence`

- Kind (Rocq): Definition
- Rocq: `prosa.analysis.definitions.delay_propagation.release_sequence`
- Lean: `Prosa.Analysis.Definitions.DelayPropagation.release_sequence`
- Certificate: `release_sequence_correspondence`

## Official Rocq

```coq
release_sequence :
forall {Job : JobType},
JobArrival Job -> JobJitter Job -> arrival_sequence Job -> instant -> seq (Equality.sort Job)

release_sequence is not universe polymorphic
Arguments release_sequence {Job original_arrival H2} arr_seq t
release_sequence is transparent
Expands to: Constant prosa.analysis.definitions.delay_propagation.release_sequence
Declared in library prosa.analysis.definitions.delay_propagation, line 185, characters 13-29
@release_sequence
     : forall Job : JobType,
       JobArrival Job -> JobJitter Job -> arrival_sequence Job -> instant -> seq (Equality.sort Job)
```

Body:

```coq
release_sequence =
fun (Job : JobType) (original_arrival : JobArrival Job) (H2 : JobJitter Job) (arr_seq : arrival_sequence Job) =>
@propagated_arrival_sequence Job Job original_arrival id arr_seq ((@cons (Equality.sort Job))^~ [::])
  (@job_jitter Job H2)
     : forall {Job : JobType},
       JobArrival Job -> JobJitter Job -> arrival_sequence Job -> instant -> seq (Equality.sort Job)

Arguments release_sequence {Job original_arrival H2} arr_seq t
```

## Lean

```lean
@Prosa.Analysis.Definitions.DelayPropagation.release_sequence : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    Prosa.Behavior.Job.JobArrival Job →
      [Prosa.Model.Readiness.Jitter.JobJitter Job] →
        Prosa.Behavior.Arrival_sequence.arrival_sequence Job → Prosa.Behavior.Time.instant → List Job
def Prosa.Analysis.Definitions.DelayPropagation.release_sequence.{u_1} : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    Prosa.Behavior.Job.JobArrival Job →
      [Prosa.Model.Readiness.Jitter.JobJitter Job] →
        Prosa.Behavior.Arrival_sequence.arrival_sequence Job → Prosa.Behavior.Time.instant → List Job :=
fun {Job} [DecidableEq Job] original_arrival [Prosa.Model.Readiness.Jitter.JobJitter Job] arr_seq =>
  Prosa.Analysis.Definitions.DelayPropagation.propagated_arrival_sequence original_arrival id arr_seq (fun j => [j])
    Prosa.Model.Readiness.Jitter.job_jitter
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Definitions_DelayPropagation_release_sequence
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job),
       Prosa_Behavior_Job_JobArrival Job
         inst_3 ->
       Prosa_Model_Readiness_Jitter_JobJitter Job
         inst_3 ->
       Prosa_Behavior_Arrival_sequence_arrival_sequence Job
         inst_3 ->
       Prosa_Behavior_Time_instant -> List Job
```

Body:

```coq
Prosa_Analysis_Definitions_DelayPropagation_release_sequence@{u_1 Lean.u_1+1.0 Lean.u_1+2.0} =
fun (Job : Prosa_Behavior_Job_JobType)
  (inst_3 : DecidableEq Job)
  (original_arrival : Prosa_Behavior_Job_JobArrival Job
                        inst_3)
  (inst_8 : 
   Prosa_Model_Readiness_Jitter_JobJitter Job
     inst_3)
  (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
               inst_3) =>
Prosa_Analysis_Definitions_DelayPropagation_propagated_arrival_sequence Job Job
  inst_3
  inst_3 original_arrival 
  (id Job) arr_seq (fun j : Job => List_cons Job j (List_nil Job))
  (Prosa_Model_Readiness_Jitter_JobJitter_job_jitter Job
     inst_3
     inst_8)
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job),
       Prosa_Behavior_Job_JobArrival Job
         inst_3 ->
       Prosa_Model_Readiness_Jitter_JobJitter Job
         inst_3 ->
       Prosa_Behavior_Arrival_sequence_arrival_sequence Job
         inst_3 ->
       Prosa_Behavior_Time_instant -> List Job

Arguments Prosa_Analysis_Definitions_DelayPropagation_release_sequence Job
  inst_3 
  original_arrival inst_8 
  arr_seq a____at____internal__hyg0
```
