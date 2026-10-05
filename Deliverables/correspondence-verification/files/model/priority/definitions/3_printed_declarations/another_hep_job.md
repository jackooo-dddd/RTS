# `another_hep_job`

- Kind (Rocq): Definition
- Rocq: `prosa.model.priority.definitions.another_hep_job`
- Lean: `Prosa.Model.Priority.Definitions.another_hep_job`
- Certificate: `pd_another_hep_job_certificate`

## Official Rocq

```coq
another_hep_job : forall {Job : JobType}, JLFP_policy Job -> Equality.sort Job -> Equality.sort Job -> bool

another_hep_job is not universe polymorphic
Arguments another_hep_job {Job H0} j1 j2
another_hep_job is transparent
Expands to: Constant prosa.model.priority.definitions.another_hep_job
Declared in library prosa.model.priority.definitions, line 170, characters 13-28
@another_hep_job
     : forall Job : JobType, JLFP_policy Job -> Equality.sort Job -> Equality.sort Job -> bool
```

Body:

```coq
another_hep_job =
fun (Job : JobType) (H0 : JLFP_policy Job) (j1 j2 : Equality.sort Job) => @hep_job Job H0 j1 j2 && (j1 != j2)
     : forall {Job : JobType}, JLFP_policy Job -> Equality.sort Job -> Equality.sort Job -> bool

Arguments another_hep_job {Job H0} j1 j2
```

## Lean

```lean
@Prosa.Model.Priority.Definitions.another_hep_job : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] → [Prosa.Model.Priority.Definitions.JLFP_policy Job] → Job → Job → Bool
def Prosa.Model.Priority.Definitions.another_hep_job.{u_1} : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] → [Prosa.Model.Priority.Definitions.JLFP_policy Job] → Job → Job → Bool :=
fun {Job} [DecidableEq Job] [Prosa.Model.Priority.Definitions.JLFP_policy Job] j1 j2 =>
  Prosa.Model.Priority.Definitions.hep_job j1 j2 && decide (j1 ≠ j2)
```

## Lean, imported into Rocq

```coq
Prosa_Model_Priority_Definitions_another_hep_job
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job),
       Prosa_Model_Priority_Definitions_JLFP_policy Job
         inst_3 ->
       Job -> Job -> Bool
```

Body:

```coq
Prosa_Model_Priority_Definitions_another_hep_job@{u_1 Lean.u_1+1.0 Lean.u_1+2.0} =
fun (Job : Prosa_Behavior_Job_JobType)
  (inst_3 : DecidableEq Job)
  (inst_6 : Prosa_Model_Priority_Definitions_JLFP_policy
                                                                             Job
                                                                             inst_3)
  (j1 j2 : Job) =>
Bool_and
  (Prosa_Model_Priority_Definitions_JLFP_policy_hep_job Job
     inst_3
     inst_6 j1 j2)
  (Decidable_decide (Ne Job j1 j2)
     (instDecidableNot (@eq Job j1 j2)
        (inst_3 j1 j2)))
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job),
       Prosa_Model_Priority_Definitions_JLFP_policy Job
         inst_3 ->
       Job -> Job -> Bool

Arguments Prosa_Model_Priority_Definitions_another_hep_job Job
  inst_3 self a____at____internal__hyg0
  a____at____internal__hyg0
```
