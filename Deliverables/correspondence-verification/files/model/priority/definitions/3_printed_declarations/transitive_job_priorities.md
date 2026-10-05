# `transitive_job_priorities`

- Kind (Rocq): Definition
- Rocq: `prosa.model.priority.definitions.transitive_job_priorities`
- Lean: `Prosa.Model.Priority.Definitions.transitive_job_priorities`
- Certificate: `pd_transitive_job_priorities_certificate`

## Official Rocq

```coq
transitive_job_priorities : forall {Job : JobType}, JLFP_policy Job -> Prop

transitive_job_priorities is not universe polymorphic
Arguments transitive_job_priorities {Job} JLFP
transitive_job_priorities is transparent
Expands to: Constant prosa.model.priority.definitions.transitive_job_priorities
Declared in library prosa.model.priority.definitions, line 88, characters 15-40
@transitive_job_priorities
     : forall Job : JobType, JLFP_policy Job -> Prop
```

Body:

```coq
transitive_job_priorities =
fun (Job : JobType) (JLFP : JLFP_policy Job) => @transitive (Equality.sort Job) (@hep_job Job JLFP)
     : forall {Job : JobType}, JLFP_policy Job -> Prop

Arguments transitive_job_priorities {Job} JLFP
```

## Lean

```lean
@Prosa.Model.Priority.Definitions.transitive_job_priorities : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] → Prosa.Model.Priority.Definitions.JLFP_policy Job → Prop
def Prosa.Model.Priority.Definitions.transitive_job_priorities.{u_1} : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] → Prosa.Model.Priority.Definitions.JLFP_policy Job → Prop :=
fun {Job} [DecidableEq Job] JLFP =>
  ∀ (y x z : Job),
    Prosa.Model.Priority.Definitions.hep_job x y = true →
      Prosa.Model.Priority.Definitions.hep_job y z = true → Prosa.Model.Priority.Definitions.hep_job x z = true
```

## Lean, imported into Rocq

```coq
Prosa_Model_Priority_Definitions_transitive_job_priorities
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job),
       Prosa_Model_Priority_Definitions_JLFP_policy Job
         inst_3 ->
       SProp
```

Body:

```coq
Prosa_Model_Priority_Definitions_transitive_job_priorities@{u_1 Lean.u_1+1.0 Lean.u_1+2.0} =
fun (Job : Prosa_Behavior_Job_JobType)
  (inst_3 : DecidableEq Job)
  (JLFP : Prosa_Model_Priority_Definitions_JLFP_policy Job
            inst_3) =>
forall y x z : Job,
@eq Bool
  (Prosa_Model_Priority_Definitions_JLFP_policy_hep_job Job
     inst_3 JLFP x y)
  Bool_true ->
@eq Bool
  (Prosa_Model_Priority_Definitions_JLFP_policy_hep_job Job
     inst_3 JLFP y z)
  Bool_true ->
@eq Bool
  (Prosa_Model_Priority_Definitions_JLFP_policy_hep_job Job
     inst_3 JLFP x z)
  Bool_true
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job),
       Prosa_Model_Priority_Definitions_JLFP_policy Job
         inst_3 ->
       SProp

Arguments Prosa_Model_Priority_Definitions_transitive_job_priorities Job
  inst_3 JLFP
```
