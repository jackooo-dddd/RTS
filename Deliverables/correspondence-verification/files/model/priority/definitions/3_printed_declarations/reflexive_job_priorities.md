# `reflexive_job_priorities`

- Kind (Rocq): Definition
- Rocq: `prosa.model.priority.definitions.reflexive_job_priorities`
- Lean: `Prosa.Model.Priority.Definitions.reflexive_job_priorities`
- Certificate: `pd_reflexive_job_priorities_certificate`

## Official Rocq

```coq
reflexive_job_priorities : forall {Job : JobType}, JLFP_policy Job -> Prop

reflexive_job_priorities is not universe polymorphic
Arguments reflexive_job_priorities {Job} JLFP
reflexive_job_priorities is transparent
Expands to: Constant prosa.model.priority.definitions.reflexive_job_priorities
Declared in library prosa.model.priority.definitions, line 85, characters 15-39
@reflexive_job_priorities
     : forall Job : JobType, JLFP_policy Job -> Prop
```

Body:

```coq
reflexive_job_priorities =
fun (Job : JobType) (JLFP : JLFP_policy Job) => @reflexive (Equality.sort Job) (@hep_job Job JLFP)
     : forall {Job : JobType}, JLFP_policy Job -> Prop

Arguments reflexive_job_priorities {Job} JLFP
```

## Lean

```lean
@Prosa.Model.Priority.Definitions.reflexive_job_priorities : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] → Prosa.Model.Priority.Definitions.JLFP_policy Job → Prop
def Prosa.Model.Priority.Definitions.reflexive_job_priorities.{u_1} : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] → Prosa.Model.Priority.Definitions.JLFP_policy Job → Prop :=
fun {Job} [DecidableEq Job] JLFP => ∀ (j : Job), Prosa.Model.Priority.Definitions.hep_job j j = true
```

## Lean, imported into Rocq

```coq
Prosa_Model_Priority_Definitions_reflexive_job_priorities
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job),
       Prosa_Model_Priority_Definitions_JLFP_policy Job
         inst_3 ->
       SProp
```

Body:

```coq
Prosa_Model_Priority_Definitions_reflexive_job_priorities@{u_1 Lean.u_1+1.0 Lean.u_1+2.0} =
fun (Job : Prosa_Behavior_Job_JobType)
  (inst_3 : DecidableEq Job)
  (JLFP : Prosa_Model_Priority_Definitions_JLFP_policy Job
            inst_3) =>
forall j : Job,
@eq Bool
  (Prosa_Model_Priority_Definitions_JLFP_policy_hep_job Job
     inst_3 JLFP j j)
  Bool_true
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job),
       Prosa_Model_Priority_Definitions_JLFP_policy Job
         inst_3 ->
       SProp

Arguments Prosa_Model_Priority_Definitions_reflexive_job_priorities Job
  inst_3 JLFP
```
