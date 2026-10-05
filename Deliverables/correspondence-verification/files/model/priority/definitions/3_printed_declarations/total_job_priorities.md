# `total_job_priorities`

- Kind (Rocq): Definition
- Rocq: `prosa.model.priority.definitions.total_job_priorities`
- Lean: `Prosa.Model.Priority.Definitions.total_job_priorities`
- Certificate: `pd_total_job_priorities_certificate`

## Official Rocq

```coq
total_job_priorities : forall {Job : JobType}, JLFP_policy Job -> Prop

total_job_priorities is not universe polymorphic
Arguments total_job_priorities {Job} JLFP
total_job_priorities is transparent
Expands to: Constant prosa.model.priority.definitions.total_job_priorities
Declared in library prosa.model.priority.definitions, line 91, characters 15-35
@total_job_priorities
     : forall Job : JobType, JLFP_policy Job -> Prop
```

Body:

```coq
total_job_priorities =
fun (Job : JobType) (JLFP : JLFP_policy Job) => @total (Equality.sort Job) (@hep_job Job JLFP)
     : forall {Job : JobType}, JLFP_policy Job -> Prop

Arguments total_job_priorities {Job} JLFP
```

## Lean

```lean
@Prosa.Model.Priority.Definitions.total_job_priorities : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] → Prosa.Model.Priority.Definitions.JLFP_policy Job → Prop
def Prosa.Model.Priority.Definitions.total_job_priorities.{u_1} : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] → Prosa.Model.Priority.Definitions.JLFP_policy Job → Prop :=
fun {Job} [DecidableEq Job] JLFP =>
  ∀ (x y : Job), (Prosa.Model.Priority.Definitions.hep_job x y || Prosa.Model.Priority.Definitions.hep_job y x) = true
```

## Lean, imported into Rocq

```coq
Prosa_Model_Priority_Definitions_total_job_priorities
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job),
       Prosa_Model_Priority_Definitions_JLFP_policy Job
         inst_3 ->
       SProp
```

Body:

```coq
Prosa_Model_Priority_Definitions_total_job_priorities@{u_1 Lean.u_1+1.0 Lean.u_1+2.0} =
fun (Job : Prosa_Behavior_Job_JobType)
  (inst_3 : DecidableEq Job)
  (JLFP : Prosa_Model_Priority_Definitions_JLFP_policy Job
            inst_3) =>
forall x y : Job,
@eq Bool
  (Bool_or
     (Prosa_Model_Priority_Definitions_JLFP_policy_hep_job Job
        inst_3 JLFP x y)
     (Prosa_Model_Priority_Definitions_JLFP_policy_hep_job Job
        inst_3 JLFP y x))
  Bool_true
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job),
       Prosa_Model_Priority_Definitions_JLFP_policy Job
         inst_3 ->
       SProp

Arguments Prosa_Model_Priority_Definitions_total_job_priorities Job
  inst_3 JLFP
```
