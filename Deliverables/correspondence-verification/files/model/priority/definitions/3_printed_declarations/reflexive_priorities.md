# `reflexive_priorities`

- Kind (Rocq): Definition
- Rocq: `prosa.model.priority.definitions.reflexive_priorities`
- Lean: `Prosa.Model.Priority.Definitions.reflexive_priorities`
- Certificate: `pd_reflexive_priorities_certificate`

## Official Rocq

```coq
reflexive_priorities : forall {Job : JobType}, JLDP_policy Job -> Prop

reflexive_priorities is not universe polymorphic
Arguments reflexive_priorities {Job} JLDP
reflexive_priorities is transparent
Expands to: Constant prosa.model.priority.definitions.reflexive_priorities
Declared in library prosa.model.priority.definitions, line 63, characters 15-35
@reflexive_priorities
     : forall Job : JobType, JLDP_policy Job -> Prop
```

Body:

```coq
reflexive_priorities =
fun (Job : JobType) (JLDP : JLDP_policy Job) =>
forall t : instant, @reflexive (Equality.sort Job) (@hep_job_at Job JLDP t)
     : forall {Job : JobType}, JLDP_policy Job -> Prop

Arguments reflexive_priorities {Job} JLDP
```

## Lean

```lean
@Prosa.Model.Priority.Definitions.reflexive_priorities : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] → Prosa.Model.Priority.Definitions.JLDP_policy Job → Prop
def Prosa.Model.Priority.Definitions.reflexive_priorities.{u_1} : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] → Prosa.Model.Priority.Definitions.JLDP_policy Job → Prop :=
fun {Job} [DecidableEq Job] JLDP =>
  ∀ (t : Prosa.Behavior.Time.instant) (j : Job), Prosa.Model.Priority.Definitions.hep_job_at t j j = true
```

## Lean, imported into Rocq

```coq
Prosa_Model_Priority_Definitions_reflexive_priorities
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job),
       Prosa_Model_Priority_Definitions_JLDP_policy Job
         inst_3 ->
       SProp
```

Body:

```coq
Prosa_Model_Priority_Definitions_reflexive_priorities@{u_1 Lean.u_1+1.0 Lean.u_1+2.0} =
fun (Job : Prosa_Behavior_Job_JobType)
  (inst_3 : DecidableEq Job)
  (JLDP : Prosa_Model_Priority_Definitions_JLDP_policy Job
            inst_3) =>
forall (t : Prosa_Behavior_Time_instant) (j : Job),
@eq Bool
  (Prosa_Model_Priority_Definitions_JLDP_policy_hep_job_at Job
     inst_3 JLDP t j j)
  Bool_true
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job),
       Prosa_Model_Priority_Definitions_JLDP_policy Job
         inst_3 ->
       SProp

Arguments Prosa_Model_Priority_Definitions_reflexive_priorities Job
  inst_3 JLDP
```
