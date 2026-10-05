# `transitive_priorities`

- Kind (Rocq): Definition
- Rocq: `prosa.model.priority.definitions.transitive_priorities`
- Lean: `Prosa.Model.Priority.Definitions.transitive_priorities`
- Certificate: `pd_transitive_priorities_certificate`

## Official Rocq

```coq
transitive_priorities : forall {Job : JobType}, JLDP_policy Job -> Prop

transitive_priorities is not universe polymorphic
Arguments transitive_priorities {Job} JLDP
transitive_priorities is transparent
Expands to: Constant prosa.model.priority.definitions.transitive_priorities
Declared in library prosa.model.priority.definitions, line 67, characters 15-36
@transitive_priorities
     : forall Job : JobType, JLDP_policy Job -> Prop
```

Body:

```coq
transitive_priorities =
fun (Job : JobType) (JLDP : JLDP_policy Job) =>
forall t : instant, @transitive (Equality.sort Job) (@hep_job_at Job JLDP t)
     : forall {Job : JobType}, JLDP_policy Job -> Prop

Arguments transitive_priorities {Job} JLDP
```

## Lean

```lean
@Prosa.Model.Priority.Definitions.transitive_priorities : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] → Prosa.Model.Priority.Definitions.JLDP_policy Job → Prop
def Prosa.Model.Priority.Definitions.transitive_priorities.{u_1} : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] → Prosa.Model.Priority.Definitions.JLDP_policy Job → Prop :=
fun {Job} [DecidableEq Job] JLDP =>
  ∀ (t : Prosa.Behavior.Time.instant) (y x z : Job),
    Prosa.Model.Priority.Definitions.hep_job_at t x y = true →
      Prosa.Model.Priority.Definitions.hep_job_at t y z = true →
        Prosa.Model.Priority.Definitions.hep_job_at t x z = true
```

## Lean, imported into Rocq

```coq
Prosa_Model_Priority_Definitions_transitive_priorities
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job),
       Prosa_Model_Priority_Definitions_JLDP_policy Job
         inst_3 ->
       SProp
```

Body:

```coq
Prosa_Model_Priority_Definitions_transitive_priorities@{u_1 Lean.u_1+1.0 Lean.u_1+2.0} =
fun (Job : Prosa_Behavior_Job_JobType)
  (inst_3 : DecidableEq Job)
  (JLDP : Prosa_Model_Priority_Definitions_JLDP_policy Job
            inst_3) =>
forall (t : Prosa_Behavior_Time_instant) (y x z : Job),
@eq Bool
  (Prosa_Model_Priority_Definitions_JLDP_policy_hep_job_at Job
     inst_3 JLDP t x y)
  Bool_true ->
@eq Bool
  (Prosa_Model_Priority_Definitions_JLDP_policy_hep_job_at Job
     inst_3 JLDP t y z)
  Bool_true ->
@eq Bool
  (Prosa_Model_Priority_Definitions_JLDP_policy_hep_job_at Job
     inst_3 JLDP t x z)
  Bool_true
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job),
       Prosa_Model_Priority_Definitions_JLDP_policy Job
         inst_3 ->
       SProp

Arguments Prosa_Model_Priority_Definitions_transitive_priorities Job
  inst_3 JLDP
```
