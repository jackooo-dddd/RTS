# `total_priorities`

- Kind (Rocq): Definition
- Rocq: `prosa.model.priority.definitions.total_priorities`
- Lean: `Prosa.Model.Priority.Definitions.total_priorities`
- Certificate: `pd_total_priorities_certificate`

## Official Rocq

```coq
total_priorities : forall {Job : JobType}, JLDP_policy Job -> Prop

total_priorities is not universe polymorphic
Arguments total_priorities {Job} JLDP
total_priorities is transparent
Expands to: Constant prosa.model.priority.definitions.total_priorities
Declared in library prosa.model.priority.definitions, line 71, characters 15-31
@total_priorities
     : forall Job : JobType, JLDP_policy Job -> Prop
```

Body:

```coq
total_priorities =
fun (Job : JobType) (JLDP : JLDP_policy Job) =>
forall t : instant, @total (Equality.sort Job) (@hep_job_at Job JLDP t)
     : forall {Job : JobType}, JLDP_policy Job -> Prop

Arguments total_priorities {Job} JLDP
```

## Lean

```lean
@Prosa.Model.Priority.Definitions.total_priorities : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] → Prosa.Model.Priority.Definitions.JLDP_policy Job → Prop
def Prosa.Model.Priority.Definitions.total_priorities.{u_1} : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] → Prosa.Model.Priority.Definitions.JLDP_policy Job → Prop :=
fun {Job} [DecidableEq Job] JLDP =>
  ∀ (t : Prosa.Behavior.Time.instant) (x y : Job),
    (Prosa.Model.Priority.Definitions.hep_job_at t x y || Prosa.Model.Priority.Definitions.hep_job_at t y x) = true
```

## Lean, imported into Rocq

```coq
Prosa_Model_Priority_Definitions_total_priorities
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job),
       Prosa_Model_Priority_Definitions_JLDP_policy Job
         inst_3 ->
       SProp
```

Body:

```coq
Prosa_Model_Priority_Definitions_total_priorities@{u_1 Lean.u_1+1.0 Lean.u_1+2.0} =
fun (Job : Prosa_Behavior_Job_JobType)
  (inst_3 : DecidableEq Job)
  (JLDP : Prosa_Model_Priority_Definitions_JLDP_policy Job
            inst_3) =>
forall (t : Prosa_Behavior_Time_instant) (x y : Job),
@eq Bool
  (Bool_or
     (Prosa_Model_Priority_Definitions_JLDP_policy_hep_job_at Job
        inst_3 JLDP t x y)
     (Prosa_Model_Priority_Definitions_JLDP_policy_hep_job_at Job
        inst_3 JLDP t y x))
  Bool_true
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job),
       Prosa_Model_Priority_Definitions_JLDP_policy Job
         inst_3 ->
       SProp

Arguments Prosa_Model_Priority_Definitions_total_priorities Job
  inst_3 JLDP
```
