# `JLFP_to_JLDP`

- Kind (Rocq): Instance
- Rocq: `prosa.model.priority.coercion.JLFP_to_JLDP`
- Lean: `Prosa.Model.Priority.Coercion.JLFP_to_JLDP`
- Certificate: `JLFP_to_JLDP_correspondence`

## Official Rocq

```coq
JLFP_to_JLDP : forall {Job : JobType}, JLFP_policy Job -> JLDP_policy Job

JLFP_to_JLDP is not universe polymorphic
Arguments JLFP_to_JLDP {Job} JLFP _ _ _
JLFP_to_JLDP is a coercion
JLFP_to_JLDP is transparent
Expands to: Constant prosa.model.priority.coercion.JLFP_to_JLDP
Declared in library prosa.model.priority.coercion, line 23, characters 0-134
@JLFP_to_JLDP
     : forall Job : JobType, JLFP_policy Job -> JLDP_policy Job
```

Body:

```coq
JLFP_to_JLDP =
fun (Job : JobType) (JLFP : JLFP_policy Job) =>
fun=> (fun j1 : Equality.sort Job => [eta @hep_job Job JLFP j1])
     : forall {Job : JobType}, JLFP_policy Job -> JLDP_policy Job

Arguments JLFP_to_JLDP {Job} JLFP _ _ _
JLFP_to_JLDP is a coercion
```

## Lean

```lean
@Prosa.Model.Priority.Coercion.JLFP_to_JLDP : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    [JLFP : Prosa.Model.Priority.Definitions.JLFP_policy Job] → Prosa.Model.Priority.Definitions.JLDP_policy Job
@[instance_reducible] def Prosa.Model.Priority.Coercion.JLFP_to_JLDP.{u_1} : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    [JLFP : Prosa.Model.Priority.Definitions.JLFP_policy Job] → Prosa.Model.Priority.Definitions.JLDP_policy Job :=
fun {Job} [DecidableEq Job] [Prosa.Model.Priority.Definitions.JLFP_policy Job] =>
  { hep_job_at := fun x j1 j2 => Prosa.Model.Priority.Definitions.hep_job j1 j2 }
```

## Lean, imported into Rocq

```coq
Prosa_Model_Priority_Coercion_JLFP_to_JLDP
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job),
       Prosa_Model_Priority_Definitions_JLFP_policy Job
         inst_3 ->
       Prosa_Model_Priority_Definitions_JLDP_policy Job
         inst_3
```

Body:

```coq
Prosa_Model_Priority_Coercion_JLFP_to_JLDP@{u_1 Lean.u_1+1.0 Lean.u_1+2.0} =
fun (Job : Prosa_Behavior_Job_JobType)
  (inst_3 : DecidableEq Job)
  (JLFP : Prosa_Model_Priority_Definitions_JLFP_policy Job
            inst_3) =>
Prosa_Model_Priority_Definitions_JLDP_policy_mk Job
  inst_3
  (fun (_ : Prosa_Behavior_Time_instant) (j1 j2 : Job) =>
   Prosa_Model_Priority_Definitions_JLFP_policy_hep_job Job
     inst_3 JLFP j1 j2)
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job),
       Prosa_Model_Priority_Definitions_JLFP_policy Job
         inst_3 ->
       Prosa_Model_Priority_Definitions_JLDP_policy Job
         inst_3

Arguments Prosa_Model_Priority_Coercion_JLFP_to_JLDP Job
  inst_3 JLFP
```
