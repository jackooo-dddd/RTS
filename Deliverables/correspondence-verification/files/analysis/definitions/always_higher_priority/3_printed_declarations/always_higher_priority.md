# `always_higher_priority`

- Kind (Rocq): Definition
- Rocq: `prosa.analysis.definitions.always_higher_priority.always_higher_priority`
- Lean: `Prosa.Analysis.Definitions.AlwaysHigherPriority.always_higher_priority`
- Certificate: `always_higher_priority_correspondence`

## Official Rocq

```coq
always_higher_priority :
forall {Job : JobType}, JLDP_policy Job -> Equality.sort Job -> Equality.sort Job -> Prop

always_higher_priority is not universe polymorphic
Arguments always_higher_priority {Job H} j1 j2
always_higher_priority is transparent
Expands to: Constant prosa.analysis.definitions.always_higher_priority.always_higher_priority
Declared in library prosa.analysis.definitions.always_higher_priority, line 17, characters 13-35
@always_higher_priority
     : forall Job : JobType, JLDP_policy Job -> Equality.sort Job -> Equality.sort Job -> Prop
```

Body:

```coq
always_higher_priority =
fun (Job : JobType) (H : JLDP_policy Job) (j1 j2 : Equality.sort Job) =>
forall t : instant, is_true (@hep_job_at Job H t j1 j2 && ~~ @hep_job_at Job H t j2 j1)
     : forall {Job : JobType}, JLDP_policy Job -> Equality.sort Job -> Equality.sort Job -> Prop

Arguments always_higher_priority {Job H} j1 j2
```

## Lean

```lean
@Prosa.Analysis.Definitions.AlwaysHigherPriority.always_higher_priority : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] → [Prosa.Model.Priority.Definitions.JLDP_policy Job] → Job → Job → Prop
```

Body:

```lean
def Prosa.Analysis.Definitions.AlwaysHigherPriority.always_higher_priority.{u_1} : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] → [Prosa.Model.Priority.Definitions.JLDP_policy Job] → Job → Job → Prop :=
fun {Job} [DecidableEq Job] [Prosa.Model.Priority.Definitions.JLDP_policy Job] j1 j2 =>
  ∀ (t : Prosa.Behavior.Time.instant),
    (Prosa.Model.Priority.Definitions.hep_job_at t j1 j2 && !Prosa.Model.Priority.Definitions.hep_job_at t j2 j1) = true
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Definitions_AlwaysHigherPriority_always_higher_priority
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : 
          DecidableEq Job),
       Prosa_Model_Priority_Definitions_JLDP_policy Job
         inst_3 ->
       Job -> Job -> SProp
```

Body:

```coq
Prosa_Analysis_Definitions_AlwaysHigherPriority_always_higher_priority@{u_1 Lean.u_1+1.0 Lean.u_1+2.0} =
fun (Job : Prosa_Behavior_Job_JobType)
  (inst_3 : DecidableEq Job)
  (inst_6 : 
   Prosa_Model_Priority_Definitions_JLDP_policy Job
     inst_3)
  (j1 j2 : Job) =>
forall t : Prosa_Behavior_Time_instant,
@eq Bool
  (Bool_and
     (Prosa_Model_Priority_Definitions_JLDP_policy_hep_job_at Job
        inst_3
        inst_6 t j1 j2)
     (Bool_not
        (Prosa_Model_Priority_Definitions_JLDP_policy_hep_job_at Job
           inst_3
           inst_6 t j2 j1)))
  Bool_true
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : 
          DecidableEq Job),
       Prosa_Model_Priority_Definitions_JLDP_policy Job
         inst_3 ->
       Job -> Job -> SProp

Arguments Prosa_Analysis_Definitions_AlwaysHigherPriority_always_higher_priority 
  Job inst_3
  inst_6 
  j1 j2
```
