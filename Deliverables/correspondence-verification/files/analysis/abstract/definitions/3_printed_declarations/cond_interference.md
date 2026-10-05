# `cond_interference`

- Kind (Rocq): Definition
- Rocq: `prosa.analysis.abstract.definitions.cond_interference`
- Lean: `Prosa.Analysis.Abstract.Definitions.cond_interference`
- Certificate: `cond_interference_correspondence`

## Official Rocq

```coq
cond_interference :
forall {Job : JobType},
Interference Job -> (Equality.sort Job -> instant -> bool) -> Equality.sort Job -> instant -> bool

cond_interference is not universe polymorphic
Arguments cond_interference {Job H2} P%function_scope j t
cond_interference is transparent
Expands to: Constant prosa.analysis.abstract.definitions.cond_interference
Declared in library prosa.analysis.abstract.definitions, line 89, characters 13-30
@cond_interference
     : forall Job : JobType,
       Interference Job -> (Equality.sort Job -> instant -> bool) -> Equality.sort Job -> instant -> bool
```

Body:

```coq
cond_interference =
fun (Job : JobType) (H2 : Interference Job) (P : Equality.sort Job -> instant -> bool)
  (j : Equality.sort Job) (t : instant) =>
P j t && @interference Job H2 j t
     : forall {Job : JobType},
       Interference Job -> (Equality.sort Job -> instant -> bool) -> Equality.sort Job -> instant -> bool

Arguments cond_interference {Job H2} P%function_scope j t
```

## Lean

```lean
@Prosa.Analysis.Abstract.Definitions.cond_interference : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    [Prosa.Analysis.Abstract.Definitions.Interference Job] →
      (Job → Prosa.Behavior.Time.instant → Bool) → Job → Prosa.Behavior.Time.instant → Bool
def Prosa.Analysis.Abstract.Definitions.cond_interference.{u_1} : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    [Prosa.Analysis.Abstract.Definitions.Interference Job] →
      (Job → Prosa.Behavior.Time.instant → Bool) → Job → Prosa.Behavior.Time.instant → Bool :=
fun {Job} [DecidableEq Job] [Prosa.Analysis.Abstract.Definitions.Interference Job] P j t =>
  P j t && Prosa.Analysis.Abstract.Definitions.interference j t
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Abstract_Definitions_cond_interference
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job),
       Prosa_Analysis_Abstract_Definitions_Interference Job
         inst_3 ->
       (Job -> Prosa_Behavior_Time_instant -> Bool) -> Job -> Prosa_Behavior_Time_instant -> Bool
```

Body:

```coq
Prosa_Analysis_Abstract_Definitions_cond_interference@{u_1 Lean.u_1+1.0 Lean.u_1+2.0} =
fun (Job : Prosa_Behavior_Job_JobType)
  (inst_3 : DecidableEq Job)
  (inst_6 : Prosa_Analysis_Abstract_Definitions_Interference
                                                                                Job
                                                                                inst_3)
  (P : Job -> Prosa_Behavior_Time_instant -> Bool) (j : Job) (t : Prosa_Behavior_Time_instant) =>
Bool_and (P j t)
  (Prosa_Analysis_Abstract_Definitions_Interference_interference Job
     inst_3
     inst_6 j t)
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job),
       Prosa_Analysis_Abstract_Definitions_Interference Job
         inst_3 ->
       (Job -> Prosa_Behavior_Time_instant -> Bool) -> Job -> Prosa_Behavior_Time_instant -> Bool

Arguments Prosa_Analysis_Abstract_Definitions_cond_interference Job
  inst_3
  inst_6 P%_function_scope 
  j a____at____internal__hyg0
```
