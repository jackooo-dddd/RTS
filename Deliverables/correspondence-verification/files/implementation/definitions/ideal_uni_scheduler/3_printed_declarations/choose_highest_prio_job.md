# `choose_highest_prio_job`

- Kind (Rocq): Definition
- Rocq: `prosa.implementation.definitions.ideal_uni_scheduler.choose_highest_prio_job`
- Lean: `Prosa.Implementation.Definitions.IdealUniScheduler.choose_highest_prio_job`
- Certificate: `choose_highest_prio_job_correspondence`

## Official Rocq

```coq
choose_highest_prio_job :
forall {Job : JobType}, JLDP_policy Job -> instant -> seq (Equality.sort Job) -> option (Equality.sort Job)

choose_highest_prio_job is not universe polymorphic
Arguments choose_highest_prio_job {Job H0} t jobs%seq_scope
choose_highest_prio_job is transparent
Expands to: Constant prosa.implementation.definitions.ideal_uni_scheduler.choose_highest_prio_job
Declared in library prosa.implementation.definitions.ideal_uni_scheduler, line 93, characters 15-38
@choose_highest_prio_job
     : forall Job : JobType,
       JLDP_policy Job -> instant -> seq (Equality.sort Job) -> option (Equality.sort Job)
```

Body:

```coq
choose_highest_prio_job =
fun (Job : JobType) (H0 : JLDP_policy Job) (t : instant) => [eta @supremum Job (@hep_job_at Job H0 t)]
     : forall {Job : JobType},
       JLDP_policy Job -> instant -> seq (Equality.sort Job) -> option (Equality.sort Job)

Arguments choose_highest_prio_job {Job H0} t jobs%seq_scope
```

## Lean

```lean
@Prosa.Implementation.Definitions.IdealUniScheduler.choose_highest_prio_job : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    [Prosa.Model.Priority.Definitions.JLDP_policy Job] → Prosa.Behavior.Time.instant → List Job → Option Job
```

Body:

```lean
def Prosa.Implementation.Definitions.IdealUniScheduler.choose_highest_prio_job.{u_1} : {Job :
    Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    [Prosa.Model.Priority.Definitions.JLDP_policy Job] → Prosa.Behavior.Time.instant → List Job → Option Job :=
fun {Job} [DecidableEq Job] [Prosa.Model.Priority.Definitions.JLDP_policy Job] t jobs =>
  Prosa.Util.Supremum.supremum (Prosa.Model.Priority.Definitions.hep_job_at t) jobs
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Definitions_IdealUniScheduler_choose_highest_prio_job
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : 
          DecidableEq Job),
       Prosa_Model_Priority_Definitions_JLDP_policy Job
         inst_3 ->
       Prosa_Behavior_Time_instant -> List Job -> Option Job
```

Body:

```coq
Prosa_Implementation_Definitions_IdealUniScheduler_choose_highest_prio_job@{u_1 Lean.u_1+1.0 Lean.u_1+2.0} =
fun (Job : Prosa_Behavior_Job_JobType)
  (inst_3 : DecidableEq Job)
  (inst_12 : 
   Prosa_Model_Priority_Definitions_JLDP_policy Job
     inst_3)
  (t : Prosa_Behavior_Time_instant) (jobs : List Job) =>
Prosa_Util_Supremum_supremum Job
  (Prosa_Model_Priority_Definitions_JLDP_policy_hep_job_at Job
     inst_3
     inst_12 t)
  jobs
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : 
          DecidableEq Job),
       Prosa_Model_Priority_Definitions_JLDP_policy Job
         inst_3 ->
       Prosa_Behavior_Time_instant -> List Job -> Option Job

Arguments Prosa_Implementation_Definitions_IdealUniScheduler_choose_highest_prio_job 
  Job inst_3
  inst_12 
  t jobs
```
