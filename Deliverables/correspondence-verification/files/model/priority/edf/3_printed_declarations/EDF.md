# `EDF`

- Kind (Rocq): Instance
- Rocq: `prosa.model.priority.edf.EDF`
- Lean: `Prosa.Model.Priority.Edf.EDF`
- Certificate: `EDF_correspondence`

## Official Rocq

```coq
EDF : forall Job : JobType, JobDeadline Job -> JLFP_policy Job

EDF is not universe polymorphic
Arguments EDF Job {H} _ _
EDF is transparent
Expands to: Constant prosa.model.priority.edf.EDF
Declared in library prosa.model.priority.edf, line 9, characters 0-145
EDF
     : forall Job : JobType, JobDeadline Job -> JLFP_policy Job
```

Body:

```coq
EDF =
fun (Job : JobType) (H : JobDeadline Job) (j1 j2 : Equality.sort Job) =>
@job_deadline Job H j1 <= @job_deadline Job H j2
     : forall Job : JobType, JobDeadline Job -> JLFP_policy Job

Arguments EDF Job {H} _ _
```

## Lean

```lean
Prosa.Model.Priority.Edf.EDF : (Job : Prosa.Behavior.Job.JobType) →
  [inst : DecidableEq Job] → [Prosa.Behavior.Job.JobDeadline Job] → Prosa.Model.Priority.Definitions.JLFP_policy Job
```

Body:

```lean
@[instance_reducible] def Prosa.Model.Priority.Edf.EDF.{u_1} : (Job : Prosa.Behavior.Job.JobType) →
  [inst : DecidableEq Job] → [Prosa.Behavior.Job.JobDeadline Job] → Prosa.Model.Priority.Definitions.JLFP_policy Job :=
fun Job [DecidableEq Job] [Prosa.Behavior.Job.JobDeadline Job] =>
  { hep_job := fun j1 j2 => decide (Prosa.Behavior.Job.job_deadline j1 ≤ Prosa.Behavior.Job.job_deadline j2) }
```

## Lean, imported into Rocq

```coq
Prosa_Model_Priority_Edf_EDF
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job),
       Prosa_Behavior_Job_JobDeadline Job inst_3 ->
       Prosa_Model_Priority_Definitions_JLFP_policy Job
         inst_3
```

Body:

```coq
Prosa_Model_Priority_Edf_EDF@{u_1 Lean.u_1+1.0 Lean.u_1+2.0} =
fun (Job : Prosa_Behavior_Job_JobType)
  (inst_3 : DecidableEq Job)
  (inst_6 : Prosa_Behavior_Job_JobDeadline Job
                                                                   inst_3) =>
Prosa_Model_Priority_Definitions_JLFP_policy_mk Job
  inst_3
  (fun j1 j2 : Job =>
   Decidable_decide
     (LE_le_inst1 Prosa_Behavior_Time_instant instLENat
        (Prosa_Behavior_Job_JobDeadline_job_deadline Job
           inst_3
           inst_6 j1)
        (Prosa_Behavior_Job_JobDeadline_job_deadline Job
           inst_3
           inst_6 j2))
     (Nat_decLe
        (Prosa_Behavior_Job_JobDeadline_job_deadline Job
           inst_3
           inst_6 j1)
        (Prosa_Behavior_Job_JobDeadline_job_deadline Job
           inst_3
           inst_6 j2)))
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job),
       Prosa_Behavior_Job_JobDeadline Job inst_3 ->
       Prosa_Model_Priority_Definitions_JLFP_policy Job
         inst_3

Arguments Prosa_Model_Priority_Edf_EDF Job inst_3
  inst_6
```
