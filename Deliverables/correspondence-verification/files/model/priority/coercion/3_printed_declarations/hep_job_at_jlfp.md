# `hep_job_at_jlfp`

- Kind (Rocq): Remark
- Rocq: `prosa.model.priority.coercion.hep_job_at_jlfp`
- Lean: `Prosa.Model.Priority.Coercion.hep_job_at_jlfp`
- Certificate: `hep_job_at_jlfp_correspondence`

## Official Rocq

```coq
hep_job_at_jlfp :
forall {Job : JobType} {H0 : JLFP_policy Job} (j j' : Equality.sort Job) (t : instant),
@hep_job_at Job (@JLFP_to_JLDP Job H0) t j j' = @hep_job Job H0 j j'

hep_job_at_jlfp is not universe polymorphic
Arguments hep_job_at_jlfp {Job H0} j j' t
hep_job_at_jlfp is opaque
Expands to: Constant prosa.model.priority.coercion.hep_job_at_jlfp
Declared in library prosa.model.priority.coercion, line 50, characters 9-24
@hep_job_at_jlfp
     : forall (Job : JobType) (H0 : JLFP_policy Job) (j j' : Equality.sort Job) (t : instant),
       @hep_job_at Job (@JLFP_to_JLDP Job H0) t j j' = @hep_job Job H0 j j'
```

## Lean

```lean
@Prosa.Model.Priority.Coercion.hep_job_at_jlfp : ∀ {Job : Prosa.Behavior.Job.JobType} [inst : DecidableEq Job]
  [inst_1 : Prosa.Model.Priority.Definitions.JLFP_policy Job] (j j' : Job) (t : Prosa.Behavior.Time.instant),
  Prosa.Model.Priority.Definitions.hep_job_at t j j' = Prosa.Model.Priority.Definitions.hep_job j j'
```

## Lean, imported into Rocq

```coq
Prosa_Model_Priority_Coercion_hep_job_at_jlfp
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (inst_6 : Prosa_Model_Priority_Definitions_JLFP_policy
                                                                                Job
                                                                                inst_3)
         (j j' : Job) (t : Prosa_Behavior_Time_instant),
       @eq Bool
         (Prosa_Model_Priority_Definitions_JLDP_policy_hep_job_at Job
            inst_3
            (Prosa_Model_Priority_Coercion_JLFP_to_JLDP Job
               inst_3
               inst_6)
            t j j')
         (Prosa_Model_Priority_Definitions_JLFP_policy_hep_job Job
            inst_3
            inst_6 j j')
```
