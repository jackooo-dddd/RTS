# `total_priorities_JLFP_implies_JLDP`

- Kind (Rocq): Lemma
- Rocq: `prosa.model.priority.coercion.total_priorities_JLFP_implies_JLDP`
- Lean: `Prosa.Model.Priority.Coercion.total_priorities_JLFP_implies_JLDP`
- Certificate: `total_priorities_JLFP_implies_JLDP_correspondence`

## Official Rocq

```coq
total_priorities_JLFP_implies_JLDP :
forall {Job : JobType} (jlfp : JLFP_policy Job),
@total_job_priorities Job jlfp -> @total_priorities Job (@JLFP_to_JLDP Job jlfp)

total_priorities_JLFP_implies_JLDP is not universe polymorphic
Arguments total_priorities_JLFP_implies_JLDP {Job} jlfp _ t x y
total_priorities_JLFP_implies_JLDP is opaque
Expands to: Constant prosa.model.priority.coercion.total_priorities_JLFP_implies_JLDP
Declared in library prosa.model.priority.coercion, line 102, characters 8-42
@total_priorities_JLFP_implies_JLDP
     : forall (Job : JobType) (jlfp : JLFP_policy Job),
       @total_job_priorities Job jlfp -> @total_priorities Job (@JLFP_to_JLDP Job jlfp)
```

## Lean

```lean
@Prosa.Model.Priority.Coercion.total_priorities_JLFP_implies_JLDP : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] (jlfp : Prosa.Model.Priority.Definitions.JLFP_policy Job),
  Prosa.Model.Priority.Definitions.total_job_priorities jlfp →
    Prosa.Model.Priority.Definitions.total_priorities Prosa.Model.Priority.Coercion.JLFP_to_JLDP
```

## Lean, imported into Rocq

```coq
Prosa_Model_Priority_Coercion_total_priorities_JLFP_implies_JLDP
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (jlfp : Prosa_Model_Priority_Definitions_JLFP_policy Job
                   inst_3),
       Prosa_Model_Priority_Definitions_total_job_priorities Job
         inst_3 jlfp ->
       Prosa_Model_Priority_Definitions_total_priorities Job
         inst_3
         (Prosa_Model_Priority_Coercion_JLFP_to_JLDP Job
            inst_3 jlfp)
```
