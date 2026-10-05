# `transitive_priorities_JLFP_implies_JLDP`

- Kind (Rocq): Lemma
- Rocq: `prosa.model.priority.coercion.transitive_priorities_JLFP_implies_JLDP`
- Lean: `Prosa.Model.Priority.Coercion.transitive_priorities_JLFP_implies_JLDP`
- Certificate: `transitive_priorities_JLFP_implies_JLDP_correspondence`

## Official Rocq

```coq
transitive_priorities_JLFP_implies_JLDP :
forall {Job : JobType} (jlfp : JLFP_policy Job),
@transitive_job_priorities Job jlfp -> @transitive_priorities Job (@JLFP_to_JLDP Job jlfp)

transitive_priorities_JLFP_implies_JLDP is not universe polymorphic
Arguments transitive_priorities_JLFP_implies_JLDP {Job} jlfp _ t y x z _ _
transitive_priorities_JLFP_implies_JLDP is opaque
Expands to: Constant prosa.model.priority.coercion.transitive_priorities_JLFP_implies_JLDP
Declared in library prosa.model.priority.coercion, line 95, characters 8-47
@transitive_priorities_JLFP_implies_JLDP
     : forall (Job : JobType) (jlfp : JLFP_policy Job),
       @transitive_job_priorities Job jlfp -> @transitive_priorities Job (@JLFP_to_JLDP Job jlfp)
```

## Lean

```lean
@Prosa.Model.Priority.Coercion.transitive_priorities_JLFP_implies_JLDP : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] (jlfp : Prosa.Model.Priority.Definitions.JLFP_policy Job),
  Prosa.Model.Priority.Definitions.transitive_job_priorities jlfp →
    Prosa.Model.Priority.Definitions.transitive_priorities Prosa.Model.Priority.Coercion.JLFP_to_JLDP
```

## Lean, imported into Rocq

```coq
Prosa_Model_Priority_Coercion_transitive_priorities_JLFP_implies_JLDP
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (jlfp : Prosa_Model_Priority_Definitions_JLFP_policy Job
                   inst_3),
       Prosa_Model_Priority_Definitions_transitive_job_priorities Job
         inst_3 jlfp ->
       Prosa_Model_Priority_Definitions_transitive_priorities Job
         inst_3
         (Prosa_Model_Priority_Coercion_JLFP_to_JLDP Job
            inst_3 jlfp)
```
