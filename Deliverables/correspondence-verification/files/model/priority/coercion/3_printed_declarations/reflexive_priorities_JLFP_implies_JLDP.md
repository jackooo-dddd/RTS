# `reflexive_priorities_JLFP_implies_JLDP`

- Kind (Rocq): Lemma
- Rocq: `prosa.model.priority.coercion.reflexive_priorities_JLFP_implies_JLDP`
- Lean: `Prosa.Model.Priority.Coercion.reflexive_priorities_JLFP_implies_JLDP`
- Certificate: `reflexive_priorities_JLFP_implies_JLDP_correspondence`

## Official Rocq

```coq
reflexive_priorities_JLFP_implies_JLDP :
forall {Job : JobType} (jlfp : JLFP_policy Job),
@reflexive_job_priorities Job jlfp -> @reflexive_priorities Job (@JLFP_to_JLDP Job jlfp)

reflexive_priorities_JLFP_implies_JLDP is not universe polymorphic
Arguments reflexive_priorities_JLFP_implies_JLDP {Job} jlfp _ t x
reflexive_priorities_JLFP_implies_JLDP is opaque
Expands to: Constant prosa.model.priority.coercion.reflexive_priorities_JLFP_implies_JLDP
Declared in library prosa.model.priority.coercion, line 88, characters 8-46
@reflexive_priorities_JLFP_implies_JLDP
     : forall (Job : JobType) (jlfp : JLFP_policy Job),
       @reflexive_job_priorities Job jlfp -> @reflexive_priorities Job (@JLFP_to_JLDP Job jlfp)
```

## Lean

```lean
@Prosa.Model.Priority.Coercion.reflexive_priorities_JLFP_implies_JLDP : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] (jlfp : Prosa.Model.Priority.Definitions.JLFP_policy Job),
  Prosa.Model.Priority.Definitions.reflexive_job_priorities jlfp →
    Prosa.Model.Priority.Definitions.reflexive_priorities Prosa.Model.Priority.Coercion.JLFP_to_JLDP
```

## Lean, imported into Rocq

```coq
Prosa_Model_Priority_Coercion_reflexive_priorities_JLFP_implies_JLDP
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (jlfp : Prosa_Model_Priority_Definitions_JLFP_policy Job
                   inst_3),
       Prosa_Model_Priority_Definitions_reflexive_job_priorities Job
         inst_3 jlfp ->
       Prosa_Model_Priority_Definitions_reflexive_priorities Job
         inst_3
         (Prosa_Model_Priority_Coercion_JLFP_to_JLDP Job
            inst_3 jlfp)
```
