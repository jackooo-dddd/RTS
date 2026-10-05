# `always_higher_priority_jlfp`

- Kind (Rocq): Fact
- Rocq: `prosa.analysis.definitions.always_higher_priority.always_higher_priority_jlfp`
- Lean: `Prosa.Analysis.Definitions.AlwaysHigherPriority.always_higher_priority_jlfp`
- Certificate: `always_higher_priority_jlfp_correspondence`

## Official Rocq

```coq
always_higher_priority_jlfp :
forall {Job : JobType} {H : JLFP_policy Job} (j j' : Equality.sort Job),
@always_higher_priority Job (@JLFP_to_JLDP Job H) j j' <->
is_true (@hep_job Job H j j' && ~~ @hep_job Job H j' j)

always_higher_priority_jlfp is not universe polymorphic
Arguments always_higher_priority_jlfp {Job H} j j'
always_higher_priority_jlfp is opaque
Expands to: Constant prosa.analysis.definitions.always_higher_priority.always_higher_priority_jlfp
Declared in library prosa.analysis.definitions.always_higher_priority, line 33, characters 7-34
@always_higher_priority_jlfp
     : forall (Job : JobType) (H : JLFP_policy Job) (j j' : Equality.sort Job),
       @always_higher_priority Job (@JLFP_to_JLDP Job H) j j' <->
       is_true (@hep_job Job H j j' && ~~ @hep_job Job H j' j)
```

## Lean

```lean
@Prosa.Analysis.Definitions.AlwaysHigherPriority.always_higher_priority_jlfp : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] [inst_1 : Prosa.Model.Priority.Definitions.JLFP_policy Job] (j j' : Job),
  Prosa.Analysis.Definitions.AlwaysHigherPriority.always_higher_priority j j' ↔
    (Prosa.Model.Priority.Definitions.hep_job j j' && !Prosa.Model.Priority.Definitions.hep_job j' j) = true
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Definitions_AlwaysHigherPriority_always_higher_priority_jlfp
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : 
          DecidableEq Job)
         (inst_6 : 
          Prosa_Model_Priority_Definitions_JLFP_policy Job
            inst_3)
         (j j' : Job),
       Iff
         (Prosa_Analysis_Definitions_AlwaysHigherPriority_always_higher_priority Job
            inst_3
            (Prosa_Model_Priority_Coercion_JLFP_to_JLDP Job
               inst_3
               inst_6)
            j j')
         (@eq Bool
            (Bool_and
               (Prosa_Model_Priority_Definitions_JLFP_policy_hep_job Job
                  inst_3
                  inst_6 j j')
               (Bool_not
                  (Prosa_Model_Priority_Definitions_JLFP_policy_hep_job Job
                     inst_3
                     inst_6 j'
                     j)))
            Bool_true)
```
