# `conversion_preserves_equivalence`

- Kind (Rocq): Remark
- Rocq: `prosa.model.preemption.parameter.conversion_preserves_equivalence`
- Lean: `Prosa.Model.Preemption.Parameter.conversion_preserves_equivalence`
- Certificate: `conversion_preserves_equivalence_correspondence`

## Official Rocq

```coq
conversion_preserves_equivalence :
forall {Job : JobType} {H0 : JobCost Job} {H1 : JobPreemptable Job} (j : Equality.sort Job) (ρ : work),
is_true (ρ <= @job_cost Job H0 j) ->
is_true (@job_preemptable Job H1 j ρ) <-> is_true (ρ \in @job_preemption_points Job H0 H1 j)

conversion_preserves_equivalence is not universe polymorphic
Arguments conversion_preserves_equivalence {Job H0 H1} j ρ _
conversion_preserves_equivalence is opaque
Expands to: Constant prosa.model.preemption.parameter.conversion_preserves_equivalence
Declared in library prosa.model.preemption.parameter, line 38, characters 9-41
@conversion_preserves_equivalence
     : forall (Job : JobType) (H0 : JobCost Job) (H1 : JobPreemptable Job) (j : Equality.sort Job) (ρ : work),
       is_true (ρ <= @job_cost Job H0 j) ->
       is_true (@job_preemptable Job H1 j ρ) <-> is_true (ρ \in @job_preemption_points Job H0 H1 j)
```

## Lean

```lean
@Prosa.Model.Preemption.Parameter.conversion_preserves_equivalence : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] [inst_1 : Prosa.Behavior.Job.JobCost Job]
  [inst_2 : Prosa.Model.Preemption.Parameter.JobPreemptable Job] (j : Job),
  ∀ ρ ≤ Prosa.Behavior.Job.job_cost j,
    Prosa.Model.Preemption.Parameter.job_preemptable j ρ = true ↔
      decide (ρ ∈ Prosa.Model.Preemption.Parameter.job_preemption_points j) = true
```

## Lean, imported into Rocq

```coq
Prosa_Model_Preemption_Parameter_conversion_preserves_equivalence
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (inst_6 : 
          Prosa_Behavior_Job_JobCost Job
            inst_3)
         (inst_9 : 
          Prosa_Model_Preemption_Parameter_JobPreemptable Job
            inst_3)
         (j : Job) (_UU03c1_ : Prosa_Behavior_Job_work),
       LE_le_inst1 Prosa_Behavior_Job_work instLENat _UU03c1_
         (Prosa_Behavior_Job_JobCost_job_cost Job
            inst_3
            inst_6 j) ->
       Iff
         (@eq Bool
            (Prosa_Model_Preemption_Parameter_JobPreemptable_job_preemptable Job
               inst_3
               inst_9 j _UU03c1_)
            Bool_true)
         (@eq Bool
            (Decidable_decide
               (Membership_mem_inst3 Prosa_Behavior_Job_work (List_inst1 Prosa_Behavior_Job_work)
                  (List_instMembership_inst1 Prosa_Behavior_Job_work)
                  (Prosa_Model_Preemption_Parameter_job_preemption_points Job
                     inst_3
                     inst_6
                     inst_9 j)
                  _UU03c1_)
               (List_instDecidableMemOfLawfulBEq_inst1 Prosa_Behavior_Job_work
                  (instBEqOfDecidableEq_inst1 Prosa_Behavior_Job_work instDecidableEqNat) Nat_instLawfulBEq
                  _UU03c1_
                  (Prosa_Model_Preemption_Parameter_job_preemption_points Job
                     inst_3
                     inst_6
                     inst_9 j)))
            Bool_true)
```
