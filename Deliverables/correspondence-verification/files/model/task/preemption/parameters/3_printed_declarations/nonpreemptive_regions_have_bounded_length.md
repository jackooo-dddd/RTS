# `nonpreemptive_regions_have_bounded_length`

- Kind (Rocq): Definition
- Rocq: `prosa.model.task.preemption.parameters.nonpreemptive_regions_have_bounded_length`
- Lean: `Prosa.Model.Task.Preemption.Parameters.nonpreemptive_regions_have_bounded_length`
- Certificate: `nonpreemptive_regions_have_bounded_length_correspondence`

## Official Rocq

```coq
nonpreemptive_regions_have_bounded_length :
forall {Job : JobType}, JobCost Job -> JobPreemptable Job -> Equality.sort Job -> Prop

nonpreemptive_regions_have_bounded_length is not universe polymorphic
Arguments nonpreemptive_regions_have_bounded_length {Job H0 H2} j
nonpreemptive_regions_have_bounded_length is transparent
Expands to: Constant prosa.model.task.preemption.parameters.nonpreemptive_regions_have_bounded_length
Declared in library prosa.model.task.preemption.parameters, line 100, characters 13-54
@nonpreemptive_regions_have_bounded_length
     : forall Job : JobType, JobCost Job -> JobPreemptable Job -> Equality.sort Job -> Prop
```

Body:

```coq
nonpreemptive_regions_have_bounded_length =
fun (Job : JobType) (H0 : JobCost Job) (H2 : JobPreemptable Job) (j : Equality.sort Job) =>
forall ρ : duration,
is_true (0 <= ρ <= @job_cost Job H0 j) ->
exists pp : duration,
  is_true (ρ <= pp <= ρ + (@job_max_nonpreemptive_segment Job H0 H2 j - 1)) /\
  is_true (@job_preemptable Job H2 j pp)
     : forall {Job : JobType}, JobCost Job -> JobPreemptable Job -> Equality.sort Job -> Prop

Arguments nonpreemptive_regions_have_bounded_length {Job H0 H2} j
```

## Lean

```lean
@Prosa.Model.Task.Preemption.Parameters.nonpreemptive_regions_have_bounded_length : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    [Prosa.Behavior.Job.JobCost Job] → [Prosa.Model.Preemption.Parameter.JobPreemptable Job] → Job → Prop
```

Body:

```lean
def Prosa.Model.Task.Preemption.Parameters.nonpreemptive_regions_have_bounded_length.{u_1} : {Job :
    Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    [Prosa.Behavior.Job.JobCost Job] → [Prosa.Model.Preemption.Parameter.JobPreemptable Job] → Job → Prop :=
fun {Job} [DecidableEq Job] [Prosa.Behavior.Job.JobCost Job] [Prosa.Model.Preemption.Parameter.JobPreemptable Job] j =>
  ∀ (ρ : Prosa.Behavior.Time.duration),
    (decide (0 ≤ ρ) && decide (ρ ≤ Prosa.Behavior.Job.job_cost j)) = true →
      ∃ pp,
        (decide (ρ ≤ pp) && decide (pp ≤ ρ + (Prosa.Model.Preemption.Parameter.job_max_nonpreemptive_segment j - 1))) =
            true ∧
          Prosa.Model.Preemption.Parameter.job_preemptable j pp = true
```

## Lean, imported into Rocq

```coq
Prosa_Model_Task_Preemption_Parameters_nonpreemptive_regions_have_bounded_length
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_7 : DecidableEq Job),
       Prosa_Behavior_Job_JobCost Job
         inst_7 ->
       Prosa_Model_Preemption_Parameter_JobPreemptable Job
         inst_7 ->
       Job -> SProp
```

Body:

```coq
Prosa_Model_Task_Preemption_Parameters_nonpreemptive_regions_have_bounded_length@{u_1 Lean.u_1+1.0
Lean.u_1+2.0} =
fun (Job : Prosa_Behavior_Job_JobType)
  (inst_7 : DecidableEq Job)
  (inst_10 : 
   Prosa_Behavior_Job_JobCost Job inst_7)
  (inst_13 : 
   Prosa_Model_Preemption_Parameter_JobPreemptable Job
     inst_7)
  (j : Job) =>
forall _UU03c1_ : Prosa_Behavior_Time_duration,
@eq Bool
  (Bool_and
     (Decidable_decide
        (LE_le_inst1 Prosa_Behavior_Time_duration instLENat
           (OfNat_ofNat_inst1 Prosa_Behavior_Time_duration 0 (instOfNatNat 0)) _UU03c1_)
        (Nat_decLe (OfNat_ofNat_inst1 Prosa_Behavior_Time_duration 0 (instOfNatNat 0)) _UU03c1_))
     (Decidable_decide
        (LE_le_inst1 Prosa_Behavior_Time_duration instLENat _UU03c1_
           (Prosa_Behavior_Job_JobCost_job_cost Job
              inst_7
              inst_10 j))
        (Nat_decLe _UU03c1_
           (Prosa_Behavior_Job_JobCost_job_cost Job
              inst_7
              inst_10 j))))
  Bool_true ->
Exists Prosa_Behavior_Time_duration
  (fun pp : Prosa_Behavior_Time_duration =>
   And
     (@eq Bool
        (Bool_and
           (Decidable_decide (LE_le_inst1 Prosa_Behavior_Time_duration instLENat _UU03c1_ pp)
              (Nat_decLe _UU03c1_ pp))
           (Decidable_decide
              (LE_le_inst1 Prosa_Behavior_Time_duration instLENat pp
                 (HAdd_hAdd_inst7 Prosa_Behavior_Time_duration Nat Prosa_Behavior_Time_duration
                    (instHAdd_inst1 Prosa_Behavior_Time_duration instAddNat) _UU03c1_
                    (HSub_hSub_inst7 Nat Prosa_Behavior_Time_duration Nat (instHSub_inst1 Nat instSubNat)
                       (Prosa_Model_Preemption_Parameter_job_max_nonpreemptive_segment Job
                          inst_7
                          inst_10
                          inst_13 j)
                       (OfNat_ofNat_inst1 Prosa_Behavior_Time_duration 1 (instOfNatNat 1)))))
              (Nat_decLe pp
                 (HAdd_hAdd_inst7 Prosa_Behavior_Time_duration Nat Prosa_Behavior_Time_duration
                    (instHAdd_inst1 Prosa_Behavior_Time_duration instAddNat) _UU03c1_
                    (HSub_hSub_inst7 Nat Prosa_Behavior_Time_duration Nat (instHSub_inst1 Nat instSubNat)
                       (Prosa_Model_Preemption_Parameter_job_max_nonpreemptive_segment Job
                          inst_7
                          inst_10
                          inst_13 j)
                       (OfNat_ofNat_inst1 Prosa_Behavior_Time_duration 1 (instOfNatNat 1)))))))
        Bool_true)
     (@eq Bool
        (Prosa_Model_Preemption_Parameter_JobPreemptable_job_preemptable Job
           inst_7
           inst_13 j pp)
        Bool_true))
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_7 : DecidableEq Job),
       Prosa_Behavior_Job_JobCost Job
         inst_7 ->
       Prosa_Model_Preemption_Parameter_JobPreemptable Job
         inst_7 ->
       Job -> SProp

Arguments Prosa_Model_Task_Preemption_Parameters_nonpreemptive_regions_have_bounded_length 
  Job inst_7
  inst_10
  inst_13 j
```
