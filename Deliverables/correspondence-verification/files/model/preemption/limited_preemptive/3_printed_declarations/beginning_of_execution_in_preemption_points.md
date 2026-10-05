# `beginning_of_execution_in_preemption_points`

- Kind (Rocq): Definition
- Rocq: `prosa.model.preemption.limited_preemptive.beginning_of_execution_in_preemption_points`
- Lean: `Prosa.Model.Preemption.LimitedPreemptive.beginning_of_execution_in_preemption_points`
- Certificate: `beginning_of_execution_in_preemption_points_correspondence`

## Official Rocq

```coq
beginning_of_execution_in_preemption_points :
forall {Job : JobType}, JobPreemptionPoints Job -> arrival_sequence Job -> Prop

beginning_of_execution_in_preemption_points is not universe polymorphic
Arguments beginning_of_execution_in_preemption_points {Job H1} arr_seq
beginning_of_execution_in_preemption_points is transparent
Expands to: Constant prosa.model.preemption.limited_preemptive.beginning_of_execution_in_preemption_points
Declared in library prosa.model.preemption.limited_preemptive, line 53, characters 15-58
@beginning_of_execution_in_preemption_points
     : forall Job : JobType, JobPreemptionPoints Job -> arrival_sequence Job -> Prop
```

Body:

```coq
beginning_of_execution_in_preemption_points =
fun (Job : JobType) (H1 : JobPreemptionPoints Job) (arr_seq : arrival_sequence Job) =>
forall j : Equality.sort Job, @arrives_in Job arr_seq j -> is_true (0 \in @job_preemptive_points Job H1 j)
     : forall {Job : JobType}, JobPreemptionPoints Job -> arrival_sequence Job -> Prop

Arguments beginning_of_execution_in_preemption_points {Job H1} arr_seq
```

## Lean

```lean
@Prosa.Model.Preemption.LimitedPreemptive.beginning_of_execution_in_preemption_points : {Job :
    Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    [Prosa.Model.Preemption.LimitedPreemptive.JobPreemptionPoints Job] →
      Prosa.Behavior.Arrival_sequence.arrival_sequence Job → Prop
```

Body:

```lean
def Prosa.Model.Preemption.LimitedPreemptive.beginning_of_execution_in_preemption_points.{u_1} : {Job :
    Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    [Prosa.Model.Preemption.LimitedPreemptive.JobPreemptionPoints Job] →
      Prosa.Behavior.Arrival_sequence.arrival_sequence Job → Prop :=
fun {Job} [DecidableEq Job] [Prosa.Model.Preemption.LimitedPreemptive.JobPreemptionPoints Job] arr_seq =>
  ∀ (j : Job),
    Prosa.Behavior.Arrival_sequence.arrives_in arr_seq j →
      decide (0 ∈ Prosa.Model.Preemption.LimitedPreemptive.job_preemptive_points j) = true
```

## Lean, imported into Rocq

```coq
Prosa_Model_Preemption_LimitedPreemptive_beginning_of_execution_in_preemption_points
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job),
       Prosa_Model_Preemption_LimitedPreemptive_JobPreemptionPoints Job
         inst_3 ->
       Prosa_Behavior_Arrival_sequence_arrival_sequence Job
         inst_3 ->
       SProp
```

Body:

```coq
Prosa_Model_Preemption_LimitedPreemptive_beginning_of_execution_in_preemption_points@{u_1 Lean.u_1+1.0
Lean.u_1+2.0} =
fun (Job : Prosa_Behavior_Job_JobType)
  (inst_3 : DecidableEq Job)
  (inst_6 : 
   Prosa_Model_Preemption_LimitedPreemptive_JobPreemptionPoints Job
     inst_3)
  (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
               inst_3) =>
forall j : Job,
Prosa_Behavior_Arrival_sequence_arrives_in Job
  inst_3 arr_seq j ->
@eq Bool
  (Decidable_decide
     (Membership_mem_inst3 Prosa_Behavior_Job_work (List_inst1 Prosa_Behavior_Job_work)
        (List_instMembership_inst1 Prosa_Behavior_Job_work)
        (Prosa_Model_Preemption_LimitedPreemptive_JobPreemptionPoints_job_preemptive_points Job
           inst_3
           inst_6 j)
        (OfNat_ofNat_inst1 Prosa_Behavior_Job_work 0 (instOfNatNat 0)))
     (List_instDecidableMemOfLawfulBEq_inst1 Prosa_Behavior_Job_work
        (instBEqOfDecidableEq_inst1 Prosa_Behavior_Job_work instDecidableEqNat) Nat_instLawfulBEq
        (OfNat_ofNat_inst1 Prosa_Behavior_Job_work 0 (instOfNatNat 0))
        (Prosa_Model_Preemption_LimitedPreemptive_JobPreemptionPoints_job_preemptive_points Job
           inst_3
           inst_6 j)))
  Bool_true
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job),
       Prosa_Model_Preemption_LimitedPreemptive_JobPreemptionPoints Job
         inst_3 ->
       Prosa_Behavior_Arrival_sequence_arrival_sequence Job
         inst_3 ->
       SProp

Arguments Prosa_Model_Preemption_LimitedPreemptive_beginning_of_execution_in_preemption_points 
  Job inst_3
  inst_6 arr_seq
```
