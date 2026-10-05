# `size_task_arrivals_between_eq0`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.periodic.task_arrivals_size.size_task_arrivals_between_eq0`
- Lean: `Prosa.Analysis.Facts.Periodic.TaskArrivalsSize.size_task_arrivals_between_eq0`
- Certificate: `size_task_arrivals_between_eq0_correspondence`

## Official Rocq

```coq
size_task_arrivals_between_eq0 :
forall {Task : TaskType} {H : TaskOffset Task} {H0 : PeriodicModel Task} {Job : JobType}
  {H1 : JobTask Job Task} {H2 : JobArrival Job} (arr_seq : arrival_sequence Job),
@valid_arrival_sequence Job H2 arr_seq ->
forall tsk : Equality.sort Task,
@valid_offset Task H Job H1 H2 arr_seq tsk ->
is_true (@valid_period Task H0 tsk) ->
@respects_periodic_task_model Task H0 Job H1 H2 arr_seq tsk ->
forall n : nat,
let l := (@task_offset Task H tsk + n * @task_period Task H0 tsk).+1 in
let r := @task_offset Task H tsk + n.+1 * @task_period Task H0 tsk in
@size (Equality.sort Job) (@task_arrivals_between Job Task H1 arr_seq tsk l r) = 0

size_task_arrivals_between_eq0 is not universe polymorphic
Arguments size_task_arrivals_between_eq0 {Task H H0 Job H1 H2} arr_seq H_valid_arrival_sequence 
  tsk H_valid_offset H_valid_period H_task_respects_periodic_model n%nat_scope
size_task_arrivals_between_eq0 is opaque
Expands to: Constant prosa.analysis.facts.periodic.task_arrivals_size.size_task_arrivals_between_eq0
Declared in library prosa.analysis.facts.periodic.task_arrivals_size, line 83, characters 8-38
@size_task_arrivals_between_eq0
     : forall (Task : TaskType) (H : TaskOffset Task) (H0 : PeriodicModel Task) (Job : JobType)
         (H1 : JobTask Job Task) (H2 : JobArrival Job) (arr_seq : arrival_sequence Job),
       @valid_arrival_sequence Job H2 arr_seq ->
       forall tsk : Equality.sort Task,
       @valid_offset Task H Job H1 H2 arr_seq tsk ->
       is_true (@valid_period Task H0 tsk) ->
       @respects_periodic_task_model Task H0 Job H1 H2 arr_seq tsk ->
       forall n : nat,
       let l := (@task_offset Task H tsk + n * @task_period Task H0 tsk).+1 in
       let r := @task_offset Task H tsk + n.+1 * @task_period Task H0 tsk in
       @size (Equality.sort Job) (@task_arrivals_between Job Task H1 arr_seq tsk l r) = 0
```

## Lean

```lean
@Prosa.Analysis.Facts.Periodic.TaskArrivalsSize.size_task_arrivals_between_eq0 : ∀
  {Task : Prosa.Model.Task.Concept.TaskType} [inst : DecidableEq Task]
  [inst_1 : Prosa.Model.Task.Offset.TaskOffset Task] [inst_2 : Prosa.Model.Task.Arrival.Periodic.PeriodicModel Task]
  {Job : Prosa.Behavior.Job.JobType} [inst_3 : DecidableEq Job] [inst_4 : Prosa.Model.Task.Concept.JobTask Job Task]
  [inst_5 : Prosa.Behavior.Job.JobArrival Job] (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
  Prosa.Behavior.Arrival_sequence.valid_arrival_sequence arr_seq →
    ∀ (tsk : Task),
      Prosa.Model.Task.Offset.valid_offset arr_seq tsk →
        Prosa.Model.Task.Arrival.Periodic.valid_period tsk = true →
          Prosa.Model.Task.Arrival.Periodic.respects_periodic_task_model arr_seq tsk →
            ∀ (n : ℕ),
              have l :=
                Prosa.Model.Task.Offset.task_offset tsk + n * Prosa.Model.Task.Arrival.Periodic.task_period tsk + 1;
              have r :=
                Prosa.Model.Task.Offset.task_offset tsk + (n + 1) * Prosa.Model.Task.Arrival.Periodic.task_period tsk;
              (Prosa.Model.Task.Arrivals.task_arrivals_between arr_seq tsk l r).length = 0
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Periodic_TaskArrivalsSize_size_task_arrivals_between_eq0
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : 
          DecidableEq Task)
         (inst_6 : 
          Prosa_Model_Task_Offset_TaskOffset Task
            inst_3)
         (inst_9 : 
          Prosa_Model_Task_Arrival_Periodic_PeriodicModel Task
            inst_3)
         (Job : Prosa_Behavior_Job_JobType)
         (inst_13 : 
          DecidableEq Job)
         (inst_16 : 
          Prosa_Model_Task_Concept_JobTask Job
            inst_13 Task
            inst_3)
         (inst_20 : 
          Prosa_Behavior_Job_JobArrival Job
            inst_13)
         (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                      inst_13),
       Prosa_Behavior_Arrival_sequence_valid_arrival_sequence Job
         inst_13
         inst_20 arr_seq ->
       forall tsk : Task,
       Prosa_Model_Task_Offset_valid_offset Task
         inst_3
         inst_6 Job
         inst_13
         inst_16
         inst_20 arr_seq tsk ->
       @eq Bool
         (Prosa_Model_Task_Arrival_Periodic_valid_period Task
            inst_3
            inst_9 tsk)
         Bool_true ->
       Prosa_Model_Task_Arrival_Periodic_respects_periodic_task_model Task
         inst_3
         inst_9 Job
         inst_13
         inst_16
         inst_20 arr_seq tsk ->
       forall n : Nat,
       let l :=
         HAdd_hAdd_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_instant Prosa_Behavior_Time_instant
           (instHAdd_inst1 Prosa_Behavior_Time_instant instAddNat)
           (HAdd_hAdd_inst7 Prosa_Behavior_Time_instant Nat Prosa_Behavior_Time_instant
              (instHAdd_inst1 Prosa_Behavior_Time_instant instAddNat)
              (Prosa_Model_Task_Offset_TaskOffset_task_offset Task
                 inst_3
                 inst_6 tsk)
              (HMul_hMul_inst7 Nat Prosa_Behavior_Time_duration Nat (instHMul_inst1 Nat instMulNat) n
                 (Prosa_Model_Task_Arrival_Periodic_PeriodicModel_task_period Task
                    inst_3
                    inst_9 tsk)))
           (OfNat_ofNat_inst1 Prosa_Behavior_Time_instant 1 (instOfNatNat 1))
         in
       let r :=
         HAdd_hAdd_inst7 Prosa_Behavior_Time_instant Nat Prosa_Behavior_Time_instant
           (instHAdd_inst1 Prosa_Behavior_Time_instant instAddNat)
           (Prosa_Model_Task_Offset_TaskOffset_task_offset Task
              inst_3
              inst_6 tsk)
           (HMul_hMul_inst7 Nat Prosa_Behavior_Time_duration Nat (instHMul_inst1 Nat instMulNat)
              (HAdd_hAdd_inst7 Nat Prosa_Behavior_Time_instant Nat (instHAdd_inst1 Nat instAddNat) n
                 (OfNat_ofNat_inst1 Prosa_Behavior_Time_instant 1 (instOfNatNat 1)))
              (Prosa_Model_Task_Arrival_Periodic_PeriodicModel_task_period Task
                 inst_3
                 inst_9 tsk))
         in
       @eq Nat
         (List_length Job
            (Prosa_Model_Task_Arrivals_task_arrivals_between Job
               inst_13 Task
               inst_3
               inst_16 arr_seq
               tsk l r))
         (OfNat_ofNat_inst1 Nat 0 (instOfNatNat 0))
```
