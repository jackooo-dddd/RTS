# `job_costs_shifted`

- Kind (Rocq): Definition
- Rocq: `prosa.analysis.facts.shifted_job_costs.job_costs_shifted`
- Lean: `Prosa.Analysis.Facts.ShiftedJobCosts.job_costs_shifted`
- Certificate: `job_costs_shifted_correspondence`

## Official Rocq

```coq
job_costs_shifted :
forall {Task : TaskType},
TaskOffset Task ->
PeriodicModel Task ->
forall {Job : JobType},
JobTask Job Task ->
JobArrival Job ->
JobCost Job ->
arrival_sequence Job -> TaskSet (Equality.sort Task) -> Equality.sort Job -> Equality.sort Job -> work

job_costs_shifted is not universe polymorphic
Arguments job_costs_shifted {Task H H0 Job H2 H3 H4} arr_seq ts j j'
job_costs_shifted is transparent
Expands to: Constant prosa.analysis.facts.shifted_job_costs.job_costs_shifted
Declared in library prosa.analysis.facts.shifted_job_costs, line 51, characters 13-30
@job_costs_shifted
     : forall Task : TaskType,
       TaskOffset Task ->
       PeriodicModel Task ->
       forall Job : JobType,
       JobTask Job Task ->
       JobArrival Job ->
       JobCost Job ->
       arrival_sequence Job -> TaskSet (Equality.sort Task) -> Equality.sort Job -> Equality.sort Job -> work
```

Body:

```coq
job_costs_shifted =
fun (Task : TaskType) (H : TaskOffset Task) (H0 : PeriodicModel Task) (Job : JobType) 
  (H2 : JobTask Job Task) (H3 : JobArrival Job) (H4 : JobCost Job) (arr_seq : arrival_sequence Job)
  (ts : TaskSet (Equality.sort Task)) (j : Equality.sort Job) =>
let O_max := @max_task_offset Task H ts in
let HP := @hyperperiod Task H0 ts in
fun j' : Equality.sort Job =>
if
 [&& O_max <= @job_arrival Job H3 j, O_max + HP <= @job_arrival Job H3 j'
   & @job_arrival Job H3 j' < O_max + 2 * HP]
then
 @job_cost Job H4
   (@corresponding_job_in_hyperperiod Task H H0 Job H2 H3 ts arr_seq j'
      (@starting_instant_of_corresponding_hyperperiod Task H H0 Job H3 ts j) (@job_task Job Task H2 j'))
else @job_cost Job H4 j'
     : forall {Task : TaskType},
       TaskOffset Task ->
       PeriodicModel Task ->
       forall {Job : JobType},
       JobTask Job Task ->
       JobArrival Job ->
       JobCost Job ->
       arrival_sequence Job -> TaskSet (Equality.sort Task) -> Equality.sort Job -> Equality.sort Job -> work

Arguments job_costs_shifted {Task H H0 Job H2 H3 H4} arr_seq ts j j'
```

## Lean

```lean
@Prosa.Analysis.Facts.ShiftedJobCosts.job_costs_shifted : {Task : Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    [Prosa.Model.Task.Offset.TaskOffset Task] →
      [Prosa.Model.Task.Arrival.Periodic.PeriodicModel Task] →
        {Job : Prosa.Behavior.Job.JobType} →
          [inst_3 : DecidableEq Job] →
            [Prosa.Model.Task.Concept.JobTask Job Task] →
              [Prosa.Behavior.Job.JobArrival Job] →
                [Prosa.Behavior.Job.JobCost Job] →
                  Prosa.Behavior.Arrival_sequence.arrival_sequence Job →
                    Prosa.Model.Task.Concept.TaskSet Task → Job → Job → Prosa.Behavior.Job.work
```

Body:

```lean
def Prosa.Analysis.Facts.ShiftedJobCosts.job_costs_shifted.{u_1, u_2} : {Task : Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    [Prosa.Model.Task.Offset.TaskOffset Task] →
      [Prosa.Model.Task.Arrival.Periodic.PeriodicModel Task] →
        {Job : Prosa.Behavior.Job.JobType} →
          [inst_3 : DecidableEq Job] →
            [Prosa.Model.Task.Concept.JobTask Job Task] →
              [Prosa.Behavior.Job.JobArrival Job] →
                [Prosa.Behavior.Job.JobCost Job] →
                  Prosa.Behavior.Arrival_sequence.arrival_sequence Job →
                    Prosa.Model.Task.Concept.TaskSet Task → Job → Job → Prosa.Behavior.Job.work :=
fun {Task} [DecidableEq Task] [Prosa.Model.Task.Offset.TaskOffset Task]
    [Prosa.Model.Task.Arrival.Periodic.PeriodicModel Task] {Job} [DecidableEq Job]
    [Prosa.Model.Task.Concept.JobTask Job Task] [Prosa.Behavior.Job.JobArrival Job] [Prosa.Behavior.Job.JobCost Job]
    arr_seq ts j j' =>
  bif
      decide (Prosa.Model.Task.Offset.max_task_offset ts ≤ Prosa.Behavior.Job.job_arrival j) &&
        (decide
            (Prosa.Model.Task.Offset.max_task_offset ts + Prosa.Analysis.Definitions.Hyperperiod.hyperperiod ts ≤
              Prosa.Behavior.Job.job_arrival j') &&
          decide
            (Prosa.Behavior.Job.job_arrival j' <
              Prosa.Model.Task.Offset.max_task_offset ts +
                2 * Prosa.Analysis.Definitions.Hyperperiod.hyperperiod ts)) then
    Prosa.Behavior.Job.job_cost
      (Prosa.Analysis.Definitions.Hyperperiod.corresponding_job_in_hyperperiod ts arr_seq j'
        (Prosa.Analysis.Definitions.Hyperperiod.starting_instant_of_corresponding_hyperperiod ts j)
        (Prosa.Model.Task.Concept.job_task j'))
  else Prosa.Behavior.Job.job_cost j'
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_ShiftedJobCosts_job_costs_shifted
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task),
       Prosa_Model_Task_Offset_TaskOffset Task
         inst_3 ->
       Prosa_Model_Task_Arrival_Periodic_PeriodicModel Task
         inst_3 ->
       forall (Job : Prosa_Behavior_Job_JobType)
         (inst_13 : DecidableEq Job),
       Prosa_Model_Task_Concept_JobTask Job
         inst_13 Task
         inst_3 ->
       Prosa_Behavior_Job_JobArrival Job
         inst_13 ->
       Prosa_Behavior_Job_JobCost Job
         inst_13 ->
       Prosa_Behavior_Arrival_sequence_arrival_sequence Job
         inst_13 ->
       Prosa_Model_Task_Concept_TaskSet Task -> Job -> Job -> Prosa_Behavior_Job_work
```

Body:

```coq
Prosa_Analysis_Facts_ShiftedJobCosts_job_costs_shifted@{u_1 u_2 Lean.u_1+1.0 Lean.max__u_1+1_u_2+1.0
Lean.u_2+1.0 Lean.u_1+2.0 Lean.u_2+2.0} =
fun (Task : Prosa_Model_Task_Concept_TaskType)
  (inst_3 : DecidableEq Task)
  (inst_6 : Prosa_Model_Task_Offset_TaskOffset
                                                                                Task
                                                                                inst_3)
  (inst_9 : Prosa_Model_Task_Arrival_Periodic_PeriodicModel
                                                                                Task
                                                                                inst_3)
  (Job : Prosa_Behavior_Job_JobType)
  (inst_13 : DecidableEq Job)
  (inst_16 : Prosa_Model_Task_Concept_JobTask
                                                                                Job
                                                                                inst_13
                                                                                Task
                                                                                inst_3)
  (inst_20 : Prosa_Behavior_Job_JobArrival
                                                                                Job
                                                                                inst_13)
  (inst_23 : Prosa_Behavior_Job_JobCost
                                                                                Job
                                                                                inst_13)
  (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
               inst_13)
  (ts : Prosa_Model_Task_Concept_TaskSet Task) (j j' : Job) =>
cond Prosa_Behavior_Job_work
  (Bool_and
     (Decidable_decide
        (LE_le_inst1 Nat instLENat
           (Prosa_Model_Task_Offset_max_task_offset Task
              inst_3
              inst_6 ts)
           (Prosa_Behavior_Job_JobArrival_job_arrival Job
              inst_13
              inst_20 j))
        (Nat_decLe
           (Prosa_Model_Task_Offset_max_task_offset Task
              inst_3
              inst_6 ts)
           (Prosa_Behavior_Job_JobArrival_job_arrival Job
              inst_13
              inst_20 j)))
     (Bool_and
        (Decidable_decide
           (LE_le_inst1 Nat instLENat
              (HAdd_hAdd_inst7 Nat Prosa_Behavior_Time_duration Nat (instHAdd_inst1 Nat instAddNat)
                 (Prosa_Model_Task_Offset_max_task_offset Task
                    inst_3
                    inst_6 ts)
                 (Prosa_Analysis_Definitions_Hyperperiod_hyperperiod Task
                    inst_3
                    inst_9 ts))
              (Prosa_Behavior_Job_JobArrival_job_arrival Job
                 inst_13
                 inst_20 j'))
           (Nat_decLe
              (HAdd_hAdd_inst7 Nat Prosa_Behavior_Time_duration Nat (instHAdd_inst1 Nat instAddNat)
                 (Prosa_Model_Task_Offset_max_task_offset Task
                    inst_3
                    inst_6 ts)
                 (Prosa_Analysis_Definitions_Hyperperiod_hyperperiod Task
                    inst_3
                    inst_9 ts))
              (Prosa_Behavior_Job_JobArrival_job_arrival Job
                 inst_13
                 inst_20 j')))
        (Decidable_decide
           (LT_lt_inst1 Prosa_Behavior_Time_instant instLTNat
              (Prosa_Behavior_Job_JobArrival_job_arrival Job
                 inst_13
                 inst_20 j')
              (HAdd_hAdd_inst7 Nat Prosa_Behavior_Time_instant Nat (instHAdd_inst1 Nat instAddNat)
                 (Prosa_Model_Task_Offset_max_task_offset Task
                    inst_3
                    inst_6 ts)
                 (HMul_hMul_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_duration
                    Prosa_Behavior_Time_instant (instHMul_inst1 Prosa_Behavior_Time_instant instMulNat)
                    (OfNat_ofNat_inst1 Prosa_Behavior_Time_instant 2 (instOfNatNat 2))
                    (Prosa_Analysis_Definitions_Hyperperiod_hyperperiod Task
                       inst_3
                       inst_9 ts))))
           (Nat_decLt
              (Prosa_Behavior_Job_JobArrival_job_arrival Job
                 inst_13
                 inst_20 j')
              (HAdd_hAdd_inst7 Nat Prosa_Behavior_Time_instant Nat (instHAdd_inst1 Nat instAddNat)
                 (Prosa_Model_Task_Offset_max_task_offset Task
                    inst_3
                    inst_6 ts)
                 (HMul_hMul_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_duration
                    Prosa_Behavior_Time_instant (instHMul_inst1 Prosa_Behavior_Time_instant instMulNat)
                    (OfNat_ofNat_inst1 Prosa_Behavior_Time_instant 2 (instOfNatNat 2))
                    (Prosa_Analysis_Definitions_Hyperperiod_hyperperiod Task
                       inst_3
                       inst_9 ts)))))))
  (Prosa_Behavior_Job_JobCost_job_cost Job
     inst_13
     inst_23
     (Prosa_Analysis_Definitions_Hyperperiod_corresponding_job_in_hyperperiod Task
        inst_3
        inst_6
        inst_9 Job
        inst_13
        inst_16
        inst_20 ts arr_seq j'
        (Prosa_Analysis_Definitions_Hyperperiod_starting_instant_of_corresponding_hyperperiod Task
           inst_3
           inst_6
           inst_9 Job
           inst_13
           inst_20 ts j)
        (Prosa_Model_Task_Concept_JobTask_job_task Job
           inst_13 Task
           inst_3
           inst_16 j')))
  (Prosa_Behavior_Job_JobCost_job_cost Job
     inst_13
     inst_23 j')
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task),
       Prosa_Model_Task_Offset_TaskOffset Task
         inst_3 ->
       Prosa_Model_Task_Arrival_Periodic_PeriodicModel Task
         inst_3 ->
       forall (Job : Prosa_Behavior_Job_JobType)
         (inst_13 : DecidableEq Job),
       Prosa_Model_Task_Concept_JobTask Job
         inst_13 Task
         inst_3 ->
       Prosa_Behavior_Job_JobArrival Job
         inst_13 ->
       Prosa_Behavior_Job_JobCost Job
         inst_13 ->
       Prosa_Behavior_Arrival_sequence_arrival_sequence Job
         inst_13 ->
       Prosa_Model_Task_Concept_TaskSet Task -> Job -> Job -> Prosa_Behavior_Job_work

Arguments Prosa_Analysis_Facts_ShiftedJobCosts_job_costs_shifted Task
  inst_3
  inst_6
  inst_9 Job
  inst_13
  inst_16
  inst_20
  inst_23 arr_seq 
  ts j j'
```
