# `busy_intervals_are_bounded_by`

- Kind (Rocq): Definition
- Rocq: `prosa.analysis.abstract.definitions.busy_intervals_are_bounded_by`
- Lean: `Prosa.Analysis.Abstract.Definitions.busy_intervals_are_bounded_by`
- Certificate: `ad_busy_intervals_bounded_correspondence`

## Official Rocq

```coq
busy_intervals_are_bounded_by :
forall {Job : JobType} {Task : TaskType},
JobTask Job Task ->
JobArrival Job ->
JobCost Job ->
forall {PState : ProcessorState Job},
arrival_sequence Job ->
@schedule Job PState -> Equality.sort Task -> Interference Job -> InterferingWorkload Job -> nat -> Prop

busy_intervals_are_bounded_by is not universe polymorphic
Arguments busy_intervals_are_bounded_by {Job Task H H0 H1 PState} arr_seq sched tsk {H2 H3} L%nat_scope
busy_intervals_are_bounded_by is transparent
Expands to: Constant prosa.analysis.abstract.definitions.busy_intervals_are_bounded_by
Declared in library prosa.analysis.abstract.definitions, line 231, characters 15-44
@busy_intervals_are_bounded_by
     : forall (Job : JobType) (Task : TaskType),
       JobTask Job Task ->
       JobArrival Job ->
       JobCost Job ->
       forall PState : ProcessorState Job,
       arrival_sequence Job ->
       @schedule Job PState ->
       Equality.sort Task -> Interference Job -> InterferingWorkload Job -> nat -> Prop
```

Body:

```coq
busy_intervals_are_bounded_by =
fun (Job : JobType) (Task : TaskType) (H : JobTask Job Task) (H0 : JobArrival Job) 
  (H1 : JobCost Job) (PState : ProcessorState Job) (arr_seq : arrival_sequence Job)
  (sched : @schedule Job PState) (tsk : Equality.sort Task) (H2 : Interference Job)
  (H3 : InterferingWorkload Job) (L : nat) =>
forall j : Equality.sort Job,
@arrives_in Job arr_seq j ->
is_true (@job_of_task Job Task H tsk j) ->
is_true (0 < @job_cost Job H1 j) ->
exists t1 t2 : nat,
  is_true (t1 <= @job_arrival Job H0 j < t2) /\
  is_true (t2 <= t1 + L) /\ @busy_interval Job H0 H1 PState sched H2 H3 j t1 t2
     : forall {Job : JobType} {Task : TaskType},
       JobTask Job Task ->
       JobArrival Job ->
       JobCost Job ->
       forall {PState : ProcessorState Job},
       arrival_sequence Job ->
       @schedule Job PState ->
       Equality.sort Task -> Interference Job -> InterferingWorkload Job -> nat -> Prop

Arguments busy_intervals_are_bounded_by {Job Task H H0 H1 PState} arr_seq sched tsk {H2 H3} L%nat_scope
```

## Lean

```lean
@Prosa.Analysis.Abstract.Definitions.busy_intervals_are_bounded_by : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    [Prosa.Analysis.Abstract.Definitions.Interference Job] →
      [Prosa.Analysis.Abstract.Definitions.InterferingWorkload Job] →
        [Prosa.Behavior.Job.JobArrival Job] →
          [Prosa.Behavior.Job.JobCost Job] →
            {PState : Prosa.Behavior.Schedule.ProcessorState Job} →
              Prosa.Behavior.Arrival_sequence.arrival_sequence Job →
                Prosa.Behavior.Schedule.schedule PState →
                  {Task : Prosa.Model.Task.Concept.TaskType} →
                    [inst_5 : DecidableEq Task] →
                      [Prosa.Model.Task.Concept.JobTask Job Task] → Task → Prosa.Behavior.Time.duration → Prop
def Prosa.Analysis.Abstract.Definitions.busy_intervals_are_bounded_by.{u_1, u_2, u_3, u_4} : {Job :
    Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    [Prosa.Analysis.Abstract.Definitions.Interference Job] →
      [Prosa.Analysis.Abstract.Definitions.InterferingWorkload Job] →
        [Prosa.Behavior.Job.JobArrival Job] →
          [Prosa.Behavior.Job.JobCost Job] →
            {PState : Prosa.Behavior.Schedule.ProcessorState Job} →
              Prosa.Behavior.Arrival_sequence.arrival_sequence Job →
                Prosa.Behavior.Schedule.schedule PState →
                  {Task : Prosa.Model.Task.Concept.TaskType} →
                    [inst_5 : DecidableEq Task] →
                      [Prosa.Model.Task.Concept.JobTask Job Task] → Task → Prosa.Behavior.Time.duration → Prop :=
fun {Job} [DecidableEq Job] [Prosa.Analysis.Abstract.Definitions.Interference Job]
    [Prosa.Analysis.Abstract.Definitions.InterferingWorkload Job] [Prosa.Behavior.Job.JobArrival Job]
    [Prosa.Behavior.Job.JobCost Job] {PState} arrSeq sched {Task} [DecidableEq Task]
    [Prosa.Model.Task.Concept.JobTask Job Task] tsk L =>
  ∀ (j : Job),
    Prosa.Behavior.Arrival_sequence.arrives_in arrSeq j →
      Prosa.Model.Task.Concept.job_of_task tsk j = true →
        Prosa.Behavior.Job.job_cost j > 0 →
          ∃ t1 t2,
            (t1 ≤ Prosa.Behavior.Job.job_arrival j ∧ Prosa.Behavior.Job.job_arrival j < t2) ∧
              t2 ≤ t1 + L ∧ Prosa.Analysis.Abstract.Definitions.busy_interval sched j t1 t2
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Abstract_Definitions_busy_intervals_are_bounded_by
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job),
       Prosa_Analysis_Abstract_Definitions_Interference Job
         inst_3 ->
       Prosa_Analysis_Abstract_Definitions_InterferingWorkload Job
         inst_3 ->
       Prosa_Behavior_Job_JobArrival Job
         inst_3 ->
       Prosa_Behavior_Job_JobCost Job
         inst_3 ->
       forall
         PState : Prosa_Behavior_Schedule_ProcessorState Job
                    inst_3,
       Prosa_Behavior_Arrival_sequence_arrival_sequence Job
         inst_3 ->
       Prosa_Behavior_Schedule_schedule Job
         inst_3 PState ->
       forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_25 : DecidableEq Task),
       Prosa_Model_Task_Concept_JobTask Job
         inst_3 Task
         inst_25 ->
       Task -> Prosa_Behavior_Time_duration -> SProp
```

Body:

```coq
Prosa_Analysis_Abstract_Definitions_busy_intervals_are_bounded_by@{u_1 u_2 u_3 u_4 Lean.u_1+1.0
Lean.max__u_1+1_u_4+1.0 Lean.max__u_1+1_u_2+2_u_3+2.0 Lean.u_2+1.0 Lean.u_3+1.0 Lean.u_4+1.0 Lean.u_1+2.0
Lean.u_3+2.0 Lean.u_4+2.0} =
fun (Job : Prosa_Behavior_Job_JobType)
  (inst_3 : DecidableEq Job)
  (inst_6 : Prosa_Analysis_Abstract_Definitions_Interference
                                                                                Job
                                                                                inst_3)
  (inst_9 : Prosa_Analysis_Abstract_Definitions_InterferingWorkload
                                                                                Job
                                                                                inst_3)
  (inst_12 : Prosa_Behavior_Job_JobArrival
                                                                                Job
                                                                                inst_3)
  (inst_15 : Prosa_Behavior_Job_JobCost Job
                                                                                inst_3)
  (PState : Prosa_Behavior_Schedule_ProcessorState Job
              inst_3)
  (arrSeq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
              inst_3)
  (sched : Prosa_Behavior_Schedule_schedule Job
             inst_3 PState)
  (Task : Prosa_Model_Task_Concept_TaskType)
  (inst_25 : DecidableEq Task)
  (inst_28 : Prosa_Model_Task_Concept_JobTask
                                                                                Job
                                                                                inst_3
                                                                                Task
                                                                                inst_25)
  (tsk : Task) (L : Prosa_Behavior_Time_duration) =>
forall j : Job,
Prosa_Behavior_Arrival_sequence_arrives_in Job
  inst_3 arrSeq j ->
@eq Bool
  (Prosa_Model_Task_Concept_job_of_task Job
     inst_3 Task
     inst_25
     inst_28 tsk j)
  Bool_true ->
GT_gt_inst1 Prosa_Behavior_Job_work instLTNat
  (Prosa_Behavior_Job_JobCost_job_cost Job
     inst_3
     inst_15 j)
  (OfNat_ofNat_inst1 Prosa_Behavior_Job_work 0 (instOfNatNat 0)) ->
Exists Prosa_Behavior_Time_instant
  (fun t1 : Prosa_Behavior_Time_instant =>
   Exists Prosa_Behavior_Time_instant
     (fun t2 : Prosa_Behavior_Time_instant =>
      And
        (And
           (LE_le_inst1 Prosa_Behavior_Time_instant instLENat t1
              (Prosa_Behavior_Job_JobArrival_job_arrival Job
                 inst_3
                 inst_12 j))
           (LT_lt_inst1 Prosa_Behavior_Time_instant instLTNat
              (Prosa_Behavior_Job_JobArrival_job_arrival Job
                 inst_3
                 inst_12 j)
              t2))
        (And
           (LE_le_inst1 Prosa_Behavior_Time_instant instLENat t2
              (HAdd_hAdd_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_duration
                 Prosa_Behavior_Time_instant (instHAdd_inst1 Prosa_Behavior_Time_instant instAddNat) t1 L))
           (Prosa_Analysis_Abstract_Definitions_busy_interval Job
              inst_3
              inst_6
              inst_9
              inst_12
              inst_15 PState sched j t1 t2))))
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job),
       Prosa_Analysis_Abstract_Definitions_Interference Job
         inst_3 ->
       Prosa_Analysis_Abstract_Definitions_InterferingWorkload Job
         inst_3 ->
       Prosa_Behavior_Job_JobArrival Job
         inst_3 ->
       Prosa_Behavior_Job_JobCost Job
         inst_3 ->
       forall
         PState : Prosa_Behavior_Schedule_ProcessorState Job
                    inst_3,
       Prosa_Behavior_Arrival_sequence_arrival_sequence Job
         inst_3 ->
       Prosa_Behavior_Schedule_schedule Job
         inst_3 PState ->
       forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_25 : DecidableEq Task),
       Prosa_Model_Task_Concept_JobTask Job
         inst_3 Task
         inst_25 ->
       Task -> Prosa_Behavior_Time_duration -> SProp

Arguments Prosa_Analysis_Abstract_Definitions_busy_intervals_are_bounded_by Job
  inst_3
  inst_6
  inst_9
  inst_12
  inst_15 PState 
  arrSeq sched Task inst_25
  inst_28 tsk L
```
