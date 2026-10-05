# `cond_interference_is_bounded_by`

- Kind (Rocq): Definition
- Rocq: `prosa.analysis.abstract.definitions.cond_interference_is_bounded_by`
- Lean: `Prosa.Analysis.Abstract.Definitions.cond_interference_is_bounded_by`
- Certificate: `ad_cond_interference_bounded_correspondence`

## Official Rocq

```coq
cond_interference_is_bounded_by :
forall {Job : JobType} {Task : TaskType},
JobTask Job Task ->
JobArrival Job ->
JobCost Job ->
forall {PState : ProcessorState Job},
arrival_sequence Job ->
@schedule Job PState ->
Equality.sort Task ->
Interference Job ->
InterferingWorkload Job ->
(duration -> duration -> work) ->
(Equality.sort Job -> nat -> Prop) -> (Equality.sort Job -> instant -> bool) -> Prop

cond_interference_is_bounded_by is not universe polymorphic
Arguments cond_interference_is_bounded_by {Job Task H H0 H1 PState} arr_seq sched 
  tsk {H2 H3} (IBF ParamSem Cond)%function_scope
cond_interference_is_bounded_by is transparent
Expands to: Constant prosa.analysis.abstract.definitions.cond_interference_is_bounded_by
Declared in library prosa.analysis.abstract.definitions, line 308, characters 15-46
@cond_interference_is_bounded_by
     : forall (Job : JobType) (Task : TaskType),
       JobTask Job Task ->
       JobArrival Job ->
       JobCost Job ->
       forall PState : ProcessorState Job,
       arrival_sequence Job ->
       @schedule Job PState ->
       Equality.sort Task ->
       Interference Job ->
       InterferingWorkload Job ->
       (duration -> duration -> work) ->
       (Equality.sort Job -> nat -> Prop) -> (Equality.sort Job -> instant -> bool) -> Prop
```

Body:

```coq
cond_interference_is_bounded_by =
fun (Job : JobType) (Task : TaskType) (H : JobTask Job Task) (H0 : JobArrival Job) 
  (H1 : JobCost Job) (PState : ProcessorState Job) (arr_seq : arrival_sequence Job)
  (sched : @schedule Job PState) (tsk : Equality.sort Task) (H2 : Interference Job)
  (H3 : InterferingWorkload Job) (IBF : duration -> duration -> work)
  (ParamSem : Equality.sort Job -> nat -> Prop) (Cond : Equality.sort Job -> instant -> bool) =>
forall (t1 t2 : instant) (Δ : nat) (j : Equality.sort Job),
@arrives_in Job arr_seq j ->
is_true (@job_of_task Job Task H tsk j) ->
@busy_interval Job H0 H1 PState sched H2 H3 j t1 t2 ->
is_true (t1 + Δ < t2) ->
is_true (~~ @completed_by Job PState sched H1 j (t1 + Δ)) ->
forall X : nat, ParamSem j X -> is_true (@cumul_cond_interference Job H2 Cond j t1 (t1 + Δ) <= IBF X Δ)
     : forall {Job : JobType} {Task : TaskType},
       JobTask Job Task ->
       JobArrival Job ->
       JobCost Job ->
       forall {PState : ProcessorState Job},
       arrival_sequence Job ->
       @schedule Job PState ->
       Equality.sort Task ->
       Interference Job ->
       InterferingWorkload Job ->
       (duration -> duration -> work) ->
       (Equality.sort Job -> nat -> Prop) -> (Equality.sort Job -> instant -> bool) -> Prop

Arguments cond_interference_is_bounded_by {Job Task H H0 H1 PState} arr_seq sched 
  tsk {H2 H3} (IBF ParamSem Cond)%function_scope
```

## Lean

```lean
@Prosa.Analysis.Abstract.Definitions.cond_interference_is_bounded_by : {Job : Prosa.Behavior.Job.JobType} →
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
                      [Prosa.Model.Task.Concept.JobTask Job Task] →
                        Task →
                          (Prosa.Behavior.Time.duration → Prosa.Behavior.Time.duration → Prosa.Behavior.Job.work) →
                            (Job → ℕ → Prop) → (Job → Prosa.Behavior.Time.instant → Bool) → Prop
def Prosa.Analysis.Abstract.Definitions.cond_interference_is_bounded_by.{u_1, u_2, u_3, u_4} : {Job :
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
                      [Prosa.Model.Task.Concept.JobTask Job Task] →
                        Task →
                          (Prosa.Behavior.Time.duration → Prosa.Behavior.Time.duration → Prosa.Behavior.Job.work) →
                            (Job → ℕ → Prop) → (Job → Prosa.Behavior.Time.instant → Bool) → Prop :=
fun {Job} [DecidableEq Job] [Prosa.Analysis.Abstract.Definitions.Interference Job]
    [Prosa.Analysis.Abstract.Definitions.InterferingWorkload Job] [Prosa.Behavior.Job.JobArrival Job]
    [Prosa.Behavior.Job.JobCost Job] {PState} arrSeq sched {Task} [DecidableEq Task]
    [Prosa.Model.Task.Concept.JobTask Job Task] tsk IBF ParamSem Cond =>
  ∀ (t1 t2 Δ : Prosa.Behavior.Time.instant) (j : Job),
    Prosa.Behavior.Arrival_sequence.arrives_in arrSeq j →
      Prosa.Model.Task.Concept.job_of_task tsk j = true →
        Prosa.Analysis.Abstract.Definitions.busy_interval sched j t1 t2 →
          t1 + Δ < t2 →
            (!Prosa.Behavior.Service.completed_by sched j (t1 + Δ)) = true →
              ∀ (X : ℕ),
                ParamSem j X → Prosa.Analysis.Abstract.Definitions.cumul_cond_interference Cond j t1 (t1 + Δ) ≤ IBF X Δ
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Abstract_Definitions_cond_interference_is_bounded_by
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
       Task ->
       (Prosa_Behavior_Time_duration -> Prosa_Behavior_Time_duration -> Prosa_Behavior_Job_work) ->
       (Job -> Nat -> SProp) -> (Job -> Prosa_Behavior_Time_instant -> Bool) -> SProp
```

Body:

```coq
Prosa_Analysis_Abstract_Definitions_cond_interference_is_bounded_by@{u_1 u_2 u_3 u_4 Lean.u_1+1.0
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
  (tsk : Task)
  (IBF : Prosa_Behavior_Time_duration -> Prosa_Behavior_Time_duration -> Prosa_Behavior_Job_work)
  (ParamSem : Job -> Nat -> SProp) (Cond : Job -> Prosa_Behavior_Time_instant -> Bool) =>
forall (t1 t2 _UU0394_ : Prosa_Behavior_Time_instant) (j : Job),
Prosa_Behavior_Arrival_sequence_arrives_in Job
  inst_3 arrSeq j ->
@eq Bool
  (Prosa_Model_Task_Concept_job_of_task Job
     inst_3 Task
     inst_25
     inst_28 tsk j)
  Bool_true ->
Prosa_Analysis_Abstract_Definitions_busy_interval Job
  inst_3
  inst_6
  inst_9
  inst_12
  inst_15 PState sched j t1 t2 ->
LT_lt_inst1 Prosa_Behavior_Time_instant instLTNat
  (HAdd_hAdd_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_instant Prosa_Behavior_Time_instant
     (instHAdd_inst1 Prosa_Behavior_Time_instant instAddNat) t1 _UU0394_)
  t2 ->
@eq Bool
  (Bool_not
     (Prosa_Behavior_Service_completed_by Job
        inst_3 PState sched
        inst_15 j
        (HAdd_hAdd_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_instant Prosa_Behavior_Time_instant
           (instHAdd_inst1 Prosa_Behavior_Time_instant instAddNat) t1 _UU0394_)))
  Bool_true ->
forall X : Nat,
ParamSem j X ->
LE_le_inst1 Nat instLENat
  (Prosa_Analysis_Abstract_Definitions_cumul_cond_interference Job
     inst_3
     inst_6 Cond j t1
     (HAdd_hAdd_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_instant Prosa_Behavior_Time_instant
        (instHAdd_inst1 Prosa_Behavior_Time_instant instAddNat) t1 _UU0394_))
  (IBF X _UU0394_)
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
       Task ->
       (Prosa_Behavior_Time_duration -> Prosa_Behavior_Time_duration -> Prosa_Behavior_Job_work) ->
       (Job -> Nat -> SProp) -> (Job -> Prosa_Behavior_Time_instant -> Bool) -> SProp

Arguments Prosa_Analysis_Abstract_Definitions_cond_interference_is_bounded_by Job
  inst_3
  inst_6
  inst_9
  inst_12
  inst_15 PState 
  arrSeq sched Task inst_25
  inst_28 tsk
  (IBF ParamSem Cond)%_function_scope
```
