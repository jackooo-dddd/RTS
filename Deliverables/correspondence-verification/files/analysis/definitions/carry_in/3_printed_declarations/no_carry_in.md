# `no_carry_in`

- Kind (Rocq): Definition
- Rocq: `prosa.analysis.definitions.carry_in.no_carry_in`
- Lean: `Prosa.Analysis.Definitions.CarryIn.no_carry_in`
- Certificate: `no_carry_in_correspondence`

## Official Rocq

```coq
no_carry_in :
forall {Job : JobType},
JobArrival Job ->
JobCost Job ->
arrival_sequence Job -> forall {PState : ProcessorState Job}, @schedule Job PState -> instant -> Prop

no_carry_in is not universe polymorphic
Arguments no_carry_in {Job H1 H2} arr_seq {PState} sched t
no_carry_in is transparent
Expands to: Constant prosa.analysis.definitions.carry_in.no_carry_in
Declared in library prosa.analysis.definitions.carry_in, line 25, characters 13-24
@no_carry_in
     : forall Job : JobType,
       JobArrival Job ->
       JobCost Job ->
       arrival_sequence Job -> forall PState : ProcessorState Job, @schedule Job PState -> instant -> Prop
```

Body:

```coq
no_carry_in =
fun (Job : JobType) (H1 : JobArrival Job) (H2 : JobCost Job) (arr_seq : arrival_sequence Job)
  (PState : ProcessorState Job) (sched : @schedule Job PState) (t : instant) =>
forall j_o : Equality.sort Job,
@arrives_in Job arr_seq j_o ->
is_true (@arrived_before Job H1 j_o t) -> is_true (@completed_by Job PState sched H2 j_o t)
     : forall {Job : JobType},
       JobArrival Job ->
       JobCost Job ->
       arrival_sequence Job -> forall {PState : ProcessorState Job}, @schedule Job PState -> instant -> Prop

Arguments no_carry_in {Job H1 H2} arr_seq {PState} sched t
```

## Lean

```lean
@Prosa.Analysis.Definitions.CarryIn.no_carry_in : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    [Prosa.Behavior.Job.JobArrival Job] →
      [Prosa.Behavior.Job.JobCost Job] →
        Prosa.Behavior.Arrival_sequence.arrival_sequence Job →
          {PState : Prosa.Behavior.Schedule.ProcessorState Job} →
            Prosa.Behavior.Schedule.schedule PState → Prosa.Behavior.Time.instant → Prop
```

Body:

```lean
def Prosa.Analysis.Definitions.CarryIn.no_carry_in.{u_1, u_2, u_3} : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    [Prosa.Behavior.Job.JobArrival Job] →
      [Prosa.Behavior.Job.JobCost Job] →
        Prosa.Behavior.Arrival_sequence.arrival_sequence Job →
          {PState : Prosa.Behavior.Schedule.ProcessorState Job} →
            Prosa.Behavior.Schedule.schedule PState → Prosa.Behavior.Time.instant → Prop :=
fun {Job} [DecidableEq Job] [Prosa.Behavior.Job.JobArrival Job] [Prosa.Behavior.Job.JobCost Job] arr_seq {PState} sched
    t =>
  ∀ (j_o : Job),
    Prosa.Behavior.Arrival_sequence.arrives_in arr_seq j_o →
      Prosa.Behavior.Arrival_sequence.arrived_before j_o t = true →
        Prosa.Behavior.Service.completed_by sched j_o t = true
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Definitions_CarryIn_no_carry_in
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job),
       Prosa_Behavior_Job_JobArrival Job
         inst_3 ->
       Prosa_Behavior_Job_JobCost Job inst_3 ->
       Prosa_Behavior_Arrival_sequence_arrival_sequence Job
         inst_3 ->
       forall
         PState : Prosa_Behavior_Schedule_ProcessorState Job
                    inst_3,
       Prosa_Behavior_Schedule_schedule Job
         inst_3 PState ->
       Prosa_Behavior_Time_instant -> SProp
```

Body:

```coq
Prosa_Analysis_Definitions_CarryIn_no_carry_in@{u_1 u_2 u_3 Lean.u_1+1.0 Lean.max__u_1+1_u_2+2_u_3+2.0
Lean.u_2+1.0 Lean.u_3+1.0 Lean.u_1+2.0 Lean.u_3+2.0} =
fun (Job : Prosa_Behavior_Job_JobType)
  (inst_3 : DecidableEq Job)
  (inst_6 : Prosa_Behavior_Job_JobArrival Job
                                                                              inst_3)
  (inst_9 : Prosa_Behavior_Job_JobCost Job
                                                                              inst_3)
  (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
               inst_3)
  (PState : Prosa_Behavior_Schedule_ProcessorState Job
              inst_3)
  (sched : Prosa_Behavior_Schedule_schedule Job
             inst_3 PState)
  (t : Prosa_Behavior_Time_instant) =>
forall j_o : Job,
Prosa_Behavior_Arrival_sequence_arrives_in Job
  inst_3 arr_seq j_o ->
@eq Bool
  (Prosa_Behavior_Arrival_sequence_arrived_before Job
     inst_3
     inst_6 j_o t)
  Bool_true ->
@eq Bool
  (Prosa_Behavior_Service_completed_by Job
     inst_3 PState sched
     inst_9 j_o t)
  Bool_true
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job),
       Prosa_Behavior_Job_JobArrival Job
         inst_3 ->
       Prosa_Behavior_Job_JobCost Job inst_3 ->
       Prosa_Behavior_Arrival_sequence_arrival_sequence Job
         inst_3 ->
       forall
         PState : Prosa_Behavior_Schedule_ProcessorState Job
                    inst_3,
       Prosa_Behavior_Schedule_schedule Job
         inst_3 PState ->
       Prosa_Behavior_Time_instant -> SProp

Arguments Prosa_Analysis_Definitions_CarryIn_no_carry_in Job
  inst_3
  inst_6
  inst_9 arr_seq 
  PState sched t
```
