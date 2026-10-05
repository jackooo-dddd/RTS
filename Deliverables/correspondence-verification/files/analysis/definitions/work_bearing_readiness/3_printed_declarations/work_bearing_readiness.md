# `work_bearing_readiness`

- Kind (Rocq): Definition
- Rocq: `prosa.analysis.definitions.work_bearing_readiness.work_bearing_readiness`
- Lean: `Prosa.Analysis.Definitions.WorkBearingReadiness.work_bearing_readiness`
- Certificate: `work_bearing_readiness_correspondence`

## Official Rocq

```coq
work_bearing_readiness :
forall {Job : JobType} {H : JobArrival Job} {H0 : JobCost Job} {PState : ProcessorState Job},
@JobReady Job PState H0 H -> arrival_sequence Job -> @schedule Job PState -> JLFP_policy Job -> Prop

work_bearing_readiness is not universe polymorphic
Arguments work_bearing_readiness {Job H H0 PState jr} arr_seq sched {H1}
work_bearing_readiness is transparent
Expands to: Constant prosa.analysis.definitions.work_bearing_readiness.work_bearing_readiness
Declared in library prosa.analysis.definitions.work_bearing_readiness, line 38, characters 13-35
@work_bearing_readiness
     : forall (Job : JobType) (H : JobArrival Job) (H0 : JobCost Job) (PState : ProcessorState Job),
       @JobReady Job PState H0 H -> arrival_sequence Job -> @schedule Job PState -> JLFP_policy Job -> Prop
```

Body:

```coq
work_bearing_readiness =
fun (Job : JobType) (H : JobArrival Job) (H0 : JobCost Job) (PState : ProcessorState Job)
  (jr : @JobReady Job PState H0 H) (arr_seq : arrival_sequence Job) (sched : @schedule Job PState)
  (H1 : JLFP_policy Job) =>
forall (j : Equality.sort Job) (t : instant),
@arrives_in Job arr_seq j ->
is_true (@pending Job PState sched H0 H j t) ->
exists j_hp : Equality.sort Job,
  @arrives_in Job arr_seq j_hp /\
  is_true (@job_ready Job PState H0 H jr sched j_hp t) /\ is_true (@hep_job Job H1 j_hp j)
     : forall {Job : JobType} {H : JobArrival Job} {H0 : JobCost Job} {PState : ProcessorState Job},
       @JobReady Job PState H0 H -> arrival_sequence Job -> @schedule Job PState -> JLFP_policy Job -> Prop

Arguments work_bearing_readiness {Job H H0 PState jr} arr_seq sched {H1}
```

## Lean

```lean
@Prosa.Analysis.Definitions.WorkBearingReadiness.work_bearing_readiness : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    [inst_1 : Prosa.Behavior.Job.JobArrival Job] →
      [inst_2 : Prosa.Behavior.Job.JobCost Job] →
        {PState : Prosa.Behavior.Schedule.ProcessorState Job} →
          [jr : Prosa.Behavior.Ready.JobReady Job PState] →
            Prosa.Behavior.Arrival_sequence.arrival_sequence Job →
              Prosa.Behavior.Schedule.schedule PState → [Prosa.Model.Priority.Definitions.JLFP_policy Job] → Prop
```

Body:

```lean
def Prosa.Analysis.Definitions.WorkBearingReadiness.work_bearing_readiness.{u_1, u_2, u_3} : {Job :
    Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    [inst_1 : Prosa.Behavior.Job.JobArrival Job] →
      [inst_2 : Prosa.Behavior.Job.JobCost Job] →
        {PState : Prosa.Behavior.Schedule.ProcessorState Job} →
          [jr : Prosa.Behavior.Ready.JobReady Job PState] →
            Prosa.Behavior.Arrival_sequence.arrival_sequence Job →
              Prosa.Behavior.Schedule.schedule PState → [Prosa.Model.Priority.Definitions.JLFP_policy Job] → Prop :=
fun {Job} [DecidableEq Job] [Prosa.Behavior.Job.JobArrival Job] [Prosa.Behavior.Job.JobCost Job] {PState}
    [Prosa.Behavior.Ready.JobReady Job PState] arr_seq sched [Prosa.Model.Priority.Definitions.JLFP_policy Job] =>
  ∀ (j : Job) (t : Prosa.Behavior.Time.instant),
    Prosa.Behavior.Arrival_sequence.arrives_in arr_seq j →
      Prosa.Behavior.Service.pending sched j t = true →
        ∃ j_hp,
          Prosa.Behavior.Arrival_sequence.arrives_in arr_seq j_hp ∧
            Prosa.Behavior.Ready.job_ready sched j_hp t = true ∧ Prosa.Model.Priority.Definitions.hep_job j_hp j = true
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Definitions_WorkBearingReadiness_work_bearing_readiness
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : 
          DecidableEq Job)
         (inst_6 : 
          Prosa_Behavior_Job_JobArrival Job
            inst_3)
         (inst_9 : 
          Prosa_Behavior_Job_JobCost Job
            inst_3)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3),
       Prosa_Behavior_Ready_JobReady Job
         inst_3 PState
         inst_9
         inst_6 ->
       Prosa_Behavior_Arrival_sequence_arrival_sequence Job
         inst_3 ->
       Prosa_Behavior_Schedule_schedule Job
         inst_3 PState ->
       Prosa_Model_Priority_Definitions_JLFP_policy Job
         inst_3 ->
       SProp
```

Body:

```coq
Prosa_Analysis_Definitions_WorkBearingReadiness_work_bearing_readiness@{u_1 u_2 u_3 Lean.u_1+1.0
Lean.max__u_1+1_u_2+1.0 Lean.max__u_1+1_u_2+2_u_3+2.0 Lean.u_2+1.0 Lean.u_3+1.0 Lean.u_1+2.0 Lean.u_3+2.0} =
fun (Job : Prosa_Behavior_Job_JobType)
  (inst_3 : DecidableEq Job)
  (inst_6 : 
   Prosa_Behavior_Job_JobArrival Job
     inst_3)
  (inst_9 : 
   Prosa_Behavior_Job_JobCost Job
     inst_3)
  (PState : Prosa_Behavior_Schedule_ProcessorState Job
              inst_3)
  (jr : Prosa_Behavior_Ready_JobReady Job
          inst_3 PState
          inst_9
          inst_6)
  (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
               inst_3)
  (sched : Prosa_Behavior_Schedule_schedule Job
             inst_3 PState)
  (inst_21 : 
   Prosa_Model_Priority_Definitions_JLFP_policy Job
     inst_3) =>
forall (j : Job) (t : Prosa_Behavior_Time_instant),
Prosa_Behavior_Arrival_sequence_arrives_in Job
  inst_3 arr_seq j ->
@eq Bool
  (Prosa_Behavior_Service_pending Job
     inst_3 PState sched
     inst_9
     inst_6 j t)
  Bool_true ->
Exists Job
  (fun j_hp : Job =>
   And
     (Prosa_Behavior_Arrival_sequence_arrives_in Job
        inst_3 arr_seq j_hp)
     (And
        (@eq Bool
           (Prosa_Behavior_Ready_JobReady_job_ready Job
              inst_3 PState
              inst_9
              inst_6 jr sched
              j_hp t)
           Bool_true)
        (@eq Bool
           (Prosa_Model_Priority_Definitions_JLFP_policy_hep_job Job
              inst_3
              inst_21 j_hp j)
           Bool_true)))
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : 
          DecidableEq Job)
         (inst_6 : 
          Prosa_Behavior_Job_JobArrival Job
            inst_3)
         (inst_9 : 
          Prosa_Behavior_Job_JobCost Job
            inst_3)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3),
       Prosa_Behavior_Ready_JobReady Job
         inst_3 PState
         inst_9
         inst_6 ->
       Prosa_Behavior_Arrival_sequence_arrival_sequence Job
         inst_3 ->
       Prosa_Behavior_Schedule_schedule Job
         inst_3 PState ->
       Prosa_Model_Priority_Definitions_JLFP_policy Job
         inst_3 ->
       SProp

Arguments Prosa_Analysis_Definitions_WorkBearingReadiness_work_bearing_readiness 
  Job inst_3
  inst_6
  inst_9 
  PState jr arr_seq sched
  inst_21
```
