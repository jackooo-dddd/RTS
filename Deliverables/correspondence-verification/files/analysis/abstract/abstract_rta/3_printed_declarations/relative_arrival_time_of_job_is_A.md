# `relative_arrival_time_of_job_is_A`

- Kind (Rocq): Definition
- Rocq: `prosa.analysis.abstract.abstract_rta.relative_arrival_time_of_job_is_A`
- Lean: `Prosa.Analysis.Abstract.AbstractRta.relative_arrival_time_of_job_is_A`
- Certificate: `relative_arrival_time_of_job_is_A_correspondence`

## Official Rocq

```coq
relative_arrival_time_of_job_is_A :
forall {Job : JobType},
JobArrival Job ->
JobCost Job ->
forall {PState : ProcessorState Job},
@schedule Job PState -> Interference Job -> InterferingWorkload Job -> Equality.sort Job -> duration -> Prop

relative_arrival_time_of_job_is_A is not universe polymorphic
Arguments relative_arrival_time_of_job_is_A {Job H2 jc PState} sched {H3 H4} j A
relative_arrival_time_of_job_is_A is transparent
Expands to: Constant prosa.analysis.abstract.abstract_rta.relative_arrival_time_of_job_is_A
Declared in library prosa.analysis.abstract.abstract_rta, line 105, characters 13-46
@relative_arrival_time_of_job_is_A
     : forall Job : JobType,
       JobArrival Job ->
       JobCost Job ->
       forall PState : ProcessorState Job,
       @schedule Job PState ->
       Interference Job -> InterferingWorkload Job -> Equality.sort Job -> duration -> Prop
```

Body:

```coq
relative_arrival_time_of_job_is_A =
fun (Job : JobType) (H2 : JobArrival Job) (jc : JobCost Job) (PState : ProcessorState Job)
  (sched : @schedule Job PState) (H3 : Interference Job) (H4 : InterferingWorkload Job)
  (j : Equality.sort Job) (A : duration) =>
forall t1 t2 : instant, @busy_interval Job H2 jc PState sched H3 H4 j t1 t2 -> A = @job_arrival Job H2 j - t1
     : forall {Job : JobType},
       JobArrival Job ->
       JobCost Job ->
       forall {PState : ProcessorState Job},
       @schedule Job PState ->
       Interference Job -> InterferingWorkload Job -> Equality.sort Job -> duration -> Prop

Arguments relative_arrival_time_of_job_is_A {Job H2 jc PState} sched {H3 H4} j A
```

## Lean

```lean
@Prosa.Analysis.Abstract.AbstractRta.relative_arrival_time_of_job_is_A : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    [Prosa.Behavior.Job.JobArrival Job] →
      [Prosa.Behavior.Job.JobCost Job] →
        {PState : Prosa.Behavior.Schedule.ProcessorState Job} →
          Prosa.Behavior.Schedule.schedule PState →
            [Prosa.Analysis.Abstract.Definitions.Interference Job] →
              [Prosa.Analysis.Abstract.Definitions.InterferingWorkload Job] → Job → Prosa.Behavior.Time.duration → Prop
```

Body:

```lean
def Prosa.Analysis.Abstract.AbstractRta.relative_arrival_time_of_job_is_A.{u_1, u_2, u_3} : {Job :
    Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    [Prosa.Behavior.Job.JobArrival Job] →
      [Prosa.Behavior.Job.JobCost Job] →
        {PState : Prosa.Behavior.Schedule.ProcessorState Job} →
          Prosa.Behavior.Schedule.schedule PState →
            [Prosa.Analysis.Abstract.Definitions.Interference Job] →
              [Prosa.Analysis.Abstract.Definitions.InterferingWorkload Job] →
                Job → Prosa.Behavior.Time.duration → Prop :=
fun {Job} [DecidableEq Job] [Prosa.Behavior.Job.JobArrival Job] [Prosa.Behavior.Job.JobCost Job] {PState} sched
    [Prosa.Analysis.Abstract.Definitions.Interference Job] [Prosa.Analysis.Abstract.Definitions.InterferingWorkload Job]
    j A =>
  ∀ (t1 t2 : Prosa.Behavior.Time.instant),
    Prosa.Analysis.Abstract.Definitions.busy_interval sched j t1 t2 → A = Prosa.Behavior.Job.job_arrival j - t1
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Abstract_AbstractRta_relative_arrival_time_of_job_is_A
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job),
       Prosa_Behavior_Job_JobArrival Job
         inst_3 ->
       Prosa_Behavior_Job_JobCost Job
         inst_3 ->
       forall
         PState : Prosa_Behavior_Schedule_ProcessorState Job
                    inst_3,
       Prosa_Behavior_Schedule_schedule Job
         inst_3 PState ->
       Prosa_Analysis_Abstract_Definitions_Interference Job
         inst_3 ->
       Prosa_Analysis_Abstract_Definitions_InterferingWorkload Job
         inst_3 ->
       Job -> Prosa_Behavior_Time_duration -> SProp
```

Body:

```coq
Prosa_Analysis_Abstract_AbstractRta_relative_arrival_time_of_job_is_A@{u_1 u_2 u_3 Lean.u_1+1.0
Lean.max__u_1+1_u_2+2_u_3+2.0 Lean.u_2+1.0 Lean.u_3+1.0 Lean.u_1+2.0 Lean.u_3+2.0} =
fun (Job : Prosa_Behavior_Job_JobType)
  (inst_3 : DecidableEq Job)
  (inst_6 : Prosa_Behavior_Job_JobArrival
                                                                                Job
                                                                                inst_3)
  (inst_9 : Prosa_Behavior_Job_JobCost Job
                                                                                inst_3)
  (PState : Prosa_Behavior_Schedule_ProcessorState Job
              inst_3)
  (sched : Prosa_Behavior_Schedule_schedule Job
             inst_3 PState)
  (inst_16 : Prosa_Analysis_Abstract_Definitions_Interference
                                                                                Job
                                                                                inst_3)
  (inst_19 : Prosa_Analysis_Abstract_Definitions_InterferingWorkload
                                                                                Job
                                                                                inst_3)
  (j : Job) (A : Prosa_Behavior_Time_duration) =>
forall t1 t2 : Prosa_Behavior_Time_instant,
Prosa_Analysis_Abstract_Definitions_busy_interval Job
  inst_3
  inst_16
  inst_19
  inst_6
  inst_9 PState sched j t1 t2 ->
@eq Prosa_Behavior_Time_duration A
  (HSub_hSub_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_instant Prosa_Behavior_Time_instant
     (instHSub_inst1 Prosa_Behavior_Time_instant instSubNat)
     (Prosa_Behavior_Job_JobArrival_job_arrival Job
        inst_3
        inst_6 j)
     t1)
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job),
       Prosa_Behavior_Job_JobArrival Job
         inst_3 ->
       Prosa_Behavior_Job_JobCost Job
         inst_3 ->
       forall
         PState : Prosa_Behavior_Schedule_ProcessorState Job
                    inst_3,
       Prosa_Behavior_Schedule_schedule Job
         inst_3 PState ->
       Prosa_Analysis_Abstract_Definitions_Interference Job
         inst_3 ->
       Prosa_Analysis_Abstract_Definitions_InterferingWorkload Job
         inst_3 ->
       Job -> Prosa_Behavior_Time_duration -> SProp

Arguments Prosa_Analysis_Abstract_AbstractRta_relative_arrival_time_of_job_is_A Job
  inst_3
  inst_6
  inst_9 PState 
  sched inst_16
  inst_19 j L
```
