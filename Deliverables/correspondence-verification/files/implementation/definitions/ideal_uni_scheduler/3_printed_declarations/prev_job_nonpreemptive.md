# `prev_job_nonpreemptive`

- Kind (Rocq): Definition
- Rocq: `prosa.implementation.definitions.ideal_uni_scheduler.prev_job_nonpreemptive`
- Lean: `Prosa.Implementation.Definitions.IdealUniScheduler.prev_job_nonpreemptive`
- Certificate: `prev_job_nonpreemptive_correspondence`

## Official Rocq

```coq
prev_job_nonpreemptive :
forall {Job : JobType} {JC : JobCost Job} {JA : JobArrival Job},
@JobReady Job (processor_state Job) JC JA ->
JobPreemptable Job -> @schedule Job (processor_state Job) -> instant -> bool

prev_job_nonpreemptive is not universe polymorphic
Arguments prev_job_nonpreemptive {Job JC JA RM H} sched_prefix t
prev_job_nonpreemptive is transparent
Expands to: Constant prosa.implementation.definitions.ideal_uni_scheduler.prev_job_nonpreemptive
Declared in library prosa.implementation.definitions.ideal_uni_scheduler, line 59, characters 17-39
@prev_job_nonpreemptive
     : forall (Job : JobType) (JC : JobCost Job) (JA : JobArrival Job),
       @JobReady Job (processor_state Job) JC JA ->
       JobPreemptable Job -> @schedule Job (processor_state Job) -> instant -> bool
```

Body:

```coq
prev_job_nonpreemptive =
fun (Job : JobType) (JC : JobCost Job) (JA : JobArrival Job) (RM : @JobReady Job (processor_state Job) JC JA)
  (H : JobPreemptable Job) (sched_prefix : @schedule Job (processor_state Job)) (t : instant) =>
match t with
| 0 => false
| t'.+1 =>
    match sched_prefix t' with
    | @Some _ j =>
        @job_ready Job (processor_state Job) JC JA RM sched_prefix j t &&
        ~~ @job_preemptable Job H j (@service Job (processor_state Job) sched_prefix j t)
    | @None _ => false
    end
end
     : forall {Job : JobType} {JC : JobCost Job} {JA : JobArrival Job},
       @JobReady Job (processor_state Job) JC JA ->
       JobPreemptable Job -> @schedule Job (processor_state Job) -> instant -> bool

Arguments prev_job_nonpreemptive {Job JC JA RM H} sched_prefix t
```

## Lean

```lean
@Prosa.Implementation.Definitions.IdealUniScheduler.prev_job_nonpreemptive : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    [inst_1 : Prosa.Behavior.Job.JobCost Job] →
      [inst_2 : Prosa.Behavior.Job.JobArrival Job] →
        [Prosa.Behavior.Ready.JobReady Job (Prosa.Model.Processor.Ideal.processor_state Job)] →
          [Prosa.Model.Preemption.Parameter.JobPreemptable Job] →
            Prosa.Behavior.Schedule.schedule (Prosa.Model.Processor.Ideal.processor_state Job) →
              Prosa.Behavior.Time.instant → Bool
```

Body:

```lean
def Prosa.Implementation.Definitions.IdealUniScheduler.prev_job_nonpreemptive.{u_1} : {Job :
    Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    [inst_1 : Prosa.Behavior.Job.JobCost Job] →
      [inst_2 : Prosa.Behavior.Job.JobArrival Job] →
        [Prosa.Behavior.Ready.JobReady Job (Prosa.Model.Processor.Ideal.processor_state Job)] →
          [Prosa.Model.Preemption.Parameter.JobPreemptable Job] →
            Prosa.Behavior.Schedule.schedule (Prosa.Model.Processor.Ideal.processor_state Job) →
              Prosa.Behavior.Time.instant → Bool :=
fun {Job} [DecidableEq Job] [Prosa.Behavior.Job.JobCost Job] [Prosa.Behavior.Job.JobArrival Job]
    [Prosa.Behavior.Ready.JobReady Job (Prosa.Model.Processor.Ideal.processor_state Job)]
    [Prosa.Model.Preemption.Parameter.JobPreemptable Job] sched_prefix t =>
  match t with
  | 0 => false
  | Nat.succ t' =>
    match sched_prefix t' with
    | some j =>
      Prosa.Behavior.Ready.job_ready sched_prefix j t &&
        !Prosa.Model.Preemption.Parameter.job_preemptable j (Prosa.Behavior.Service.service sched_prefix j t)
    | none => false
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Definitions_IdealUniScheduler_prev_job_nonpreemptive
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : 
          DecidableEq Job)
         (inst_6 : 
          Prosa_Behavior_Job_JobCost Job
            inst_3)
         (inst_9 : 
          Prosa_Behavior_Job_JobArrival Job
            inst_3),
       Prosa_Behavior_Ready_JobReady_inst4 Job
         inst_3
         (Prosa_Model_Processor_Ideal_processor_state Job
            inst_3)
         inst_6
         inst_9 ->
       Prosa_Model_Preemption_Parameter_JobPreemptable Job
         inst_3 ->
       Prosa_Behavior_Schedule_schedule_inst4 Job
         inst_3
         (Prosa_Model_Processor_Ideal_processor_state Job
            inst_3) ->
       Prosa_Behavior_Time_instant -> Bool
```

Body:

```coq
Prosa_Implementation_Definitions_IdealUniScheduler_prev_job_nonpreemptive@{u_1 Lean.u_1+1.0 Lean.u_1+2.0} =
fun (Job : Prosa_Behavior_Job_JobType)
  (inst_3 : DecidableEq Job)
  (inst_6 : 
   Prosa_Behavior_Job_JobCost Job
     inst_3)
  (inst_9 : 
   Prosa_Behavior_Job_JobArrival Job
     inst_3)
  (inst_12 : 
   Prosa_Behavior_Ready_JobReady_inst4 Job
     inst_3
     (Prosa_Model_Processor_Ideal_processor_state Job
        inst_3)
     inst_6
     inst_9)
  (inst_19 : 
   Prosa_Model_Preemption_Parameter_JobPreemptable Job
     inst_3)
  (sched_prefix : Prosa_Behavior_Schedule_schedule_inst4 Job
                    inst_3
                    (Prosa_Model_Processor_Ideal_processor_state Job
                       inst_3))
  (t : Prosa_Behavior_Time_instant) =>
Prosa_Implementation_Definitions_IdealUniScheduler_prev_job_nonpreemptive_match_3
  (fun _ : Prosa_Behavior_Time_instant => Bool) t (fun _ : Unit => Bool_false)
  (fun t' : Prosa_Behavior_Time_instant =>
   Prosa_Implementation_Definitions_IdealUniScheduler_prev_job_nonpreemptive_match_1 Job
     inst_3
     (fun
        _ : Prosa_Behavior_Schedule_ProcessorState_State_inst2 Job
              inst_3
              (Prosa_Model_Processor_Ideal_processor_state Job
                 inst_3) =>
      Bool)
     (sched_prefix t')
     (fun j : Job =>
      Bool_and
        (Prosa_Behavior_Ready_JobReady_job_ready_inst4 Job
           inst_3
           (Prosa_Model_Processor_Ideal_processor_state Job
              inst_3)
           inst_6
           inst_9
           inst_12
           sched_prefix j t)
        (Bool_not
           (Prosa_Model_Preemption_Parameter_JobPreemptable_job_preemptable Job
              inst_3
              inst_19 j
              (Prosa_Behavior_Service_service_inst4 Job
                 inst_3
                 (Prosa_Model_Processor_Ideal_processor_state Job
                    inst_3)
                 sched_prefix j t))))
     (fun _ : Unit => Bool_false))
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : 
          DecidableEq Job)
         (inst_6 : 
          Prosa_Behavior_Job_JobCost Job
            inst_3)
         (inst_9 : 
          Prosa_Behavior_Job_JobArrival Job
            inst_3),
       Prosa_Behavior_Ready_JobReady_inst4 Job
         inst_3
         (Prosa_Model_Processor_Ideal_processor_state Job
            inst_3)
         inst_6
         inst_9 ->
       Prosa_Model_Preemption_Parameter_JobPreemptable Job
         inst_3 ->
       Prosa_Behavior_Schedule_schedule_inst4 Job
         inst_3
         (Prosa_Model_Processor_Ideal_processor_state Job
            inst_3) ->
       Prosa_Behavior_Time_instant -> Bool

Arguments Prosa_Implementation_Definitions_IdealUniScheduler_prev_job_nonpreemptive 
  Job inst_3
  inst_6
  inst_9
  inst_12
  inst_19 
  sched_prefix t
```
