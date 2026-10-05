# `overhead_resource_model`

- Kind (Rocq): Definition
- Rocq: `prosa.model.processor.overhead_resource_model.overhead_resource_model`
- Lean: `Prosa.Model.Processor.OverheadResourceModel.overhead_resource_model`
- Certificate: `overhead_resource_model_correspondence`

## Official Rocq

```coq
overhead_resource_model :
forall {Job : JobType}, @schedule Job (processor_state Job) -> duration -> duration -> duration -> Prop

overhead_resource_model is not universe polymorphic
Arguments overhead_resource_model {Job} sched DB CSB CRPDB
overhead_resource_model is transparent
Expands to: Constant prosa.model.processor.overhead_resource_model.overhead_resource_model
Declared in library prosa.model.processor.overhead_resource_model, line 100, characters 13-36
@overhead_resource_model
     : forall Job : JobType, @schedule Job (processor_state Job) -> duration -> duration -> duration -> Prop
```

Body:

```coq
overhead_resource_model =
fun (Job : JobType) (sched : @schedule Job (processor_state Job)) (DB CSB CRPDB : duration) =>
@time_spent_in_dispatch_is_bounded_by Job sched DB /\
@time_spent_in_context_switch_is_bounded_by Job sched CSB /\
@time_spent_in_CRPD_is_bounded_by Job sched CRPDB /\
@dispatch_precedes_context_switch Job sched /\
@context_switch_precedes_progress Job sched /\ @context_switch_precedes_CRPD Job sched
     : forall {Job : JobType},
       @schedule Job (processor_state Job) -> duration -> duration -> duration -> Prop

Arguments overhead_resource_model {Job} sched DB CSB CRPDB
```

## Lean

```lean
@Prosa.Model.Processor.OverheadResourceModel.overhead_resource_model : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    Prosa.Behavior.Schedule.schedule (Prosa.Model.Processor.Overheads.processor_state Job) →
      Prosa.Behavior.Time.duration → Prosa.Behavior.Time.duration → Prosa.Behavior.Time.duration → Prop
```

Body:

```lean
def Prosa.Model.Processor.OverheadResourceModel.overhead_resource_model.{u_1} : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    Prosa.Behavior.Schedule.schedule (Prosa.Model.Processor.Overheads.processor_state Job) →
      Prosa.Behavior.Time.duration → Prosa.Behavior.Time.duration → Prosa.Behavior.Time.duration → Prop :=
fun {Job} [DecidableEq Job] sched DB CSB CRPDB =>
  Prosa.Model.Processor.OverheadResourceModel.time_spent_in_dispatch_is_bounded_by sched DB ∧
    Prosa.Model.Processor.OverheadResourceModel.time_spent_in_context_switch_is_bounded_by sched CSB ∧
      Prosa.Model.Processor.OverheadResourceModel.time_spent_in_CRPD_is_bounded_by sched CRPDB ∧
        Prosa.Model.Processor.OverheadResourceModel.dispatch_precedes_context_switch sched ∧
          Prosa.Model.Processor.OverheadResourceModel.context_switch_precedes_progress sched ∧
            Prosa.Model.Processor.OverheadResourceModel.context_switch_precedes_CRPD sched
```

## Lean, imported into Rocq

```coq
Prosa_Model_Processor_OverheadResourceModel_overhead_resource_model
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job),
       Prosa_Behavior_Schedule_schedule_inst4 Job
         inst_3
         (Prosa_Model_Processor_Overheads_processor_state Job
            inst_3) ->
       Prosa_Behavior_Time_duration -> Prosa_Behavior_Time_duration -> Prosa_Behavior_Time_duration -> SProp
```

Body:

```coq
Prosa_Model_Processor_OverheadResourceModel_overhead_resource_model@{u_1 Lean.u_1+1.0 Lean.u_1+2.0} =
fun (Job : Prosa_Behavior_Job_JobType)
  (inst_3 : DecidableEq Job)
  (sched : Prosa_Behavior_Schedule_schedule_inst4 Job
             inst_3
             (Prosa_Model_Processor_Overheads_processor_state Job
                inst_3))
  (DB CSB CRPDB : Prosa_Behavior_Time_duration) =>
And
  (Prosa_Model_Processor_OverheadResourceModel_time_spent_in_dispatch_is_bounded_by Job
     inst_3 sched DB)
  (And
     (Prosa_Model_Processor_OverheadResourceModel_time_spent_in_context_switch_is_bounded_by Job
        inst_3 sched CSB)
     (And
        (Prosa_Model_Processor_OverheadResourceModel_time_spent_in_CRPD_is_bounded_by Job
           inst_3 sched CRPDB)
        (And
           (Prosa_Model_Processor_OverheadResourceModel_dispatch_precedes_context_switch Job
              inst_3 sched)
           (And
              (Prosa_Model_Processor_OverheadResourceModel_context_switch_precedes_progress Job
                 inst_3 sched)
              (Prosa_Model_Processor_OverheadResourceModel_context_switch_precedes_CRPD Job
                 inst_3 sched)))))
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job),
       Prosa_Behavior_Schedule_schedule_inst4 Job
         inst_3
         (Prosa_Model_Processor_Overheads_processor_state Job
            inst_3) ->
       Prosa_Behavior_Time_duration -> Prosa_Behavior_Time_duration -> Prosa_Behavior_Time_duration -> SProp

Arguments Prosa_Model_Processor_OverheadResourceModel_overhead_resource_model Job
  inst_3 
  sched DB CSB CRPDB
```
