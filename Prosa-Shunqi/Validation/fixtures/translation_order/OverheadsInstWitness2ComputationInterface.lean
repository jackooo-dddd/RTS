import Validation.fixtures.translation_order.OverheadsInstWitnessComputationInterface

/-!
Second set of validation-only universe witnesses for the overheads processor model: every generic
processor-state-dependent constant used by the replayed certificate helpers that is not already witnessed by
`OverheadsInstWitnessComputationInterface` is applied at the overheads processor model, so that every export whose
root imports this module contains it at the overheads universe instance. No statement or equation is added.
-/

namespace Prosa.Validation.OverheadsInstWitness2
open Prosa.Behavior.Job Prosa.Behavior.Schedule Prosa.Model.Processor.Overheads

noncomputable def w_Analysis_Definitions_BusyInterval_Classical_busy_interval_prefix (Job : JobType) [DecidableEq Job] := @Prosa.Analysis.Definitions.BusyInterval.Classical.busy_interval_prefix (Job := Job) (PState := processor_state Job)
noncomputable def w_Analysis_Definitions_BusyInterval_Classical_quiet_time (Job : JobType) [DecidableEq Job] := @Prosa.Analysis.Definitions.BusyInterval.Classical.quiet_time (Job := Job) (PState := processor_state Job)
noncomputable def w_Analysis_Definitions_WorkBearingReadiness_work_bearing_readiness (Job : JobType) [DecidableEq Job] := @Prosa.Analysis.Definitions.WorkBearingReadiness.work_bearing_readiness (Job := Job) (PState := processor_state Job)
noncomputable def w_Behavior_Ready_backlogged (Job : JobType) [DecidableEq Job] := @Prosa.Behavior.Ready.backlogged (Job := Job) (PState := processor_state Job)
noncomputable def w_Behavior_Ready_jobs_come_from_arrival_sequence (Job : JobType) [DecidableEq Job] := @Prosa.Behavior.Ready.jobs_come_from_arrival_sequence (Job := Job) (PState := processor_state Job)
noncomputable def w_Behavior_Ready_jobs_must_be_ready_to_execute (Job : JobType) [DecidableEq Job] := @Prosa.Behavior.Ready.jobs_must_be_ready_to_execute (Job := Job) (PState := processor_state Job)
noncomputable def w_Behavior_Ready_valid_schedule (Job : JobType) [DecidableEq Job] := @Prosa.Behavior.Ready.valid_schedule (Job := Job) (PState := processor_state Job)
noncomputable def w_Behavior_Service_completed_by (Job : JobType) [DecidableEq Job] := @Prosa.Behavior.Service.completed_by (Job := Job) (PState := processor_state Job)
noncomputable def w_Behavior_Service_pending (Job : JobType) [DecidableEq Job] := @Prosa.Behavior.Service.pending (Job := Job) (PState := processor_state Job)
noncomputable def w_Behavior_Service_scheduled_at (Job : JobType) [DecidableEq Job] := @Prosa.Behavior.Service.scheduled_at (Job := Job) (PState := processor_state Job)
noncomputable def w_Behavior_Service_service_at (Job : JobType) [DecidableEq Job] := @Prosa.Behavior.Service.service_at (Job := Job) (PState := processor_state Job)
noncomputable def w_Model_Processor_PlatformProperties_uniprocessor_model (Job : JobType) [DecidableEq Job] := @Prosa.Model.Processor.PlatformProperties.uniprocessor_model (Job := Job) (PState := processor_state Job)
noncomputable def w_Model_Schedule_WorkConserving_work_conserving (Job : JobType) [DecidableEq Job] := @Prosa.Model.Schedule.WorkConserving.work_conserving (Job := Job) (PState := processor_state Job)
noncomputable def w_Validation_ServiceInterface_serviceDuringProjection (Job : JobType) [DecidableEq Job] := @Prosa.Validation.ServiceInterface.serviceDuringProjection (Job := Job) (PState := processor_state Job)
noncomputable def w_Behavior_Schedule_schedule (Job : JobType) [DecidableEq Job] := @Prosa.Behavior.Schedule.schedule (Job := Job) (PState := processor_state Job)
noncomputable def w_ProcessorState_Core (Job : JobType) [DecidableEq Job] := @Prosa.Behavior.Schedule.ProcessorState.Core Job _ (processor_state Job)
noncomputable def w_ProcessorState_State (Job : JobType) [DecidableEq Job] := @Prosa.Behavior.Schedule.ProcessorState.State Job _ (processor_state Job)
noncomputable def w_ProcessorState_coreDecidableEq (Job : JobType) [DecidableEq Job] := @Prosa.Behavior.Schedule.ProcessorState.coreDecidableEq Job _ (processor_state Job)
noncomputable def w_ProcessorState_scheduled_in (Job : JobType) [DecidableEq Job] := @Prosa.Behavior.Schedule.ProcessorState.scheduled_in Job _ (processor_state Job)
noncomputable def w_ProcessorState_scheduled_on (Job : JobType) [DecidableEq Job] := @Prosa.Behavior.Schedule.ProcessorState.scheduled_on Job _ (processor_state Job)
noncomputable def w_ProcessorState_service_in (Job : JobType) [DecidableEq Job] := @Prosa.Behavior.Schedule.ProcessorState.service_in Job _ (processor_state Job)
noncomputable def w_ProcessorState_service_on (Job : JobType) [DecidableEq Job] := @Prosa.Behavior.Schedule.ProcessorState.service_on Job _ (processor_state Job)
noncomputable def w_ProcessorState_supply_in (Job : JobType) [DecidableEq Job] := @Prosa.Behavior.Schedule.ProcessorState.supply_in Job _ (processor_state Job)
noncomputable def w_ProcessorState_supply_on (Job : JobType) [DecidableEq Job] := @Prosa.Behavior.Schedule.ProcessorState.supply_on Job _ (processor_state Job)
noncomputable def w_JobReady_job_ready (Job : JobType) [DecidableEq Job] [Prosa.Behavior.Job.JobCost Job] [Prosa.Behavior.Job.JobArrival Job]
    (jr : Prosa.Behavior.Ready.JobReady Job (processor_state Job)) := jr.job_ready

end Prosa.Validation.OverheadsInstWitness2
