import Prosa.Model.Processor.IdealUniExceed
import Validation.fixtures.translation_order.PiComputationInterface
import Validation.fixtures.translation_order.PreemptionTimeComputationInterface
import Validation.fixtures.translation_order.PriorityInversionComputationInterface
import Validation.fixtures.translation_order.ScheduleComputationInterface
import Validation.fixtures.translation_order.SbfBusyComputationInterface

/-!
Validation-only universe witnesses for the exceedance processor model: each definition applies one generic
processor-state-dependent constant used by the replayed certificate helpers at the exceedance processor model
(the same constants as the accepted overheads witnesses), so that every export whose root imports this module
contains it at the exceedance universe instance.  No statement or equation is added.
-/

namespace Prosa.Validation.ExceedanceInstWitness
open Prosa.Behavior.Job Prosa.Behavior.Schedule Prosa.Model.Processor.IdealUniExceed

noncomputable def w_Analysis_Definitions_BusyInterval_Classical_busy_interval (Job : JobType) [DecidableEq Job] := @Prosa.Analysis.Definitions.BusyInterval.Classical.busy_interval (Job := Job) (PState := exceedance_proc_state Job)
noncomputable def w_Analysis_Definitions_PriorityInversion_cumulative_priority_inversion (Job : JobType) [DecidableEq Job] := @Prosa.Analysis.Definitions.PriorityInversion.cumulative_priority_inversion (Job := Job) (PState := exceedance_proc_state Job)
noncomputable def w_Analysis_Definitions_PriorityInversion_cumulative_priority_inversion_cond (Job : JobType) [DecidableEq Job] := @Prosa.Analysis.Definitions.PriorityInversion.cumulative_priority_inversion_cond (Job := Job) (PState := exceedance_proc_state Job)
noncomputable def w_Analysis_Definitions_PriorityInversion_priority_inversion (Job : JobType) [DecidableEq Job] := @Prosa.Analysis.Definitions.PriorityInversion.priority_inversion (Job := Job) (PState := exceedance_proc_state Job)
noncomputable def w_Analysis_Definitions_PriorityInversion_priority_inversion_cond (Job : JobType) [DecidableEq Job] := @Prosa.Analysis.Definitions.PriorityInversion.priority_inversion_cond (Job := Job) (PState := exceedance_proc_state Job)
noncomputable def w_Analysis_Definitions_PriorityInversion_priority_inversion_cond_is_bounded_by (Job : JobType) [DecidableEq Job] := @Prosa.Analysis.Definitions.PriorityInversion.priority_inversion_cond_is_bounded_by (Job := Job) (PState := exceedance_proc_state Job)
noncomputable def w_Analysis_Definitions_PriorityInversion_priority_inversion_is_bounded_by (Job : JobType) [DecidableEq Job] := @Prosa.Analysis.Definitions.PriorityInversion.priority_inversion_is_bounded_by (Job := Job) (PState := exceedance_proc_state Job)
noncomputable def w_Analysis_Definitions_PriorityInversion_priority_inversion_of_job_cond_is_bounded_by (Job : JobType) [DecidableEq Job] := @Prosa.Analysis.Definitions.PriorityInversion.priority_inversion_of_job_cond_is_bounded_by (Job := Job) (PState := exceedance_proc_state Job)
noncomputable def w_Analysis_Definitions_PriorityInversion_priority_inversion_of_job_is_bounded_by (Job : JobType) [DecidableEq Job] := @Prosa.Analysis.Definitions.PriorityInversion.priority_inversion_of_job_is_bounded_by (Job := Job) (PState := exceedance_proc_state Job)
noncomputable def w_Behavior_Ready_JobReady_ready_implies_pending (Job : JobType) [DecidableEq Job] := @Prosa.Behavior.Ready.JobReady.ready_implies_pending (Job := Job) (PState := exceedance_proc_state Job)
noncomputable def w_Behavior_Ready_completed_jobs_dont_execute (Job : JobType) [DecidableEq Job] := @Prosa.Behavior.Ready.completed_jobs_dont_execute (Job := Job) (PState := exceedance_proc_state Job)
noncomputable def w_Behavior_Ready_jobs_must_arrive_to_execute (Job : JobType) [DecidableEq Job] := @Prosa.Behavior.Ready.jobs_must_arrive_to_execute (Job := Job) (PState := exceedance_proc_state Job)
noncomputable def w_Behavior_Service_service (Job : JobType) [DecidableEq Job] := @Prosa.Behavior.Service.service (Job := Job) (PState := exceedance_proc_state Job)
noncomputable def w_Behavior_Service_service_during (Job : JobType) [DecidableEq Job] := @Prosa.Behavior.Service.service_during (Job := Job) (PState := exceedance_proc_state Job)
noncomputable def w_Model_Aggregate_ServiceOfJobs_service_of_higher_or_equal_priority_jobs (Job : JobType) [DecidableEq Job] := @Prosa.Model.Aggregate.ServiceOfJobs.service_of_higher_or_equal_priority_jobs (Job := Job) (PState := exceedance_proc_state Job)
noncomputable def w_Model_Aggregate_ServiceOfJobs_service_of_jobs (Job : JobType) [DecidableEq Job] := @Prosa.Model.Aggregate.ServiceOfJobs.service_of_jobs (Job := Job) (PState := exceedance_proc_state Job)
noncomputable def w_Model_Aggregate_ServiceOfJobs_total_service_of_jobs_in (Job : JobType) [DecidableEq Job] := @Prosa.Model.Aggregate.ServiceOfJobs.total_service_of_jobs_in (Job := Job) (PState := exceedance_proc_state Job)
noncomputable def w_Model_Preemption_Parameter_execution_starts_with_preemption_point (Job : JobType) [DecidableEq Job] := @Prosa.Model.Preemption.Parameter.execution_starts_with_preemption_point (Job := Job) (PState := exceedance_proc_state Job)
noncomputable def w_Model_Preemption_Parameter_no_superfluous_preemptions (Job : JobType) [DecidableEq Job] := @Prosa.Model.Preemption.Parameter.no_superfluous_preemptions (Job := Job) (PState := exceedance_proc_state Job)
noncomputable def w_Model_Preemption_Parameter_not_preemptive_implies_scheduled (Job : JobType) [DecidableEq Job] := @Prosa.Model.Preemption.Parameter.not_preemptive_implies_scheduled (Job := Job) (PState := exceedance_proc_state Job)
noncomputable def w_Model_Preemption_Parameter_preempted_at (Job : JobType) [DecidableEq Job] := @Prosa.Model.Preemption.Parameter.preempted_at (Job := Job) (PState := exceedance_proc_state Job)
noncomputable def w_Model_Preemption_Parameter_valid_preemption_model (Job : JobType) [DecidableEq Job] := @Prosa.Model.Preemption.Parameter.valid_preemption_model (Job := Job) (PState := exceedance_proc_state Job)
noncomputable def w_Model_Processor_PlatformProperties_ideal_progress_proc_model (Job : JobType) [DecidableEq Job] := @Prosa.Model.Processor.PlatformProperties.ideal_progress_proc_model (Job := Job) (PState := exceedance_proc_state Job)
noncomputable def w_Model_Processor_PlatformProperties_unit_service_proc_model (Job : JobType) [DecidableEq Job] := @Prosa.Model.Processor.PlatformProperties.unit_service_proc_model (Job := Job) (PState := exceedance_proc_state Job)
noncomputable def w_Model_Schedule_PreemptionTime_preemption_time (Job : JobType) [DecidableEq Job] := @Prosa.Model.Schedule.PreemptionTime.preemption_time (Job := Job) (PState := exceedance_proc_state Job)
noncomputable def w_Model_Schedule_PriorityDriven_respects_FP_policy_at_preemption_point (Job : JobType) [DecidableEq Job] := @Prosa.Model.Schedule.PriorityDriven.respects_FP_policy_at_preemption_point (Job := Job) (PState := exceedance_proc_state Job)
noncomputable def w_Model_Schedule_PriorityDriven_respects_JLDP_policy_at_preemption_point (Job : JobType) [DecidableEq Job] := @Prosa.Model.Schedule.PriorityDriven.respects_JLDP_policy_at_preemption_point (Job := Job) (PState := exceedance_proc_state Job)
noncomputable def w_Model_Schedule_PriorityDriven_respects_JLFP_policy_at_preemption_point (Job : JobType) [DecidableEq Job] := @Prosa.Model.Schedule.PriorityDriven.respects_JLFP_policy_at_preemption_point (Job := Job) (PState := exceedance_proc_state Job)
noncomputable def w_Model_Schedule_Scheduled_is_idle (Job : JobType) [DecidableEq Job] := @Prosa.Model.Schedule.Scheduled.is_idle (Job := Job) (PState := exceedance_proc_state Job)
noncomputable def w_Model_Schedule_Scheduled_scheduled_jobs_at (Job : JobType) [DecidableEq Job] := @Prosa.Model.Schedule.Scheduled.scheduled_jobs_at (Job := Job) (PState := exceedance_proc_state Job)
noncomputable def w_Model_Task_Preemption_Parameters_valid_model_with_bounded_nonpreemptive_segments (Job : JobType) [DecidableEq Job] := @Prosa.Model.Task.Preemption.Parameters.valid_model_with_bounded_nonpreemptive_segments (Job := Job) (PState := exceedance_proc_state Job)
noncomputable def w_Validation_PreemptionTimeInterface_production_preemption_time_none (Job : JobType) [DecidableEq Job] := @Prosa.Validation.PreemptionTimeInterface.production_preemption_time_none (Job := Job) (PState := exceedance_proc_state Job)
noncomputable def w_Validation_PreemptionTimeInterface_production_preemption_time_some (Job : JobType) [DecidableEq Job] := @Prosa.Validation.PreemptionTimeInterface.production_preemption_time_some (Job := Job) (PState := exceedance_proc_state Job)
noncomputable def w_Validation_PreemptionTimeInterface_production_scheduled_job_at_eq (Job : JobType) [DecidableEq Job] := @Prosa.Validation.PreemptionTimeInterface.production_scheduled_job_at_eq (Job := Job) (PState := exceedance_proc_state Job)
noncomputable def w_Validation_PriorityInversionInterface_cumulPriorityInversionCondProjection (Job : JobType) [DecidableEq Job] := @Prosa.Validation.PriorityInversionInterface.cumulPriorityInversionCondProjection (Job := Job) (PState := exceedance_proc_state Job)
noncomputable def w_Validation_PriorityInversionInterface_cumulPriorityInversionProjection (Job : JobType) [DecidableEq Job] := @Prosa.Validation.PriorityInversionInterface.cumulPriorityInversionProjection (Job := Job) (PState := exceedance_proc_state Job)
noncomputable def w_Validation_ScheduleInterface_coreEnumeration (Job : JobType) [DecidableEq Job] := @Prosa.Validation.ScheduleInterface.coreEnumeration (Job := Job) (PState := exceedance_proc_state Job)
noncomputable def w_Validation_ScheduleInterface_coreEnumeration_complete (Job : JobType) [DecidableEq Job] := @Prosa.Validation.ScheduleInterface.coreEnumeration_complete (Job := Job) (PState := exceedance_proc_state Job)
noncomputable def w_Validation_ScheduleInterface_coreEnumeration_nodup (Job : JobType) [DecidableEq Job] := @Prosa.Validation.ScheduleInterface.coreEnumeration_nodup (Job := Job) (PState := exceedance_proc_state Job)
noncomputable def w_Validation_ScheduleInterface_production_scheduled_in_eq_true_iff (Job : JobType) [DecidableEq Job] := @Prosa.Validation.ScheduleInterface.production_scheduled_in_eq_true_iff (Job := Job) (PState := exceedance_proc_state Job)
noncomputable def w_Validation_ScheduleInterface_production_service_in_as_list_sum (Job : JobType) [DecidableEq Job] := @Prosa.Validation.ScheduleInterface.production_service_in_as_list_sum (Job := Job) (PState := exceedance_proc_state Job)
noncomputable def w_Validation_ScheduleInterface_production_supply_in_as_list_sum (Job : JobType) [DecidableEq Job] := @Prosa.Validation.ScheduleInterface.production_supply_in_as_list_sum (Job := Job) (PState := exceedance_proc_state Job)
noncomputable def w_Analysis_Definitions_BusyInterval_Classical_busy_interval_prefix (Job : JobType) [DecidableEq Job] := @Prosa.Analysis.Definitions.BusyInterval.Classical.busy_interval_prefix (Job := Job) (PState := exceedance_proc_state Job)
noncomputable def w_Analysis_Definitions_BusyInterval_Classical_quiet_time (Job : JobType) [DecidableEq Job] := @Prosa.Analysis.Definitions.BusyInterval.Classical.quiet_time (Job := Job) (PState := exceedance_proc_state Job)
noncomputable def w_Analysis_Definitions_WorkBearingReadiness_work_bearing_readiness (Job : JobType) [DecidableEq Job] := @Prosa.Analysis.Definitions.WorkBearingReadiness.work_bearing_readiness (Job := Job) (PState := exceedance_proc_state Job)
noncomputable def w_Behavior_Ready_backlogged (Job : JobType) [DecidableEq Job] := @Prosa.Behavior.Ready.backlogged (Job := Job) (PState := exceedance_proc_state Job)
noncomputable def w_Behavior_Ready_jobs_come_from_arrival_sequence (Job : JobType) [DecidableEq Job] := @Prosa.Behavior.Ready.jobs_come_from_arrival_sequence (Job := Job) (PState := exceedance_proc_state Job)
noncomputable def w_Behavior_Ready_jobs_must_be_ready_to_execute (Job : JobType) [DecidableEq Job] := @Prosa.Behavior.Ready.jobs_must_be_ready_to_execute (Job := Job) (PState := exceedance_proc_state Job)
noncomputable def w_Behavior_Ready_valid_schedule (Job : JobType) [DecidableEq Job] := @Prosa.Behavior.Ready.valid_schedule (Job := Job) (PState := exceedance_proc_state Job)
noncomputable def w_Behavior_Service_completed_by (Job : JobType) [DecidableEq Job] := @Prosa.Behavior.Service.completed_by (Job := Job) (PState := exceedance_proc_state Job)
noncomputable def w_Behavior_Service_pending (Job : JobType) [DecidableEq Job] := @Prosa.Behavior.Service.pending (Job := Job) (PState := exceedance_proc_state Job)
noncomputable def w_Behavior_Service_scheduled_at (Job : JobType) [DecidableEq Job] := @Prosa.Behavior.Service.scheduled_at (Job := Job) (PState := exceedance_proc_state Job)
noncomputable def w_Behavior_Service_service_at (Job : JobType) [DecidableEq Job] := @Prosa.Behavior.Service.service_at (Job := Job) (PState := exceedance_proc_state Job)
noncomputable def w_Model_Processor_PlatformProperties_uniprocessor_model (Job : JobType) [DecidableEq Job] := @Prosa.Model.Processor.PlatformProperties.uniprocessor_model (Job := Job) (PState := exceedance_proc_state Job)
noncomputable def w_Model_Schedule_WorkConserving_work_conserving (Job : JobType) [DecidableEq Job] := @Prosa.Model.Schedule.WorkConserving.work_conserving (Job := Job) (PState := exceedance_proc_state Job)
noncomputable def w_Validation_ServiceInterface_serviceDuringProjection (Job : JobType) [DecidableEq Job] := @Prosa.Validation.ServiceInterface.serviceDuringProjection (Job := Job) (PState := exceedance_proc_state Job)
noncomputable def w_Behavior_Schedule_schedule (Job : JobType) [DecidableEq Job] := @Prosa.Behavior.Schedule.schedule (Job := Job) (PState := exceedance_proc_state Job)
noncomputable def w_ProcessorState_Core (Job : JobType) [DecidableEq Job] := @Prosa.Behavior.Schedule.ProcessorState.Core Job _ (exceedance_proc_state Job)
noncomputable def w_ProcessorState_State (Job : JobType) [DecidableEq Job] := @Prosa.Behavior.Schedule.ProcessorState.State Job _ (exceedance_proc_state Job)
noncomputable def w_ProcessorState_coreDecidableEq (Job : JobType) [DecidableEq Job] := @Prosa.Behavior.Schedule.ProcessorState.coreDecidableEq Job _ (exceedance_proc_state Job)
noncomputable def w_ProcessorState_scheduled_in (Job : JobType) [DecidableEq Job] := @Prosa.Behavior.Schedule.ProcessorState.scheduled_in Job _ (exceedance_proc_state Job)
noncomputable def w_ProcessorState_scheduled_on (Job : JobType) [DecidableEq Job] := @Prosa.Behavior.Schedule.ProcessorState.scheduled_on Job _ (exceedance_proc_state Job)
noncomputable def w_ProcessorState_service_in (Job : JobType) [DecidableEq Job] := @Prosa.Behavior.Schedule.ProcessorState.service_in Job _ (exceedance_proc_state Job)
noncomputable def w_ProcessorState_service_on (Job : JobType) [DecidableEq Job] := @Prosa.Behavior.Schedule.ProcessorState.service_on Job _ (exceedance_proc_state Job)
noncomputable def w_ProcessorState_supply_in (Job : JobType) [DecidableEq Job] := @Prosa.Behavior.Schedule.ProcessorState.supply_in Job _ (exceedance_proc_state Job)
noncomputable def w_ProcessorState_supply_on (Job : JobType) [DecidableEq Job] := @Prosa.Behavior.Schedule.ProcessorState.supply_on Job _ (exceedance_proc_state Job)
noncomputable def w_JobReady_job_ready (Job : JobType) [DecidableEq Job] [Prosa.Behavior.Job.JobCost Job] [Prosa.Behavior.Job.JobArrival Job]
    (jr : Prosa.Behavior.Ready.JobReady Job (exceedance_proc_state Job)) := jr.job_ready

end Prosa.Validation.ExceedanceInstWitness
