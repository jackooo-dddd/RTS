import Validation.fixtures.translation_order.OverheadsScheduleComputationInterface
import Validation.fixtures.translation_order.PreemptionTimeComputationInterface
import Validation.fixtures.translation_order.PriorityInversionComputationInterface
import Validation.fixtures.translation_order.ScheduleComputationInterface

/-!
Validation-only universe witnesses for `analysis/facts/model/overheads/schedule.v`: each definition applies one
generic processor-state-dependent constant at the overheads processor model, so that the exported closure contains
that constant at the overheads universe instance (the Rocq import then provides its specialised copy, and the
generic certificate helpers replay over it).  No statement or equation is added.
-/

namespace Prosa.Validation.OverheadsInstWitness
open Prosa.Behavior.Job Prosa.Model.Processor.Overheads

noncomputable def w_Analysis_Definitions_BusyInterval_Classical_busy_interval (Job : JobType) [DecidableEq Job] := @Prosa.Analysis.Definitions.BusyInterval.Classical.busy_interval (Job := Job) (PState := processor_state Job)
noncomputable def w_Analysis_Definitions_PriorityInversion_cumulative_priority_inversion (Job : JobType) [DecidableEq Job] := @Prosa.Analysis.Definitions.PriorityInversion.cumulative_priority_inversion (Job := Job) (PState := processor_state Job)
noncomputable def w_Analysis_Definitions_PriorityInversion_cumulative_priority_inversion_cond (Job : JobType) [DecidableEq Job] := @Prosa.Analysis.Definitions.PriorityInversion.cumulative_priority_inversion_cond (Job := Job) (PState := processor_state Job)
noncomputable def w_Analysis_Definitions_PriorityInversion_priority_inversion (Job : JobType) [DecidableEq Job] := @Prosa.Analysis.Definitions.PriorityInversion.priority_inversion (Job := Job) (PState := processor_state Job)
noncomputable def w_Analysis_Definitions_PriorityInversion_priority_inversion_cond (Job : JobType) [DecidableEq Job] := @Prosa.Analysis.Definitions.PriorityInversion.priority_inversion_cond (Job := Job) (PState := processor_state Job)
noncomputable def w_Analysis_Definitions_PriorityInversion_priority_inversion_cond_is_bounded_by (Job : JobType) [DecidableEq Job] := @Prosa.Analysis.Definitions.PriorityInversion.priority_inversion_cond_is_bounded_by (Job := Job) (PState := processor_state Job)
noncomputable def w_Analysis_Definitions_PriorityInversion_priority_inversion_is_bounded_by (Job : JobType) [DecidableEq Job] := @Prosa.Analysis.Definitions.PriorityInversion.priority_inversion_is_bounded_by (Job := Job) (PState := processor_state Job)
noncomputable def w_Analysis_Definitions_PriorityInversion_priority_inversion_of_job_cond_is_bounded_by (Job : JobType) [DecidableEq Job] := @Prosa.Analysis.Definitions.PriorityInversion.priority_inversion_of_job_cond_is_bounded_by (Job := Job) (PState := processor_state Job)
noncomputable def w_Analysis_Definitions_PriorityInversion_priority_inversion_of_job_is_bounded_by (Job : JobType) [DecidableEq Job] := @Prosa.Analysis.Definitions.PriorityInversion.priority_inversion_of_job_is_bounded_by (Job := Job) (PState := processor_state Job)
noncomputable def w_Behavior_Ready_JobReady_ready_implies_pending (Job : JobType) [DecidableEq Job] := @Prosa.Behavior.Ready.JobReady.ready_implies_pending (Job := Job) (PState := processor_state Job)
noncomputable def w_Behavior_Ready_completed_jobs_dont_execute (Job : JobType) [DecidableEq Job] := @Prosa.Behavior.Ready.completed_jobs_dont_execute (Job := Job) (PState := processor_state Job)
noncomputable def w_Behavior_Ready_jobs_must_arrive_to_execute (Job : JobType) [DecidableEq Job] := @Prosa.Behavior.Ready.jobs_must_arrive_to_execute (Job := Job) (PState := processor_state Job)
noncomputable def w_Behavior_Service_service (Job : JobType) [DecidableEq Job] := @Prosa.Behavior.Service.service (Job := Job) (PState := processor_state Job)
noncomputable def w_Behavior_Service_service_during (Job : JobType) [DecidableEq Job] := @Prosa.Behavior.Service.service_during (Job := Job) (PState := processor_state Job)
noncomputable def w_Model_Aggregate_ServiceOfJobs_service_of_higher_or_equal_priority_jobs (Job : JobType) [DecidableEq Job] := @Prosa.Model.Aggregate.ServiceOfJobs.service_of_higher_or_equal_priority_jobs (Job := Job) (PState := processor_state Job)
noncomputable def w_Model_Aggregate_ServiceOfJobs_service_of_jobs (Job : JobType) [DecidableEq Job] := @Prosa.Model.Aggregate.ServiceOfJobs.service_of_jobs (Job := Job) (PState := processor_state Job)
noncomputable def w_Model_Aggregate_ServiceOfJobs_total_service_of_jobs_in (Job : JobType) [DecidableEq Job] := @Prosa.Model.Aggregate.ServiceOfJobs.total_service_of_jobs_in (Job := Job) (PState := processor_state Job)
noncomputable def w_Model_Preemption_Parameter_execution_starts_with_preemption_point (Job : JobType) [DecidableEq Job] := @Prosa.Model.Preemption.Parameter.execution_starts_with_preemption_point (Job := Job) (PState := processor_state Job)
noncomputable def w_Model_Preemption_Parameter_no_superfluous_preemptions (Job : JobType) [DecidableEq Job] := @Prosa.Model.Preemption.Parameter.no_superfluous_preemptions (Job := Job) (PState := processor_state Job)
noncomputable def w_Model_Preemption_Parameter_not_preemptive_implies_scheduled (Job : JobType) [DecidableEq Job] := @Prosa.Model.Preemption.Parameter.not_preemptive_implies_scheduled (Job := Job) (PState := processor_state Job)
noncomputable def w_Model_Preemption_Parameter_preempted_at (Job : JobType) [DecidableEq Job] := @Prosa.Model.Preemption.Parameter.preempted_at (Job := Job) (PState := processor_state Job)
noncomputable def w_Model_Preemption_Parameter_valid_preemption_model (Job : JobType) [DecidableEq Job] := @Prosa.Model.Preemption.Parameter.valid_preemption_model (Job := Job) (PState := processor_state Job)
noncomputable def w_Model_Processor_PlatformProperties_ideal_progress_proc_model (Job : JobType) [DecidableEq Job] := @Prosa.Model.Processor.PlatformProperties.ideal_progress_proc_model (Job := Job) (PState := processor_state Job)
noncomputable def w_Model_Processor_PlatformProperties_unit_service_proc_model (Job : JobType) [DecidableEq Job] := @Prosa.Model.Processor.PlatformProperties.unit_service_proc_model (Job := Job) (PState := processor_state Job)
noncomputable def w_Model_Schedule_PreemptionTime_preemption_time (Job : JobType) [DecidableEq Job] := @Prosa.Model.Schedule.PreemptionTime.preemption_time (Job := Job) (PState := processor_state Job)
noncomputable def w_Model_Schedule_PriorityDriven_respects_FP_policy_at_preemption_point (Job : JobType) [DecidableEq Job] := @Prosa.Model.Schedule.PriorityDriven.respects_FP_policy_at_preemption_point (Job := Job) (PState := processor_state Job)
noncomputable def w_Model_Schedule_PriorityDriven_respects_JLDP_policy_at_preemption_point (Job : JobType) [DecidableEq Job] := @Prosa.Model.Schedule.PriorityDriven.respects_JLDP_policy_at_preemption_point (Job := Job) (PState := processor_state Job)
noncomputable def w_Model_Schedule_PriorityDriven_respects_JLFP_policy_at_preemption_point (Job : JobType) [DecidableEq Job] := @Prosa.Model.Schedule.PriorityDriven.respects_JLFP_policy_at_preemption_point (Job := Job) (PState := processor_state Job)
noncomputable def w_Model_Schedule_Scheduled_is_idle (Job : JobType) [DecidableEq Job] := @Prosa.Model.Schedule.Scheduled.is_idle (Job := Job) (PState := processor_state Job)
noncomputable def w_Model_Schedule_Scheduled_scheduled_jobs_at (Job : JobType) [DecidableEq Job] := @Prosa.Model.Schedule.Scheduled.scheduled_jobs_at (Job := Job) (PState := processor_state Job)
noncomputable def w_Model_Task_Preemption_Parameters_valid_model_with_bounded_nonpreemptive_segments (Job : JobType) [DecidableEq Job] := @Prosa.Model.Task.Preemption.Parameters.valid_model_with_bounded_nonpreemptive_segments (Job := Job) (PState := processor_state Job)
noncomputable def w_Validation_PreemptionTimeInterface_production_preemption_time_none (Job : JobType) [DecidableEq Job] := @Prosa.Validation.PreemptionTimeInterface.production_preemption_time_none (Job := Job) (PState := processor_state Job)
noncomputable def w_Validation_PreemptionTimeInterface_production_preemption_time_some (Job : JobType) [DecidableEq Job] := @Prosa.Validation.PreemptionTimeInterface.production_preemption_time_some (Job := Job) (PState := processor_state Job)
noncomputable def w_Validation_PreemptionTimeInterface_production_scheduled_job_at_eq (Job : JobType) [DecidableEq Job] := @Prosa.Validation.PreemptionTimeInterface.production_scheduled_job_at_eq (Job := Job) (PState := processor_state Job)
noncomputable def w_Validation_PriorityInversionInterface_cumulPriorityInversionCondProjection (Job : JobType) [DecidableEq Job] := @Prosa.Validation.PriorityInversionInterface.cumulPriorityInversionCondProjection (Job := Job) (PState := processor_state Job)
noncomputable def w_Validation_PriorityInversionInterface_cumulPriorityInversionProjection (Job : JobType) [DecidableEq Job] := @Prosa.Validation.PriorityInversionInterface.cumulPriorityInversionProjection (Job := Job) (PState := processor_state Job)
noncomputable def w_Validation_ScheduleInterface_coreEnumeration (Job : JobType) [DecidableEq Job] := @Prosa.Validation.ScheduleInterface.coreEnumeration (Job := Job) (PState := processor_state Job)
noncomputable def w_Validation_ScheduleInterface_coreEnumeration_complete (Job : JobType) [DecidableEq Job] := @Prosa.Validation.ScheduleInterface.coreEnumeration_complete (Job := Job) (PState := processor_state Job)
noncomputable def w_Validation_ScheduleInterface_coreEnumeration_nodup (Job : JobType) [DecidableEq Job] := @Prosa.Validation.ScheduleInterface.coreEnumeration_nodup (Job := Job) (PState := processor_state Job)
noncomputable def w_Validation_ScheduleInterface_production_scheduled_in_eq_true_iff (Job : JobType) [DecidableEq Job] := @Prosa.Validation.ScheduleInterface.production_scheduled_in_eq_true_iff (Job := Job) (PState := processor_state Job)
noncomputable def w_Validation_ScheduleInterface_production_service_in_as_list_sum (Job : JobType) [DecidableEq Job] := @Prosa.Validation.ScheduleInterface.production_service_in_as_list_sum (Job := Job) (PState := processor_state Job)
noncomputable def w_Validation_ScheduleInterface_production_supply_in_as_list_sum (Job : JobType) [DecidableEq Job] := @Prosa.Validation.ScheduleInterface.production_supply_in_as_list_sum (Job := Job) (PState := processor_state Job)

end Prosa.Validation.OverheadsInstWitness
