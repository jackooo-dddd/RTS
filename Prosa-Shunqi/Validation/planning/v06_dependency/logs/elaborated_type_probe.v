Set Warnings "-notation-overridden".
Set Printing Width 100000.
Require Import prosa.behavior.time.
Require Import prosa.util.bigop.
Require Import prosa.util.epsilon.
Require Import prosa.util.int.
Require Import prosa.util.notation.
Require Import prosa.util.rel.
Require Import prosa.util.seqset.
Require Import prosa.util.setoid.
Require Import prosa.util.subadditivity.
Require Import prosa.util.supremum.
Require Import prosa.util.tactics.
Require Import prosa.util.lcmseq.
Require Import prosa.util.list.
Require Import prosa.util.nat.
Require Import prosa.util.search_arg.
Require Import prosa.util.unit_growth.
Require Import prosa.util.bigcat.
Require Import prosa.util.div_mod.
Require Import prosa.util.minmax.
Require Import prosa.util.nondecreasing.
Require Import prosa.util.poet.
Require Import prosa.util.sum.
Require Import prosa.util.superadditivity.
Require Import prosa.util.all.
Require Import prosa.util.fixpoint.
Require Import prosa.behavior.job.
Require Import prosa.implementation.definitions.extrapolated_arrival_curve.
Require Import prosa.analysis.definitions.sbf.sbf.
Require Import prosa.behavior.arrival_sequence.
Require Import prosa.implementation.definitions.arrival_bound.
Require Import prosa.implementation.facts.extrapolated_arrival_curve.
Require Import prosa.behavior.schedule.
Require Import prosa.behavior.service.
Require Import prosa.model.processor.supply.
Require Import prosa.analysis.definitions.completion_sequence.
Require Import prosa.analysis.definitions.finish_time.
Require Import prosa.analysis.definitions.sbf.average.
Require Import prosa.analysis.definitions.sbf.periodic.
Require Import prosa.analysis.definitions.sbf.pred.
Require Import prosa.analysis.definitions.service.
Require Import prosa.behavior.ready.
Require Import prosa.analysis.definitions.sbf.plain.
Require Import prosa.analysis.definitions.schedule_prefix.
Require Import prosa.behavior.all.
Require Import prosa.analysis.definitions.job_response_time.
Require Import prosa.analysis.transform.swap.
Require Import prosa.model.job.properties.
Require Import prosa.model.processor.ideal.
Require Import prosa.model.processor.ideal_uni_exceed.
Require Import prosa.model.processor.overheads.
Require Import prosa.model.processor.platform_properties.
Require Import prosa.model.processor.restricted_supply.
Require Import prosa.model.processor.spin.
Require Import prosa.model.processor.varspeed.
Require Import prosa.model.readiness.basic.
Require Import prosa.model.readiness.jitter.
Require Import prosa.model.schedule.edf.
Require Import prosa.model.schedule.nonpreemptive.
Require Import prosa.model.schedule.scheduled.
Require Import prosa.model.schedule.work_conserving.
Require Import prosa.model.task.concept.
Require Import prosa.analysis.abstract.definitions.
Require Import prosa.analysis.abstract.search_space.
Require Import prosa.analysis.definitions.overheads.schedule_change.
Require Import prosa.analysis.definitions.task_schedule.
Require Import prosa.analysis.facts.behavior.supply.
Require Import prosa.analysis.facts.model.ideal_uni_exceed.
Require Import prosa.analysis.facts.model.restricted_supply.schedule.
Require Import prosa.analysis.facts.model.task_cost.
Require Import prosa.analysis.facts.model.uniprocessor.
Require Import prosa.implementation.definitions.generic_scheduler.
Require Import prosa.model.priority.definitions.
Require Import prosa.model.schedule.tdma.
Require Import prosa.model.task.absolute_deadline.
Require Import prosa.model.task.arrival.sporadic.
Require Import prosa.model.task.arrivals.
Require Import prosa.model.task.jitter.
Require Import prosa.analysis.abstract.restricted_supply.busy_sbf.
Require Import prosa.analysis.definitions.infinite_jobs.
Require Import prosa.analysis.definitions.readiness_interference.
Require Import prosa.analysis.facts.SBF.
Require Import prosa.analysis.facts.behavior.arrivals.
Require Import prosa.analysis.facts.tdma.
Require Import prosa.model.priority.coercion.
Require Import prosa.model.task.arrival.curves.
Require Import prosa.model.task.arrival.request_bound_functions.
Require Import prosa.model.task.arrival.task_max_inter_arrival.
Require Import prosa.model.task.sequentiality.
Require Import prosa.analysis.definitions.delay_propagation.
Require Import prosa.analysis.facts.model.scheduled.
Require Import prosa.analysis.facts.model.task_arrivals.
Require Import prosa.implementation.definitions.maximal_arrival_sequence.
Require Import prosa.model.composite.valid_task_arrival_sequence.
Require Import prosa.model.priority.classes.
Require Import prosa.model.readiness.sequential.
Require Import prosa.model.task.arrival.curve_as_rbf.
Require Import prosa.analysis.definitions.always_higher_priority.
Require Import prosa.analysis.definitions.carry_in.
Require Import prosa.analysis.definitions.overheads.priority_bump.
Require Import prosa.analysis.definitions.priority.classes.
Require Import prosa.analysis.definitions.work_bearing_readiness.
Require Import prosa.analysis.facts.behavior.service.
Require Import prosa.analysis.facts.delay_propagation.
Require Import prosa.analysis.facts.job_index.
Require Import prosa.analysis.facts.model.arrival_curves.
Require Import prosa.analysis.facts.model.sbf.average.
Require Import prosa.analysis.facts.model.sbf.periodic.
Require Import prosa.analysis.facts.sporadic.arrival_bound.
Require Import prosa.implementation.facts.maximal_arrival_sequence.
Require Import prosa.model.aggregate.service_of_jobs.
Require Import prosa.model.aggregate.workload.
Require Import prosa.model.preemption.parameter.
Require Import prosa.model.priority.deadline_monotonic.
Require Import prosa.model.priority.edf.
Require Import prosa.model.priority.fifo.
Require Import prosa.model.priority.gel.
Require Import prosa.model.priority.numeric_fixed_priority.
Require Import prosa.model.priority.rate_monotonic.
Require Import prosa.analysis.definitions.interference.
Require Import prosa.analysis.definitions.progress.
Require Import prosa.analysis.definitions.readiness.
Require Import prosa.analysis.facts.behavior.completion.
Require Import prosa.analysis.facts.model.ideal.schedule.
Require Import prosa.analysis.facts.model.ideal.service_of_jobs.
Require Import prosa.analysis.facts.model.task_schedule.
Require Import prosa.analysis.facts.model.workload.
Require Import prosa.analysis.facts.priority.classes.
Require Import prosa.analysis.facts.sporadic.arrival_times.
Require Import prosa.implementation.definitions.task.
Require Import prosa.model.preemption.fully_nonpreemptive.
Require Import prosa.model.preemption.fully_preemptive.
Require Import prosa.model.preemption.limited_preemptive.
Require Import prosa.model.priority.elf.
Require Import prosa.model.processor.multiprocessor.
Require Import prosa.model.schedule.limited_preemptive.
Require Import prosa.model.schedule.preemption_time.
Require Import prosa.model.task.arrival.sporadic_as_curve.
Require Import prosa.model.task.preemption.parameters.
Require Import prosa.analysis.definitions.blocking_bound.edf.
Require Import prosa.analysis.definitions.blocking_bound.elf.
Require Import prosa.analysis.definitions.blocking_bound.fp.
Require Import prosa.analysis.definitions.busy_interval.classical.
Require Import prosa.analysis.definitions.request_bound_function.
Require Import prosa.analysis.definitions.schedulability.
Require Import prosa.analysis.definitions.service_inversion.pred.
Require Import prosa.analysis.facts.behavior.deadlines.
Require Import prosa.analysis.facts.preemption.job.preemptive.
Require Import prosa.analysis.facts.priority.jlfp_with_fp.
Require Import prosa.analysis.facts.readiness.backlogged.
Require Import prosa.analysis.facts.readiness.basic.
Require Import prosa.analysis.facts.readiness.sequential.
Require Import prosa.analysis.facts.sporadic.arrival_sequence.
Require Import prosa.analysis.facts.transform.replace_at.
Require Import prosa.implementation.definitions.job_constructor.
Require Import prosa.model.readiness.suspension.
Require Import prosa.model.schedule.priority_driven.
Require Import prosa.model.task.preemption.floating_nonpreemptive.
Require Import prosa.model.task.preemption.fully_nonpreemptive.
Require Import prosa.model.task.preemption.fully_preemptive.
Require Import prosa.model.task.preemption.limited_preemptive.
Require Import prosa.analysis.abstract.restricted_supply.busy_prefix.
Require Import prosa.analysis.definitions.busy_interval.edf_pi_bound.
Require Import prosa.analysis.definitions.demand_bound_function.
Require Import prosa.analysis.definitions.priority_inversion.
Require Import prosa.analysis.definitions.sbf.busy.
Require Import prosa.analysis.definitions.service_inversion.busy_prefix.
Require Import prosa.analysis.definitions.service_inversion.readiness_aware.
Require Import prosa.analysis.definitions.tardiness.
Require Import prosa.analysis.definitions.workload.bounded.
Require Import prosa.analysis.definitions.workload.edf_athep_bound.
Require Import prosa.analysis.definitions.workload.elf_athep_bound.
Require Import prosa.analysis.facts.behavior.all.
Require Import prosa.analysis.facts.busy_interval.quiet_time.
Require Import prosa.analysis.facts.edf_definitions.
Require Import prosa.analysis.facts.jitter.
Require Import prosa.analysis.facts.model.preemption.
Require Import prosa.analysis.facts.preemption.task.preemptive.
Require Import prosa.analysis.facts.suspension.
Require Import prosa.analysis.facts.transform.swaps.
Require Import prosa.implementation.definitions.ideal_uni_scheduler.
Require Import prosa.implementation.facts.generic_schedule.
Require Import prosa.implementation.facts.job_constructor.
Require Import prosa.model.task.suspension.dynamic.
Require Import prosa.analysis.facts.completes_at.
Require Import prosa.analysis.facts.model.dynamic_suspension.
Require Import prosa.analysis.facts.model.exceedance.SBF.
Require Import prosa.analysis.facts.model.rbf.
Require Import prosa.analysis.facts.model.sequential.
Require Import prosa.analysis.facts.model.service_of_jobs.
Require Import prosa.analysis.facts.preemption.job.nonpreemptive.
Require Import prosa.analysis.facts.preemption.rtc_threshold.job_preemptable.
Require Import prosa.analysis.facts.priority.inversion.
Require Import prosa.analysis.facts.priority.sequential.
Require Import prosa.analysis.transform.prefix.
Require Import prosa.implementation.facts.ideal_uni.preemption_aware.
Require Import prosa.model.task.offset.
Require Import prosa.analysis.abstract.iw_auxiliary.
Require Import prosa.analysis.abstract.restricted_supply.search_space.fp.
Require Import prosa.analysis.facts.busy_interval.existence.
Require Import prosa.analysis.facts.interference.
Require Import prosa.analysis.facts.model.dbf.
Require Import prosa.analysis.facts.model.ideal.priority_inversion.
Require Import prosa.analysis.facts.model.offset.
Require Import prosa.analysis.facts.preemption.job.limited.
Require Import prosa.analysis.facts.preemption.rtc_threshold.nonpreemptive.
Require Import prosa.analysis.facts.preemption.rtc_threshold.preemptive.
Require Import prosa.analysis.facts.preemption.task.nonpreemptive.
Require Import prosa.analysis.facts.priority.edf.
Require Import prosa.analysis.facts.priority.gel.
Require Import prosa.analysis.facts.workload.edf_athep_bound.
Require Import prosa.analysis.facts.workload.elf_athep_bound.
Require Import prosa.analysis.transform.edf_trans.
Require Import prosa.analysis.transform.wc_trans.
Require Import prosa.implementation.facts.ideal_uni.prio_aware.
Require Import prosa.model.task.arrival.periodic.
Require Import prosa.results.transfer_schedulability.criterion.
Require Import prosa.analysis.abstract.busy_interval.
Require Import prosa.analysis.abstract.restricted_supply.search_space.edf.
Require Import prosa.analysis.abstract.restricted_supply.search_space.elf.
Require Import prosa.analysis.definitions.hyperperiod.
Require Import prosa.analysis.facts.busy_interval.carry_in.
Require Import prosa.analysis.facts.busy_interval.hep_at_pt.
Require Import prosa.analysis.facts.preemption.task.floating.
Require Import prosa.analysis.facts.preemption.task.limited.
Require Import prosa.analysis.facts.priority.elf.
Require Import prosa.analysis.facts.readiness_interference.
Require Import prosa.analysis.facts.transform.edf_opt.
Require Import prosa.analysis.facts.transform.wc_correctness.
Require Import prosa.model.task.arrival.periodic_as_sporadic.
Require Import prosa.results.transfer_schedulability.paper_model.
Require Import prosa.analysis.abstract.lower_bound_on_service.
Require Import prosa.analysis.facts.busy_interval.arrival.
Require Import prosa.analysis.facts.busy_interval.pi.
Require Import prosa.analysis.facts.periodic.arrival_separation.
Require Import prosa.analysis.facts.preemption.rtc_threshold.floating.
Require Import prosa.analysis.facts.preemption.rtc_threshold.limited.
Require Import prosa.analysis.facts.transform.edf_wc.
Require Import prosa.model.task.arrival.example.
Require Import prosa.results.generality.elf.
Require Import prosa.analysis.abstract.abstract_rta.
Require Import prosa.analysis.facts.blocking_bound.edf.
Require Import prosa.analysis.facts.blocking_bound.elf.
Require Import prosa.analysis.facts.blocking_bound.fp.
Require Import prosa.analysis.facts.busy_interval.pi_bound.
Require Import prosa.analysis.facts.busy_interval.pi_cond.
Require Import prosa.analysis.facts.busy_interval.service_inversion.
Require Import prosa.analysis.facts.model.overheads.schedule.
Require Import prosa.analysis.facts.periodic.max_inter_arrival.
Require Import prosa.results.optimality.edf.
Require Import prosa.analysis.abstract.IBF.supply.
Require Import prosa.analysis.abstract.IBF.task.
Require Import prosa.analysis.abstract.ideal.abstract_rta.
Require Import prosa.analysis.facts.busy_interval.all.
Require Import prosa.analysis.facts.model.overheads.priority_bump.
Require Import prosa.analysis.facts.model.overheads.schedule_change.
Require Import prosa.analysis.facts.periodic.arrival_times.
Require Import prosa.analysis.abstract.IBF.supply_task.
Require Import prosa.analysis.abstract.ideal.abstract_seq_rta.
Require Import prosa.analysis.abstract.ideal.iw_instantiation.
Require Import prosa.analysis.abstract.restricted_supply.abstract_rta.
Require Import prosa.analysis.facts.model.overheads.schedule_change_bound.
Require Import prosa.analysis.facts.periodic.task_arrivals_size.
Require Import prosa.analysis.facts.priority.fifo.
Require Import prosa.model.processor.overhead_resource_model.
Require Import prosa.analysis.abstract.ideal.cumulative_bounds.
Require Import prosa.analysis.abstract.restricted_supply.abstract_seq_rta.
Require Import prosa.analysis.abstract.restricted_supply.iw_instantiation.
Require Import prosa.analysis.abstract.restricted_supply.iw_readiness.
Require Import prosa.analysis.abstract.restricted_supply.search_space.fifo.
Require Import prosa.analysis.facts.hyperperiod.
Require Import prosa.analysis.facts.model.overheads.blackout_bound.
Require Import prosa.analysis.facts.priority.fifo_ahep_bound.
Require Import prosa.results.generality.gel.
Require Import prosa.results.rta.ideal.fp.bounded_pi.
Require Import prosa.analysis.abstract.restricted_supply.bounded_bi.aux.
Require Import prosa.analysis.abstract.restricted_supply.search_space.fifo_fixpoint.
Require Import prosa.analysis.abstract.restricted_supply.task_ibf_readiness.
Require Import prosa.analysis.abstract.restricted_supply.task_intra_interference_bound.
Require Import prosa.analysis.facts.model.overheads.sbf.fifo.
Require Import prosa.analysis.facts.model.overheads.sbf.fp.
Require Import prosa.analysis.facts.model.overheads.sbf.jlfp.
Require Import prosa.analysis.facts.shifted_job_costs.
Require Import prosa.results.rta.ideal.edf.bounded_pi.
Require Import prosa.results.rta.ideal.elf.bounded_pi.
Require Import prosa.results.rta.ideal.fifo.bounded_nps.
Require Import prosa.results.rta.ideal.fp.bounded_nps.
Require Import prosa.results.rta.ideal.fp.nonseq.bounded_pi.
Require Import prosa.results.rta.ideal.gel.bounded_pi.
Require Import prosa.analysis.abstract.restricted_supply.bounded_bi.edf.
Require Import prosa.analysis.abstract.restricted_supply.bounded_bi.elf.
Require Import prosa.analysis.abstract.restricted_supply.bounded_bi.fp.
Require Import prosa.analysis.abstract.restricted_supply.bounded_bi.jlfp.
Require Import prosa.results.rta.ideal.edf.bounded_nps.
Require Import prosa.results.rta.ideal.fp.floating_nonpreemptive.
Require Import prosa.results.rta.ideal.fp.fully_nonpreemptive.
Require Import prosa.results.rta.ideal.fp.fully_preemptive.
Require Import prosa.results.rta.ideal.fp.limited_preemptive.
Require Import prosa.results.rta.arm.edf.floating_nonpreemptive.
Require Import prosa.results.rta.arm.edf.fully_nonpreemptive.
Require Import prosa.results.rta.arm.edf.fully_preemptive.
Require Import prosa.results.rta.arm.edf.limited_preemptive.
Require Import prosa.results.rta.arm.fifo.bounded_nps.
Require Import prosa.results.rta.arm.fp.floating_nonpreemptive.
Require Import prosa.results.rta.arm.fp.fully_nonpreemptive.
Require Import prosa.results.rta.arm.fp.fully_preemptive.
Require Import prosa.results.rta.arm.fp.limited_preemptive.
Require Import prosa.results.rta.exc.fp.fully_nonpreemptive.
Require Import prosa.results.rta.ideal.edf.floating_nonpreemptive.
Require Import prosa.results.rta.ideal.edf.fully_nonpreemptive.
Require Import prosa.results.rta.ideal.edf.fully_preemptive.
Require Import prosa.results.rta.ideal.edf.limited_preemptive.
Require Import prosa.results.rta.ideal.fp.comp.fully_preemptive.
Require Import prosa.results.rta.ovh.edf.floating_nonpreemptive.
Require Import prosa.results.rta.ovh.edf.fully_nonpreemptive.
Require Import prosa.results.rta.ovh.edf.fully_preemptive.
Require Import prosa.results.rta.ovh.edf.limited_preemptive.
Require Import prosa.results.rta.ovh.fifo.bounded_nps.
Require Import prosa.results.rta.ovh.fp.floating_nonpreemptive.
Require Import prosa.results.rta.ovh.fp.fully_nonpreemptive.
Require Import prosa.results.rta.ovh.fp.fully_preemptive.
Require Import prosa.results.rta.ovh.fp.limited_preemptive.
Require Import prosa.results.rta.prm.edf.floating_nonpreemptive.
Require Import prosa.results.rta.prm.edf.fully_nonpreemptive.
Require Import prosa.results.rta.prm.edf.fully_preemptive.
Require Import prosa.results.rta.prm.edf.limited_preemptive.
Require Import prosa.results.rta.prm.fifo.bounded_nps.
Require Import prosa.results.rta.prm.fp.floating_nonpreemptive.
Require Import prosa.results.rta.prm.fp.fully_nonpreemptive.
Require Import prosa.results.rta.prm.fp.fully_preemptive.
Require Import prosa.results.rta.prm.fp.limited_preemptive.
Require Import prosa.results.rta.rs.edf.floating_nonpreemptive.
Require Import prosa.results.rta.rs.edf.fully_nonpreemptive.
Require Import prosa.results.rta.rs.edf.fully_preemptive.
Require Import prosa.results.rta.rs.edf.limited_preemptive.
Require Import prosa.results.rta.rs.elf.floating_nonpreemptive.
Require Import prosa.results.rta.rs.elf.fully_nonpreemptive.
Require Import prosa.results.rta.rs.elf.fully_preemptive.
Require Import prosa.results.rta.rs.elf.limited_preemptive.
Require Import prosa.results.rta.rs.fifo.bounded_nps.
Require Import prosa.results.rta.rs.fp.floating_nonpreemptive.
Require Import prosa.results.rta.rs.fp.fully_nonpreemptive.
Require Import prosa.results.rta.rs.fp.fully_preemptive.
Require Import prosa.results.rta.rs.fp.limited_preemptive.
Goal True. idtac "BEGIN|prosa.analysis.abstract.IBF.supply.intra_interference". Abort.
Check @prosa.analysis.abstract.IBF.supply.intra_interference.
Goal True. idtac "END|prosa.analysis.abstract.IBF.supply.intra_interference". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.IBF.supply.cumul_intra_interference". Abort.
Check @prosa.analysis.abstract.IBF.supply.cumul_intra_interference.
Goal True. idtac "END|prosa.analysis.abstract.IBF.supply.cumul_intra_interference". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.IBF.supply.intra_interference_is_bounded_by". Abort.
Check @prosa.analysis.abstract.IBF.supply.intra_interference_is_bounded_by.
Goal True. idtac "END|prosa.analysis.abstract.IBF.supply.intra_interference_is_bounded_by". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.IBF.supply_task.nonself_intra". Abort.
Check @prosa.analysis.abstract.IBF.supply_task.nonself_intra.
Goal True. idtac "END|prosa.analysis.abstract.IBF.supply_task.nonself_intra". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.IBF.supply_task.task_intra_interference". Abort.
Check @prosa.analysis.abstract.IBF.supply_task.task_intra_interference.
Goal True. idtac "END|prosa.analysis.abstract.IBF.supply_task.task_intra_interference". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.IBF.supply_task.task_intra_interference_is_bounded_by". Abort.
Check @prosa.analysis.abstract.IBF.supply_task.task_intra_interference_is_bounded_by.
Goal True. idtac "END|prosa.analysis.abstract.IBF.supply_task.task_intra_interference_is_bounded_by". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.IBF.task.nonself". Abort.
Check @prosa.analysis.abstract.IBF.task.nonself.
Goal True. idtac "END|prosa.analysis.abstract.IBF.task.nonself". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.IBF.task.task_interference". Abort.
Check @prosa.analysis.abstract.IBF.task.task_interference.
Goal True. idtac "END|prosa.analysis.abstract.IBF.task.task_interference". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.IBF.task.cumul_task_interference". Abort.
Check @prosa.analysis.abstract.IBF.task.cumul_task_interference.
Goal True. idtac "END|prosa.analysis.abstract.IBF.task.cumul_task_interference". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.IBF.task.task_interference_is_bounded_by". Abort.
Check @prosa.analysis.abstract.IBF.task.task_interference_is_bounded_by.
Goal True. idtac "END|prosa.analysis.abstract.IBF.task.task_interference_is_bounded_by". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.IBF.task.interference_and_workload_consistent_with_sequential_tasks". Abort.
Check @prosa.analysis.abstract.IBF.task.interference_and_workload_consistent_with_sequential_tasks.
Goal True. idtac "END|prosa.analysis.abstract.IBF.task.interference_and_workload_consistent_with_sequential_tasks". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.IBF.task.completed_before_beginning_of_busy_interval". Abort.
Check @prosa.analysis.abstract.IBF.task.completed_before_beginning_of_busy_interval.
Goal True. idtac "END|prosa.analysis.abstract.IBF.task.completed_before_beginning_of_busy_interval". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.IBF.task.arrives_after_beginning_of_busy_interval". Abort.
Check @prosa.analysis.abstract.IBF.task.arrives_after_beginning_of_busy_interval.
Goal True. idtac "END|prosa.analysis.abstract.IBF.task.arrives_after_beginning_of_busy_interval". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.IBF.task.interference_plus_sched_le_serv_of_task_plus_task_interference_idle". Abort.
Check @prosa.analysis.abstract.IBF.task.interference_plus_sched_le_serv_of_task_plus_task_interference_idle.
Goal True. idtac "END|prosa.analysis.abstract.IBF.task.interference_plus_sched_le_serv_of_task_plus_task_interference_idle". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.IBF.task.interference_plus_sched_le_serv_of_task_plus_task_interference_task". Abort.
Check @prosa.analysis.abstract.IBF.task.interference_plus_sched_le_serv_of_task_plus_task_interference_task.
Goal True. idtac "END|prosa.analysis.abstract.IBF.task.interference_plus_sched_le_serv_of_task_plus_task_interference_task". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.IBF.task.interference_plus_sched_le_serv_of_task_plus_task_interference_job". Abort.
Check @prosa.analysis.abstract.IBF.task.interference_plus_sched_le_serv_of_task_plus_task_interference_job.
Goal True. idtac "END|prosa.analysis.abstract.IBF.task.interference_plus_sched_le_serv_of_task_plus_task_interference_job". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.IBF.task.interference_and_service_eq_1". Abort.
Check @prosa.analysis.abstract.IBF.task.interference_and_service_eq_1.
Goal True. idtac "END|prosa.analysis.abstract.IBF.task.interference_and_service_eq_1". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.IBF.task.interference_plus_sched_le_serv_of_task_plus_task_interference_j". Abort.
Check @prosa.analysis.abstract.IBF.task.interference_plus_sched_le_serv_of_task_plus_task_interference_j.
Goal True. idtac "END|prosa.analysis.abstract.IBF.task.interference_plus_sched_le_serv_of_task_plus_task_interference_j". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.IBF.task.interference_plus_sched_le_serv_of_task_plus_task_interference". Abort.
Check @prosa.analysis.abstract.IBF.task.interference_plus_sched_le_serv_of_task_plus_task_interference.
Goal True. idtac "END|prosa.analysis.abstract.IBF.task.interference_plus_sched_le_serv_of_task_plus_task_interference". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.IBF.task.cumul_interference_plus_sched_le_serv_of_task_plus_cumul_task_interference". Abort.
Check @prosa.analysis.abstract.IBF.task.cumul_interference_plus_sched_le_serv_of_task_plus_cumul_task_interference.
Goal True. idtac "END|prosa.analysis.abstract.IBF.task.cumul_interference_plus_sched_le_serv_of_task_plus_cumul_task_interference". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.IBF.task.serv_of_task_le_workload_of_task_plus". Abort.
Check @prosa.analysis.abstract.IBF.task.serv_of_task_le_workload_of_task_plus.
Goal True. idtac "END|prosa.analysis.abstract.IBF.task.serv_of_task_le_workload_of_task_plus". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.IBF.task.cumulative_job_interference_le_task_interference_bound". Abort.
Check @prosa.analysis.abstract.IBF.task.cumulative_job_interference_le_task_interference_bound.
Goal True. idtac "END|prosa.analysis.abstract.IBF.task.cumulative_job_interference_le_task_interference_bound". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.IBF.task.cumulative_job_interference_bound". Abort.
Check @prosa.analysis.abstract.IBF.task.cumulative_job_interference_bound.
Goal True. idtac "END|prosa.analysis.abstract.IBF.task.cumulative_job_interference_bound". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.IBF.task.task_IBF_implies_job_IBF". Abort.
Check @prosa.analysis.abstract.IBF.task.task_IBF_implies_job_IBF.
Goal True. idtac "END|prosa.analysis.abstract.IBF.task.task_IBF_implies_job_IBF". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.abstract_rta.relative_arrival_time_of_job_is_A". Abort.
Check @prosa.analysis.abstract.abstract_rta.relative_arrival_time_of_job_is_A.
Goal True. idtac "END|prosa.analysis.abstract.abstract_rta.relative_arrival_time_of_job_is_A". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.abstract_rta.relative_time_to_reach_rtct". Abort.
Check @prosa.analysis.abstract.abstract_rta.relative_time_to_reach_rtct.
Goal True. idtac "END|prosa.analysis.abstract.abstract_rta.relative_time_to_reach_rtct". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.abstract_rta.job_arrival_eq_t1_plus_A". Abort.
Check @prosa.analysis.abstract.abstract_rta.job_arrival_eq_t1_plus_A.
Goal True. idtac "END|prosa.analysis.abstract.abstract_rta.job_arrival_eq_t1_plus_A". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.abstract_rta.relative_arrival_is_bounded". Abort.
Check @prosa.analysis.abstract.abstract_rta.relative_arrival_is_bounded.
Goal True. idtac "END|prosa.analysis.abstract.abstract_rta.relative_arrival_is_bounded". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.abstract_rta.t2_le_arrival_plus_R_1". Abort.
Check @prosa.analysis.abstract.abstract_rta.t2_le_arrival_plus_R_1.
Goal True. idtac "END|prosa.analysis.abstract.abstract_rta.t2_le_arrival_plus_R_1". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.abstract_rta.job_completed_by_arrival_plus_R_1". Abort.
Check @prosa.analysis.abstract.abstract_rta.job_completed_by_arrival_plus_R_1.
Goal True. idtac "END|prosa.analysis.abstract.abstract_rta.job_completed_by_arrival_plus_R_1". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.abstract_rta.t2_le_arrival_plus_R_2". Abort.
Check @prosa.analysis.abstract.abstract_rta.t2_le_arrival_plus_R_2.
Goal True. idtac "END|prosa.analysis.abstract.abstract_rta.t2_le_arrival_plus_R_2". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.abstract_rta.job_completed_by_arrival_plus_R_2". Abort.
Check @prosa.analysis.abstract.abstract_rta.job_completed_by_arrival_plus_R_2.
Goal True. idtac "END|prosa.analysis.abstract.abstract_rta.job_completed_by_arrival_plus_R_2". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.abstract_rta.relative_rtc_time_is_bounded". Abort.
Check @prosa.analysis.abstract.abstract_rta.relative_rtc_time_is_bounded.
Goal True. idtac "END|prosa.analysis.abstract.abstract_rta.relative_rtc_time_is_bounded". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.abstract_rta.job_receives_enough_service_1". Abort.
Check @prosa.analysis.abstract.abstract_rta.job_receives_enough_service_1.
Goal True. idtac "END|prosa.analysis.abstract.abstract_rta.job_receives_enough_service_1". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.abstract_rta.job_receives_enough_service_2". Abort.
Check @prosa.analysis.abstract.abstract_rta.job_receives_enough_service_2.
Goal True. idtac "END|prosa.analysis.abstract.abstract_rta.job_receives_enough_service_2". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.abstract_rta.job_receives_enough_service_3". Abort.
Check @prosa.analysis.abstract.abstract_rta.job_receives_enough_service_3.
Goal True. idtac "END|prosa.analysis.abstract.abstract_rta.job_receives_enough_service_3". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.abstract_rta.job_is_completed_by_arrival_plus_R". Abort.
Check @prosa.analysis.abstract.abstract_rta.job_is_completed_by_arrival_plus_R.
Goal True. idtac "END|prosa.analysis.abstract.abstract_rta.job_is_completed_by_arrival_plus_R". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.abstract_rta.uniprocessor_response_time_bound". Abort.
Check @prosa.analysis.abstract.abstract_rta.uniprocessor_response_time_bound.
Goal True. idtac "END|prosa.analysis.abstract.abstract_rta.uniprocessor_response_time_bound". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.busy_interval.busy_interval_prefix_case". Abort.
Check @prosa.analysis.abstract.busy_interval.busy_interval_prefix_case.
Goal True. idtac "END|prosa.analysis.abstract.busy_interval.busy_interval_prefix_case". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.busy_interval.terminating_busy_prefix_is_busy_interval". Abort.
Check @prosa.analysis.abstract.busy_interval.terminating_busy_prefix_is_busy_interval.
Goal True. idtac "END|prosa.analysis.abstract.busy_interval.terminating_busy_prefix_is_busy_interval". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.busy_interval.job_completes_within_busy_interval". Abort.
Check @prosa.analysis.abstract.busy_interval.job_completes_within_busy_interval.
Goal True. idtac "END|prosa.analysis.abstract.busy_interval.job_completes_within_busy_interval". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.busy_interval.no_service_before_busy_interval". Abort.
Check @prosa.analysis.abstract.busy_interval.no_service_before_busy_interval.
Goal True. idtac "END|prosa.analysis.abstract.busy_interval.no_service_before_busy_interval". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.busy_interval.service_within_busy_interval_ge_job_cost". Abort.
Check @prosa.analysis.abstract.busy_interval.service_within_busy_interval_ge_job_cost.
Goal True. idtac "END|prosa.analysis.abstract.busy_interval.service_within_busy_interval_ge_job_cost". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.busy_interval.abstract_busy_interval_arrivals_before". Abort.
Check @prosa.analysis.abstract.busy_interval.abstract_busy_interval_arrivals_before.
Goal True. idtac "END|prosa.analysis.abstract.busy_interval.abstract_busy_interval_arrivals_before". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.busy_interval.abstract_busy_interval_prefix_job_arrival". Abort.
Check @prosa.analysis.abstract.busy_interval.abstract_busy_interval_prefix_job_arrival.
Goal True. idtac "END|prosa.analysis.abstract.busy_interval.abstract_busy_interval_prefix_job_arrival". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.busy_interval.abstract_busy_interval_job_arrival". Abort.
Check @prosa.analysis.abstract.busy_interval.abstract_busy_interval_job_arrival.
Goal True. idtac "END|prosa.analysis.abstract.busy_interval.abstract_busy_interval_job_arrival". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.busy_interval.service_and_interference_bound". Abort.
Check @prosa.analysis.abstract.busy_interval.service_and_interference_bound.
Goal True. idtac "END|prosa.analysis.abstract.busy_interval.service_and_interference_bound". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.busy_interval.exists_busy_interval_prefix". Abort.
Check @prosa.analysis.abstract.busy_interval.exists_busy_interval_prefix.
Goal True. idtac "END|prosa.analysis.abstract.busy_interval.exists_busy_interval_prefix". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.busy_interval.busy_interval_has_uninterrupted_service". Abort.
Check @prosa.analysis.abstract.busy_interval.busy_interval_has_uninterrupted_service.
Goal True. idtac "END|prosa.analysis.abstract.busy_interval.busy_interval_has_uninterrupted_service". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.busy_interval.busy_interval_too_much_workload". Abort.
Check @prosa.analysis.abstract.busy_interval.busy_interval_too_much_workload.
Goal True. idtac "END|prosa.analysis.abstract.busy_interval.busy_interval_too_much_workload". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.busy_interval.t1δ_is_quiet". Abort.
Check @prosa.analysis.abstract.busy_interval.t1δ_is_quiet.
Goal True. idtac "END|prosa.analysis.abstract.busy_interval.t1δ_is_quiet". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.busy_interval.t1δ_is_quiet_contra". Abort.
Check @prosa.analysis.abstract.busy_interval.t1δ_is_quiet_contra.
Goal True. idtac "END|prosa.analysis.abstract.busy_interval.t1δ_is_quiet_contra". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.busy_interval.busy_interval_is_bounded". Abort.
Check @prosa.analysis.abstract.busy_interval.busy_interval_is_bounded.
Goal True. idtac "END|prosa.analysis.abstract.busy_interval.busy_interval_is_bounded". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.definitions.Interference". Abort.
Check @prosa.analysis.abstract.definitions.Interference.
Goal True. idtac "END|prosa.analysis.abstract.definitions.Interference". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.definitions.InterferingWorkload". Abort.
Check @prosa.analysis.abstract.definitions.InterferingWorkload.
Goal True. idtac "END|prosa.analysis.abstract.definitions.InterferingWorkload". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.definitions.cond_interference". Abort.
Check @prosa.analysis.abstract.definitions.cond_interference.
Goal True. idtac "END|prosa.analysis.abstract.definitions.cond_interference". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.definitions.cumul_cond_interference". Abort.
Check @prosa.analysis.abstract.definitions.cumul_cond_interference.
Goal True. idtac "END|prosa.analysis.abstract.definitions.cumul_cond_interference". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.definitions.cumulative_interference". Abort.
Check @prosa.analysis.abstract.definitions.cumulative_interference.
Goal True. idtac "END|prosa.analysis.abstract.definitions.cumulative_interference". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.definitions.cumulative_interfering_workload". Abort.
Check @prosa.analysis.abstract.definitions.cumulative_interfering_workload.
Goal True. idtac "END|prosa.analysis.abstract.definitions.cumulative_interfering_workload". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.definitions.no_speculative_execution". Abort.
Check @prosa.analysis.abstract.definitions.no_speculative_execution.
Goal True. idtac "END|prosa.analysis.abstract.definitions.no_speculative_execution". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.definitions.quiet_time". Abort.
Check @prosa.analysis.abstract.definitions.quiet_time.
Goal True. idtac "END|prosa.analysis.abstract.definitions.quiet_time". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.definitions.busy_interval_prefix". Abort.
Check @prosa.analysis.abstract.definitions.busy_interval_prefix.
Goal True. idtac "END|prosa.analysis.abstract.definitions.busy_interval_prefix". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.definitions.busy_interval". Abort.
Check @prosa.analysis.abstract.definitions.busy_interval.
Goal True. idtac "END|prosa.analysis.abstract.definitions.busy_interval". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.definitions.busy_interval_is_unique". Abort.
Check @prosa.analysis.abstract.definitions.busy_interval_is_unique.
Goal True. idtac "END|prosa.analysis.abstract.definitions.busy_interval_is_unique". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.definitions.work_conserving". Abort.
Check @prosa.analysis.abstract.definitions.work_conserving.
Goal True. idtac "END|prosa.analysis.abstract.definitions.work_conserving". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.definitions.busy_intervals_are_bounded_by". Abort.
Check @prosa.analysis.abstract.definitions.busy_intervals_are_bounded_by.
Goal True. idtac "END|prosa.analysis.abstract.definitions.busy_intervals_are_bounded_by". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.definitions.cond_interference_is_bounded_by". Abort.
Check @prosa.analysis.abstract.definitions.cond_interference_is_bounded_by.
Goal True. idtac "END|prosa.analysis.abstract.definitions.cond_interference_is_bounded_by". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.definitions.job_interference_is_bounded_by". Abort.
Check @prosa.analysis.abstract.definitions.job_interference_is_bounded_by.
Goal True. idtac "END|prosa.analysis.abstract.definitions.job_interference_is_bounded_by". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.ideal.abstract_rta.nonpreemptive_interference_is_bounded". Abort.
Check @prosa.analysis.abstract.ideal.abstract_rta.nonpreemptive_interference_is_bounded.
Goal True. idtac "END|prosa.analysis.abstract.ideal.abstract_rta.nonpreemptive_interference_is_bounded". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.ideal.abstract_rta.uniprocessor_response_time_bound_ideal". Abort.
Check @prosa.analysis.abstract.ideal.abstract_rta.uniprocessor_response_time_bound_ideal.
Goal True. idtac "END|prosa.analysis.abstract.ideal.abstract_rta.uniprocessor_response_time_bound_ideal". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.ideal.abstract_seq_rta.max_in_seq_hypothesis_implies_max_in_nonseq_hypothesis". Abort.
Check @prosa.analysis.abstract.ideal.abstract_seq_rta.max_in_seq_hypothesis_implies_max_in_nonseq_hypothesis.
Goal True. idtac "END|prosa.analysis.abstract.ideal.abstract_seq_rta.max_in_seq_hypothesis_implies_max_in_nonseq_hypothesis". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.ideal.abstract_seq_rta.uniprocessor_response_time_bound_seq". Abort.
Check @prosa.analysis.abstract.ideal.abstract_seq_rta.uniprocessor_response_time_bound_seq.
Goal True. idtac "END|prosa.analysis.abstract.ideal.abstract_seq_rta.uniprocessor_response_time_bound_seq". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.ideal.cumulative_bounds.cumulative_priority_inversion_is_bounded". Abort.
Check @prosa.analysis.abstract.ideal.cumulative_bounds.cumulative_priority_inversion_is_bounded.
Goal True. idtac "END|prosa.analysis.abstract.ideal.cumulative_bounds.cumulative_priority_inversion_is_bounded". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.ideal.cumulative_bounds.cumulative_interference_is_bounded_by_total_service". Abort.
Check @prosa.analysis.abstract.ideal.cumulative_bounds.cumulative_interference_is_bounded_by_total_service.
Goal True. idtac "END|prosa.analysis.abstract.ideal.cumulative_bounds.cumulative_interference_is_bounded_by_total_service". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.ideal.iw_instantiation.no_interference_when_idle". Abort.
Check @prosa.analysis.abstract.ideal.iw_instantiation.no_interference_when_idle.
Goal True. idtac "END|prosa.analysis.abstract.ideal.iw_instantiation.no_interference_when_idle". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.ideal.iw_instantiation.no_task_interference_when_idle". Abort.
Check @prosa.analysis.abstract.ideal.iw_instantiation.no_task_interference_when_idle.
Goal True. idtac "END|prosa.analysis.abstract.ideal.iw_instantiation.no_task_interference_when_idle". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.ideal.iw_instantiation.task_interference_eq_false". Abort.
Check @prosa.analysis.abstract.ideal.iw_instantiation.task_interference_eq_false.
Goal True. idtac "END|prosa.analysis.abstract.ideal.iw_instantiation.task_interference_eq_false". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.ideal.iw_instantiation.sched_athep_implies_task_interference". Abort.
Check @prosa.analysis.abstract.ideal.iw_instantiation.sched_athep_implies_task_interference.
Goal True. idtac "END|prosa.analysis.abstract.ideal.iw_instantiation.sched_athep_implies_task_interference". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.ideal.iw_instantiation.cumulative_interference_split". Abort.
Check @prosa.analysis.abstract.ideal.iw_instantiation.cumulative_interference_split.
Goal True. idtac "END|prosa.analysis.abstract.ideal.iw_instantiation.cumulative_interference_split". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.ideal.iw_instantiation.cumulative_interfering_workload_split". Abort.
Check @prosa.analysis.abstract.ideal.iw_instantiation.cumulative_interfering_workload_split.
Goal True. idtac "END|prosa.analysis.abstract.ideal.iw_instantiation.cumulative_interfering_workload_split". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.ideal.iw_instantiation.cumulative_task_interference_split". Abort.
Check @prosa.analysis.abstract.ideal.iw_instantiation.cumulative_task_interference_split.
Goal True. idtac "END|prosa.analysis.abstract.ideal.iw_instantiation.cumulative_task_interference_split". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.ideal.iw_instantiation.cumulative_iw_hep_eq_workload_of_ohep". Abort.
Check @prosa.analysis.abstract.ideal.iw_instantiation.cumulative_iw_hep_eq_workload_of_ohep.
Goal True. idtac "END|prosa.analysis.abstract.ideal.iw_instantiation.cumulative_iw_hep_eq_workload_of_ohep". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.ideal.iw_instantiation.quiet_time_cl_implies_quiet_time_ab". Abort.
Check @prosa.analysis.abstract.ideal.iw_instantiation.quiet_time_cl_implies_quiet_time_ab.
Goal True. idtac "END|prosa.analysis.abstract.ideal.iw_instantiation.quiet_time_cl_implies_quiet_time_ab". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.ideal.iw_instantiation.quiet_time_ab_implies_quiet_time_cl". Abort.
Check @prosa.analysis.abstract.ideal.iw_instantiation.quiet_time_ab_implies_quiet_time_cl.
Goal True. idtac "END|prosa.analysis.abstract.ideal.iw_instantiation.quiet_time_ab_implies_quiet_time_cl". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.ideal.iw_instantiation.instantiated_quiet_time_equivalent_quiet_time". Abort.
Check @prosa.analysis.abstract.ideal.iw_instantiation.instantiated_quiet_time_equivalent_quiet_time.
Goal True. idtac "END|prosa.analysis.abstract.ideal.iw_instantiation.instantiated_quiet_time_equivalent_quiet_time". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.ideal.iw_instantiation.instantiated_busy_interval_prefix_equivalent_busy_interval_prefix". Abort.
Check @prosa.analysis.abstract.ideal.iw_instantiation.instantiated_busy_interval_prefix_equivalent_busy_interval_prefix.
Goal True. idtac "END|prosa.analysis.abstract.ideal.iw_instantiation.instantiated_busy_interval_prefix_equivalent_busy_interval_prefix". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.ideal.iw_instantiation.instantiated_busy_interval_equivalent_busy_interval". Abort.
Check @prosa.analysis.abstract.ideal.iw_instantiation.instantiated_busy_interval_equivalent_busy_interval.
Goal True. idtac "END|prosa.analysis.abstract.ideal.iw_instantiation.instantiated_busy_interval_equivalent_busy_interval". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.ideal.iw_instantiation.abstract_busy_interval_classic_quiet_time". Abort.
Check @prosa.analysis.abstract.ideal.iw_instantiation.abstract_busy_interval_classic_quiet_time.
Goal True. idtac "END|prosa.analysis.abstract.ideal.iw_instantiation.abstract_busy_interval_classic_quiet_time". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.ideal.iw_instantiation.abstract_busy_interval_classic_busy_interval_prefix". Abort.
Check @prosa.analysis.abstract.ideal.iw_instantiation.abstract_busy_interval_classic_busy_interval_prefix.
Goal True. idtac "END|prosa.analysis.abstract.ideal.iw_instantiation.abstract_busy_interval_classic_busy_interval_prefix". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.ideal.iw_instantiation.not_interference_implies_scheduled". Abort.
Check @prosa.analysis.abstract.ideal.iw_instantiation.not_interference_implies_scheduled.
Goal True. idtac "END|prosa.analysis.abstract.ideal.iw_instantiation.not_interference_implies_scheduled". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.ideal.iw_instantiation.scheduled_implies_no_interference". Abort.
Check @prosa.analysis.abstract.ideal.iw_instantiation.scheduled_implies_no_interference.
Goal True. idtac "END|prosa.analysis.abstract.ideal.iw_instantiation.scheduled_implies_no_interference". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.ideal.iw_instantiation.instantiated_i_and_w_are_coherent_with_schedule". Abort.
Check @prosa.analysis.abstract.ideal.iw_instantiation.instantiated_i_and_w_are_coherent_with_schedule.
Goal True. idtac "END|prosa.analysis.abstract.ideal.iw_instantiation.instantiated_i_and_w_are_coherent_with_schedule". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.ideal.iw_instantiation.instantiated_interference_and_workload_consistent_with_sequential_tasks". Abort.
Check @prosa.analysis.abstract.ideal.iw_instantiation.instantiated_interference_and_workload_consistent_with_sequential_tasks.
Goal True. idtac "END|prosa.analysis.abstract.ideal.iw_instantiation.instantiated_interference_and_workload_consistent_with_sequential_tasks". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.ideal.iw_instantiation.instantiated_busy_intervals_are_bounded". Abort.
Check @prosa.analysis.abstract.ideal.iw_instantiation.instantiated_busy_intervals_are_bounded.
Goal True. idtac "END|prosa.analysis.abstract.ideal.iw_instantiation.instantiated_busy_intervals_are_bounded". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.iw_auxiliary.fold_cumul_interference". Abort.
Check @prosa.analysis.abstract.iw_auxiliary.fold_cumul_interference.
Goal True. idtac "END|prosa.analysis.abstract.iw_auxiliary.fold_cumul_interference". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.iw_auxiliary.cumul_cond_interference_alt". Abort.
Check @prosa.analysis.abstract.iw_auxiliary.cumul_cond_interference_alt.
Goal True. idtac "END|prosa.analysis.abstract.iw_auxiliary.cumul_cond_interference_alt". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.iw_auxiliary.cumulative_interference_sub". Abort.
Check @prosa.analysis.abstract.iw_auxiliary.cumulative_interference_sub.
Goal True. idtac "END|prosa.analysis.abstract.iw_auxiliary.cumulative_interference_sub". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.iw_auxiliary.cumulative_interference_cat". Abort.
Check @prosa.analysis.abstract.iw_auxiliary.cumulative_interference_cat.
Goal True. idtac "END|prosa.analysis.abstract.iw_auxiliary.cumulative_interference_cat". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.iw_auxiliary.cumul_cond_interference_ID". Abort.
Check @prosa.analysis.abstract.iw_auxiliary.cumul_cond_interference_ID.
Goal True. idtac "END|prosa.analysis.abstract.iw_auxiliary.cumul_cond_interference_ID". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.iw_auxiliary.cumul_cond_interference_pred_eq". Abort.
Check @prosa.analysis.abstract.iw_auxiliary.cumul_cond_interference_pred_eq.
Goal True. idtac "END|prosa.analysis.abstract.iw_auxiliary.cumul_cond_interference_pred_eq". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.lower_bound_on_service.interference_is_complement_to_schedule". Abort.
Check @prosa.analysis.abstract.lower_bound_on_service.interference_is_complement_to_schedule.
Goal True. idtac "END|prosa.analysis.abstract.lower_bound_on_service.interference_is_complement_to_schedule". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.lower_bound_on_service.service_and_interference_bounded". Abort.
Check @prosa.analysis.abstract.lower_bound_on_service.service_and_interference_bounded.
Goal True. idtac "END|prosa.analysis.abstract.lower_bound_on_service.service_and_interference_bounded". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.lower_bound_on_service.j_receives_enough_service". Abort.
Check @prosa.analysis.abstract.lower_bound_on_service.j_receives_enough_service.
Goal True. idtac "END|prosa.analysis.abstract.lower_bound_on_service.j_receives_enough_service". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.restricted_supply.abstract_rta.blackout_impl_interference". Abort.
Check @prosa.analysis.abstract.restricted_supply.abstract_rta.blackout_impl_interference.
Goal True. idtac "END|prosa.analysis.abstract.restricted_supply.abstract_rta.blackout_impl_interference". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.restricted_supply.abstract_rta.blackout_plus_local_is_interference". Abort.
Check @prosa.analysis.abstract.restricted_supply.abstract_rta.blackout_plus_local_is_interference.
Goal True. idtac "END|prosa.analysis.abstract.restricted_supply.abstract_rta.blackout_plus_local_is_interference". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.restricted_supply.abstract_rta.blackout_plus_local_is_interference_cumul". Abort.
Check @prosa.analysis.abstract.restricted_supply.abstract_rta.blackout_plus_local_is_interference_cumul.
Goal True. idtac "END|prosa.analysis.abstract.restricted_supply.abstract_rta.blackout_plus_local_is_interference_cumul". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.restricted_supply.abstract_rta.cumulative_job_interference_bound". Abort.
Check @prosa.analysis.abstract.restricted_supply.abstract_rta.cumulative_job_interference_bound.
Goal True. idtac "END|prosa.analysis.abstract.restricted_supply.abstract_rta.cumulative_job_interference_bound". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.restricted_supply.abstract_rta.no_intra_interference_after_F". Abort.
Check @prosa.analysis.abstract.restricted_supply.abstract_rta.no_intra_interference_after_F.
Goal True. idtac "END|prosa.analysis.abstract.restricted_supply.abstract_rta.no_intra_interference_after_F". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.restricted_supply.abstract_rta.IBF_P_bounds_interference". Abort.
Check @prosa.analysis.abstract.restricted_supply.abstract_rta.IBF_P_bounds_interference.
Goal True. idtac "END|prosa.analysis.abstract.restricted_supply.abstract_rta.IBF_P_bounds_interference". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.restricted_supply.abstract_rta.IBF_NP_bounds_interference". Abort.
Check @prosa.analysis.abstract.restricted_supply.abstract_rta.IBF_NP_bounds_interference.
Goal True. idtac "END|prosa.analysis.abstract.restricted_supply.abstract_rta.IBF_NP_bounds_interference". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.restricted_supply.abstract_rta.IBF_P_sol_le_IBF_NP". Abort.
Check @prosa.analysis.abstract.restricted_supply.abstract_rta.IBF_P_sol_le_IBF_NP.
Goal True. idtac "END|prosa.analysis.abstract.restricted_supply.abstract_rta.IBF_P_sol_le_IBF_NP". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.restricted_supply.abstract_rta.max_in_rs_hypothesis_impl_max_in_arta_hypothesis". Abort.
Check @prosa.analysis.abstract.restricted_supply.abstract_rta.max_in_rs_hypothesis_impl_max_in_arta_hypothesis.
Goal True. idtac "END|prosa.analysis.abstract.restricted_supply.abstract_rta.max_in_rs_hypothesis_impl_max_in_arta_hypothesis". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.restricted_supply.abstract_rta.uniprocessor_response_time_bound_restricted_supply". Abort.
Check @prosa.analysis.abstract.restricted_supply.abstract_rta.uniprocessor_response_time_bound_restricted_supply.
Goal True. idtac "END|prosa.analysis.abstract.restricted_supply.abstract_rta.uniprocessor_response_time_bound_restricted_supply". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.restricted_supply.abstract_seq_rta.IBF_P_bounds_interference". Abort.
Check @prosa.analysis.abstract.restricted_supply.abstract_seq_rta.IBF_P_bounds_interference.
Goal True. idtac "END|prosa.analysis.abstract.restricted_supply.abstract_seq_rta.IBF_P_bounds_interference". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.restricted_supply.abstract_seq_rta.sol_seq_rs_equation_impl_sol_rs_equation". Abort.
Check @prosa.analysis.abstract.restricted_supply.abstract_seq_rta.sol_seq_rs_equation_impl_sol_rs_equation.
Goal True. idtac "END|prosa.analysis.abstract.restricted_supply.abstract_seq_rta.sol_seq_rs_equation_impl_sol_rs_equation". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.restricted_supply.abstract_seq_rta.uniprocessor_response_time_bound_restricted_supply_seq". Abort.
Check @prosa.analysis.abstract.restricted_supply.abstract_seq_rta.uniprocessor_response_time_bound_restricted_supply_seq.
Goal True. idtac "END|prosa.analysis.abstract.restricted_supply.abstract_seq_rta.uniprocessor_response_time_bound_restricted_supply_seq". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.restricted_supply.bounded_bi.aux.busy_interval_prefix_exists". Abort.
Check @prosa.analysis.abstract.restricted_supply.bounded_bi.aux.busy_interval_prefix_exists.
Goal True. idtac "END|prosa.analysis.abstract.restricted_supply.bounded_bi.aux.busy_interval_prefix_exists". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.restricted_supply.bounded_bi.aux.service_lt_workload_in_busy". Abort.
Check @prosa.analysis.abstract.restricted_supply.bounded_bi.aux.service_lt_workload_in_busy.
Goal True. idtac "END|prosa.analysis.abstract.restricted_supply.bounded_bi.aux.service_lt_workload_in_busy". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.restricted_supply.bounded_bi.aux.workload_exceeds_interval". Abort.
Check @prosa.analysis.abstract.restricted_supply.bounded_bi.aux.workload_exceeds_interval.
Goal True. idtac "END|prosa.analysis.abstract.restricted_supply.bounded_bi.aux.workload_exceeds_interval". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.restricted_supply.bounded_bi.edf.longest_bi_with_pi_bound_is_valid". Abort.
Check @prosa.analysis.abstract.restricted_supply.bounded_bi.edf.longest_bi_with_pi_bound_is_valid.
Goal True. idtac "END|prosa.analysis.abstract.restricted_supply.bounded_bi.edf.longest_bi_with_pi_bound_is_valid". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.restricted_supply.bounded_bi.edf.busy_intervals_are_bounded_rs_edf". Abort.
Check @prosa.analysis.abstract.restricted_supply.bounded_bi.edf.busy_intervals_are_bounded_rs_edf.
Goal True. idtac "END|prosa.analysis.abstract.restricted_supply.bounded_bi.edf.busy_intervals_are_bounded_rs_edf". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.restricted_supply.bounded_bi.elf.busy_intervals_are_bounded_rs_elf". Abort.
Check @prosa.analysis.abstract.restricted_supply.bounded_bi.elf.busy_intervals_are_bounded_rs_elf.
Goal True. idtac "END|prosa.analysis.abstract.restricted_supply.bounded_bi.elf.busy_intervals_are_bounded_rs_elf". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.restricted_supply.bounded_bi.fp.busy_intervals_are_bounded_rs_fp". Abort.
Check @prosa.analysis.abstract.restricted_supply.bounded_bi.fp.busy_intervals_are_bounded_rs_fp.
Goal True. idtac "END|prosa.analysis.abstract.restricted_supply.bounded_bi.fp.busy_intervals_are_bounded_rs_fp". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.restricted_supply.bounded_bi.jlfp.busy_intervals_are_bounded_rs_jlfp". Abort.
Check @prosa.analysis.abstract.restricted_supply.bounded_bi.jlfp.busy_intervals_are_bounded_rs_jlfp.
Goal True. idtac "END|prosa.analysis.abstract.restricted_supply.bounded_bi.jlfp.busy_intervals_are_bounded_rs_jlfp". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.restricted_supply.busy_prefix.service_inversion_of_job_is_bounded_by". Abort.
Check @prosa.analysis.abstract.restricted_supply.busy_prefix.service_inversion_of_job_is_bounded_by.
Goal True. idtac "END|prosa.analysis.abstract.restricted_supply.busy_prefix.service_inversion_of_job_is_bounded_by". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.restricted_supply.busy_prefix.service_inversion_is_bounded_by". Abort.
Check @prosa.analysis.abstract.restricted_supply.busy_prefix.service_inversion_is_bounded_by.
Goal True. idtac "END|prosa.analysis.abstract.restricted_supply.busy_prefix.service_inversion_is_bounded_by". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.restricted_supply.busy_sbf.sbf_respected_in_busy_interval". Abort.
Check @prosa.analysis.abstract.restricted_supply.busy_sbf.sbf_respected_in_busy_interval.
Goal True. idtac "END|prosa.analysis.abstract.restricted_supply.busy_sbf.sbf_respected_in_busy_interval". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.restricted_supply.busy_sbf.valid_busy_sbf". Abort.
Check @prosa.analysis.abstract.restricted_supply.busy_sbf.valid_busy_sbf.
Goal True. idtac "END|prosa.analysis.abstract.restricted_supply.busy_sbf.valid_busy_sbf". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.restricted_supply.iw_instantiation.cumulative_interference_split". Abort.
Check @prosa.analysis.abstract.restricted_supply.iw_instantiation.cumulative_interference_split.
Goal True. idtac "END|prosa.analysis.abstract.restricted_supply.iw_instantiation.cumulative_interference_split". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.restricted_supply.iw_instantiation.cumulative_interfering_workload_split". Abort.
Check @prosa.analysis.abstract.restricted_supply.iw_instantiation.cumulative_interfering_workload_split.
Goal True. idtac "END|prosa.analysis.abstract.restricted_supply.iw_instantiation.cumulative_interfering_workload_split". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.restricted_supply.iw_instantiation.cumulative_task_interference_split". Abort.
Check @prosa.analysis.abstract.restricted_supply.iw_instantiation.cumulative_task_interference_split.
Goal True. idtac "END|prosa.analysis.abstract.restricted_supply.iw_instantiation.cumulative_task_interference_split". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.restricted_supply.iw_instantiation.cumulative_intra_interference_split". Abort.
Check @prosa.analysis.abstract.restricted_supply.iw_instantiation.cumulative_intra_interference_split.
Goal True. idtac "END|prosa.analysis.abstract.restricted_supply.iw_instantiation.cumulative_intra_interference_split". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.restricted_supply.iw_instantiation.cumulative_iw_hep_eq_workload_of_ohep". Abort.
Check @prosa.analysis.abstract.restricted_supply.iw_instantiation.cumulative_iw_hep_eq_workload_of_ohep.
Goal True. idtac "END|prosa.analysis.abstract.restricted_supply.iw_instantiation.cumulative_iw_hep_eq_workload_of_ohep". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.restricted_supply.iw_instantiation.quiet_time_cl_implies_quiet_time_ab". Abort.
Check @prosa.analysis.abstract.restricted_supply.iw_instantiation.quiet_time_cl_implies_quiet_time_ab.
Goal True. idtac "END|prosa.analysis.abstract.restricted_supply.iw_instantiation.quiet_time_cl_implies_quiet_time_ab". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.restricted_supply.iw_instantiation.quiet_time_ab_implies_quiet_time_cl". Abort.
Check @prosa.analysis.abstract.restricted_supply.iw_instantiation.quiet_time_ab_implies_quiet_time_cl.
Goal True. idtac "END|prosa.analysis.abstract.restricted_supply.iw_instantiation.quiet_time_ab_implies_quiet_time_cl". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.restricted_supply.iw_instantiation.instantiated_quiet_time_equivalent_quiet_time". Abort.
Check @prosa.analysis.abstract.restricted_supply.iw_instantiation.instantiated_quiet_time_equivalent_quiet_time.
Goal True. idtac "END|prosa.analysis.abstract.restricted_supply.iw_instantiation.instantiated_quiet_time_equivalent_quiet_time". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.restricted_supply.iw_instantiation.instantiated_busy_interval_prefix_equivalent_busy_interval_prefix". Abort.
Check @prosa.analysis.abstract.restricted_supply.iw_instantiation.instantiated_busy_interval_prefix_equivalent_busy_interval_prefix.
Goal True. idtac "END|prosa.analysis.abstract.restricted_supply.iw_instantiation.instantiated_busy_interval_prefix_equivalent_busy_interval_prefix". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.restricted_supply.iw_instantiation.instantiated_busy_interval_equivalent_busy_interval". Abort.
Check @prosa.analysis.abstract.restricted_supply.iw_instantiation.instantiated_busy_interval_equivalent_busy_interval.
Goal True. idtac "END|prosa.analysis.abstract.restricted_supply.iw_instantiation.instantiated_busy_interval_equivalent_busy_interval". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.restricted_supply.iw_instantiation.abstract_busy_interval_classic_quiet_time". Abort.
Check @prosa.analysis.abstract.restricted_supply.iw_instantiation.abstract_busy_interval_classic_quiet_time.
Goal True. idtac "END|prosa.analysis.abstract.restricted_supply.iw_instantiation.abstract_busy_interval_classic_quiet_time". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.restricted_supply.iw_instantiation.abstract_busy_interval_classic_busy_interval_prefix". Abort.
Check @prosa.analysis.abstract.restricted_supply.iw_instantiation.abstract_busy_interval_classic_busy_interval_prefix.
Goal True. idtac "END|prosa.analysis.abstract.restricted_supply.iw_instantiation.abstract_busy_interval_classic_busy_interval_prefix". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.restricted_supply.iw_instantiation.not_interference_implies_scheduled". Abort.
Check @prosa.analysis.abstract.restricted_supply.iw_instantiation.not_interference_implies_scheduled.
Goal True. idtac "END|prosa.analysis.abstract.restricted_supply.iw_instantiation.not_interference_implies_scheduled". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.restricted_supply.iw_instantiation.scheduled_implies_no_interference". Abort.
Check @prosa.analysis.abstract.restricted_supply.iw_instantiation.scheduled_implies_no_interference.
Goal True. idtac "END|prosa.analysis.abstract.restricted_supply.iw_instantiation.scheduled_implies_no_interference". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.restricted_supply.iw_instantiation.instantiated_i_and_w_are_coherent_with_schedule". Abort.
Check @prosa.analysis.abstract.restricted_supply.iw_instantiation.instantiated_i_and_w_are_coherent_with_schedule.
Goal True. idtac "END|prosa.analysis.abstract.restricted_supply.iw_instantiation.instantiated_i_and_w_are_coherent_with_schedule". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.restricted_supply.iw_instantiation.instantiated_interference_and_workload_consistent_with_sequential_tasks". Abort.
Check @prosa.analysis.abstract.restricted_supply.iw_instantiation.instantiated_interference_and_workload_consistent_with_sequential_tasks.
Goal True. idtac "END|prosa.analysis.abstract.restricted_supply.iw_instantiation.instantiated_interference_and_workload_consistent_with_sequential_tasks". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.restricted_supply.iw_instantiation.instantiated_i_and_w_no_speculative_execution". Abort.
Check @prosa.analysis.abstract.restricted_supply.iw_instantiation.instantiated_i_and_w_no_speculative_execution.
Goal True. idtac "END|prosa.analysis.abstract.restricted_supply.iw_instantiation.instantiated_i_and_w_no_speculative_execution". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.restricted_supply.iw_readiness.cumulative_interference_split". Abort.
Check @prosa.analysis.abstract.restricted_supply.iw_readiness.cumulative_interference_split.
Goal True. idtac "END|prosa.analysis.abstract.restricted_supply.iw_readiness.cumulative_interference_split". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.restricted_supply.iw_readiness.cumulative_interfering_workload_split". Abort.
Check @prosa.analysis.abstract.restricted_supply.iw_readiness.cumulative_interfering_workload_split.
Goal True. idtac "END|prosa.analysis.abstract.restricted_supply.iw_readiness.cumulative_interfering_workload_split". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.restricted_supply.iw_readiness.cumulative_task_interference_split". Abort.
Check @prosa.analysis.abstract.restricted_supply.iw_readiness.cumulative_task_interference_split.
Goal True. idtac "END|prosa.analysis.abstract.restricted_supply.iw_readiness.cumulative_task_interference_split". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.restricted_supply.iw_readiness.cumulative_intra_interference_split". Abort.
Check @prosa.analysis.abstract.restricted_supply.iw_readiness.cumulative_intra_interference_split.
Goal True. idtac "END|prosa.analysis.abstract.restricted_supply.iw_readiness.cumulative_intra_interference_split". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.restricted_supply.iw_readiness.cumulative_iw_hep_eq_workload_of_ohep". Abort.
Check @prosa.analysis.abstract.restricted_supply.iw_readiness.cumulative_iw_hep_eq_workload_of_ohep.
Goal True. idtac "END|prosa.analysis.abstract.restricted_supply.iw_readiness.cumulative_iw_hep_eq_workload_of_ohep". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.restricted_supply.iw_readiness.quiet_time_cl_implies_quiet_time_ab". Abort.
Check @prosa.analysis.abstract.restricted_supply.iw_readiness.quiet_time_cl_implies_quiet_time_ab.
Goal True. idtac "END|prosa.analysis.abstract.restricted_supply.iw_readiness.quiet_time_cl_implies_quiet_time_ab". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.restricted_supply.iw_readiness.quiet_time_ab_implies_quiet_time_cl". Abort.
Check @prosa.analysis.abstract.restricted_supply.iw_readiness.quiet_time_ab_implies_quiet_time_cl.
Goal True. idtac "END|prosa.analysis.abstract.restricted_supply.iw_readiness.quiet_time_ab_implies_quiet_time_cl". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.restricted_supply.iw_readiness.instantiated_quiet_time_equivalent_quiet_time". Abort.
Check @prosa.analysis.abstract.restricted_supply.iw_readiness.instantiated_quiet_time_equivalent_quiet_time.
Goal True. idtac "END|prosa.analysis.abstract.restricted_supply.iw_readiness.instantiated_quiet_time_equivalent_quiet_time". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.restricted_supply.iw_readiness.instantiated_busy_interval_prefix_equivalent_busy_interval_prefix". Abort.
Check @prosa.analysis.abstract.restricted_supply.iw_readiness.instantiated_busy_interval_prefix_equivalent_busy_interval_prefix.
Goal True. idtac "END|prosa.analysis.abstract.restricted_supply.iw_readiness.instantiated_busy_interval_prefix_equivalent_busy_interval_prefix". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.restricted_supply.iw_readiness.instantiated_busy_interval_equivalent_busy_interval". Abort.
Check @prosa.analysis.abstract.restricted_supply.iw_readiness.instantiated_busy_interval_equivalent_busy_interval.
Goal True. idtac "END|prosa.analysis.abstract.restricted_supply.iw_readiness.instantiated_busy_interval_equivalent_busy_interval". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.restricted_supply.iw_readiness.abstract_busy_interval_classic_quiet_time". Abort.
Check @prosa.analysis.abstract.restricted_supply.iw_readiness.abstract_busy_interval_classic_quiet_time.
Goal True. idtac "END|prosa.analysis.abstract.restricted_supply.iw_readiness.abstract_busy_interval_classic_quiet_time". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.restricted_supply.iw_readiness.abstract_busy_interval_classic_busy_interval_prefix". Abort.
Check @prosa.analysis.abstract.restricted_supply.iw_readiness.abstract_busy_interval_classic_busy_interval_prefix.
Goal True. idtac "END|prosa.analysis.abstract.restricted_supply.iw_readiness.abstract_busy_interval_classic_busy_interval_prefix". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.restricted_supply.iw_readiness.pending_hep_job_exists_inside_busy_interval". Abort.
Check @prosa.analysis.abstract.restricted_supply.iw_readiness.pending_hep_job_exists_inside_busy_interval.
Goal True. idtac "END|prosa.analysis.abstract.restricted_supply.iw_readiness.pending_hep_job_exists_inside_busy_interval". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.restricted_supply.iw_readiness.not_interference_implies_scheduled". Abort.
Check @prosa.analysis.abstract.restricted_supply.iw_readiness.not_interference_implies_scheduled.
Goal True. idtac "END|prosa.analysis.abstract.restricted_supply.iw_readiness.not_interference_implies_scheduled". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.restricted_supply.iw_readiness.scheduled_implies_no_interference". Abort.
Check @prosa.analysis.abstract.restricted_supply.iw_readiness.scheduled_implies_no_interference.
Goal True. idtac "END|prosa.analysis.abstract.restricted_supply.iw_readiness.scheduled_implies_no_interference". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.restricted_supply.iw_readiness.instantiated_i_and_w_are_coherent_with_schedule". Abort.
Check @prosa.analysis.abstract.restricted_supply.iw_readiness.instantiated_i_and_w_are_coherent_with_schedule.
Goal True. idtac "END|prosa.analysis.abstract.restricted_supply.iw_readiness.instantiated_i_and_w_are_coherent_with_schedule". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.restricted_supply.iw_readiness.instantiated_interference_and_workload_consistent_with_sequential_tasks". Abort.
Check @prosa.analysis.abstract.restricted_supply.iw_readiness.instantiated_interference_and_workload_consistent_with_sequential_tasks.
Goal True. idtac "END|prosa.analysis.abstract.restricted_supply.iw_readiness.instantiated_interference_and_workload_consistent_with_sequential_tasks". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.restricted_supply.iw_readiness.instantiated_i_and_w_no_speculative_execution". Abort.
Check @prosa.analysis.abstract.restricted_supply.iw_readiness.instantiated_i_and_w_no_speculative_execution.
Goal True. idtac "END|prosa.analysis.abstract.restricted_supply.iw_readiness.instantiated_i_and_w_no_speculative_execution". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.restricted_supply.search_space.edf.is_in_search_space". Abort.
Check @prosa.analysis.abstract.restricted_supply.search_space.edf.is_in_search_space.
Goal True. idtac "END|prosa.analysis.abstract.restricted_supply.search_space.edf.is_in_search_space". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.restricted_supply.search_space.edf.search_space_sub". Abort.
Check @prosa.analysis.abstract.restricted_supply.search_space.edf.search_space_sub.
Goal True. idtac "END|prosa.analysis.abstract.restricted_supply.search_space.edf.search_space_sub". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.restricted_supply.search_space.elf.is_in_search_space". Abort.
Check @prosa.analysis.abstract.restricted_supply.search_space.elf.is_in_search_space.
Goal True. idtac "END|prosa.analysis.abstract.restricted_supply.search_space.elf.is_in_search_space". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.restricted_supply.search_space.elf.search_space_sub". Abort.
Check @prosa.analysis.abstract.restricted_supply.search_space.elf.search_space_sub.
Goal True. idtac "END|prosa.analysis.abstract.restricted_supply.search_space.elf.search_space_sub". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.restricted_supply.search_space.fifo.is_in_search_space". Abort.
Check @prosa.analysis.abstract.restricted_supply.search_space.fifo.is_in_search_space.
Goal True. idtac "END|prosa.analysis.abstract.restricted_supply.search_space.fifo.is_in_search_space". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.restricted_supply.search_space.fifo.search_space_sub". Abort.
Check @prosa.analysis.abstract.restricted_supply.search_space.fifo.search_space_sub.
Goal True. idtac "END|prosa.analysis.abstract.restricted_supply.search_space.fifo.search_space_sub". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.restricted_supply.search_space.fifo_fixpoint.soln_abstract_response_time_recurrence". Abort.
Check @prosa.analysis.abstract.restricted_supply.search_space.fifo_fixpoint.soln_abstract_response_time_recurrence.
Goal True. idtac "END|prosa.analysis.abstract.restricted_supply.search_space.fifo_fixpoint.soln_abstract_response_time_recurrence". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.restricted_supply.search_space.fp.is_in_search_space". Abort.
Check @prosa.analysis.abstract.restricted_supply.search_space.fp.is_in_search_space.
Goal True. idtac "END|prosa.analysis.abstract.restricted_supply.search_space.fp.is_in_search_space". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.restricted_supply.search_space.fp.search_space_sub". Abort.
Check @prosa.analysis.abstract.restricted_supply.search_space.fp.search_space_sub.
Goal True. idtac "END|prosa.analysis.abstract.restricted_supply.search_space.fp.search_space_sub". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.restricted_supply.task_ibf_readiness.task_intra_IBF". Abort.
Check @prosa.analysis.abstract.restricted_supply.task_ibf_readiness.task_intra_IBF.
Goal True. idtac "END|prosa.analysis.abstract.restricted_supply.task_ibf_readiness.task_intra_IBF". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.restricted_supply.task_ibf_readiness.instantiated_task_intra_interference_is_bounded". Abort.
Check @prosa.analysis.abstract.restricted_supply.task_ibf_readiness.instantiated_task_intra_interference_is_bounded.
Goal True. idtac "END|prosa.analysis.abstract.restricted_supply.task_ibf_readiness.instantiated_task_intra_interference_is_bounded". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.restricted_supply.task_intra_interference_bound.task_intra_IBF". Abort.
Check @prosa.analysis.abstract.restricted_supply.task_intra_interference_bound.task_intra_IBF.
Goal True. idtac "END|prosa.analysis.abstract.restricted_supply.task_intra_interference_bound.task_intra_IBF". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.restricted_supply.task_intra_interference_bound.instantiated_task_intra_interference_is_bounded". Abort.
Check @prosa.analysis.abstract.restricted_supply.task_intra_interference_bound.instantiated_task_intra_interference_is_bounded.
Goal True. idtac "END|prosa.analysis.abstract.restricted_supply.task_intra_interference_bound.instantiated_task_intra_interference_is_bounded". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.search_space.are_equivalent_at_values_less_than". Abort.
Check @prosa.analysis.abstract.search_space.are_equivalent_at_values_less_than.
Goal True. idtac "END|prosa.analysis.abstract.search_space.are_equivalent_at_values_less_than". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.search_space.are_not_equivalent_at_values_less_than". Abort.
Check @prosa.analysis.abstract.search_space.are_not_equivalent_at_values_less_than.
Goal True. idtac "END|prosa.analysis.abstract.search_space.are_not_equivalent_at_values_less_than". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.search_space.is_in_search_space". Abort.
Check @prosa.analysis.abstract.search_space.is_in_search_space.
Goal True. idtac "END|prosa.analysis.abstract.search_space.is_in_search_space". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.search_space.representative_exists". Abort.
Check @prosa.analysis.abstract.search_space.representative_exists.
Goal True. idtac "END|prosa.analysis.abstract.search_space.representative_exists". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.search_space.solution_for_A_exists". Abort.
Check @prosa.analysis.abstract.search_space.solution_for_A_exists.
Goal True. idtac "END|prosa.analysis.abstract.search_space.solution_for_A_exists". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.search_space.search_space_switch_IBF". Abort.
Check @prosa.analysis.abstract.search_space.search_space_switch_IBF.
Goal True. idtac "END|prosa.analysis.abstract.search_space.search_space_switch_IBF". Abort.
Goal True. idtac "BEGIN|prosa.analysis.definitions.always_higher_priority.always_higher_priority". Abort.
Check @prosa.analysis.definitions.always_higher_priority.always_higher_priority.
Goal True. idtac "END|prosa.analysis.definitions.always_higher_priority.always_higher_priority". Abort.
Goal True. idtac "BEGIN|prosa.analysis.definitions.always_higher_priority.always_higher_priority_jlfp". Abort.
Check @prosa.analysis.definitions.always_higher_priority.always_higher_priority_jlfp.
Goal True. idtac "END|prosa.analysis.definitions.always_higher_priority.always_higher_priority_jlfp". Abort.
Goal True. idtac "BEGIN|prosa.analysis.definitions.blocking_bound.edf.blocking_relevant". Abort.
Check @prosa.analysis.definitions.blocking_bound.edf.blocking_relevant.
Goal True. idtac "END|prosa.analysis.definitions.blocking_bound.edf.blocking_relevant". Abort.
Goal True. idtac "BEGIN|prosa.analysis.definitions.blocking_bound.edf.blocking_bound". Abort.
Check @prosa.analysis.definitions.blocking_bound.edf.blocking_bound.
Goal True. idtac "END|prosa.analysis.definitions.blocking_bound.edf.blocking_bound". Abort.
Goal True. idtac "BEGIN|prosa.analysis.definitions.blocking_bound.elf.blocking_bound". Abort.
Check @prosa.analysis.definitions.blocking_bound.elf.blocking_bound.
Goal True. idtac "END|prosa.analysis.definitions.blocking_bound.elf.blocking_bound". Abort.
Goal True. idtac "BEGIN|prosa.analysis.definitions.blocking_bound.fp.blocking_bound". Abort.
Check @prosa.analysis.definitions.blocking_bound.fp.blocking_bound.
Goal True. idtac "END|prosa.analysis.definitions.blocking_bound.fp.blocking_bound". Abort.
Goal True. idtac "BEGIN|prosa.analysis.definitions.busy_interval.classical.quiet_time". Abort.
Check @prosa.analysis.definitions.busy_interval.classical.quiet_time.
Goal True. idtac "END|prosa.analysis.definitions.busy_interval.classical.quiet_time". Abort.
Goal True. idtac "BEGIN|prosa.analysis.definitions.busy_interval.classical.busy_interval_prefix". Abort.
Check @prosa.analysis.definitions.busy_interval.classical.busy_interval_prefix.
Goal True. idtac "END|prosa.analysis.definitions.busy_interval.classical.busy_interval_prefix". Abort.
Goal True. idtac "BEGIN|prosa.analysis.definitions.busy_interval.classical.busy_interval". Abort.
Check @prosa.analysis.definitions.busy_interval.classical.busy_interval.
Goal True. idtac "END|prosa.analysis.definitions.busy_interval.classical.busy_interval". Abort.
Goal True. idtac "BEGIN|prosa.analysis.definitions.busy_interval.classical.quiet_time_dec". Abort.
Check @prosa.analysis.definitions.busy_interval.classical.quiet_time_dec.
Goal True. idtac "END|prosa.analysis.definitions.busy_interval.classical.quiet_time_dec". Abort.
Goal True. idtac "BEGIN|prosa.analysis.definitions.busy_interval.classical.quiet_time_P". Abort.
Check @prosa.analysis.definitions.busy_interval.classical.quiet_time_P.
Goal True. idtac "END|prosa.analysis.definitions.busy_interval.classical.quiet_time_P". Abort.
Goal True. idtac "BEGIN|prosa.analysis.definitions.busy_interval.edf_pi_bound.longest_busy_interval_with_pi". Abort.
Check @prosa.analysis.definitions.busy_interval.edf_pi_bound.longest_busy_interval_with_pi.
Goal True. idtac "END|prosa.analysis.definitions.busy_interval.edf_pi_bound.longest_busy_interval_with_pi". Abort.
Goal True. idtac "BEGIN|prosa.analysis.definitions.carry_in.no_carry_in". Abort.
Check @prosa.analysis.definitions.carry_in.no_carry_in.
Goal True. idtac "END|prosa.analysis.definitions.carry_in.no_carry_in". Abort.
Goal True. idtac "BEGIN|prosa.analysis.definitions.completion_sequence.completion_sequence". Abort.
Check @prosa.analysis.definitions.completion_sequence.completion_sequence.
Goal True. idtac "END|prosa.analysis.definitions.completion_sequence.completion_sequence". Abort.
Goal True. idtac "BEGIN|prosa.analysis.definitions.delay_propagation.valid_delay_propagation_mapping". Abort.
Check @prosa.analysis.definitions.delay_propagation.valid_delay_propagation_mapping.
Goal True. idtac "END|prosa.analysis.definitions.delay_propagation.valid_delay_propagation_mapping". Abort.
Goal True. idtac "BEGIN|prosa.analysis.definitions.delay_propagation.propagated_arrival_sequence". Abort.
Check @prosa.analysis.definitions.delay_propagation.propagated_arrival_sequence.
Goal True. idtac "END|prosa.analysis.definitions.delay_propagation.propagated_arrival_sequence". Abort.
Goal True. idtac "BEGIN|prosa.analysis.definitions.delay_propagation.job_mapping_uniq". Abort.
Check @prosa.analysis.definitions.delay_propagation.job_mapping_uniq.
Goal True. idtac "END|prosa.analysis.definitions.delay_propagation.job_mapping_uniq". Abort.
Goal True. idtac "BEGIN|prosa.analysis.definitions.delay_propagation.valid_arr_seq_propagation_mapping". Abort.
Check @prosa.analysis.definitions.delay_propagation.valid_arr_seq_propagation_mapping.
Goal True. idtac "END|prosa.analysis.definitions.delay_propagation.valid_arr_seq_propagation_mapping". Abort.
Goal True. idtac "BEGIN|prosa.analysis.definitions.delay_propagation.jitter_delay_mapping_valid". Abort.
Check @prosa.analysis.definitions.delay_propagation.jitter_delay_mapping_valid.
Goal True. idtac "END|prosa.analysis.definitions.delay_propagation.jitter_delay_mapping_valid". Abort.
Goal True. idtac "BEGIN|prosa.analysis.definitions.delay_propagation.release_sequence". Abort.
Check @prosa.analysis.definitions.delay_propagation.release_sequence.
Goal True. idtac "END|prosa.analysis.definitions.delay_propagation.release_sequence". Abort.
Goal True. idtac "BEGIN|prosa.analysis.definitions.delay_propagation.jitter_arr_seq_mapping_valid". Abort.
Check @prosa.analysis.definitions.delay_propagation.jitter_arr_seq_mapping_valid.
Goal True. idtac "END|prosa.analysis.definitions.delay_propagation.jitter_arr_seq_mapping_valid". Abort.
Goal True. idtac "BEGIN|prosa.analysis.definitions.demand_bound_function.task_demand_bound_function". Abort.
Check @prosa.analysis.definitions.demand_bound_function.task_demand_bound_function.
Goal True. idtac "END|prosa.analysis.definitions.demand_bound_function.task_demand_bound_function". Abort.
Goal True. idtac "BEGIN|prosa.analysis.definitions.demand_bound_function.total_demand_bound_function". Abort.
Check @prosa.analysis.definitions.demand_bound_function.total_demand_bound_function.
Goal True. idtac "END|prosa.analysis.definitions.demand_bound_function.total_demand_bound_function". Abort.
Goal True. idtac "BEGIN|prosa.analysis.definitions.finish_time.finish_time". Abort.
Check @prosa.analysis.definitions.finish_time.finish_time.
Goal True. idtac "END|prosa.analysis.definitions.finish_time.finish_time". Abort.
Goal True. idtac "BEGIN|prosa.analysis.definitions.finish_time.finished_at_finish_time". Abort.
Check @prosa.analysis.definitions.finish_time.finished_at_finish_time.
Goal True. idtac "END|prosa.analysis.definitions.finish_time.finished_at_finish_time". Abort.
Goal True. idtac "BEGIN|prosa.analysis.definitions.finish_time.earliest_finish_time". Abort.
Check @prosa.analysis.definitions.finish_time.earliest_finish_time.
Goal True. idtac "END|prosa.analysis.definitions.finish_time.earliest_finish_time". Abort.
Goal True. idtac "BEGIN|prosa.analysis.definitions.finish_time.completes_at_finish_time". Abort.
Check @prosa.analysis.definitions.finish_time.completes_at_finish_time.
Goal True. idtac "END|prosa.analysis.definitions.finish_time.completes_at_finish_time". Abort.
Goal True. idtac "BEGIN|prosa.analysis.definitions.finish_time.response_time". Abort.
Check @prosa.analysis.definitions.finish_time.response_time.
Goal True. idtac "END|prosa.analysis.definitions.finish_time.response_time". Abort.
Goal True. idtac "BEGIN|prosa.analysis.definitions.hyperperiod.hyperperiod". Abort.
Check @prosa.analysis.definitions.hyperperiod.hyperperiod.
Goal True. idtac "END|prosa.analysis.definitions.hyperperiod.hyperperiod". Abort.
Goal True. idtac "BEGIN|prosa.analysis.definitions.hyperperiod.hyperperiod_index". Abort.
Check @prosa.analysis.definitions.hyperperiod.hyperperiod_index.
Goal True. idtac "END|prosa.analysis.definitions.hyperperiod.hyperperiod_index". Abort.
Goal True. idtac "BEGIN|prosa.analysis.definitions.hyperperiod.starting_instant_of_hyperperiod". Abort.
Check @prosa.analysis.definitions.hyperperiod.starting_instant_of_hyperperiod.
Goal True. idtac "END|prosa.analysis.definitions.hyperperiod.starting_instant_of_hyperperiod". Abort.
Goal True. idtac "BEGIN|prosa.analysis.definitions.hyperperiod.starting_instant_of_corresponding_hyperperiod". Abort.
Check @prosa.analysis.definitions.hyperperiod.starting_instant_of_corresponding_hyperperiod.
Goal True. idtac "END|prosa.analysis.definitions.hyperperiod.starting_instant_of_corresponding_hyperperiod". Abort.
Goal True. idtac "BEGIN|prosa.analysis.definitions.hyperperiod.jobs_in_hyperperiod". Abort.
Check @prosa.analysis.definitions.hyperperiod.jobs_in_hyperperiod.
Goal True. idtac "END|prosa.analysis.definitions.hyperperiod.jobs_in_hyperperiod". Abort.
Goal True. idtac "BEGIN|prosa.analysis.definitions.hyperperiod.job_index_in_hyperperiod". Abort.
Check @prosa.analysis.definitions.hyperperiod.job_index_in_hyperperiod.
Goal True. idtac "END|prosa.analysis.definitions.hyperperiod.job_index_in_hyperperiod". Abort.
Goal True. idtac "BEGIN|prosa.analysis.definitions.hyperperiod.corresponding_job_in_hyperperiod". Abort.
Check @prosa.analysis.definitions.hyperperiod.corresponding_job_in_hyperperiod.
Goal True. idtac "END|prosa.analysis.definitions.hyperperiod.corresponding_job_in_hyperperiod". Abort.
Goal True. idtac "BEGIN|prosa.analysis.definitions.infinite_jobs.infinite_jobs". Abort.
Check @prosa.analysis.definitions.infinite_jobs.infinite_jobs.
Goal True. idtac "END|prosa.analysis.definitions.infinite_jobs.infinite_jobs". Abort.
Goal True. idtac "BEGIN|prosa.analysis.definitions.interference.hp_task_interference". Abort.
Check @prosa.analysis.definitions.interference.hp_task_interference.
Goal True. idtac "END|prosa.analysis.definitions.interference.hp_task_interference". Abort.
Goal True. idtac "BEGIN|prosa.analysis.definitions.interference.ep_task_hep_job". Abort.
Check @prosa.analysis.definitions.interference.ep_task_hep_job.
Goal True. idtac "END|prosa.analysis.definitions.interference.ep_task_hep_job". Abort.
Goal True. idtac "BEGIN|prosa.analysis.definitions.interference.other_ep_task_hep_job". Abort.
Check @prosa.analysis.definitions.interference.other_ep_task_hep_job.
Goal True. idtac "END|prosa.analysis.definitions.interference.other_ep_task_hep_job". Abort.
Goal True. idtac "BEGIN|prosa.analysis.definitions.interference.hep_job_from_other_ep_task_interference". Abort.
Check @prosa.analysis.definitions.interference.hep_job_from_other_ep_task_interference.
Goal True. idtac "END|prosa.analysis.definitions.interference.hep_job_from_other_ep_task_interference". Abort.
Goal True. idtac "BEGIN|prosa.analysis.definitions.interference.hp_task_hep_job". Abort.
Check @prosa.analysis.definitions.interference.hp_task_hep_job.
Goal True. idtac "END|prosa.analysis.definitions.interference.hp_task_hep_job". Abort.
Goal True. idtac "BEGIN|prosa.analysis.definitions.interference.hep_job_from_hp_task_interference". Abort.
Check @prosa.analysis.definitions.interference.hep_job_from_hp_task_interference.
Goal True. idtac "END|prosa.analysis.definitions.interference.hep_job_from_hp_task_interference". Abort.
Goal True. idtac "BEGIN|prosa.analysis.definitions.interference.cumulative_interference_from_hep_jobs_from_hp_tasks". Abort.
Check @prosa.analysis.definitions.interference.cumulative_interference_from_hep_jobs_from_hp_tasks.
Goal True. idtac "END|prosa.analysis.definitions.interference.cumulative_interference_from_hep_jobs_from_hp_tasks". Abort.
Goal True. idtac "BEGIN|prosa.analysis.definitions.interference.cumulative_interference_from_hep_jobs_from_other_ep_tasks". Abort.
Check @prosa.analysis.definitions.interference.cumulative_interference_from_hep_jobs_from_other_ep_tasks.
Goal True. idtac "END|prosa.analysis.definitions.interference.cumulative_interference_from_hep_jobs_from_other_ep_tasks". Abort.
Goal True. idtac "BEGIN|prosa.analysis.definitions.interference.another_hep_job_interference". Abort.
Check @prosa.analysis.definitions.interference.another_hep_job_interference.
Goal True. idtac "END|prosa.analysis.definitions.interference.another_hep_job_interference". Abort.
Goal True. idtac "BEGIN|prosa.analysis.definitions.interference.another_task_hep_job_interference". Abort.
Check @prosa.analysis.definitions.interference.another_task_hep_job_interference.
Goal True. idtac "END|prosa.analysis.definitions.interference.another_task_hep_job_interference". Abort.
Goal True. idtac "BEGIN|prosa.analysis.definitions.interference.another_hep_job_of_same_task_interference". Abort.
Check @prosa.analysis.definitions.interference.another_hep_job_of_same_task_interference.
Goal True. idtac "END|prosa.analysis.definitions.interference.another_hep_job_of_same_task_interference". Abort.
Goal True. idtac "BEGIN|prosa.analysis.definitions.interference.other_hep_jobs_interfering_workload". Abort.
Check @prosa.analysis.definitions.interference.other_hep_jobs_interfering_workload.
Goal True. idtac "END|prosa.analysis.definitions.interference.other_hep_jobs_interfering_workload". Abort.
Goal True. idtac "BEGIN|prosa.analysis.definitions.interference.cumulative_another_hep_job_interference". Abort.
Check @prosa.analysis.definitions.interference.cumulative_another_hep_job_interference.
Goal True. idtac "END|prosa.analysis.definitions.interference.cumulative_another_hep_job_interference". Abort.
Goal True. idtac "BEGIN|prosa.analysis.definitions.interference.cumulative_another_task_hep_job_interference". Abort.
Check @prosa.analysis.definitions.interference.cumulative_another_task_hep_job_interference.
Goal True. idtac "END|prosa.analysis.definitions.interference.cumulative_another_task_hep_job_interference". Abort.
Goal True. idtac "BEGIN|prosa.analysis.definitions.interference.cumulative_other_hep_jobs_interfering_workload". Abort.
Check @prosa.analysis.definitions.interference.cumulative_other_hep_jobs_interfering_workload.
Goal True. idtac "END|prosa.analysis.definitions.interference.cumulative_other_hep_jobs_interfering_workload". Abort.
Goal True. idtac "BEGIN|prosa.analysis.definitions.job_response_time.job_response_time_exceeds". Abort.
Check @prosa.analysis.definitions.job_response_time.job_response_time_exceeds.
Goal True. idtac "END|prosa.analysis.definitions.job_response_time.job_response_time_exceeds". Abort.
Goal True. idtac "BEGIN|prosa.analysis.definitions.overheads.priority_bump.priority_bump". Abort.
Check @prosa.analysis.definitions.overheads.priority_bump.priority_bump.
Goal True. idtac "END|prosa.analysis.definitions.overheads.priority_bump.priority_bump". Abort.
Goal True. idtac "BEGIN|prosa.analysis.definitions.overheads.schedule_change.schedule_change". Abort.
Check @prosa.analysis.definitions.overheads.schedule_change.schedule_change.
Goal True. idtac "END|prosa.analysis.definitions.overheads.schedule_change.schedule_change". Abort.
Goal True. idtac "BEGIN|prosa.analysis.definitions.overheads.schedule_change.number_schedule_changes". Abort.
Check @prosa.analysis.definitions.overheads.schedule_change.number_schedule_changes.
Goal True. idtac "END|prosa.analysis.definitions.overheads.schedule_change.number_schedule_changes". Abort.
Goal True. idtac "BEGIN|prosa.analysis.definitions.overheads.schedule_change.no_schedule_changes_during". Abort.
Check @prosa.analysis.definitions.overheads.schedule_change.no_schedule_changes_during.
Goal True. idtac "END|prosa.analysis.definitions.overheads.schedule_change.no_schedule_changes_during". Abort.
Goal True. idtac "BEGIN|prosa.analysis.definitions.overheads.schedule_change.scheduled_job_invariant". Abort.
Check @prosa.analysis.definitions.overheads.schedule_change.scheduled_job_invariant.
Goal True. idtac "END|prosa.analysis.definitions.overheads.schedule_change.scheduled_job_invariant". Abort.
Goal True. idtac "BEGIN|prosa.analysis.definitions.priority.classes.JLFP_FP_compatible". Abort.
Check @prosa.analysis.definitions.priority.classes.JLFP_FP_compatible.
Goal True. idtac "END|prosa.analysis.definitions.priority.classes.JLFP_FP_compatible". Abort.
Goal True. idtac "BEGIN|prosa.analysis.definitions.priority_inversion.priority_inversion". Abort.
Check @prosa.analysis.definitions.priority_inversion.priority_inversion.
Goal True. idtac "END|prosa.analysis.definitions.priority_inversion.priority_inversion". Abort.
Goal True. idtac "BEGIN|prosa.analysis.definitions.priority_inversion.priority_inversion_cond". Abort.
Check @prosa.analysis.definitions.priority_inversion.priority_inversion_cond.
Goal True. idtac "END|prosa.analysis.definitions.priority_inversion.priority_inversion_cond". Abort.
Goal True. idtac "BEGIN|prosa.analysis.definitions.priority_inversion.cumulative_priority_inversion". Abort.
Check @prosa.analysis.definitions.priority_inversion.cumulative_priority_inversion.
Goal True. idtac "END|prosa.analysis.definitions.priority_inversion.cumulative_priority_inversion". Abort.
Goal True. idtac "BEGIN|prosa.analysis.definitions.priority_inversion.cumulative_priority_inversion_cond". Abort.
Check @prosa.analysis.definitions.priority_inversion.cumulative_priority_inversion_cond.
Goal True. idtac "END|prosa.analysis.definitions.priority_inversion.cumulative_priority_inversion_cond". Abort.
Goal True. idtac "BEGIN|prosa.analysis.definitions.priority_inversion.priority_inversion_of_job_is_bounded_by". Abort.
Check @prosa.analysis.definitions.priority_inversion.priority_inversion_of_job_is_bounded_by.
Goal True. idtac "END|prosa.analysis.definitions.priority_inversion.priority_inversion_of_job_is_bounded_by". Abort.
Goal True. idtac "BEGIN|prosa.analysis.definitions.priority_inversion.priority_inversion_of_job_cond_is_bounded_by". Abort.
Check @prosa.analysis.definitions.priority_inversion.priority_inversion_of_job_cond_is_bounded_by.
Goal True. idtac "END|prosa.analysis.definitions.priority_inversion.priority_inversion_of_job_cond_is_bounded_by". Abort.
Goal True. idtac "BEGIN|prosa.analysis.definitions.priority_inversion.priority_inversion_is_bounded_by". Abort.
Check @prosa.analysis.definitions.priority_inversion.priority_inversion_is_bounded_by.
Goal True. idtac "END|prosa.analysis.definitions.priority_inversion.priority_inversion_is_bounded_by". Abort.
Goal True. idtac "BEGIN|prosa.analysis.definitions.priority_inversion.priority_inversion_cond_is_bounded_by". Abort.
Check @prosa.analysis.definitions.priority_inversion.priority_inversion_cond_is_bounded_by.
Goal True. idtac "END|prosa.analysis.definitions.priority_inversion.priority_inversion_cond_is_bounded_by". Abort.
Goal True. idtac "BEGIN|prosa.analysis.definitions.progress.job_has_progressed". Abort.
Check @prosa.analysis.definitions.progress.job_has_progressed.
Goal True. idtac "END|prosa.analysis.definitions.progress.job_has_progressed". Abort.
Goal True. idtac "BEGIN|prosa.analysis.definitions.progress.no_progress". Abort.
Check @prosa.analysis.definitions.progress.no_progress.
Goal True. idtac "END|prosa.analysis.definitions.progress.no_progress". Abort.
Goal True. idtac "BEGIN|prosa.analysis.definitions.progress.no_progress_equiv". Abort.
Check @prosa.analysis.definitions.progress.no_progress_equiv.
Goal True. idtac "END|prosa.analysis.definitions.progress.no_progress_equiv". Abort.
Goal True. idtac "BEGIN|prosa.analysis.definitions.progress.no_progress_for". Abort.
Check @prosa.analysis.definitions.progress.no_progress_for.
Goal True. idtac "END|prosa.analysis.definitions.progress.no_progress_for". Abort.
Goal True. idtac "BEGIN|prosa.analysis.definitions.readiness.nonclairvoyant_readiness". Abort.
Check @prosa.analysis.definitions.readiness.nonclairvoyant_readiness.
Goal True. idtac "END|prosa.analysis.definitions.readiness.nonclairvoyant_readiness". Abort.
Goal True. idtac "BEGIN|prosa.analysis.definitions.readiness.valid_nonpreemptive_readiness". Abort.
Check @prosa.analysis.definitions.readiness.valid_nonpreemptive_readiness.
Goal True. idtac "END|prosa.analysis.definitions.readiness.valid_nonpreemptive_readiness". Abort.
Goal True. idtac "BEGIN|prosa.analysis.definitions.readiness.sequential_readiness". Abort.
Check @prosa.analysis.definitions.readiness.sequential_readiness.
Goal True. idtac "END|prosa.analysis.definitions.readiness.sequential_readiness". Abort.
Goal True. idtac "BEGIN|prosa.analysis.definitions.readiness_interference.some_hep_job_ready". Abort.
Check @prosa.analysis.definitions.readiness_interference.some_hep_job_ready.
Goal True. idtac "END|prosa.analysis.definitions.readiness_interference.some_hep_job_ready". Abort.
Goal True. idtac "BEGIN|prosa.analysis.definitions.readiness_interference.cumulative_readiness_interference". Abort.
Check @prosa.analysis.definitions.readiness_interference.cumulative_readiness_interference.
Goal True. idtac "END|prosa.analysis.definitions.readiness_interference.cumulative_readiness_interference". Abort.
Goal True. idtac "BEGIN|prosa.analysis.definitions.readiness_interference.readiness_interference_is_bounded". Abort.
Check @prosa.analysis.definitions.readiness_interference.readiness_interference_is_bounded.
Goal True. idtac "END|prosa.analysis.definitions.readiness_interference.readiness_interference_is_bounded". Abort.
Goal True. idtac "BEGIN|prosa.analysis.definitions.request_bound_function.task_request_bound_function". Abort.
Check @prosa.analysis.definitions.request_bound_function.task_request_bound_function.
Goal True. idtac "END|prosa.analysis.definitions.request_bound_function.task_request_bound_function". Abort.
Goal True. idtac "BEGIN|prosa.analysis.definitions.request_bound_function.total_request_bound_function". Abort.
Check @prosa.analysis.definitions.request_bound_function.total_request_bound_function.
Goal True. idtac "END|prosa.analysis.definitions.request_bound_function.total_request_bound_function". Abort.
Goal True. idtac "BEGIN|prosa.analysis.definitions.request_bound_function.total_hep_request_bound_function_FP". Abort.
Check @prosa.analysis.definitions.request_bound_function.total_hep_request_bound_function_FP.
Goal True. idtac "END|prosa.analysis.definitions.request_bound_function.total_hep_request_bound_function_FP". Abort.
Goal True. idtac "BEGIN|prosa.analysis.definitions.request_bound_function.total_ohep_request_bound_function_FP". Abort.
Check @prosa.analysis.definitions.request_bound_function.total_ohep_request_bound_function_FP.
Goal True. idtac "END|prosa.analysis.definitions.request_bound_function.total_ohep_request_bound_function_FP". Abort.
Goal True. idtac "BEGIN|prosa.analysis.definitions.request_bound_function.total_ep_request_bound_function_FP". Abort.
Check @prosa.analysis.definitions.request_bound_function.total_ep_request_bound_function_FP.
Goal True. idtac "END|prosa.analysis.definitions.request_bound_function.total_ep_request_bound_function_FP". Abort.
Goal True. idtac "BEGIN|prosa.analysis.definitions.request_bound_function.total_hp_request_bound_function_FP". Abort.
Check @prosa.analysis.definitions.request_bound_function.total_hp_request_bound_function_FP.
Goal True. idtac "END|prosa.analysis.definitions.request_bound_function.total_hp_request_bound_function_FP". Abort.
Goal True. idtac "BEGIN|prosa.analysis.definitions.sbf.average.average_resource_model". Abort.
Check @prosa.analysis.definitions.sbf.average.average_resource_model.
Goal True. idtac "END|prosa.analysis.definitions.sbf.average.average_resource_model". Abort.
Goal True. idtac "BEGIN|prosa.analysis.definitions.sbf.average.arm_sbf". Abort.
Check @prosa.analysis.definitions.sbf.average.arm_sbf.
Goal True. idtac "END|prosa.analysis.definitions.sbf.average.arm_sbf". Abort.
Goal True. idtac "BEGIN|prosa.analysis.definitions.sbf.busy.sbf_respected_in_busy_interval". Abort.
Check @prosa.analysis.definitions.sbf.busy.sbf_respected_in_busy_interval.
Goal True. idtac "END|prosa.analysis.definitions.sbf.busy.sbf_respected_in_busy_interval". Abort.
Goal True. idtac "BEGIN|prosa.analysis.definitions.sbf.busy.valid_busy_sbf". Abort.
Check @prosa.analysis.definitions.sbf.busy.valid_busy_sbf.
Goal True. idtac "END|prosa.analysis.definitions.sbf.busy.valid_busy_sbf". Abort.
Goal True. idtac "BEGIN|prosa.analysis.definitions.sbf.periodic.periodic_resource_model". Abort.
Check @prosa.analysis.definitions.sbf.periodic.periodic_resource_model.
Goal True. idtac "END|prosa.analysis.definitions.sbf.periodic.periodic_resource_model". Abort.
Goal True. idtac "BEGIN|prosa.analysis.definitions.sbf.periodic.prm_sbf". Abort.
Check @prosa.analysis.definitions.sbf.periodic.prm_sbf.
Goal True. idtac "END|prosa.analysis.definitions.sbf.periodic.prm_sbf". Abort.
Goal True. idtac "BEGIN|prosa.analysis.definitions.sbf.plain.supply_bound_function_respected". Abort.
Check @prosa.analysis.definitions.sbf.plain.supply_bound_function_respected.
Goal True. idtac "END|prosa.analysis.definitions.sbf.plain.supply_bound_function_respected". Abort.
Goal True. idtac "BEGIN|prosa.analysis.definitions.sbf.plain.valid_supply_bound_function". Abort.
Check @prosa.analysis.definitions.sbf.plain.valid_supply_bound_function.
Goal True. idtac "END|prosa.analysis.definitions.sbf.plain.valid_supply_bound_function". Abort.
Goal True. idtac "BEGIN|prosa.analysis.definitions.sbf.plain.sbf_respected_simplified". Abort.
Check @prosa.analysis.definitions.sbf.plain.sbf_respected_simplified.
Goal True. idtac "END|prosa.analysis.definitions.sbf.plain.sbf_respected_simplified". Abort.
Goal True. idtac "BEGIN|prosa.analysis.definitions.sbf.pred.pred_sbf_respected". Abort.
Check @prosa.analysis.definitions.sbf.pred.pred_sbf_respected.
Goal True. idtac "END|prosa.analysis.definitions.sbf.pred.pred_sbf_respected". Abort.
Goal True. idtac "BEGIN|prosa.analysis.definitions.sbf.pred.valid_pred_sbf". Abort.
Check @prosa.analysis.definitions.sbf.pred.valid_pred_sbf.
Goal True. idtac "END|prosa.analysis.definitions.sbf.pred.valid_pred_sbf". Abort.
Goal True. idtac "BEGIN|prosa.analysis.definitions.sbf.pred.sbf_is_monotone". Abort.
Check @prosa.analysis.definitions.sbf.pred.sbf_is_monotone.
Goal True. idtac "END|prosa.analysis.definitions.sbf.pred.sbf_is_monotone". Abort.
Goal True. idtac "BEGIN|prosa.analysis.definitions.sbf.pred.unit_supply_bound_function". Abort.
Check @prosa.analysis.definitions.sbf.pred.unit_supply_bound_function.
Goal True. idtac "END|prosa.analysis.definitions.sbf.pred.unit_supply_bound_function". Abort.
Goal True. idtac "BEGIN|prosa.analysis.definitions.sbf.pred.sbf_bounded_by_duration". Abort.
Check @prosa.analysis.definitions.sbf.pred.sbf_bounded_by_duration.
Goal True. idtac "END|prosa.analysis.definitions.sbf.pred.sbf_bounded_by_duration". Abort.
Goal True. idtac "BEGIN|prosa.analysis.definitions.sbf.sbf.SupplyBoundFunction". Abort.
Check @prosa.analysis.definitions.sbf.sbf.SupplyBoundFunction.
Goal True. idtac "END|prosa.analysis.definitions.sbf.sbf.SupplyBoundFunction". Abort.
Goal True. idtac "BEGIN|prosa.analysis.definitions.schedulability.task_response_time_bound". Abort.
Check @prosa.analysis.definitions.schedulability.task_response_time_bound.
Goal True. idtac "END|prosa.analysis.definitions.schedulability.task_response_time_bound". Abort.
Goal True. idtac "BEGIN|prosa.analysis.definitions.schedulability.schedulable_task". Abort.
Check @prosa.analysis.definitions.schedulability.schedulable_task.
Goal True. idtac "END|prosa.analysis.definitions.schedulability.schedulable_task". Abort.
Goal True. idtac "BEGIN|prosa.analysis.definitions.schedulability.schedulability_from_response_time_bound". Abort.
Check @prosa.analysis.definitions.schedulability.schedulability_from_response_time_bound.
Goal True. idtac "END|prosa.analysis.definitions.schedulability.schedulability_from_response_time_bound". Abort.
Goal True. idtac "BEGIN|prosa.analysis.definitions.schedulability.all_deadlines_met". Abort.
Check @prosa.analysis.definitions.schedulability.all_deadlines_met.
Goal True. idtac "END|prosa.analysis.definitions.schedulability.all_deadlines_met". Abort.
Goal True. idtac "BEGIN|prosa.analysis.definitions.schedulability.all_deadlines_of_arrivals_met". Abort.
Check @prosa.analysis.definitions.schedulability.all_deadlines_of_arrivals_met.
Goal True. idtac "END|prosa.analysis.definitions.schedulability.all_deadlines_of_arrivals_met". Abort.
Goal True. idtac "BEGIN|prosa.analysis.definitions.schedulability.all_deadlines_met_in_valid_schedule". Abort.
Check @prosa.analysis.definitions.schedulability.all_deadlines_met_in_valid_schedule.
Goal True. idtac "END|prosa.analysis.definitions.schedulability.all_deadlines_met_in_valid_schedule". Abort.
Goal True. idtac "BEGIN|prosa.analysis.definitions.schedule_prefix.identical_prefix". Abort.
Check @prosa.analysis.definitions.schedule_prefix.identical_prefix.
Goal True. idtac "END|prosa.analysis.definitions.schedule_prefix.identical_prefix". Abort.
Goal True. idtac "BEGIN|prosa.analysis.definitions.schedule_prefix.identical_prefix_scheduled_at". Abort.
Check @prosa.analysis.definitions.schedule_prefix.identical_prefix_scheduled_at.
Goal True. idtac "END|prosa.analysis.definitions.schedule_prefix.identical_prefix_scheduled_at". Abort.
Goal True. idtac "BEGIN|prosa.analysis.definitions.schedule_prefix.identical_prefix_inclusion". Abort.
Check @prosa.analysis.definitions.schedule_prefix.identical_prefix_inclusion.
Goal True. idtac "END|prosa.analysis.definitions.schedule_prefix.identical_prefix_inclusion". Abort.
Goal True. idtac "BEGIN|prosa.analysis.definitions.service.served_jobs_at". Abort.
Check @prosa.analysis.definitions.service.served_jobs_at.
Goal True. idtac "END|prosa.analysis.definitions.service.served_jobs_at". Abort.
Goal True. idtac "BEGIN|prosa.analysis.definitions.service.served_job_at". Abort.
Check @prosa.analysis.definitions.service.served_job_at.
Goal True. idtac "END|prosa.analysis.definitions.service.served_job_at". Abort.
Goal True. idtac "BEGIN|prosa.analysis.definitions.service_inversion.busy_prefix.service_inversion_of_job_is_bounded_by". Abort.
Check @prosa.analysis.definitions.service_inversion.busy_prefix.service_inversion_of_job_is_bounded_by.
Goal True. idtac "END|prosa.analysis.definitions.service_inversion.busy_prefix.service_inversion_of_job_is_bounded_by". Abort.
Goal True. idtac "BEGIN|prosa.analysis.definitions.service_inversion.busy_prefix.service_inversion_is_bounded_by". Abort.
Check @prosa.analysis.definitions.service_inversion.busy_prefix.service_inversion_is_bounded_by.
Goal True. idtac "END|prosa.analysis.definitions.service_inversion.busy_prefix.service_inversion_is_bounded_by". Abort.
Goal True. idtac "BEGIN|prosa.analysis.definitions.service_inversion.pred.service_inversion". Abort.
Check @prosa.analysis.definitions.service_inversion.pred.service_inversion.
Goal True. idtac "END|prosa.analysis.definitions.service_inversion.pred.service_inversion". Abort.
Goal True. idtac "BEGIN|prosa.analysis.definitions.service_inversion.pred.cumulative_service_inversion". Abort.
Check @prosa.analysis.definitions.service_inversion.pred.cumulative_service_inversion.
Goal True. idtac "END|prosa.analysis.definitions.service_inversion.pred.cumulative_service_inversion". Abort.
Goal True. idtac "BEGIN|prosa.analysis.definitions.service_inversion.pred.pred_service_inversion_of_job_is_bounded_by". Abort.
Check @prosa.analysis.definitions.service_inversion.pred.pred_service_inversion_of_job_is_bounded_by.
Goal True. idtac "END|prosa.analysis.definitions.service_inversion.pred.pred_service_inversion_of_job_is_bounded_by". Abort.
Goal True. idtac "BEGIN|prosa.analysis.definitions.service_inversion.pred.pred_service_inversion_is_bounded_by". Abort.
Check @prosa.analysis.definitions.service_inversion.pred.pred_service_inversion_is_bounded_by.
Goal True. idtac "END|prosa.analysis.definitions.service_inversion.pred.pred_service_inversion_is_bounded_by". Abort.
Goal True. idtac "BEGIN|prosa.analysis.definitions.service_inversion.readiness_aware.service_inversion". Abort.
Check @prosa.analysis.definitions.service_inversion.readiness_aware.service_inversion.
Goal True. idtac "END|prosa.analysis.definitions.service_inversion.readiness_aware.service_inversion". Abort.
Goal True. idtac "BEGIN|prosa.analysis.definitions.service_inversion.readiness_aware.cumulative_service_inversion". Abort.
Check @prosa.analysis.definitions.service_inversion.readiness_aware.cumulative_service_inversion.
Goal True. idtac "END|prosa.analysis.definitions.service_inversion.readiness_aware.cumulative_service_inversion". Abort.
Goal True. idtac "BEGIN|prosa.analysis.definitions.service_inversion.readiness_aware.service_inversion_is_bounded". Abort.
Check @prosa.analysis.definitions.service_inversion.readiness_aware.service_inversion_is_bounded.
Goal True. idtac "END|prosa.analysis.definitions.service_inversion.readiness_aware.service_inversion_is_bounded". Abort.
Goal True. idtac "BEGIN|prosa.analysis.definitions.tardiness.task_tardiness_is_bounded". Abort.
Check @prosa.analysis.definitions.tardiness.task_tardiness_is_bounded.
Goal True. idtac "END|prosa.analysis.definitions.tardiness.task_tardiness_is_bounded". Abort.
Goal True. idtac "BEGIN|prosa.analysis.definitions.task_schedule.scheduled_jobs_of_task_at". Abort.
Check @prosa.analysis.definitions.task_schedule.scheduled_jobs_of_task_at.
Goal True. idtac "END|prosa.analysis.definitions.task_schedule.scheduled_jobs_of_task_at". Abort.
Goal True. idtac "BEGIN|prosa.analysis.definitions.task_schedule.task_scheduled_at". Abort.
Check @prosa.analysis.definitions.task_schedule.task_scheduled_at.
Goal True. idtac "END|prosa.analysis.definitions.task_schedule.task_scheduled_at". Abort.
Goal True. idtac "BEGIN|prosa.analysis.definitions.task_schedule.task_service_at". Abort.
Check @prosa.analysis.definitions.task_schedule.task_service_at.
Goal True. idtac "END|prosa.analysis.definitions.task_schedule.task_service_at". Abort.
Goal True. idtac "BEGIN|prosa.analysis.definitions.task_schedule.task_service_during". Abort.
Check @prosa.analysis.definitions.task_schedule.task_service_during.
Goal True. idtac "END|prosa.analysis.definitions.task_schedule.task_service_during". Abort.
Goal True. idtac "BEGIN|prosa.analysis.definitions.task_schedule.task_service". Abort.
Check @prosa.analysis.definitions.task_schedule.task_service.
Goal True. idtac "END|prosa.analysis.definitions.task_schedule.task_service". Abort.
Goal True. idtac "BEGIN|prosa.analysis.definitions.task_schedule.served_jobs_of_task_at". Abort.
Check @prosa.analysis.definitions.task_schedule.served_jobs_of_task_at.
Goal True. idtac "END|prosa.analysis.definitions.task_schedule.served_jobs_of_task_at". Abort.
Goal True. idtac "BEGIN|prosa.analysis.definitions.task_schedule.task_served_at". Abort.
Check @prosa.analysis.definitions.task_schedule.task_served_at.
Goal True. idtac "END|prosa.analysis.definitions.task_schedule.task_served_at". Abort.
Goal True. idtac "BEGIN|prosa.analysis.definitions.work_bearing_readiness.work_bearing_readiness". Abort.
Check @prosa.analysis.definitions.work_bearing_readiness.work_bearing_readiness.
Goal True. idtac "END|prosa.analysis.definitions.work_bearing_readiness.work_bearing_readiness". Abort.
Goal True. idtac "BEGIN|prosa.analysis.definitions.workload.bounded.athep_workload_is_bounded". Abort.
Check @prosa.analysis.definitions.workload.bounded.athep_workload_is_bounded.
Goal True. idtac "END|prosa.analysis.definitions.workload.bounded.athep_workload_is_bounded". Abort.
Goal True. idtac "BEGIN|prosa.analysis.definitions.workload.edf_athep_bound.bound_on_athep_workload". Abort.
Check @prosa.analysis.definitions.workload.edf_athep_bound.bound_on_athep_workload.
Goal True. idtac "END|prosa.analysis.definitions.workload.edf_athep_bound.bound_on_athep_workload". Abort.
Goal True. idtac "BEGIN|prosa.analysis.definitions.workload.elf_athep_bound.ep_task_interfering_interval_length". Abort.
Check @prosa.analysis.definitions.workload.elf_athep_bound.ep_task_interfering_interval_length.
Goal True. idtac "END|prosa.analysis.definitions.workload.elf_athep_bound.ep_task_interfering_interval_length". Abort.
Goal True. idtac "BEGIN|prosa.analysis.definitions.workload.elf_athep_bound.bound_on_ep_task_workload". Abort.
Check @prosa.analysis.definitions.workload.elf_athep_bound.bound_on_ep_task_workload.
Goal True. idtac "END|prosa.analysis.definitions.workload.elf_athep_bound.bound_on_ep_task_workload". Abort.
Goal True. idtac "BEGIN|prosa.analysis.definitions.workload.elf_athep_bound.bound_on_hp_task_workload". Abort.
Check @prosa.analysis.definitions.workload.elf_athep_bound.bound_on_hp_task_workload.
Goal True. idtac "END|prosa.analysis.definitions.workload.elf_athep_bound.bound_on_hp_task_workload". Abort.
Goal True. idtac "BEGIN|prosa.analysis.definitions.workload.elf_athep_bound.bound_on_athep_workload". Abort.
Check @prosa.analysis.definitions.workload.elf_athep_bound.bound_on_athep_workload.
Goal True. idtac "END|prosa.analysis.definitions.workload.elf_athep_bound.bound_on_athep_workload". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.SBF.valid_pred_sbf_switch_predicate". Abort.
Check @prosa.analysis.facts.SBF.valid_pred_sbf_switch_predicate.
Goal True. idtac "END|prosa.analysis.facts.SBF.valid_pred_sbf_switch_predicate". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.SBF.blackout_during_bound_SBF". Abort.
Check @prosa.analysis.facts.SBF.blackout_during_bound_SBF.
Goal True. idtac "END|prosa.analysis.facts.SBF.blackout_during_bound_SBF". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.SBF.complement_SBF_monotone". Abort.
Check @prosa.analysis.facts.SBF.complement_SBF_monotone.
Goal True. idtac "END|prosa.analysis.facts.SBF.complement_SBF_monotone". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.arrivals.arrived_between_before". Abort.
Check @prosa.analysis.facts.behavior.arrivals.arrived_between_before.
Goal True. idtac "END|prosa.analysis.facts.behavior.arrivals.arrived_between_before". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.arrivals.arrived_before_has_arrived". Abort.
Check @prosa.analysis.facts.behavior.arrivals.arrived_before_has_arrived.
Goal True. idtac "END|prosa.analysis.facts.behavior.arrivals.arrived_before_has_arrived". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.arrivals.consistent_times_valid_arrival". Abort.
Check @prosa.analysis.facts.behavior.arrivals.consistent_times_valid_arrival.
Goal True. idtac "END|prosa.analysis.facts.behavior.arrivals.consistent_times_valid_arrival". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.arrivals.uniq_valid_arrival". Abort.
Check @prosa.analysis.facts.behavior.arrivals.uniq_valid_arrival.
Goal True. idtac "END|prosa.analysis.facts.behavior.arrivals.uniq_valid_arrival". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.arrivals.any_ready_job_is_pending". Abort.
Check @prosa.analysis.facts.behavior.arrivals.any_ready_job_is_pending.
Goal True. idtac "END|prosa.analysis.facts.behavior.arrivals.any_ready_job_is_pending". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.arrivals.ready_implies_arrived". Abort.
Check @prosa.analysis.facts.behavior.arrivals.ready_implies_arrived.
Goal True. idtac "END|prosa.analysis.facts.behavior.arrivals.ready_implies_arrived". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.arrivals.jobs_must_arrive_to_be_ready". Abort.
Check @prosa.analysis.facts.behavior.arrivals.jobs_must_arrive_to_be_ready.
Goal True. idtac "END|prosa.analysis.facts.behavior.arrivals.jobs_must_arrive_to_be_ready". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.arrivals.valid_schedule_implies_jobs_must_arrive_to_execute". Abort.
Check @prosa.analysis.facts.behavior.arrivals.valid_schedule_implies_jobs_must_arrive_to_execute.
Goal True. idtac "END|prosa.analysis.facts.behavior.arrivals.valid_schedule_implies_jobs_must_arrive_to_execute". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.arrivals.backlogged_implies_arrived". Abort.
Check @prosa.analysis.facts.behavior.arrivals.backlogged_implies_arrived.
Goal True. idtac "END|prosa.analysis.facts.behavior.arrivals.backlogged_implies_arrived". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.arrivals.backlogged_implies_incomplete". Abort.
Check @prosa.analysis.facts.behavior.arrivals.backlogged_implies_incomplete.
Goal True. idtac "END|prosa.analysis.facts.behavior.arrivals.backlogged_implies_incomplete". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.arrivals.job_scheduled_implies_ready". Abort.
Check @prosa.analysis.facts.behavior.arrivals.job_scheduled_implies_ready.
Goal True. idtac "END|prosa.analysis.facts.behavior.arrivals.job_scheduled_implies_ready". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.arrivals.valid_schedule_jobs_come_from_arrival_sequence". Abort.
Check @prosa.analysis.facts.behavior.arrivals.valid_schedule_jobs_come_from_arrival_sequence.
Goal True. idtac "END|prosa.analysis.facts.behavior.arrivals.valid_schedule_jobs_come_from_arrival_sequence". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.arrivals.valid_schedule_jobs_must_be_ready_to_execute". Abort.
Check @prosa.analysis.facts.behavior.arrivals.valid_schedule_jobs_must_be_ready_to_execute.
Goal True. idtac "END|prosa.analysis.facts.behavior.arrivals.valid_schedule_jobs_must_be_ready_to_execute". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.arrivals.arrivals_between_cat". Abort.
Check @prosa.analysis.facts.behavior.arrivals.arrivals_between_cat.
Goal True. idtac "END|prosa.analysis.facts.behavior.arrivals.arrivals_between_cat". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.arrivals.arrivals_P_cat". Abort.
Check @prosa.analysis.facts.behavior.arrivals.arrivals_P_cat.
Goal True. idtac "END|prosa.analysis.facts.behavior.arrivals.arrivals_P_cat". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.arrivals.arrivals_between_mem_cat". Abort.
Check @prosa.analysis.facts.behavior.arrivals.arrivals_between_mem_cat.
Goal True. idtac "END|prosa.analysis.facts.behavior.arrivals.arrivals_between_mem_cat". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.arrivals.arrivals_between_sub". Abort.
Check @prosa.analysis.facts.behavior.arrivals.arrivals_between_sub.
Goal True. idtac "END|prosa.analysis.facts.behavior.arrivals.arrivals_between_sub". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.arrivals.job_arrival_arrives_at". Abort.
Check @prosa.analysis.facts.behavior.arrivals.job_arrival_arrives_at.
Goal True. idtac "END|prosa.analysis.facts.behavior.arrivals.job_arrival_arrives_at". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.arrivals.job_arrival_at". Abort.
Check @prosa.analysis.facts.behavior.arrivals.job_arrival_at.
Goal True. idtac "END|prosa.analysis.facts.behavior.arrivals.job_arrival_at". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.arrivals.job_in_arrivals_at". Abort.
Check @prosa.analysis.facts.behavior.arrivals.job_in_arrivals_at.
Goal True. idtac "END|prosa.analysis.facts.behavior.arrivals.job_in_arrivals_at". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.arrivals.job_arrival_between". Abort.
Check @prosa.analysis.facts.behavior.arrivals.job_arrival_between.
Goal True. idtac "END|prosa.analysis.facts.behavior.arrivals.job_arrival_between". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.arrivals.job_arrival_between_ge". Abort.
Check @prosa.analysis.facts.behavior.arrivals.job_arrival_between_ge.
Goal True. idtac "END|prosa.analysis.facts.behavior.arrivals.job_arrival_between_ge". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.arrivals.job_arrival_between_lt". Abort.
Check @prosa.analysis.facts.behavior.arrivals.job_arrival_between_lt.
Goal True. idtac "END|prosa.analysis.facts.behavior.arrivals.job_arrival_between_lt". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.arrivals.arrivals_between_filter_nil". Abort.
Check @prosa.analysis.facts.behavior.arrivals.arrivals_between_filter_nil.
Goal True. idtac "END|prosa.analysis.facts.behavior.arrivals.arrivals_between_filter_nil". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.arrivals.arrivals_between_filter". Abort.
Check @prosa.analysis.facts.behavior.arrivals.arrivals_between_filter.
Goal True. idtac "END|prosa.analysis.facts.behavior.arrivals.arrivals_between_filter". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.arrivals.in_arrivals_implies_arrived". Abort.
Check @prosa.analysis.facts.behavior.arrivals.in_arrivals_implies_arrived.
Goal True. idtac "END|prosa.analysis.facts.behavior.arrivals.in_arrivals_implies_arrived". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.arrivals.in_arrseq_implies_arrives". Abort.
Check @prosa.analysis.facts.behavior.arrivals.in_arrseq_implies_arrives.
Goal True. idtac "END|prosa.analysis.facts.behavior.arrivals.in_arrseq_implies_arrives". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.arrivals.in_arrivals_implies_arrived_between". Abort.
Check @prosa.analysis.facts.behavior.arrivals.in_arrivals_implies_arrived_between.
Goal True. idtac "END|prosa.analysis.facts.behavior.arrivals.in_arrivals_implies_arrived_between". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.arrivals.in_arrivals_implies_arrived_before". Abort.
Check @prosa.analysis.facts.behavior.arrivals.in_arrivals_implies_arrived_before.
Goal True. idtac "END|prosa.analysis.facts.behavior.arrivals.in_arrivals_implies_arrived_before". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.arrivals.arrived_between_implies_in_arrivals". Abort.
Check @prosa.analysis.facts.behavior.arrivals.arrived_between_implies_in_arrivals.
Goal True. idtac "END|prosa.analysis.facts.behavior.arrivals.arrived_between_implies_in_arrivals". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.arrivals.job_arrival_between_P". Abort.
Check @prosa.analysis.facts.behavior.arrivals.job_arrival_between_P.
Goal True. idtac "END|prosa.analysis.facts.behavior.arrivals.job_arrival_between_P". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.arrivals.job_in_arrivals_between". Abort.
Check @prosa.analysis.facts.behavior.arrivals.job_in_arrivals_between.
Goal True. idtac "END|prosa.analysis.facts.behavior.arrivals.job_in_arrivals_between". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.arrivals.arrivals_uniq". Abort.
Check @prosa.analysis.facts.behavior.arrivals.arrivals_uniq.
Goal True. idtac "END|prosa.analysis.facts.behavior.arrivals.arrivals_uniq". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.arrivals.arrivals_between_geq". Abort.
Check @prosa.analysis.facts.behavior.arrivals.arrivals_between_geq.
Goal True. idtac "END|prosa.analysis.facts.behavior.arrivals.arrivals_between_geq". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.arrivals.arrivals_between_nonempty". Abort.
Check @prosa.analysis.facts.behavior.arrivals.arrivals_between_nonempty.
Goal True. idtac "END|prosa.analysis.facts.behavior.arrivals.arrivals_between_nonempty". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.arrivals.arrival_lt_implies_job_in_arrivals_between_P". Abort.
Check @prosa.analysis.facts.behavior.arrivals.arrival_lt_implies_job_in_arrivals_between_P.
Goal True. idtac "END|prosa.analysis.facts.behavior.arrivals.arrival_lt_implies_job_in_arrivals_between_P". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.arrivals.job_arrival_in_bounds". Abort.
Check @prosa.analysis.facts.behavior.arrivals.job_arrival_in_bounds.
Goal True. idtac "END|prosa.analysis.facts.behavior.arrivals.job_arrival_in_bounds". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.arrivals.by_arrival_times". Abort.
Check @prosa.analysis.facts.behavior.arrivals.by_arrival_times.
Goal True. idtac "END|prosa.analysis.facts.behavior.arrivals.by_arrival_times". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.arrivals.arrivals_at_sorted". Abort.
Check @prosa.analysis.facts.behavior.arrivals.arrivals_at_sorted.
Goal True. idtac "END|prosa.analysis.facts.behavior.arrivals.arrivals_at_sorted". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.arrivals.arrivals_between_sorted". Abort.
Check @prosa.analysis.facts.behavior.arrivals.arrivals_between_sorted.
Goal True. idtac "END|prosa.analysis.facts.behavior.arrivals.arrivals_between_sorted". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.arrivals.arrivals_between_partitioned_by_task". Abort.
Check @prosa.analysis.facts.behavior.arrivals.arrivals_between_partitioned_by_task.
Goal True. idtac "END|prosa.analysis.facts.behavior.arrivals.arrivals_between_partitioned_by_task". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.arrivals.arrives_in_jobs_come_from_arrival_sequence". Abort.
Check @prosa.analysis.facts.behavior.arrivals.arrives_in_jobs_come_from_arrival_sequence.
Goal True. idtac "END|prosa.analysis.facts.behavior.arrivals.arrives_in_jobs_come_from_arrival_sequence". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.arrivals.arrived_between_jobs_must_arrive_to_execute". Abort.
Check @prosa.analysis.facts.behavior.arrivals.arrived_between_jobs_must_arrive_to_execute.
Goal True. idtac "END|prosa.analysis.facts.behavior.arrivals.arrived_between_jobs_must_arrive_to_execute". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.arrivals.arrivals_before_scheduled_at". Abort.
Check @prosa.analysis.facts.behavior.arrivals.arrivals_before_scheduled_at.
Goal True. idtac "END|prosa.analysis.facts.behavior.arrivals.arrivals_before_scheduled_at". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.arrivals.arrivals_up_to_scheduled_at". Abort.
Check @prosa.analysis.facts.behavior.arrivals.arrivals_up_to_scheduled_at.
Goal True. idtac "END|prosa.analysis.facts.behavior.arrivals.arrivals_up_to_scheduled_at". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.completion.completion_monotonic". Abort.
Check @prosa.analysis.facts.behavior.completion.completion_monotonic.
Goal True. idtac "END|prosa.analysis.facts.behavior.completion.completion_monotonic". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.completion.incompletion_monotonic". Abort.
Check @prosa.analysis.facts.behavior.completion.incompletion_monotonic.
Goal True. idtac "END|prosa.analysis.facts.behavior.completion.incompletion_monotonic". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.completion.less_service_than_cost_is_incomplete". Abort.
Check @prosa.analysis.facts.behavior.completion.less_service_than_cost_is_incomplete.
Goal True. idtac "END|prosa.analysis.facts.behavior.completion.less_service_than_cost_is_incomplete". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.completion.incomplete_is_positive_remaining_cost". Abort.
Check @prosa.analysis.facts.behavior.completion.incomplete_is_positive_remaining_cost.
Goal True. idtac "END|prosa.analysis.facts.behavior.completion.incomplete_is_positive_remaining_cost". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.completion.incomplete_implies_positive_cost". Abort.
Check @prosa.analysis.facts.behavior.completion.incomplete_implies_positive_cost.
Goal True. idtac "END|prosa.analysis.facts.behavior.completion.incomplete_implies_positive_cost". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.completion.scheduled_implies_positive_cost". Abort.
Check @prosa.analysis.facts.behavior.completion.scheduled_implies_positive_cost.
Goal True. idtac "END|prosa.analysis.facts.behavior.completion.scheduled_implies_positive_cost". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.completion.service_lt_cost". Abort.
Check @prosa.analysis.facts.behavior.completion.service_lt_cost.
Goal True. idtac "END|prosa.analysis.facts.behavior.completion.service_lt_cost". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.completion.completed_on_arrival_implies_zero_cost". Abort.
Check @prosa.analysis.facts.behavior.completion.completed_on_arrival_implies_zero_cost.
Goal True. idtac "END|prosa.analysis.facts.behavior.completion.completed_on_arrival_implies_zero_cost". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.completion.serviced_implies_positive_remaining_cost". Abort.
Check @prosa.analysis.facts.behavior.completion.serviced_implies_positive_remaining_cost.
Goal True. idtac "END|prosa.analysis.facts.behavior.completion.serviced_implies_positive_remaining_cost". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.completion.scheduled_implies_serviced". Abort.
Check @prosa.analysis.facts.behavior.completion.scheduled_implies_serviced.
Goal True. idtac "END|prosa.analysis.facts.behavior.completion.scheduled_implies_serviced". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.completion.scheduled_implies_positive_remaining_cost". Abort.
Check @prosa.analysis.facts.behavior.completion.scheduled_implies_positive_remaining_cost.
Goal True. idtac "END|prosa.analysis.facts.behavior.completion.scheduled_implies_positive_remaining_cost". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.completion.scheduled_implies_not_completed". Abort.
Check @prosa.analysis.facts.behavior.completion.scheduled_implies_not_completed.
Goal True. idtac "END|prosa.analysis.facts.behavior.completion.scheduled_implies_not_completed". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.completion.not_scheduled_remains_incomplete". Abort.
Check @prosa.analysis.facts.behavior.completion.not_scheduled_remains_incomplete.
Goal True. idtac "END|prosa.analysis.facts.behavior.completion.not_scheduled_remains_incomplete". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.completion.completed_implies_not_scheduled". Abort.
Check @prosa.analysis.facts.behavior.completion.completed_implies_not_scheduled.
Goal True. idtac "END|prosa.analysis.facts.behavior.completion.completed_implies_not_scheduled". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.completion.not_pending_earlier_and_at_0". Abort.
Check @prosa.analysis.facts.behavior.completion.not_pending_earlier_and_at_0.
Goal True. idtac "END|prosa.analysis.facts.behavior.completion.not_pending_earlier_and_at_0". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.completion.unit_service". Abort.
Check @prosa.analysis.facts.behavior.completion.unit_service.
Goal True. idtac "END|prosa.analysis.facts.behavior.completion.unit_service". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.completion.service_at_most_cost". Abort.
Check @prosa.analysis.facts.behavior.completion.service_at_most_cost.
Goal True. idtac "END|prosa.analysis.facts.behavior.completion.service_at_most_cost". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.completion.service_cost_invariant". Abort.
Check @prosa.analysis.facts.behavior.completion.service_cost_invariant.
Goal True. idtac "END|prosa.analysis.facts.behavior.completion.service_cost_invariant". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.completion.cumulative_service_le_job_cost". Abort.
Check @prosa.analysis.facts.behavior.completion.cumulative_service_le_job_cost.
Goal True. idtac "END|prosa.analysis.facts.behavior.completion.cumulative_service_le_job_cost". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.completion.job_doesnt_complete_before_remaining_cost". Abort.
Check @prosa.analysis.facts.behavior.completion.job_doesnt_complete_before_remaining_cost.
Goal True. idtac "END|prosa.analysis.facts.behavior.completion.job_doesnt_complete_before_remaining_cost". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.completion.has_arrived_scheduled". Abort.
Check @prosa.analysis.facts.behavior.completion.has_arrived_scheduled.
Goal True. idtac "END|prosa.analysis.facts.behavior.completion.has_arrived_scheduled". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.completion.scheduled_implies_pending". Abort.
Check @prosa.analysis.facts.behavior.completion.scheduled_implies_pending.
Goal True. idtac "END|prosa.analysis.facts.behavior.completion.scheduled_implies_pending". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.completion.completed_implies_scheduled_before". Abort.
Check @prosa.analysis.facts.behavior.completion.completed_implies_scheduled_before.
Goal True. idtac "END|prosa.analysis.facts.behavior.completion.completed_implies_scheduled_before". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.completion.job_pending_at_arrival". Abort.
Check @prosa.analysis.facts.behavior.completion.job_pending_at_arrival.
Goal True. idtac "END|prosa.analysis.facts.behavior.completion.job_pending_at_arrival". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.completion.ready_implies_incomplete". Abort.
Check @prosa.analysis.facts.behavior.completion.ready_implies_incomplete.
Goal True. idtac "END|prosa.analysis.facts.behavior.completion.ready_implies_incomplete". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.completion.completed_jobs_are_not_ready". Abort.
Check @prosa.analysis.facts.behavior.completion.completed_jobs_are_not_ready.
Goal True. idtac "END|prosa.analysis.facts.behavior.completion.completed_jobs_are_not_ready". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.completion.valid_schedule_implies_completed_jobs_dont_execute". Abort.
Check @prosa.analysis.facts.behavior.completion.valid_schedule_implies_completed_jobs_dont_execute.
Goal True. idtac "END|prosa.analysis.facts.behavior.completion.valid_schedule_implies_completed_jobs_dont_execute". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.completion.ideal_progress_completed_jobs". Abort.
Check @prosa.analysis.facts.behavior.completion.ideal_progress_completed_jobs.
Goal True. idtac "END|prosa.analysis.facts.behavior.completion.ideal_progress_completed_jobs". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.completion.identical_prefix_completed_by". Abort.
Check @prosa.analysis.facts.behavior.completion.identical_prefix_completed_by.
Goal True. idtac "END|prosa.analysis.facts.behavior.completion.identical_prefix_completed_by". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.completion.identical_prefix_pending". Abort.
Check @prosa.analysis.facts.behavior.completion.identical_prefix_pending.
Goal True. idtac "END|prosa.analysis.facts.behavior.completion.identical_prefix_pending". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.deadlines.incomplete_implies_later_deadline". Abort.
Check @prosa.analysis.facts.behavior.deadlines.incomplete_implies_later_deadline.
Goal True. idtac "END|prosa.analysis.facts.behavior.deadlines.incomplete_implies_later_deadline". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.deadlines.incomplete_implies_scheduled_later". Abort.
Check @prosa.analysis.facts.behavior.deadlines.incomplete_implies_scheduled_later.
Goal True. idtac "END|prosa.analysis.facts.behavior.deadlines.incomplete_implies_scheduled_later". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.deadlines.scheduled_at_implies_later_deadline". Abort.
Check @prosa.analysis.facts.behavior.deadlines.scheduled_at_implies_later_deadline.
Goal True. idtac "END|prosa.analysis.facts.behavior.deadlines.scheduled_at_implies_later_deadline". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.deadlines.service_invariant_implies_deadline_met". Abort.
Check @prosa.analysis.facts.behavior.deadlines.service_invariant_implies_deadline_met.
Goal True. idtac "END|prosa.analysis.facts.behavior.deadlines.service_invariant_implies_deadline_met". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.service.service_during_geq". Abort.
Check @prosa.analysis.facts.behavior.service.service_during_geq.
Goal True. idtac "END|prosa.analysis.facts.behavior.service.service_during_geq". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.service.service_during_ge". Abort.
Check @prosa.analysis.facts.behavior.service.service_during_ge.
Goal True. idtac "END|prosa.analysis.facts.behavior.service.service_during_ge". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.service.service0". Abort.
Check @prosa.analysis.facts.behavior.service.service0.
Goal True. idtac "END|prosa.analysis.facts.behavior.service.service0". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.service.service_during_instant". Abort.
Check @prosa.analysis.facts.behavior.service.service_during_instant.
Goal True. idtac "END|prosa.analysis.facts.behavior.service.service_during_instant". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.service.service_during_cat". Abort.
Check @prosa.analysis.facts.behavior.service.service_during_cat.
Goal True. idtac "END|prosa.analysis.facts.behavior.service.service_during_cat". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.service.service_cat". Abort.
Check @prosa.analysis.facts.behavior.service.service_cat.
Goal True. idtac "END|prosa.analysis.facts.behavior.service.service_cat". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.service.service_during_first_plus_later". Abort.
Check @prosa.analysis.facts.behavior.service.service_during_first_plus_later.
Goal True. idtac "END|prosa.analysis.facts.behavior.service.service_during_first_plus_later". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.service.service_during_last_plus_before". Abort.
Check @prosa.analysis.facts.behavior.service.service_during_last_plus_before.
Goal True. idtac "END|prosa.analysis.facts.behavior.service.service_during_last_plus_before". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.service.service_last_plus_before". Abort.
Check @prosa.analysis.facts.behavior.service.service_last_plus_before.
Goal True. idtac "END|prosa.analysis.facts.behavior.service.service_last_plus_before". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.service.service_split_at_point". Abort.
Check @prosa.analysis.facts.behavior.service.service_split_at_point.
Goal True. idtac "END|prosa.analysis.facts.behavior.service.service_split_at_point". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.service.service_at_most_one". Abort.
Check @prosa.analysis.facts.behavior.service.service_at_most_one.
Goal True. idtac "END|prosa.analysis.facts.behavior.service.service_at_most_one". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.service.service_is_zero_or_one". Abort.
Check @prosa.analysis.facts.behavior.service.service_is_zero_or_one.
Goal True. idtac "END|prosa.analysis.facts.behavior.service.service_is_zero_or_one". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.service.cumulative_service_le_delta". Abort.
Check @prosa.analysis.facts.behavior.service.cumulative_service_le_delta.
Goal True. idtac "END|prosa.analysis.facts.behavior.service.cumulative_service_le_delta". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.service.cumulative_service_ge_delta". Abort.
Check @prosa.analysis.facts.behavior.service.cumulative_service_ge_delta.
Goal True. idtac "END|prosa.analysis.facts.behavior.service.cumulative_service_ge_delta". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.service.service_during_is_unit_growth_function". Abort.
Check @prosa.analysis.facts.behavior.service.service_during_is_unit_growth_function.
Goal True. idtac "END|prosa.analysis.facts.behavior.service.service_during_is_unit_growth_function". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.service.service_is_unit_growth_function". Abort.
Check @prosa.analysis.facts.behavior.service.service_is_unit_growth_function.
Goal True. idtac "END|prosa.analysis.facts.behavior.service.service_is_unit_growth_function". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.service.exists_intermediate_service_during". Abort.
Check @prosa.analysis.facts.behavior.service.exists_intermediate_service_during.
Goal True. idtac "END|prosa.analysis.facts.behavior.service.exists_intermediate_service_during". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.service.exists_intermediate_service". Abort.
Check @prosa.analysis.facts.behavior.service.exists_intermediate_service.
Goal True. idtac "END|prosa.analysis.facts.behavior.service.exists_intermediate_service". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.service.ideal_progress_inside_supplies". Abort.
Check @prosa.analysis.facts.behavior.service.ideal_progress_inside_supplies.
Goal True. idtac "END|prosa.analysis.facts.behavior.service.ideal_progress_inside_supplies". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.service.service_monotonic". Abort.
Check @prosa.analysis.facts.behavior.service.service_monotonic.
Goal True. idtac "END|prosa.analysis.facts.behavior.service.service_monotonic". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.service.service_in_implies_scheduled_in". Abort.
Check @prosa.analysis.facts.behavior.service.service_in_implies_scheduled_in.
Goal True. idtac "END|prosa.analysis.facts.behavior.service.service_in_implies_scheduled_in". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.service.not_scheduled_implies_no_service". Abort.
Check @prosa.analysis.facts.behavior.service.not_scheduled_implies_no_service.
Goal True. idtac "END|prosa.analysis.facts.behavior.service.not_scheduled_implies_no_service". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.service.not_scheduled_during_implies_zero_service". Abort.
Check @prosa.analysis.facts.behavior.service.not_scheduled_during_implies_zero_service.
Goal True. idtac "END|prosa.analysis.facts.behavior.service.not_scheduled_during_implies_zero_service". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.service.service_at_implies_scheduled_at". Abort.
Check @prosa.analysis.facts.behavior.service.service_at_implies_scheduled_at.
Goal True. idtac "END|prosa.analysis.facts.behavior.service.service_at_implies_scheduled_at". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.service.service_delta_implies_scheduled". Abort.
Check @prosa.analysis.facts.behavior.service.service_delta_implies_scheduled.
Goal True. idtac "END|prosa.analysis.facts.behavior.service.service_delta_implies_scheduled". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.service.service_during_service_at". Abort.
Check @prosa.analysis.facts.behavior.service.service_during_service_at.
Goal True. idtac "END|prosa.analysis.facts.behavior.service.service_during_service_at". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.service.cumulative_service_implies_scheduled". Abort.
Check @prosa.analysis.facts.behavior.service.cumulative_service_implies_scheduled.
Goal True. idtac "END|prosa.analysis.facts.behavior.service.cumulative_service_implies_scheduled". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.service.positive_service_implies_scheduled_before". Abort.
Check @prosa.analysis.facts.behavior.service.positive_service_implies_scheduled_before.
Goal True. idtac "END|prosa.analysis.facts.behavior.service.positive_service_implies_scheduled_before". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.service.service_during_service_at_earliest". Abort.
Check @prosa.analysis.facts.behavior.service.service_during_service_at_earliest.
Goal True. idtac "END|prosa.analysis.facts.behavior.service.service_during_service_at_earliest". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.service.service_during_scheduled_at_earliest". Abort.
Check @prosa.analysis.facts.behavior.service.service_during_scheduled_at_earliest.
Goal True. idtac "END|prosa.analysis.facts.behavior.service.service_during_scheduled_at_earliest". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.service.no_service_not_scheduled". Abort.
Check @prosa.analysis.facts.behavior.service.no_service_not_scheduled.
Goal True. idtac "END|prosa.analysis.facts.behavior.service.no_service_not_scheduled". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.service.no_service_during_implies_not_scheduled". Abort.
Check @prosa.analysis.facts.behavior.service.no_service_during_implies_not_scheduled.
Goal True. idtac "END|prosa.analysis.facts.behavior.service.no_service_during_implies_not_scheduled". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.service.scheduled_implies_cumulative_service". Abort.
Check @prosa.analysis.facts.behavior.service.scheduled_implies_cumulative_service.
Goal True. idtac "END|prosa.analysis.facts.behavior.service.scheduled_implies_cumulative_service". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.service.scheduled_implies_nonzero_service". Abort.
Check @prosa.analysis.facts.behavior.service.scheduled_implies_nonzero_service.
Goal True. idtac "END|prosa.analysis.facts.behavior.service.scheduled_implies_nonzero_service". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.service.unit_service_at1". Abort.
Check @prosa.analysis.facts.behavior.service.unit_service_at1.
Goal True. idtac "END|prosa.analysis.facts.behavior.service.unit_service_at1". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.service.not_scheduled_before_arrival". Abort.
Check @prosa.analysis.facts.behavior.service.not_scheduled_before_arrival.
Goal True. idtac "END|prosa.analysis.facts.behavior.service.not_scheduled_before_arrival". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.service.positive_service_implies_scheduled_since_arrival". Abort.
Check @prosa.analysis.facts.behavior.service.positive_service_implies_scheduled_since_arrival.
Goal True. idtac "END|prosa.analysis.facts.behavior.service.positive_service_implies_scheduled_since_arrival". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.service.service_before_job_arrival_zero". Abort.
Check @prosa.analysis.facts.behavior.service.service_before_job_arrival_zero.
Goal True. idtac "END|prosa.analysis.facts.behavior.service.service_before_job_arrival_zero". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.service.cumulative_service_before_job_arrival_zero". Abort.
Check @prosa.analysis.facts.behavior.service.cumulative_service_before_job_arrival_zero.
Goal True. idtac "END|prosa.analysis.facts.behavior.service.cumulative_service_before_job_arrival_zero". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.service.ignore_service_before_arrival". Abort.
Check @prosa.analysis.facts.behavior.service.ignore_service_before_arrival.
Goal True. idtac "END|prosa.analysis.facts.behavior.service.ignore_service_before_arrival". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.service.no_service_before_arrival". Abort.
Check @prosa.analysis.facts.behavior.service.no_service_before_arrival.
Goal True. idtac "END|prosa.analysis.facts.behavior.service.no_service_before_arrival". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.service.constant_service_implies_no_service_during". Abort.
Check @prosa.analysis.facts.behavior.service.constant_service_implies_no_service_during.
Goal True. idtac "END|prosa.analysis.facts.behavior.service.constant_service_implies_no_service_during". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.service.constant_service_implies_not_scheduled". Abort.
Check @prosa.analysis.facts.behavior.service.constant_service_implies_not_scheduled.
Goal True. idtac "END|prosa.analysis.facts.behavior.service.constant_service_implies_not_scheduled". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.service.same_service_implies_serviced_at_earlier_times". Abort.
Check @prosa.analysis.facts.behavior.service.same_service_implies_serviced_at_earlier_times.
Goal True. idtac "END|prosa.analysis.facts.behavior.service.same_service_implies_serviced_at_earlier_times". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.service.same_service_implies_scheduled_at_earlier_times". Abort.
Check @prosa.analysis.facts.behavior.service.same_service_implies_scheduled_at_earlier_times.
Goal True. idtac "END|prosa.analysis.facts.behavior.service.same_service_implies_scheduled_at_earlier_times". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.service.receives_service_and_served_at_consistent". Abort.
Check @prosa.analysis.facts.behavior.service.receives_service_and_served_at_consistent.
Goal True. idtac "END|prosa.analysis.facts.behavior.service.receives_service_and_served_at_consistent". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.service.served_at_and_receives_service_consistent". Abort.
Check @prosa.analysis.facts.behavior.service.served_at_and_receives_service_consistent.
Goal True. idtac "END|prosa.analysis.facts.behavior.service.served_at_and_receives_service_consistent". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.service.no_service_received_when_idle". Abort.
Check @prosa.analysis.facts.behavior.service.no_service_received_when_idle.
Goal True. idtac "END|prosa.analysis.facts.behavior.service.no_service_received_when_idle". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.service.receives_service_implies_has_supply". Abort.
Check @prosa.analysis.facts.behavior.service.receives_service_implies_has_supply.
Goal True. idtac "END|prosa.analysis.facts.behavior.service.receives_service_implies_has_supply". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.service.no_blackout_when_service_received". Abort.
Check @prosa.analysis.facts.behavior.service.no_blackout_when_service_received.
Goal True. idtac "END|prosa.analysis.facts.behavior.service.no_blackout_when_service_received". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.service.no_service_during_blackout". Abort.
Check @prosa.analysis.facts.behavior.service.no_service_during_blackout.
Goal True. idtac "END|prosa.analysis.facts.behavior.service.no_service_during_blackout". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.service.only_one_job_receives_service_at_uni". Abort.
Check @prosa.analysis.facts.behavior.service.only_one_job_receives_service_at_uni.
Goal True. idtac "END|prosa.analysis.facts.behavior.service.only_one_job_receives_service_at_uni". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.service.incremental_service_during". Abort.
Check @prosa.analysis.facts.behavior.service.incremental_service_during.
Goal True. idtac "END|prosa.analysis.facts.behavior.service.incremental_service_during". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.service.kth_scheduling_time". Abort.
Check @prosa.analysis.facts.behavior.service.kth_scheduling_time.
Goal True. idtac "END|prosa.analysis.facts.behavior.service.kth_scheduling_time". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.service.same_service_during". Abort.
Check @prosa.analysis.facts.behavior.service.same_service_during.
Goal True. idtac "END|prosa.analysis.facts.behavior.service.same_service_during". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.service.equal_prefix_implies_same_service_during". Abort.
Check @prosa.analysis.facts.behavior.service.equal_prefix_implies_same_service_during.
Goal True. idtac "END|prosa.analysis.facts.behavior.service.equal_prefix_implies_same_service_during". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.service.identical_prefix_service". Abort.
Check @prosa.analysis.facts.behavior.service.identical_prefix_service.
Goal True. idtac "END|prosa.analysis.facts.behavior.service.identical_prefix_service". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.supply.service_at_le_supply_at". Abort.
Check @prosa.analysis.facts.behavior.supply.service_at_le_supply_at.
Goal True. idtac "END|prosa.analysis.facts.behavior.supply.service_at_le_supply_at". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.supply.pos_service_impl_pos_supply". Abort.
Check @prosa.analysis.facts.behavior.supply.pos_service_impl_pos_supply.
Goal True. idtac "END|prosa.analysis.facts.behavior.supply.pos_service_impl_pos_supply". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.supply.blackout_or_supply". Abort.
Check @prosa.analysis.facts.behavior.supply.blackout_or_supply.
Goal True. idtac "END|prosa.analysis.facts.behavior.supply.blackout_or_supply". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.supply.supply_at_complement". Abort.
Check @prosa.analysis.facts.behavior.supply.supply_at_complement.
Goal True. idtac "END|prosa.analysis.facts.behavior.supply.supply_at_complement". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.supply.is_blackout_complement". Abort.
Check @prosa.analysis.facts.behavior.supply.is_blackout_complement.
Goal True. idtac "END|prosa.analysis.facts.behavior.supply.is_blackout_complement". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.supply.supply_at_le_1". Abort.
Check @prosa.analysis.facts.behavior.supply.supply_at_le_1.
Goal True. idtac "END|prosa.analysis.facts.behavior.supply.supply_at_le_1". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.supply.unit_supply_proc_service_case". Abort.
Check @prosa.analysis.facts.behavior.supply.unit_supply_proc_service_case.
Goal True. idtac "END|prosa.analysis.facts.behavior.supply.unit_supply_proc_service_case". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.supply.supply_during_bound". Abort.
Check @prosa.analysis.facts.behavior.supply.supply_during_bound.
Goal True. idtac "END|prosa.analysis.facts.behavior.supply.supply_during_bound". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.supply.blackout_during_bound". Abort.
Check @prosa.analysis.facts.behavior.supply.blackout_during_bound.
Goal True. idtac "END|prosa.analysis.facts.behavior.supply.blackout_during_bound". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.supply.supply_during_last_plus_before". Abort.
Check @prosa.analysis.facts.behavior.supply.supply_during_last_plus_before.
Goal True. idtac "END|prosa.analysis.facts.behavior.supply.supply_during_last_plus_before". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.supply.blackout_during_last_plus_before". Abort.
Check @prosa.analysis.facts.behavior.supply.blackout_during_last_plus_before.
Goal True. idtac "END|prosa.analysis.facts.behavior.supply.blackout_during_last_plus_before". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.supply.supply_during_complement". Abort.
Check @prosa.analysis.facts.behavior.supply.supply_during_complement.
Goal True. idtac "END|prosa.analysis.facts.behavior.supply.supply_during_complement". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.supply.blackout_during_complement". Abort.
Check @prosa.analysis.facts.behavior.supply.blackout_during_complement.
Goal True. idtac "END|prosa.analysis.facts.behavior.supply.blackout_during_complement". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.supply.blackout_during_cat". Abort.
Check @prosa.analysis.facts.behavior.supply.blackout_during_cat.
Goal True. idtac "END|prosa.analysis.facts.behavior.supply.blackout_during_cat". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.supply.blackout_during_unit_growth". Abort.
Check @prosa.analysis.facts.behavior.supply.blackout_during_unit_growth.
Goal True. idtac "END|prosa.analysis.facts.behavior.supply.blackout_during_unit_growth". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.behavior.supply.progress_inside_supplies". Abort.
Check @prosa.analysis.facts.behavior.supply.progress_inside_supplies.
Goal True. idtac "END|prosa.analysis.facts.behavior.supply.progress_inside_supplies". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.blocking_bound.edf.nonpreemptive_segments_bounded_by_blocking". Abort.
Check @prosa.analysis.facts.blocking_bound.edf.nonpreemptive_segments_bounded_by_blocking.
Goal True. idtac "END|prosa.analysis.facts.blocking_bound.edf.nonpreemptive_segments_bounded_by_blocking". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.blocking_bound.elf.nonpreemptive_segments_bounded_by_blocking". Abort.
Check @prosa.analysis.facts.blocking_bound.elf.nonpreemptive_segments_bounded_by_blocking.
Goal True. idtac "END|prosa.analysis.facts.blocking_bound.elf.nonpreemptive_segments_bounded_by_blocking". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.blocking_bound.fp.nonpreemptive_segments_bounded_by_blocking". Abort.
Check @prosa.analysis.facts.blocking_bound.fp.nonpreemptive_segments_bounded_by_blocking.
Goal True. idtac "END|prosa.analysis.facts.blocking_bound.fp.nonpreemptive_segments_bounded_by_blocking". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.busy_interval.arrival.busy_interval_prefix_job_arrival". Abort.
Check @prosa.analysis.facts.busy_interval.arrival.busy_interval_prefix_job_arrival.
Goal True. idtac "END|prosa.analysis.facts.busy_interval.arrival.busy_interval_prefix_job_arrival". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.busy_interval.arrival.busy_interval_job_arrival". Abort.
Check @prosa.analysis.facts.busy_interval.arrival.busy_interval_job_arrival.
Goal True. idtac "END|prosa.analysis.facts.busy_interval.arrival.busy_interval_job_arrival". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.busy_interval.arrival.busy_prefix_starts_when_hep_job_arrives". Abort.
Check @prosa.analysis.facts.busy_interval.arrival.busy_prefix_starts_when_hep_job_arrives.
Goal True. idtac "END|prosa.analysis.facts.busy_interval.arrival.busy_prefix_starts_when_hep_job_arrives". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.busy_interval.carry_in.no_carry_in_at_zero". Abort.
Check @prosa.analysis.facts.busy_interval.carry_in.no_carry_in_at_zero.
Goal True. idtac "END|prosa.analysis.facts.busy_interval.carry_in.no_carry_in_at_zero". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.busy_interval.carry_in.pending_job_not_idle". Abort.
Check @prosa.analysis.facts.busy_interval.carry_in.pending_job_not_idle.
Goal True. idtac "END|prosa.analysis.facts.busy_interval.carry_in.pending_job_not_idle". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.busy_interval.carry_in.idle_instant_no_carry_in". Abort.
Check @prosa.analysis.facts.busy_interval.carry_in.idle_instant_no_carry_in.
Goal True. idtac "END|prosa.analysis.facts.busy_interval.carry_in.idle_instant_no_carry_in". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.busy_interval.carry_in.idle_instant_next_no_carry_in". Abort.
Check @prosa.analysis.facts.busy_interval.carry_in.idle_instant_next_no_carry_in.
Goal True. idtac "END|prosa.analysis.facts.busy_interval.carry_in.idle_instant_next_no_carry_in". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.busy_interval.carry_in.total_service_is_bounded_by_Δ". Abort.
Check @prosa.analysis.facts.busy_interval.carry_in.total_service_is_bounded_by_Δ.
Goal True. idtac "END|prosa.analysis.facts.busy_interval.carry_in.total_service_is_bounded_by_Δ". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.busy_interval.carry_in.low_total_service_implies_existence_of_time_with_no_carry_in". Abort.
Check @prosa.analysis.facts.busy_interval.carry_in.low_total_service_implies_existence_of_time_with_no_carry_in.
Goal True. idtac "END|prosa.analysis.facts.busy_interval.carry_in.low_total_service_implies_existence_of_time_with_no_carry_in". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.busy_interval.carry_in.completion_of_all_jobs_implies_no_carry_in". Abort.
Check @prosa.analysis.facts.busy_interval.carry_in.completion_of_all_jobs_implies_no_carry_in.
Goal True. idtac "END|prosa.analysis.facts.busy_interval.carry_in.completion_of_all_jobs_implies_no_carry_in". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.busy_interval.carry_in.processor_is_not_too_busy". Abort.
Check @prosa.analysis.facts.busy_interval.carry_in.processor_is_not_too_busy.
Goal True. idtac "END|prosa.analysis.facts.busy_interval.carry_in.processor_is_not_too_busy". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.busy_interval.carry_in.busy_interval_from_total_workload_bound". Abort.
Check @prosa.analysis.facts.busy_interval.carry_in.busy_interval_from_total_workload_bound.
Goal True. idtac "END|prosa.analysis.facts.busy_interval.carry_in.busy_interval_from_total_workload_bound". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.busy_interval.existence.job_completes_within_busy_interval". Abort.
Check @prosa.analysis.facts.busy_interval.existence.job_completes_within_busy_interval.
Goal True. idtac "END|prosa.analysis.facts.busy_interval.existence.job_completes_within_busy_interval". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.busy_interval.existence.not_quiet_implies_exists_pending_job". Abort.
Check @prosa.analysis.facts.busy_interval.existence.not_quiet_implies_exists_pending_job.
Goal True. idtac "END|prosa.analysis.facts.busy_interval.existence.not_quiet_implies_exists_pending_job". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.busy_interval.existence.idle_time_implies_quiet_time_at_the_next_time_instant". Abort.
Check @prosa.analysis.facts.busy_interval.existence.idle_time_implies_quiet_time_at_the_next_time_instant.
Goal True. idtac "END|prosa.analysis.facts.busy_interval.existence.idle_time_implies_quiet_time_at_the_next_time_instant". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.busy_interval.existence.pending_hp_job_exists". Abort.
Check @prosa.analysis.facts.busy_interval.existence.pending_hp_job_exists.
Goal True. idtac "END|prosa.analysis.facts.busy_interval.existence.pending_hp_job_exists". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.busy_interval.existence.not_quiet_implies_not_idle". Abort.
Check @prosa.analysis.facts.busy_interval.existence.not_quiet_implies_not_idle.
Goal True. idtac "END|prosa.analysis.facts.busy_interval.existence.not_quiet_implies_not_idle". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.busy_interval.existence.hep_jobs_receive_no_service_before_quiet_time". Abort.
Check @prosa.analysis.facts.busy_interval.existence.hep_jobs_receive_no_service_before_quiet_time.
Goal True. idtac "END|prosa.analysis.facts.busy_interval.existence.hep_jobs_receive_no_service_before_quiet_time". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.busy_interval.existence.no_idle_time_within_non_quiet_time_interval". Abort.
Check @prosa.analysis.facts.busy_interval.existence.no_idle_time_within_non_quiet_time_interval.
Goal True. idtac "END|prosa.analysis.facts.busy_interval.existence.no_idle_time_within_non_quiet_time_interval". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.busy_interval.existence.exists_busy_interval_prefix". Abort.
Check @prosa.analysis.facts.busy_interval.existence.exists_busy_interval_prefix.
Goal True. idtac "END|prosa.analysis.facts.busy_interval.existence.exists_busy_interval_prefix". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.busy_interval.existence.busy_interval_has_uninterrupted_service". Abort.
Check @prosa.analysis.facts.busy_interval.existence.busy_interval_has_uninterrupted_service.
Goal True. idtac "END|prosa.analysis.facts.busy_interval.existence.busy_interval_has_uninterrupted_service". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.busy_interval.existence.busy_interval_too_much_workload". Abort.
Check @prosa.analysis.facts.busy_interval.existence.busy_interval_too_much_workload.
Goal True. idtac "END|prosa.analysis.facts.busy_interval.existence.busy_interval_too_much_workload". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.busy_interval.existence.busy_interval_workload_larger_than_interval". Abort.
Check @prosa.analysis.facts.busy_interval.existence.busy_interval_workload_larger_than_interval.
Goal True. idtac "END|prosa.analysis.facts.busy_interval.existence.busy_interval_workload_larger_than_interval". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.busy_interval.existence.busy_interval_is_bounded". Abort.
Check @prosa.analysis.facts.busy_interval.existence.busy_interval_is_bounded.
Goal True. idtac "END|prosa.analysis.facts.busy_interval.existence.busy_interval_is_bounded". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.busy_interval.existence.exists_busy_interval". Abort.
Check @prosa.analysis.facts.busy_interval.existence.exists_busy_interval.
Goal True. idtac "END|prosa.analysis.facts.busy_interval.existence.exists_busy_interval". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.busy_interval.existence.busy_interval_bounds_response_time". Abort.
Check @prosa.analysis.facts.busy_interval.existence.busy_interval_bounds_response_time.
Goal True. idtac "END|prosa.analysis.facts.busy_interval.existence.busy_interval_bounds_response_time". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.busy_interval.hep_at_pt.instant_t_is_not_idle". Abort.
Check @prosa.analysis.facts.busy_interval.hep_at_pt.instant_t_is_not_idle.
Goal True. idtac "END|prosa.analysis.facts.busy_interval.hep_at_pt.instant_t_is_not_idle". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.busy_interval.hep_at_pt.scheduled_at_preemption_time_implies_higher_or_equal_priority_lt". Abort.
Check @prosa.analysis.facts.busy_interval.hep_at_pt.scheduled_at_preemption_time_implies_higher_or_equal_priority_lt.
Goal True. idtac "END|prosa.analysis.facts.busy_interval.hep_at_pt.scheduled_at_preemption_time_implies_higher_or_equal_priority_lt". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.busy_interval.hep_at_pt.scheduled_at_preemption_time_implies_higher_or_equal_priority_eq". Abort.
Check @prosa.analysis.facts.busy_interval.hep_at_pt.scheduled_at_preemption_time_implies_higher_or_equal_priority_eq.
Goal True. idtac "END|prosa.analysis.facts.busy_interval.hep_at_pt.scheduled_at_preemption_time_implies_higher_or_equal_priority_eq". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.busy_interval.hep_at_pt.scheduled_at_preemption_time_implies_higher_or_equal_priority". Abort.
Check @prosa.analysis.facts.busy_interval.hep_at_pt.scheduled_at_preemption_time_implies_higher_or_equal_priority.
Goal True. idtac "END|prosa.analysis.facts.busy_interval.hep_at_pt.scheduled_at_preemption_time_implies_higher_or_equal_priority". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.busy_interval.hep_at_pt.scheduled_at_preemption_time_implies_arrived_between_within_busy_interval". Abort.
Check @prosa.analysis.facts.busy_interval.hep_at_pt.scheduled_at_preemption_time_implies_arrived_between_within_busy_interval.
Goal True. idtac "END|prosa.analysis.facts.busy_interval.hep_at_pt.scheduled_at_preemption_time_implies_arrived_between_within_busy_interval". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.busy_interval.hep_at_pt.not_quiet_implies_exists_scheduled_hp_job_at_preemption_point". Abort.
Check @prosa.analysis.facts.busy_interval.hep_at_pt.not_quiet_implies_exists_scheduled_hp_job_at_preemption_point.
Goal True. idtac "END|prosa.analysis.facts.busy_interval.hep_at_pt.not_quiet_implies_exists_scheduled_hp_job_at_preemption_point". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.busy_interval.hep_at_pt.not_quiet_implies_exists_scheduled_hp_job_after_preemption_point". Abort.
Check @prosa.analysis.facts.busy_interval.hep_at_pt.not_quiet_implies_exists_scheduled_hp_job_after_preemption_point.
Goal True. idtac "END|prosa.analysis.facts.busy_interval.hep_at_pt.not_quiet_implies_exists_scheduled_hp_job_after_preemption_point". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.busy_interval.hep_at_pt.not_quiet_implies_exists_scheduled_hp_job". Abort.
Check @prosa.analysis.facts.busy_interval.hep_at_pt.not_quiet_implies_exists_scheduled_hp_job.
Goal True. idtac "END|prosa.analysis.facts.busy_interval.hep_at_pt.not_quiet_implies_exists_scheduled_hp_job". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.busy_interval.pi.lower_priority_job_scheduled_implies_no_preemption_time". Abort.
Check @prosa.analysis.facts.busy_interval.pi.lower_priority_job_scheduled_implies_no_preemption_time.
Goal True. idtac "END|prosa.analysis.facts.busy_interval.pi.lower_priority_job_scheduled_implies_no_preemption_time". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.busy_interval.pi.lower_priority_job_continuously_scheduled". Abort.
Check @prosa.analysis.facts.busy_interval.pi.lower_priority_job_continuously_scheduled.
Goal True. idtac "END|prosa.analysis.facts.busy_interval.pi.lower_priority_job_continuously_scheduled". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.busy_interval.pi.low_priority_job_arrives_before_busy_interval_prefix". Abort.
Check @prosa.analysis.facts.busy_interval.pi.low_priority_job_arrives_before_busy_interval_prefix.
Goal True. idtac "END|prosa.analysis.facts.busy_interval.pi.low_priority_job_arrives_before_busy_interval_prefix". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.busy_interval.pi.low_priority_job_scheduled_before_busy_interval_prefix". Abort.
Check @prosa.analysis.facts.busy_interval.pi.low_priority_job_scheduled_before_busy_interval_prefix.
Goal True. idtac "END|prosa.analysis.facts.busy_interval.pi.low_priority_job_scheduled_before_busy_interval_prefix". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.busy_interval.pi.lp_job_should_arrive_early_for_pi". Abort.
Check @prosa.analysis.facts.busy_interval.pi.lp_job_should_arrive_early_for_pi.
Goal True. idtac "END|prosa.analysis.facts.busy_interval.pi.lp_job_should_arrive_early_for_pi". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.busy_interval.pi.lower_priority_jobs_never_scheduled_if_no_inversion". Abort.
Check @prosa.analysis.facts.busy_interval.pi.lower_priority_jobs_never_scheduled_if_no_inversion.
Goal True. idtac "END|prosa.analysis.facts.busy_interval.pi.lower_priority_jobs_never_scheduled_if_no_inversion". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.busy_interval.pi.no_preemption_time_before_pi". Abort.
Check @prosa.analysis.facts.busy_interval.pi.no_preemption_time_before_pi.
Goal True. idtac "END|prosa.analysis.facts.busy_interval.pi.no_preemption_time_before_pi". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.busy_interval.pi.pi_job_remains_scheduled". Abort.
Check @prosa.analysis.facts.busy_interval.pi.pi_job_remains_scheduled.
Goal True. idtac "END|prosa.analysis.facts.busy_interval.pi.pi_job_remains_scheduled". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.busy_interval.pi.pi_continuous". Abort.
Check @prosa.analysis.facts.busy_interval.pi.pi_continuous.
Goal True. idtac "END|prosa.analysis.facts.busy_interval.pi.pi_continuous". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.busy_interval.pi.only_one_pi_job". Abort.
Check @prosa.analysis.facts.busy_interval.pi.only_one_pi_job.
Goal True. idtac "END|prosa.analysis.facts.busy_interval.pi.only_one_pi_job". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.busy_interval.pi.busy_interval_pi_cases". Abort.
Check @prosa.analysis.facts.busy_interval.pi.busy_interval_pi_cases.
Goal True. idtac "END|prosa.analysis.facts.busy_interval.pi.busy_interval_pi_cases". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.busy_interval.pi.max_lp_nonpreemptive_segment". Abort.
Check @prosa.analysis.facts.busy_interval.pi.max_lp_nonpreemptive_segment.
Goal True. idtac "END|prosa.analysis.facts.busy_interval.pi.max_lp_nonpreemptive_segment". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.busy_interval.pi.max_np_job_segment_bounded_by_max_np_task_segment". Abort.
Check @prosa.analysis.facts.busy_interval.pi.max_np_job_segment_bounded_by_max_np_task_segment.
Goal True. idtac "END|prosa.analysis.facts.busy_interval.pi.max_np_job_segment_bounded_by_max_np_task_segment". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.busy_interval.pi.hp_job_not_scheduled_before_quiet_time". Abort.
Check @prosa.analysis.facts.busy_interval.pi.hp_job_not_scheduled_before_quiet_time.
Goal True. idtac "END|prosa.analysis.facts.busy_interval.pi.hp_job_not_scheduled_before_quiet_time". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.busy_interval.pi.preemption_time_exists_case1". Abort.
Check @prosa.analysis.facts.busy_interval.pi.preemption_time_exists_case1.
Goal True. idtac "END|prosa.analysis.facts.busy_interval.pi.preemption_time_exists_case1". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.busy_interval.pi.preemption_time_exists_case2". Abort.
Check @prosa.analysis.facts.busy_interval.pi.preemption_time_exists_case2.
Goal True. idtac "END|prosa.analysis.facts.busy_interval.pi.preemption_time_exists_case2". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.busy_interval.pi.no_intermediate_preemption_point". Abort.
Check @prosa.analysis.facts.busy_interval.pi.no_intermediate_preemption_point.
Goal True. idtac "END|prosa.analysis.facts.busy_interval.pi.no_intermediate_preemption_point". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.busy_interval.pi.continuously_scheduled_between_preemption_points". Abort.
Check @prosa.analysis.facts.busy_interval.pi.continuously_scheduled_between_preemption_points.
Goal True. idtac "END|prosa.analysis.facts.busy_interval.pi.continuously_scheduled_between_preemption_points". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.busy_interval.pi.first_preemption_time". Abort.
Check @prosa.analysis.facts.busy_interval.pi.first_preemption_time.
Goal True. idtac "END|prosa.analysis.facts.busy_interval.pi.first_preemption_time". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.busy_interval.pi.preemption_time_le_max_len_of_np_segment". Abort.
Check @prosa.analysis.facts.busy_interval.pi.preemption_time_le_max_len_of_np_segment.
Goal True. idtac "END|prosa.analysis.facts.busy_interval.pi.preemption_time_le_max_len_of_np_segment". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.busy_interval.pi.preemption_time_exists_case3". Abort.
Check @prosa.analysis.facts.busy_interval.pi.preemption_time_exists_case3.
Goal True. idtac "END|prosa.analysis.facts.busy_interval.pi.preemption_time_exists_case3". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.busy_interval.pi.preemption_time_exists". Abort.
Check @prosa.analysis.facts.busy_interval.pi.preemption_time_exists.
Goal True. idtac "END|prosa.analysis.facts.busy_interval.pi.preemption_time_exists". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.busy_interval.pi.no_priority_inversion_after_preemption_point". Abort.
Check @prosa.analysis.facts.busy_interval.pi.no_priority_inversion_after_preemption_point.
Goal True. idtac "END|prosa.analysis.facts.busy_interval.pi.no_priority_inversion_after_preemption_point". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.busy_interval.pi.priority_inversion_occurs_only_till_preemption_point". Abort.
Check @prosa.analysis.facts.busy_interval.pi.priority_inversion_occurs_only_till_preemption_point.
Goal True. idtac "END|prosa.analysis.facts.busy_interval.pi.priority_inversion_occurs_only_till_preemption_point". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.busy_interval.pi_bound.priority_inversion_is_bounded". Abort.
Check @prosa.analysis.facts.busy_interval.pi_bound.priority_inversion_is_bounded.
Goal True. idtac "END|prosa.analysis.facts.busy_interval.pi_bound.priority_inversion_is_bounded". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.busy_interval.pi_cond.cum_task_pi_eq". Abort.
Check @prosa.analysis.facts.busy_interval.pi_cond.cum_task_pi_eq.
Goal True. idtac "END|prosa.analysis.facts.busy_interval.pi_cond.cum_task_pi_eq". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.busy_interval.quiet_time.zero_is_quiet_time". Abort.
Check @prosa.analysis.facts.busy_interval.quiet_time.zero_is_quiet_time.
Goal True. idtac "END|prosa.analysis.facts.busy_interval.quiet_time.zero_is_quiet_time". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.busy_interval.quiet_time.no_carry_in_implies_quiet_time". Abort.
Check @prosa.analysis.facts.busy_interval.quiet_time.no_carry_in_implies_quiet_time.
Goal True. idtac "END|prosa.analysis.facts.busy_interval.quiet_time.no_carry_in_implies_quiet_time". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.busy_interval.quiet_time.busy_interval_prefix_no_quiet_time". Abort.
Check @prosa.analysis.facts.busy_interval.quiet_time.busy_interval_prefix_no_quiet_time.
Goal True. idtac "END|prosa.analysis.facts.busy_interval.quiet_time.busy_interval_prefix_no_quiet_time". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.busy_interval.quiet_time.busy_interval_no_quiet_time". Abort.
Check @prosa.analysis.facts.busy_interval.quiet_time.busy_interval_no_quiet_time.
Goal True. idtac "END|prosa.analysis.facts.busy_interval.quiet_time.busy_interval_no_quiet_time". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.busy_interval.service_inversion.blackout_implies_no_service_inversion". Abort.
Check @prosa.analysis.facts.busy_interval.service_inversion.blackout_implies_no_service_inversion.
Goal True. idtac "END|prosa.analysis.facts.busy_interval.service_inversion.blackout_implies_no_service_inversion". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.busy_interval.service_inversion.idle_implies_no_service_inversion". Abort.
Check @prosa.analysis.facts.busy_interval.service_inversion.idle_implies_no_service_inversion.
Goal True. idtac "END|prosa.analysis.facts.busy_interval.service_inversion.idle_implies_no_service_inversion". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.busy_interval.service_inversion.receives_service_implies_no_service_inversion". Abort.
Check @prosa.analysis.facts.busy_interval.service_inversion.receives_service_implies_no_service_inversion.
Goal True. idtac "END|prosa.analysis.facts.busy_interval.service_inversion.receives_service_implies_no_service_inversion". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.busy_interval.service_inversion.service_inversion_cat". Abort.
Check @prosa.analysis.facts.busy_interval.service_inversion.service_inversion_cat.
Goal True. idtac "END|prosa.analysis.facts.busy_interval.service_inversion.service_inversion_cat". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.busy_interval.service_inversion.service_inversion_widen". Abort.
Check @prosa.analysis.facts.busy_interval.service_inversion.service_inversion_widen.
Goal True. idtac "END|prosa.analysis.facts.busy_interval.service_inversion.service_inversion_widen". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.busy_interval.service_inversion.service_inversion_supply_sched". Abort.
Check @prosa.analysis.facts.busy_interval.service_inversion.service_inversion_supply_sched.
Goal True. idtac "END|prosa.analysis.facts.busy_interval.service_inversion.service_inversion_supply_sched". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.busy_interval.service_inversion.service_inv_implies_priority_inv". Abort.
Check @prosa.analysis.facts.busy_interval.service_inversion.service_inv_implies_priority_inv.
Goal True. idtac "END|prosa.analysis.facts.busy_interval.service_inversion.service_inv_implies_priority_inv". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.busy_interval.service_inversion.cumul_service_inv_le_cumul_priority_inv". Abort.
Check @prosa.analysis.facts.busy_interval.service_inversion.cumul_service_inv_le_cumul_priority_inv.
Goal True. idtac "END|prosa.analysis.facts.busy_interval.service_inversion.cumul_service_inv_le_cumul_priority_inv". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.busy_interval.service_inversion.cumulative_service_inversion_from_one_job". Abort.
Check @prosa.analysis.facts.busy_interval.service_inversion.cumulative_service_inversion_from_one_job.
Goal True. idtac "END|prosa.analysis.facts.busy_interval.service_inversion.cumulative_service_inversion_from_one_job". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.busy_interval.service_inversion.lp_job_bounded_service". Abort.
Check @prosa.analysis.facts.busy_interval.service_inversion.lp_job_bounded_service.
Goal True. idtac "END|prosa.analysis.facts.busy_interval.service_inversion.lp_job_bounded_service". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.busy_interval.service_inversion.lp_job_bounded_service_max". Abort.
Check @prosa.analysis.facts.busy_interval.service_inversion.lp_job_bounded_service_max.
Goal True. idtac "END|prosa.analysis.facts.busy_interval.service_inversion.lp_job_bounded_service_max". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.busy_interval.service_inversion.service_inversion_is_bounded". Abort.
Check @prosa.analysis.facts.busy_interval.service_inversion.service_inversion_is_bounded.
Goal True. idtac "END|prosa.analysis.facts.busy_interval.service_inversion.service_inversion_is_bounded". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.completes_at.scheduled_at_precedes_completes_at". Abort.
Check @prosa.analysis.facts.completes_at.scheduled_at_precedes_completes_at.
Goal True. idtac "END|prosa.analysis.facts.completes_at.scheduled_at_precedes_completes_at". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.completes_at.job_completes_at_most_once". Abort.
Check @prosa.analysis.facts.completes_at.job_completes_at_most_once.
Goal True. idtac "END|prosa.analysis.facts.completes_at.job_completes_at_most_once". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.completes_at.only_one_job_completes_at_a_time". Abort.
Check @prosa.analysis.facts.completes_at.only_one_job_completes_at_a_time.
Goal True. idtac "END|prosa.analysis.facts.completes_at.only_one_job_completes_at_a_time". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.completes_at.completetion_time_is_preemption_time". Abort.
Check @prosa.analysis.facts.completes_at.completetion_time_is_preemption_time.
Goal True. idtac "END|prosa.analysis.facts.completes_at.completetion_time_is_preemption_time". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.completes_at.no_early_hep_job_completes_during_busy_prefix". Abort.
Check @prosa.analysis.facts.completes_at.no_early_hep_job_completes_during_busy_prefix.
Goal True. idtac "END|prosa.analysis.facts.completes_at.no_early_hep_job_completes_during_busy_prefix". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.delay_propagation.consistent_propagated_arrival_sequence". Abort.
Check @prosa.analysis.facts.delay_propagation.consistent_propagated_arrival_sequence.
Goal True. idtac "END|prosa.analysis.facts.delay_propagation.consistent_propagated_arrival_sequence". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.delay_propagation.propagated_arrival_sequence_uniq". Abort.
Check @prosa.analysis.facts.delay_propagation.propagated_arrival_sequence_uniq.
Goal True. idtac "END|prosa.analysis.facts.delay_propagation.propagated_arrival_sequence_uniq". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.delay_propagation.valid_propagated_arrival_sequence". Abort.
Check @prosa.analysis.facts.delay_propagation.valid_propagated_arrival_sequence.
Goal True. idtac "END|prosa.analysis.facts.delay_propagation.valid_propagated_arrival_sequence". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.delay_propagation.arrives_in_propagated_if". Abort.
Check @prosa.analysis.facts.delay_propagation.arrives_in_propagated_if.
Goal True. idtac "END|prosa.analysis.facts.delay_propagation.arrives_in_propagated_if". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.delay_propagation.arrives_in_propagated_only_if". Abort.
Check @prosa.analysis.facts.delay_propagation.arrives_in_propagated_only_if.
Goal True. idtac "END|prosa.analysis.facts.delay_propagation.arrives_in_propagated_only_if". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.delay_propagation.propagated_arrival_curve_valid". Abort.
Check @prosa.analysis.facts.delay_propagation.propagated_arrival_curve_valid.
Goal True. idtac "END|prosa.analysis.facts.delay_propagation.propagated_arrival_curve_valid". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.delay_propagation.trigger_job_arrival_bounded". Abort.
Check @prosa.analysis.facts.delay_propagation.trigger_job_arrival_bounded.
Goal True. idtac "END|prosa.analysis.facts.delay_propagation.trigger_job_arrival_bounded". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.delay_propagation.subset_trigger_jobs". Abort.
Check @prosa.analysis.facts.delay_propagation.subset_trigger_jobs.
Goal True. idtac "END|prosa.analysis.facts.delay_propagation.subset_trigger_jobs". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.delay_propagation.job1_of_inj". Abort.
Check @prosa.analysis.facts.delay_propagation.job1_of_inj.
Goal True. idtac "END|prosa.analysis.facts.delay_propagation.job1_of_inj". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.delay_propagation.uniq_trigger_jobs". Abort.
Check @prosa.analysis.facts.delay_propagation.uniq_trigger_jobs.
Goal True. idtac "END|prosa.analysis.facts.delay_propagation.uniq_trigger_jobs". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.delay_propagation.trigger_job_size". Abort.
Check @prosa.analysis.facts.delay_propagation.trigger_job_size.
Goal True. idtac "END|prosa.analysis.facts.delay_propagation.trigger_job_size". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.delay_propagation.propagated_arrival_curve_respected". Abort.
Check @prosa.analysis.facts.delay_propagation.propagated_arrival_curve_respected.
Goal True. idtac "END|prosa.analysis.facts.delay_propagation.propagated_arrival_curve_respected". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.edf_definitions.EDF_schedule_implies_respects_policy_at_preemption_point". Abort.
Check @prosa.analysis.facts.edf_definitions.EDF_schedule_implies_respects_policy_at_preemption_point.
Goal True. idtac "END|prosa.analysis.facts.edf_definitions.EDF_schedule_implies_respects_policy_at_preemption_point". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.edf_definitions.respects_policy_at_preemption_point_implies_EDF_schedule". Abort.
Check @prosa.analysis.facts.edf_definitions.respects_policy_at_preemption_point_implies_EDF_schedule.
Goal True. idtac "END|prosa.analysis.facts.edf_definitions.respects_policy_at_preemption_point_implies_EDF_schedule". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.edf_definitions.EDF_schedule_equiv". Abort.
Check @prosa.analysis.facts.edf_definitions.EDF_schedule_equiv.
Goal True. idtac "END|prosa.analysis.facts.edf_definitions.EDF_schedule_equiv". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.hyperperiod.hyperperiod_int_mult_of_any_task". Abort.
Check @prosa.analysis.facts.hyperperiod.hyperperiod_int_mult_of_any_task.
Goal True. idtac "END|prosa.analysis.facts.hyperperiod.hyperperiod_int_mult_of_any_task". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.hyperperiod.valid_periods_imply_pos_hp". Abort.
Check @prosa.analysis.facts.hyperperiod.valid_periods_imply_pos_hp.
Goal True. idtac "END|prosa.analysis.facts.hyperperiod.valid_periods_imply_pos_hp". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.hyperperiod.corresponding_jobs_have_same_task". Abort.
Check @prosa.analysis.facts.hyperperiod.corresponding_jobs_have_same_task.
Goal True. idtac "END|prosa.analysis.facts.hyperperiod.corresponding_jobs_have_same_task". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.hyperperiod.all_jobs_arrive_within_hyperperiod". Abort.
Check @prosa.analysis.facts.hyperperiod.all_jobs_arrive_within_hyperperiod.
Goal True. idtac "END|prosa.analysis.facts.hyperperiod.all_jobs_arrive_within_hyperperiod". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.hyperperiod.eq_size_hyp_lt". Abort.
Check @prosa.analysis.facts.hyperperiod.eq_size_hyp_lt.
Goal True. idtac "END|prosa.analysis.facts.hyperperiod.eq_size_hyp_lt". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.hyperperiod.eq_size_of_arrivals_in_hyperperiod". Abort.
Check @prosa.analysis.facts.hyperperiod.eq_size_of_arrivals_in_hyperperiod.
Goal True. idtac "END|prosa.analysis.facts.hyperperiod.eq_size_of_arrivals_in_hyperperiod". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.hyperperiod.job_in_hp_arrives_in_task_arrivals_up_to". Abort.
Check @prosa.analysis.facts.hyperperiod.job_in_hp_arrives_in_task_arrivals_up_to.
Goal True. idtac "END|prosa.analysis.facts.hyperperiod.job_in_hp_arrives_in_task_arrivals_up_to". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.hyperperiod.job_in_own_hp". Abort.
Check @prosa.analysis.facts.hyperperiod.job_in_own_hp.
Goal True. idtac "END|prosa.analysis.facts.hyperperiod.job_in_own_hp". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.hyperperiod.corr_job_in_task_arrivals_up_to". Abort.
Check @prosa.analysis.facts.hyperperiod.corr_job_in_task_arrivals_up_to.
Goal True. idtac "END|prosa.analysis.facts.hyperperiod.corr_job_in_task_arrivals_up_to". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.hyperperiod.corresponding_job_arrives". Abort.
Check @prosa.analysis.facts.hyperperiod.corresponding_job_arrives.
Goal True. idtac "END|prosa.analysis.facts.hyperperiod.corresponding_job_arrives". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.interference.another_task_hep_job_split_hp_ep". Abort.
Check @prosa.analysis.facts.interference.another_task_hep_job_split_hp_ep.
Goal True. idtac "END|prosa.analysis.facts.interference.another_task_hep_job_split_hp_ep". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.interference.hep_interference_another_task_split". Abort.
Check @prosa.analysis.facts.interference.hep_interference_another_task_split.
Goal True. idtac "END|prosa.analysis.facts.interference.hep_interference_another_task_split". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.interference.cumulative_hep_interference_split_tasks_new". Abort.
Check @prosa.analysis.facts.interference.cumulative_hep_interference_split_tasks_new.
Goal True. idtac "END|prosa.analysis.facts.interference.cumulative_hep_interference_split_tasks_new". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.interference.no_hep_job_interference_without_supply". Abort.
Check @prosa.analysis.facts.interference.no_hep_job_interference_without_supply.
Goal True. idtac "END|prosa.analysis.facts.interference.no_hep_job_interference_without_supply". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.interference.no_hep_task_interference_without_supply". Abort.
Check @prosa.analysis.facts.interference.no_hep_task_interference_without_supply.
Goal True. idtac "END|prosa.analysis.facts.interference.no_hep_task_interference_without_supply". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.interference.no_hep_job_interference_when_idle". Abort.
Check @prosa.analysis.facts.interference.no_hep_job_interference_when_idle.
Goal True. idtac "END|prosa.analysis.facts.interference.no_hep_job_interference_when_idle". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.interference.no_hep_task_interference_when_idle". Abort.
Check @prosa.analysis.facts.interference.no_hep_task_interference_when_idle.
Goal True. idtac "END|prosa.analysis.facts.interference.no_hep_task_interference_when_idle". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.interference.interference_ahep_def". Abort.
Check @prosa.analysis.facts.interference.interference_ahep_def.
Goal True. idtac "END|prosa.analysis.facts.interference.interference_ahep_def". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.interference.interference_athep_def". Abort.
Check @prosa.analysis.facts.interference.interference_athep_def.
Goal True. idtac "END|prosa.analysis.facts.interference.interference_athep_def". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.interference.no_ahep_interference_when_scheduled". Abort.
Check @prosa.analysis.facts.interference.no_ahep_interference_when_scheduled.
Goal True. idtac "END|prosa.analysis.facts.interference.no_ahep_interference_when_scheduled". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.interference.no_ahep_interference_when_served". Abort.
Check @prosa.analysis.facts.interference.no_ahep_interference_when_served.
Goal True. idtac "END|prosa.analysis.facts.interference.no_ahep_interference_when_served". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.interference.no_athep_interference_when_scheduled". Abort.
Check @prosa.analysis.facts.interference.no_athep_interference_when_scheduled.
Goal True. idtac "END|prosa.analysis.facts.interference.no_athep_interference_when_scheduled". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.interference.athep_interference_iff". Abort.
Check @prosa.analysis.facts.interference.athep_interference_iff.
Goal True. idtac "END|prosa.analysis.facts.interference.athep_interference_iff". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.interference.athep_interference_if". Abort.
Check @prosa.analysis.facts.interference.athep_interference_if.
Goal True. idtac "END|prosa.analysis.facts.interference.athep_interference_if". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.interference.no_ahep_interference_when_scheduled_lp". Abort.
Check @prosa.analysis.facts.interference.no_ahep_interference_when_scheduled_lp.
Goal True. idtac "END|prosa.analysis.facts.interference.no_ahep_interference_when_scheduled_lp". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.interference.cumulative_i_ohep_eq_service_of_ohep". Abort.
Check @prosa.analysis.facts.interference.cumulative_i_ohep_eq_service_of_ohep.
Goal True. idtac "END|prosa.analysis.facts.interference.cumulative_i_ohep_eq_service_of_ohep". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.interference.cumulative_i_thep_eq_service_of_othep". Abort.
Check @prosa.analysis.facts.interference.cumulative_i_thep_eq_service_of_othep.
Goal True. idtac "END|prosa.analysis.facts.interference.cumulative_i_thep_eq_service_of_othep". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.jitter.jitter_arrives_in_iff". Abort.
Check @prosa.analysis.facts.jitter.jitter_arrives_in_iff.
Goal True. idtac "END|prosa.analysis.facts.jitter.jitter_arrives_in_iff". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.jitter.valid_release_sequence". Abort.
Check @prosa.analysis.facts.jitter.valid_release_sequence.
Goal True. idtac "END|prosa.analysis.facts.jitter.valid_release_sequence". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.jitter.valid_release_curve". Abort.
Check @prosa.analysis.facts.jitter.valid_release_curve.
Goal True. idtac "END|prosa.analysis.facts.jitter.valid_release_curve". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.jitter.release_curve_respected". Abort.
Check @prosa.analysis.facts.jitter.release_curve_respected.
Goal True. idtac "END|prosa.analysis.facts.jitter.release_curve_respected". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.jitter.jitter_prop_same_jobs". Abort.
Check @prosa.analysis.facts.jitter.jitter_prop_same_jobs.
Goal True. idtac "END|prosa.analysis.facts.jitter.jitter_prop_same_jobs". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.jitter.jitter_prop_same_jobs'". Abort.
Check @prosa.analysis.facts.jitter.jitter_prop_same_jobs'.
Goal True. idtac "END|prosa.analysis.facts.jitter.jitter_prop_same_jobs'". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.jitter.jitter_prop_valid_costs". Abort.
Check @prosa.analysis.facts.jitter.jitter_prop_valid_costs.
Goal True. idtac "END|prosa.analysis.facts.jitter.jitter_prop_valid_costs". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.jitter.jitter_ready_to_execute". Abort.
Check @prosa.analysis.facts.jitter.jitter_ready_to_execute.
Goal True. idtac "END|prosa.analysis.facts.jitter.jitter_ready_to_execute". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.jitter.jitter_work_conservation". Abort.
Check @prosa.analysis.facts.jitter.jitter_work_conservation.
Goal True. idtac "END|prosa.analysis.facts.jitter.jitter_work_conservation". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.jitter.jitter_valid_schedule". Abort.
Check @prosa.analysis.facts.jitter.jitter_valid_schedule.
Goal True. idtac "END|prosa.analysis.facts.jitter.jitter_valid_schedule". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.jitter.jitter_scheduled_jobs_at_equiv". Abort.
Check @prosa.analysis.facts.jitter.jitter_scheduled_jobs_at_equiv.
Goal True. idtac "END|prosa.analysis.facts.jitter.jitter_scheduled_jobs_at_equiv". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.jitter.jitter_scheduled_job_at_eq". Abort.
Check @prosa.analysis.facts.jitter.jitter_scheduled_job_at_eq.
Goal True. idtac "END|prosa.analysis.facts.jitter.jitter_scheduled_job_at_eq". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.jitter.jitter_FP_compliance". Abort.
Check @prosa.analysis.facts.jitter.jitter_FP_compliance.
Goal True. idtac "END|prosa.analysis.facts.jitter.jitter_FP_compliance". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.jitter.jitter_response_time_bound". Abort.
Check @prosa.analysis.facts.jitter.jitter_response_time_bound.
Goal True. idtac "END|prosa.analysis.facts.jitter.jitter_response_time_bound". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.job_index.case_arrival_lte_implies_equal_job". Abort.
Check @prosa.analysis.facts.job_index.case_arrival_lte_implies_equal_job.
Goal True. idtac "END|prosa.analysis.facts.job_index.case_arrival_lte_implies_equal_job". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.job_index.case_arrival_gt_implies_equal_job". Abort.
Check @prosa.analysis.facts.job_index.case_arrival_gt_implies_equal_job.
Goal True. idtac "END|prosa.analysis.facts.job_index.case_arrival_gt_implies_equal_job". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.job_index.equal_index_implies_equal_jobs". Abort.
Check @prosa.analysis.facts.job_index.equal_index_implies_equal_jobs.
Goal True. idtac "END|prosa.analysis.facts.job_index.equal_index_implies_equal_jobs". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.job_index.diff_jobs_iff_diff_indices". Abort.
Check @prosa.analysis.facts.job_index.diff_jobs_iff_diff_indices.
Goal True. idtac "END|prosa.analysis.facts.job_index.diff_jobs_iff_diff_indices". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.job_index.index_as_sum_size_and_index". Abort.
Check @prosa.analysis.facts.job_index.index_as_sum_size_and_index.
Goal True. idtac "END|prosa.analysis.facts.job_index.index_as_sum_size_and_index". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.job_index.arrival_lt_implies_job_in_arrivals_between_P". Abort.
Check @prosa.analysis.facts.job_index.arrival_lt_implies_job_in_arrivals_between_P.
Goal True. idtac "END|prosa.analysis.facts.job_index.arrival_lt_implies_job_in_arrivals_between_P". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.job_index.index_lte_implies_arrival_lte_P". Abort.
Check @prosa.analysis.facts.job_index.index_lte_implies_arrival_lte_P.
Goal True. idtac "END|prosa.analysis.facts.job_index.index_lte_implies_arrival_lte_P". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.job_index.job_index_same_in_task_arrivals". Abort.
Check @prosa.analysis.facts.job_index.job_index_same_in_task_arrivals.
Goal True. idtac "END|prosa.analysis.facts.job_index.job_index_same_in_task_arrivals". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.job_index.index_job_lt_size_task_arrivals_up_to_job". Abort.
Check @prosa.analysis.facts.job_index.index_job_lt_size_task_arrivals_up_to_job.
Goal True. idtac "END|prosa.analysis.facts.job_index.index_job_lt_size_task_arrivals_up_to_job". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.job_index.index_lte_implies_arrival_lte". Abort.
Check @prosa.analysis.facts.job_index.index_lte_implies_arrival_lte.
Goal True. idtac "END|prosa.analysis.facts.job_index.index_lte_implies_arrival_lte". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.job_index.earlier_arrival_implies_lower_index". Abort.
Check @prosa.analysis.facts.job_index.earlier_arrival_implies_lower_index.
Goal True. idtac "END|prosa.analysis.facts.job_index.earlier_arrival_implies_lower_index". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.job_index.job_index_minus_one_lt_size_task_arrivals_up_to". Abort.
Check @prosa.analysis.facts.job_index.job_index_minus_one_lt_size_task_arrivals_up_to.
Goal True. idtac "END|prosa.analysis.facts.job_index.job_index_minus_one_lt_size_task_arrivals_up_to". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.job_index.positive_job_index_implies_positive_size_of_task_arrivals". Abort.
Check @prosa.analysis.facts.job_index.positive_job_index_implies_positive_size_of_task_arrivals.
Goal True. idtac "END|prosa.analysis.facts.job_index.positive_job_index_implies_positive_size_of_task_arrivals". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.job_index.prev_job_arr". Abort.
Check @prosa.analysis.facts.job_index.prev_job_arr.
Goal True. idtac "END|prosa.analysis.facts.job_index.prev_job_arr". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.job_index.prev_job_index". Abort.
Check @prosa.analysis.facts.job_index.prev_job_index.
Goal True. idtac "END|prosa.analysis.facts.job_index.prev_job_index". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.job_index.prev_job_task". Abort.
Check @prosa.analysis.facts.job_index.prev_job_task.
Goal True. idtac "END|prosa.analysis.facts.job_index.prev_job_task". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.job_index.prev_job_in_task_arrivals_up_to_j". Abort.
Check @prosa.analysis.facts.job_index.prev_job_in_task_arrivals_up_to_j.
Goal True. idtac "END|prosa.analysis.facts.job_index.prev_job_in_task_arrivals_up_to_j". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.job_index.prev_job_arr_lte". Abort.
Check @prosa.analysis.facts.job_index.prev_job_arr_lte.
Goal True. idtac "END|prosa.analysis.facts.job_index.prev_job_arr_lte". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.job_index.prev_job_index_j". Abort.
Check @prosa.analysis.facts.job_index.prev_job_index_j.
Goal True. idtac "END|prosa.analysis.facts.job_index.prev_job_index_j". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.job_index.no_jobs_between_consecutive_jobs". Abort.
Check @prosa.analysis.facts.job_index.no_jobs_between_consecutive_jobs.
Goal True. idtac "END|prosa.analysis.facts.job_index.no_jobs_between_consecutive_jobs". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.job_index.exists_jobs_before_j". Abort.
Check @prosa.analysis.facts.job_index.exists_jobs_before_j.
Goal True. idtac "END|prosa.analysis.facts.job_index.exists_jobs_before_j". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.arrival_curves.non_pathological_max_arrivals". Abort.
Check @prosa.analysis.facts.model.arrival_curves.non_pathological_max_arrivals.
Goal True. idtac "END|prosa.analysis.facts.model.arrival_curves.non_pathological_max_arrivals". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.arrival_curves.jlfp_hep_arrivals_bounded_by_sum_max_arrivals". Abort.
Check @prosa.analysis.facts.model.arrival_curves.jlfp_hep_arrivals_bounded_by_sum_max_arrivals.
Goal True. idtac "END|prosa.analysis.facts.model.arrival_curves.jlfp_hep_arrivals_bounded_by_sum_max_arrivals". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.arrival_curves.fp_hep_arrivals_bounded_by_sum_max_arrivals". Abort.
Check @prosa.analysis.facts.model.arrival_curves.fp_hep_arrivals_bounded_by_sum_max_arrivals.
Goal True. idtac "END|prosa.analysis.facts.model.arrival_curves.fp_hep_arrivals_bounded_by_sum_max_arrivals". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.dbf.task_arrivals_with_deadline_within_eq". Abort.
Check @prosa.analysis.facts.model.dbf.task_arrivals_with_deadline_within_eq.
Goal True. idtac "END|prosa.analysis.facts.model.dbf.task_arrivals_with_deadline_within_eq". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.dbf.num_task_arrivals_with_deadline_within_eq". Abort.
Check @prosa.analysis.facts.model.dbf.num_task_arrivals_with_deadline_within_eq.
Goal True. idtac "END|prosa.analysis.facts.model.dbf.num_task_arrivals_with_deadline_within_eq". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.dbf.task_demand_within". Abort.
Check @prosa.analysis.facts.model.dbf.task_demand_within.
Goal True. idtac "END|prosa.analysis.facts.model.dbf.task_demand_within". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.dbf.task_demand_within_le_task_dbf". Abort.
Check @prosa.analysis.facts.model.dbf.task_demand_within_le_task_dbf.
Goal True. idtac "END|prosa.analysis.facts.model.dbf.task_demand_within_le_task_dbf". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.dbf.task_demand_within_le_task_rbf_shifted". Abort.
Check @prosa.analysis.facts.model.dbf.task_demand_within_le_task_rbf_shifted.
Goal True. idtac "END|prosa.analysis.facts.model.dbf.task_demand_within_le_task_rbf_shifted". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.dbf.total_demand_within". Abort.
Check @prosa.analysis.facts.model.dbf.total_demand_within.
Goal True. idtac "END|prosa.analysis.facts.model.dbf.total_demand_within". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.dbf.total_demand_within_le_total_dbf". Abort.
Check @prosa.analysis.facts.model.dbf.total_demand_within_le_total_dbf.
Goal True. idtac "END|prosa.analysis.facts.model.dbf.total_demand_within_le_total_dbf". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.dbf.total_demand_within_le_sum_task_rbf_shifted". Abort.
Check @prosa.analysis.facts.model.dbf.total_demand_within_le_sum_task_rbf_shifted.
Goal True. idtac "END|prosa.analysis.facts.model.dbf.total_demand_within_le_sum_task_rbf_shifted". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.dynamic_suspension.job_suspension_bounded". Abort.
Check @prosa.analysis.facts.model.dynamic_suspension.job_suspension_bounded.
Goal True. idtac "END|prosa.analysis.facts.model.dynamic_suspension.job_suspension_bounded". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.dynamic_suspension.suspension_of_task_bounded". Abort.
Check @prosa.analysis.facts.model.dynamic_suspension.suspension_of_task_bounded.
Goal True. idtac "END|prosa.analysis.facts.model.dynamic_suspension.suspension_of_task_bounded". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.exceedance.SBF.eps_sbf". Abort.
Check @prosa.analysis.facts.model.exceedance.SBF.eps_sbf.
Goal True. idtac "END|prosa.analysis.facts.model.exceedance.SBF.eps_sbf". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.exceedance.SBF.blackout_during_bounded". Abort.
Check @prosa.analysis.facts.model.exceedance.SBF.blackout_during_bounded.
Goal True. idtac "END|prosa.analysis.facts.model.exceedance.SBF.blackout_during_bounded". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.exceedance.SBF.eps_sbf_is_valid". Abort.
Check @prosa.analysis.facts.model.exceedance.SBF.eps_sbf_is_valid.
Goal True. idtac "END|prosa.analysis.facts.model.exceedance.SBF.eps_sbf_is_valid". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.exceedance.SBF.eps_sbf_is_unit". Abort.
Check @prosa.analysis.facts.model.exceedance.SBF.eps_sbf_is_unit.
Goal True. idtac "END|prosa.analysis.facts.model.exceedance.SBF.eps_sbf_is_unit". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.ideal.priority_inversion.idle_implies_no_priority_inversion". Abort.
Check @prosa.analysis.facts.model.ideal.priority_inversion.idle_implies_no_priority_inversion.
Goal True. idtac "END|prosa.analysis.facts.model.ideal.priority_inversion.idle_implies_no_priority_inversion". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.ideal.priority_inversion.priority_inversion_equiv_sched_lower_priority". Abort.
Check @prosa.analysis.facts.model.ideal.priority_inversion.priority_inversion_equiv_sched_lower_priority.
Goal True. idtac "END|prosa.analysis.facts.model.ideal.priority_inversion.priority_inversion_equiv_sched_lower_priority". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.ideal.priority_inversion.sched_hep_implies_no_priority_inversion". Abort.
Check @prosa.analysis.facts.model.ideal.priority_inversion.sched_hep_implies_no_priority_inversion.
Goal True. idtac "END|prosa.analysis.facts.model.ideal.priority_inversion.sched_hep_implies_no_priority_inversion". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.ideal.priority_inversion.sched_lp_implies_priority_inversion". Abort.
Check @prosa.analysis.facts.model.ideal.priority_inversion.sched_lp_implies_priority_inversion.
Goal True. idtac "END|prosa.analysis.facts.model.ideal.priority_inversion.sched_lp_implies_priority_inversion". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.ideal.schedule.ideal_proc_model_is_a_uniprocessor_model". Abort.
Check @prosa.analysis.facts.model.ideal.schedule.ideal_proc_model_is_a_uniprocessor_model.
Goal True. idtac "END|prosa.analysis.facts.model.ideal.schedule.ideal_proc_model_is_a_uniprocessor_model". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.ideal.schedule.service_in_service_on". Abort.
Check @prosa.analysis.facts.model.ideal.schedule.service_in_service_on.
Goal True. idtac "END|prosa.analysis.facts.model.ideal.schedule.service_in_service_on". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.ideal.schedule.service_in_def". Abort.
Check @prosa.analysis.facts.model.ideal.schedule.service_in_def.
Goal True. idtac "END|prosa.analysis.facts.model.ideal.schedule.service_in_def". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.ideal.schedule.ideal_proc_model_ensures_ideal_progress". Abort.
Check @prosa.analysis.facts.model.ideal.schedule.ideal_proc_model_ensures_ideal_progress.
Goal True. idtac "END|prosa.analysis.facts.model.ideal.schedule.ideal_proc_model_ensures_ideal_progress". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.ideal.schedule.ideal_proc_model_provides_unit_service". Abort.
Check @prosa.analysis.facts.model.ideal.schedule.ideal_proc_model_provides_unit_service.
Goal True. idtac "END|prosa.analysis.facts.model.ideal.schedule.ideal_proc_model_provides_unit_service". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.ideal.schedule.ideal_proc_model_provides_unit_supply". Abort.
Check @prosa.analysis.facts.model.ideal.schedule.ideal_proc_model_provides_unit_supply.
Goal True. idtac "END|prosa.analysis.facts.model.ideal.schedule.ideal_proc_model_provides_unit_supply". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.ideal.schedule.scheduled_in_def". Abort.
Check @prosa.analysis.facts.model.ideal.schedule.scheduled_in_def.
Goal True. idtac "END|prosa.analysis.facts.model.ideal.schedule.scheduled_in_def". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.ideal.schedule.scheduled_at_def". Abort.
Check @prosa.analysis.facts.model.ideal.schedule.scheduled_at_def.
Goal True. idtac "END|prosa.analysis.facts.model.ideal.schedule.scheduled_at_def". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.ideal.schedule.service_on_def". Abort.
Check @prosa.analysis.facts.model.ideal.schedule.service_on_def.
Goal True. idtac "END|prosa.analysis.facts.model.ideal.schedule.service_on_def". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.ideal.schedule.service_at_def". Abort.
Check @prosa.analysis.facts.model.ideal.schedule.service_at_def.
Goal True. idtac "END|prosa.analysis.facts.model.ideal.schedule.service_at_def". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.ideal.schedule.service_in_is_scheduled_in". Abort.
Check @prosa.analysis.facts.model.ideal.schedule.service_in_is_scheduled_in.
Goal True. idtac "END|prosa.analysis.facts.model.ideal.schedule.service_in_is_scheduled_in". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.ideal.schedule.service_at_is_scheduled_at". Abort.
Check @prosa.analysis.facts.model.ideal.schedule.service_at_is_scheduled_at.
Goal True. idtac "END|prosa.analysis.facts.model.ideal.schedule.service_at_is_scheduled_at". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.ideal.schedule.ideal_proc_model_fully_consuming". Abort.
Check @prosa.analysis.facts.model.ideal.schedule.ideal_proc_model_fully_consuming.
Goal True. idtac "END|prosa.analysis.facts.model.ideal.schedule.ideal_proc_model_fully_consuming". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.ideal.schedule.ideal_proc_has_supply". Abort.
Check @prosa.analysis.facts.model.ideal.schedule.ideal_proc_has_supply.
Goal True. idtac "END|prosa.analysis.facts.model.ideal.schedule.ideal_proc_has_supply". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.ideal.schedule.ideal_proc_model_sched_case_analysis". Abort.
Check @prosa.analysis.facts.model.ideal.schedule.ideal_proc_model_sched_case_analysis.
Goal True. idtac "END|prosa.analysis.facts.model.ideal.schedule.ideal_proc_model_sched_case_analysis". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.ideal.schedule.ideal_sched_implies_not_idle". Abort.
Check @prosa.analysis.facts.model.ideal.schedule.ideal_sched_implies_not_idle.
Goal True. idtac "END|prosa.analysis.facts.model.ideal.schedule.ideal_sched_implies_not_idle". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.ideal.schedule.ideal_not_idle_implies_sched". Abort.
Check @prosa.analysis.facts.model.ideal.schedule.ideal_not_idle_implies_sched.
Goal True. idtac "END|prosa.analysis.facts.model.ideal.schedule.ideal_not_idle_implies_sched". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.ideal.schedule.scheduled_job_at_def". Abort.
Check @prosa.analysis.facts.model.ideal.schedule.scheduled_job_at_def.
Goal True. idtac "END|prosa.analysis.facts.model.ideal.schedule.scheduled_job_at_def". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.ideal.schedule.is_idle_def". Abort.
Check @prosa.analysis.facts.model.ideal.schedule.is_idle_def.
Goal True. idtac "END|prosa.analysis.facts.model.ideal.schedule.is_idle_def". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.ideal.service_of_jobs.low_service_implies_existence_of_idle_time_rs". Abort.
Check @prosa.analysis.facts.model.ideal.service_of_jobs.low_service_implies_existence_of_idle_time_rs.
Goal True. idtac "END|prosa.analysis.facts.model.ideal.service_of_jobs.low_service_implies_existence_of_idle_time_rs". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.ideal.service_of_jobs.low_service_implies_existence_of_idle_time". Abort.
Check @prosa.analysis.facts.model.ideal.service_of_jobs.low_service_implies_existence_of_idle_time.
Goal True. idtac "END|prosa.analysis.facts.model.ideal.service_of_jobs.low_service_implies_existence_of_idle_time". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.ideal_uni_exceed.eps_is_unit_supply". Abort.
Check @prosa.analysis.facts.model.ideal_uni_exceed.eps_is_unit_supply.
Goal True. idtac "END|prosa.analysis.facts.model.ideal_uni_exceed.eps_is_unit_supply". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.ideal_uni_exceed.scheduled_at_procstate". Abort.
Check @prosa.analysis.facts.model.ideal_uni_exceed.scheduled_at_procstate.
Goal True. idtac "END|prosa.analysis.facts.model.ideal_uni_exceed.scheduled_at_procstate". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.ideal_uni_exceed.eps_is_uniproc". Abort.
Check @prosa.analysis.facts.model.ideal_uni_exceed.eps_is_uniproc.
Goal True. idtac "END|prosa.analysis.facts.model.ideal_uni_exceed.eps_is_uniproc". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.ideal_uni_exceed.eps_is_fully_consuming". Abort.
Check @prosa.analysis.facts.model.ideal_uni_exceed.eps_is_fully_consuming.
Goal True. idtac "END|prosa.analysis.facts.model.ideal_uni_exceed.eps_is_fully_consuming". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.ideal_uni_exceed.eps_is_unit_service". Abort.
Check @prosa.analysis.facts.model.ideal_uni_exceed.eps_is_unit_service.
Goal True. idtac "END|prosa.analysis.facts.model.ideal_uni_exceed.eps_is_unit_service". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.ideal_uni_exceed.is_exceedance_exec". Abort.
Check @prosa.analysis.facts.model.ideal_uni_exceed.is_exceedance_exec.
Goal True. idtac "END|prosa.analysis.facts.model.ideal_uni_exceed.is_exceedance_exec". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.ideal_uni_exceed.blackout_implies_exceedance_execution". Abort.
Check @prosa.analysis.facts.model.ideal_uni_exceed.blackout_implies_exceedance_execution.
Goal True. idtac "END|prosa.analysis.facts.model.ideal_uni_exceed.blackout_implies_exceedance_execution". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.offset.first_job_arrival". Abort.
Check @prosa.analysis.facts.model.offset.first_job_arrival.
Goal True. idtac "END|prosa.analysis.facts.model.offset.first_job_arrival". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.offset.max_offset_g". Abort.
Check @prosa.analysis.facts.model.offset.max_offset_g.
Goal True. idtac "END|prosa.analysis.facts.model.offset.max_offset_g". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.overheads.blackout_bound.blackout_during_split". Abort.
Check @prosa.analysis.facts.model.overheads.blackout_bound.blackout_during_split.
Goal True. idtac "END|prosa.analysis.facts.model.overheads.blackout_bound.blackout_during_split". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.overheads.blackout_bound.total_dispatch_time_eq_job_dispatch_time". Abort.
Check @prosa.analysis.facts.model.overheads.blackout_bound.total_dispatch_time_eq_job_dispatch_time.
Goal True. idtac "END|prosa.analysis.facts.model.overheads.blackout_bound.total_dispatch_time_eq_job_dispatch_time". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.overheads.blackout_bound.total_cswitch_time_eq_job_cswitch_time". Abort.
Check @prosa.analysis.facts.model.overheads.blackout_bound.total_cswitch_time_eq_job_cswitch_time.
Goal True. idtac "END|prosa.analysis.facts.model.overheads.blackout_bound.total_cswitch_time_eq_job_cswitch_time". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.overheads.blackout_bound.total_CRPD_time_eq_job_CRPD_time". Abort.
Check @prosa.analysis.facts.model.overheads.blackout_bound.total_CRPD_time_eq_job_CRPD_time.
Goal True. idtac "END|prosa.analysis.facts.model.overheads.blackout_bound.total_CRPD_time_eq_job_CRPD_time". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.overheads.blackout_bound.total_time_in_dispatch_is_bounded". Abort.
Check @prosa.analysis.facts.model.overheads.blackout_bound.total_time_in_dispatch_is_bounded.
Goal True. idtac "END|prosa.analysis.facts.model.overheads.blackout_bound.total_time_in_dispatch_is_bounded". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.overheads.blackout_bound.total_time_in_cswitch_is_bounded". Abort.
Check @prosa.analysis.facts.model.overheads.blackout_bound.total_time_in_cswitch_is_bounded.
Goal True. idtac "END|prosa.analysis.facts.model.overheads.blackout_bound.total_time_in_cswitch_is_bounded". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.overheads.blackout_bound.total_time_in_CRPD_is_bounded". Abort.
Check @prosa.analysis.facts.model.overheads.blackout_bound.total_time_in_CRPD_is_bounded.
Goal True. idtac "END|prosa.analysis.facts.model.overheads.blackout_bound.total_time_in_CRPD_is_bounded". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.overheads.blackout_bound.no_sched_changes_bounded_overheads_blackout". Abort.
Check @prosa.analysis.facts.model.overheads.blackout_bound.no_sched_changes_bounded_overheads_blackout.
Goal True. idtac "END|prosa.analysis.facts.model.overheads.blackout_bound.no_sched_changes_bounded_overheads_blackout". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.overheads.blackout_bound.sched_changes_start_busy_pref_bounded_overheads_blackout". Abort.
Check @prosa.analysis.facts.model.overheads.blackout_bound.sched_changes_start_busy_pref_bounded_overheads_blackout.
Goal True. idtac "END|prosa.analysis.facts.model.overheads.blackout_bound.sched_changes_start_busy_pref_bounded_overheads_blackout". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.overheads.blackout_bound.fin_sched_changes_start_busy_pref_bounded_overheads_blackout". Abort.
Check @prosa.analysis.facts.model.overheads.blackout_bound.fin_sched_changes_start_busy_pref_bounded_overheads_blackout.
Goal True. idtac "END|prosa.analysis.facts.model.overheads.blackout_bound.fin_sched_changes_start_busy_pref_bounded_overheads_blackout". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.overheads.blackout_bound.finite_sched_changes_bounded_overheads_blackout". Abort.
Check @prosa.analysis.facts.model.overheads.blackout_bound.finite_sched_changes_bounded_overheads_blackout.
Goal True. idtac "END|prosa.analysis.facts.model.overheads.blackout_bound.finite_sched_changes_bounded_overheads_blackout". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.overheads.priority_bump.priority_bump_implies_preemption_time". Abort.
Check @prosa.analysis.facts.model.overheads.priority_bump.priority_bump_implies_preemption_time.
Goal True. idtac "END|prosa.analysis.facts.model.overheads.priority_bump.priority_bump_implies_preemption_time". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.overheads.priority_bump.priority_bump_implies_hp_arrival_in_prefix". Abort.
Check @prosa.analysis.facts.model.overheads.priority_bump.priority_bump_implies_hp_arrival_in_prefix.
Goal True. idtac "END|prosa.analysis.facts.model.overheads.priority_bump.priority_bump_implies_hp_arrival_in_prefix". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.overheads.priority_bump.no_priority_bumps_in_fifo". Abort.
Check @prosa.analysis.facts.model.overheads.priority_bump.no_priority_bumps_in_fifo.
Goal True. idtac "END|prosa.analysis.facts.model.overheads.priority_bump.no_priority_bumps_in_fifo". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.overheads.sbf.fifo.fifo_blackout_bound". Abort.
Check @prosa.analysis.facts.model.overheads.sbf.fifo.fifo_blackout_bound.
Goal True. idtac "END|prosa.analysis.facts.model.overheads.sbf.fifo.fifo_blackout_bound". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.overheads.sbf.fifo.fifo_ovh_sbf_slow". Abort.
Check @prosa.analysis.facts.model.overheads.sbf.fifo.fifo_ovh_sbf_slow.
Goal True. idtac "END|prosa.analysis.facts.model.overheads.sbf.fifo.fifo_ovh_sbf_slow". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.overheads.sbf.fifo.overheads_sbf_monotone". Abort.
Check @prosa.analysis.facts.model.overheads.sbf.fifo.overheads_sbf_monotone.
Goal True. idtac "END|prosa.analysis.facts.model.overheads.sbf.fifo.overheads_sbf_monotone". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.overheads.sbf.fifo.fifo_blackout_bound_monotone". Abort.
Check @prosa.analysis.facts.model.overheads.sbf.fifo.fifo_blackout_bound_monotone.
Goal True. idtac "END|prosa.analysis.facts.model.overheads.sbf.fifo.fifo_blackout_bound_monotone". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.overheads.sbf.fifo.overheads_sbf_unit". Abort.
Check @prosa.analysis.facts.model.overheads.sbf.fifo.overheads_sbf_unit.
Goal True. idtac "END|prosa.analysis.facts.model.overheads.sbf.fifo.overheads_sbf_unit". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.overheads.sbf.fifo.overheads_sbf_busy_valid". Abort.
Check @prosa.analysis.facts.model.overheads.sbf.fifo.overheads_sbf_busy_valid.
Goal True. idtac "END|prosa.analysis.facts.model.overheads.sbf.fifo.overheads_sbf_busy_valid". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.overheads.sbf.fp.fp_blackout_bound". Abort.
Check @prosa.analysis.facts.model.overheads.sbf.fp.fp_blackout_bound.
Goal True. idtac "END|prosa.analysis.facts.model.overheads.sbf.fp.fp_blackout_bound". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.overheads.sbf.fp.fp_ovh_sbf_slow". Abort.
Check @prosa.analysis.facts.model.overheads.sbf.fp.fp_ovh_sbf_slow.
Goal True. idtac "END|prosa.analysis.facts.model.overheads.sbf.fp.fp_ovh_sbf_slow". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.overheads.sbf.fp.overheads_sbf_monotone". Abort.
Check @prosa.analysis.facts.model.overheads.sbf.fp.overheads_sbf_monotone.
Goal True. idtac "END|prosa.analysis.facts.model.overheads.sbf.fp.overheads_sbf_monotone". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.overheads.sbf.fp.fp_blackout_bound_monotone". Abort.
Check @prosa.analysis.facts.model.overheads.sbf.fp.fp_blackout_bound_monotone.
Goal True. idtac "END|prosa.analysis.facts.model.overheads.sbf.fp.fp_blackout_bound_monotone". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.overheads.sbf.fp.overheads_sbf_unit". Abort.
Check @prosa.analysis.facts.model.overheads.sbf.fp.overheads_sbf_unit.
Goal True. idtac "END|prosa.analysis.facts.model.overheads.sbf.fp.overheads_sbf_unit". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.overheads.sbf.fp.overheads_sbf_busy_valid". Abort.
Check @prosa.analysis.facts.model.overheads.sbf.fp.overheads_sbf_busy_valid.
Goal True. idtac "END|prosa.analysis.facts.model.overheads.sbf.fp.overheads_sbf_busy_valid". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.overheads.sbf.jlfp.jlfp_blackout_bound". Abort.
Check @prosa.analysis.facts.model.overheads.sbf.jlfp.jlfp_blackout_bound.
Goal True. idtac "END|prosa.analysis.facts.model.overheads.sbf.jlfp.jlfp_blackout_bound". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.overheads.sbf.jlfp.jlfp_ovh_sbf_slow". Abort.
Check @prosa.analysis.facts.model.overheads.sbf.jlfp.jlfp_ovh_sbf_slow.
Goal True. idtac "END|prosa.analysis.facts.model.overheads.sbf.jlfp.jlfp_ovh_sbf_slow". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.overheads.sbf.jlfp.overheads_sbf_monotone". Abort.
Check @prosa.analysis.facts.model.overheads.sbf.jlfp.overheads_sbf_monotone.
Goal True. idtac "END|prosa.analysis.facts.model.overheads.sbf.jlfp.overheads_sbf_monotone". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.overheads.sbf.jlfp.jlfp_blackout_bound_monotone". Abort.
Check @prosa.analysis.facts.model.overheads.sbf.jlfp.jlfp_blackout_bound_monotone.
Goal True. idtac "END|prosa.analysis.facts.model.overheads.sbf.jlfp.jlfp_blackout_bound_monotone". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.overheads.sbf.jlfp.overheads_sbf_unit". Abort.
Check @prosa.analysis.facts.model.overheads.sbf.jlfp.overheads_sbf_unit.
Goal True. idtac "END|prosa.analysis.facts.model.overheads.sbf.jlfp.overheads_sbf_unit". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.overheads.sbf.jlfp.overheads_sbf_busy_valid". Abort.
Check @prosa.analysis.facts.model.overheads.sbf.jlfp.overheads_sbf_busy_valid.
Goal True. idtac "END|prosa.analysis.facts.model.overheads.sbf.jlfp.overheads_sbf_busy_valid". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.overheads.schedule.overheads_proc_model_is_a_uniprocessor_model". Abort.
Check @prosa.analysis.facts.model.overheads.schedule.overheads_proc_model_is_a_uniprocessor_model.
Goal True. idtac "END|prosa.analysis.facts.model.overheads.schedule.overheads_proc_model_is_a_uniprocessor_model". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.overheads.schedule.overheads_proc_model_provides_unit_supply". Abort.
Check @prosa.analysis.facts.model.overheads.schedule.overheads_proc_model_provides_unit_supply.
Goal True. idtac "END|prosa.analysis.facts.model.overheads.schedule.overheads_proc_model_provides_unit_supply". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.overheads.schedule.overheads_proc_model_fully_consuming". Abort.
Check @prosa.analysis.facts.model.overheads.schedule.overheads_proc_model_fully_consuming.
Goal True. idtac "END|prosa.analysis.facts.model.overheads.schedule.overheads_proc_model_fully_consuming". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.overheads.schedule.scheduled_job_dec". Abort.
Check @prosa.analysis.facts.model.overheads.schedule.scheduled_job_dec.
Goal True. idtac "END|prosa.analysis.facts.model.overheads.schedule.scheduled_job_dec". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.overheads.schedule.scheduled_at_iff_scheduled_job". Abort.
Check @prosa.analysis.facts.model.overheads.schedule.scheduled_at_iff_scheduled_job.
Goal True. idtac "END|prosa.analysis.facts.model.overheads.schedule.scheduled_at_iff_scheduled_job". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.overheads.schedule.job_scheduled_in_busy_interval_prefix". Abort.
Check @prosa.analysis.facts.model.overheads.schedule.job_scheduled_in_busy_interval_prefix.
Goal True. idtac "END|prosa.analysis.facts.model.overheads.schedule.job_scheduled_in_busy_interval_prefix". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.overheads.schedule_change.number_schedule_changes_cat". Abort.
Check @prosa.analysis.facts.model.overheads.schedule_change.number_schedule_changes_cat.
Goal True. idtac "END|prosa.analysis.facts.model.overheads.schedule_change.number_schedule_changes_cat". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.overheads.schedule_change.first_schedule_change_exists". Abort.
Check @prosa.analysis.facts.model.overheads.schedule_change.first_schedule_change_exists.
Goal True. idtac "END|prosa.analysis.facts.model.overheads.schedule_change.first_schedule_change_exists". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.overheads.schedule_change.number_schedule_changes_widen". Abort.
Check @prosa.analysis.facts.model.overheads.schedule_change.number_schedule_changes_widen.
Goal True. idtac "END|prosa.analysis.facts.model.overheads.schedule_change.number_schedule_changes_widen". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.overheads.schedule_change.same_scheduled_state_merge". Abort.
Check @prosa.analysis.facts.model.overheads.schedule_change.same_scheduled_state_merge.
Goal True. idtac "END|prosa.analysis.facts.model.overheads.schedule_change.same_scheduled_state_merge". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.overheads.schedule_change.no_schedule_changes_implies_constant_schedule". Abort.
Check @prosa.analysis.facts.model.overheads.schedule_change.no_schedule_changes_implies_constant_schedule.
Goal True. idtac "END|prosa.analysis.facts.model.overheads.schedule_change.no_schedule_changes_implies_constant_schedule". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.overheads.schedule_change.no_changes_implies_same_scheduled_job". Abort.
Check @prosa.analysis.facts.model.overheads.schedule_change.no_changes_implies_same_scheduled_job.
Goal True. idtac "END|prosa.analysis.facts.model.overheads.schedule_change.no_changes_implies_same_scheduled_job". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.overheads.schedule_change_bound.schedule_changes_bounded_by_total_arrivals_JLFP". Abort.
Check @prosa.analysis.facts.model.overheads.schedule_change_bound.schedule_changes_bounded_by_total_arrivals_JLFP.
Goal True. idtac "END|prosa.analysis.facts.model.overheads.schedule_change_bound.schedule_changes_bounded_by_total_arrivals_JLFP". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.overheads.schedule_change_bound.schedule_changes_bounded_by_total_arrivals_FP". Abort.
Check @prosa.analysis.facts.model.overheads.schedule_change_bound.schedule_changes_bounded_by_total_arrivals_FP.
Goal True. idtac "END|prosa.analysis.facts.model.overheads.schedule_change_bound.schedule_changes_bounded_by_total_arrivals_FP". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.overheads.schedule_change_bound.schedule_changes_bounded_by_total_arrivals_FIFO". Abort.
Check @prosa.analysis.facts.model.overheads.schedule_change_bound.schedule_changes_bounded_by_total_arrivals_FIFO.
Goal True. idtac "END|prosa.analysis.facts.model.overheads.schedule_change_bound.schedule_changes_bounded_by_total_arrivals_FIFO". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.preemption.preemption_time_interval_case". Abort.
Check @prosa.analysis.facts.model.preemption.preemption_time_interval_case.
Goal True. idtac "END|prosa.analysis.facts.model.preemption.preemption_time_interval_case". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.preemption.idle_time_is_pt". Abort.
Check @prosa.analysis.facts.model.preemption.idle_time_is_pt.
Goal True. idtac "END|prosa.analysis.facts.model.preemption.idle_time_is_pt". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.preemption.zero_is_pt". Abort.
Check @prosa.analysis.facts.model.preemption.zero_is_pt.
Goal True. idtac "END|prosa.analysis.facts.model.preemption.zero_is_pt". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.preemption.first_moment_is_pt". Abort.
Check @prosa.analysis.facts.model.preemption.first_moment_is_pt.
Goal True. idtac "END|prosa.analysis.facts.model.preemption.first_moment_is_pt". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.preemption.neg_pt_scheduled_at". Abort.
Check @prosa.analysis.facts.model.preemption.neg_pt_scheduled_at.
Goal True. idtac "END|prosa.analysis.facts.model.preemption.neg_pt_scheduled_at". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.preemption.neg_pt_scheduled_before". Abort.
Check @prosa.analysis.facts.model.preemption.neg_pt_scheduled_before.
Goal True. idtac "END|prosa.analysis.facts.model.preemption.neg_pt_scheduled_before". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.preemption.neg_pt_scheduled_continuously_before". Abort.
Check @prosa.analysis.facts.model.preemption.neg_pt_scheduled_continuously_before.
Goal True. idtac "END|prosa.analysis.facts.model.preemption.neg_pt_scheduled_continuously_before". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.preemption.neg_pt_scheduled_continuously_after". Abort.
Check @prosa.analysis.facts.model.preemption.neg_pt_scheduled_continuously_after.
Goal True. idtac "END|prosa.analysis.facts.model.preemption.neg_pt_scheduled_continuously_after". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.preemption.neg_pt_scheduled_continuous". Abort.
Check @prosa.analysis.facts.model.preemption.neg_pt_scheduled_continuous.
Goal True. idtac "END|prosa.analysis.facts.model.preemption.neg_pt_scheduled_continuous". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.preemption.neq_scheduled_at_pt". Abort.
Check @prosa.analysis.facts.model.preemption.neq_scheduled_at_pt.
Goal True. idtac "END|prosa.analysis.facts.model.preemption.neq_scheduled_at_pt". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.preemption.neq_scheduled_at_pt_continuous_sched". Abort.
Check @prosa.analysis.facts.model.preemption.neq_scheduled_at_pt_continuous_sched.
Goal True. idtac "END|prosa.analysis.facts.model.preemption.neq_scheduled_at_pt_continuous_sched". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.preemption.scheduling_of_any_segment_starts_with_preemption_time". Abort.
Check @prosa.analysis.facts.model.preemption.scheduling_of_any_segment_starts_with_preemption_time.
Goal True. idtac "END|prosa.analysis.facts.model.preemption.scheduling_of_any_segment_starts_with_preemption_time". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.preemption.scheduling_of_any_segment_starts_with_preemption_time_continuously_sched". Abort.
Check @prosa.analysis.facts.model.preemption.scheduling_of_any_segment_starts_with_preemption_time_continuously_sched.
Goal True. idtac "END|prosa.analysis.facts.model.preemption.scheduling_of_any_segment_starts_with_preemption_time_continuously_sched". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.preemption.priority_higher_than_pending_job_priority". Abort.
Check @prosa.analysis.facts.model.preemption.priority_higher_than_pending_job_priority.
Goal True. idtac "END|prosa.analysis.facts.model.preemption.priority_higher_than_pending_job_priority". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.rbf.task_workload_between_bounded". Abort.
Check @prosa.analysis.facts.model.rbf.task_workload_between_bounded.
Goal True. idtac "END|prosa.analysis.facts.model.rbf.task_workload_between_bounded". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.rbf.rbf_spec". Abort.
Check @prosa.analysis.facts.model.rbf.rbf_spec.
Goal True. idtac "END|prosa.analysis.facts.model.rbf.rbf_spec". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.rbf.rbf_spec'". Abort.
Check @prosa.analysis.facts.model.rbf.rbf_spec'.
Goal True. idtac "END|prosa.analysis.facts.model.rbf.rbf_spec'". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.rbf.total_workload_le_total_rbf". Abort.
Check @prosa.analysis.facts.model.rbf.total_workload_le_total_rbf.
Goal True. idtac "END|prosa.analysis.facts.model.rbf.total_workload_le_total_rbf". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.rbf.workload_of_jobs_bounded". Abort.
Check @prosa.analysis.facts.model.rbf.workload_of_jobs_bounded.
Goal True. idtac "END|prosa.analysis.facts.model.rbf.workload_of_jobs_bounded". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.rbf.athep_workload_le_total_ohep_rbf". Abort.
Check @prosa.analysis.facts.model.rbf.athep_workload_le_total_ohep_rbf.
Goal True. idtac "END|prosa.analysis.facts.model.rbf.athep_workload_le_total_ohep_rbf". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.rbf.hep_workload_le_total_hep_rbf". Abort.
Check @prosa.analysis.facts.model.rbf.hep_workload_le_total_hep_rbf.
Goal True. idtac "END|prosa.analysis.facts.model.rbf.hep_workload_le_total_hep_rbf". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.rbf.hep_workload_le_total_rbf". Abort.
Check @prosa.analysis.facts.model.rbf.hep_workload_le_total_rbf.
Goal True. idtac "END|prosa.analysis.facts.model.rbf.hep_workload_le_total_rbf". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.rbf.task_rbf_0_zero". Abort.
Check @prosa.analysis.facts.model.rbf.task_rbf_0_zero.
Goal True. idtac "END|prosa.analysis.facts.model.rbf.task_rbf_0_zero". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.rbf.task_rbf_monotone". Abort.
Check @prosa.analysis.facts.model.rbf.task_rbf_monotone.
Goal True. idtac "END|prosa.analysis.facts.model.rbf.task_rbf_monotone". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.rbf.task_rbf_1_ge_task_cost". Abort.
Check @prosa.analysis.facts.model.rbf.task_rbf_1_ge_task_cost.
Goal True. idtac "END|prosa.analysis.facts.model.rbf.task_rbf_1_ge_task_cost". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.rbf.task_rbf_ge_task_cost". Abort.
Check @prosa.analysis.facts.model.rbf.task_rbf_ge_task_cost.
Goal True. idtac "END|prosa.analysis.facts.model.rbf.task_rbf_ge_task_cost". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.rbf.task_rbf_epsilon_gt_0". Abort.
Check @prosa.analysis.facts.model.rbf.task_rbf_epsilon_gt_0.
Goal True. idtac "END|prosa.analysis.facts.model.rbf.task_rbf_epsilon_gt_0". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.rbf.task_cost_le_sum_rbf". Abort.
Check @prosa.analysis.facts.model.rbf.task_cost_le_sum_rbf.
Goal True. idtac "END|prosa.analysis.facts.model.rbf.task_cost_le_sum_rbf". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.rbf.total_rbf_monotone". Abort.
Check @prosa.analysis.facts.model.rbf.total_rbf_monotone.
Goal True. idtac "END|prosa.analysis.facts.model.rbf.total_rbf_monotone". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.rbf.total_hep_rbf_monotone". Abort.
Check @prosa.analysis.facts.model.rbf.total_hep_rbf_monotone.
Goal True. idtac "END|prosa.analysis.facts.model.rbf.total_hep_rbf_monotone". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.rbf.total_ohep_rbf_monotone". Abort.
Check @prosa.analysis.facts.model.rbf.total_ohep_rbf_monotone.
Goal True. idtac "END|prosa.analysis.facts.model.rbf.total_ohep_rbf_monotone". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.rbf.pathological_rbf_response_time_bound". Abort.
Check @prosa.analysis.facts.model.rbf.pathological_rbf_response_time_bound.
Goal True. idtac "END|prosa.analysis.facts.model.rbf.pathological_rbf_response_time_bound". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.rbf.pathological_total_hep_rbf_response_time_bound". Abort.
Check @prosa.analysis.facts.model.rbf.pathological_total_hep_rbf_response_time_bound.
Goal True. idtac "END|prosa.analysis.facts.model.rbf.pathological_total_hep_rbf_response_time_bound". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.rbf.pathological_total_hep_rbf_any_bound". Abort.
Check @prosa.analysis.facts.model.rbf.pathological_total_hep_rbf_any_bound.
Goal True. idtac "END|prosa.analysis.facts.model.rbf.pathological_total_hep_rbf_any_bound". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.rbf.hep_rbf_taskwise_partitioning". Abort.
Check @prosa.analysis.facts.model.rbf.hep_rbf_taskwise_partitioning.
Goal True. idtac "END|prosa.analysis.facts.model.rbf.hep_rbf_taskwise_partitioning". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.rbf.split_hep_rbf". Abort.
Check @prosa.analysis.facts.model.rbf.split_hep_rbf.
Goal True. idtac "END|prosa.analysis.facts.model.rbf.split_hep_rbf". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.rbf.split_hep_rbf_weaken". Abort.
Check @prosa.analysis.facts.model.rbf.split_hep_rbf_weaken.
Goal True. idtac "END|prosa.analysis.facts.model.rbf.split_hep_rbf_weaken". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.rbf.total_ohep_rbf0". Abort.
Check @prosa.analysis.facts.model.rbf.total_ohep_rbf0.
Goal True. idtac "END|prosa.analysis.facts.model.rbf.total_ohep_rbf0". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.rbf.ohep_workload_le_rbf". Abort.
Check @prosa.analysis.facts.model.rbf.ohep_workload_le_rbf.
Goal True. idtac "END|prosa.analysis.facts.model.rbf.ohep_workload_le_rbf". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.rbf.task_rbf_without_job_under_analysis_from_arrival". Abort.
Check @prosa.analysis.facts.model.rbf.task_rbf_without_job_under_analysis_from_arrival.
Goal True. idtac "END|prosa.analysis.facts.model.rbf.task_rbf_without_job_under_analysis_from_arrival". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.rbf.task_rbf_without_job_under_analysis". Abort.
Check @prosa.analysis.facts.model.rbf.task_rbf_without_job_under_analysis.
Goal True. idtac "END|prosa.analysis.facts.model.rbf.task_rbf_without_job_under_analysis". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.restricted_supply.schedule.rs_proc_model_is_a_uniprocessor_model". Abort.
Check @prosa.analysis.facts.model.restricted_supply.schedule.rs_proc_model_is_a_uniprocessor_model.
Goal True. idtac "END|prosa.analysis.facts.model.restricted_supply.schedule.rs_proc_model_is_a_uniprocessor_model". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.restricted_supply.schedule.rs_proc_is_unit_supply". Abort.
Check @prosa.analysis.facts.model.restricted_supply.schedule.rs_proc_is_unit_supply.
Goal True. idtac "END|prosa.analysis.facts.model.restricted_supply.schedule.rs_proc_is_unit_supply". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.restricted_supply.schedule.rs_proc_model_fully_consuming". Abort.
Check @prosa.analysis.facts.model.restricted_supply.schedule.rs_proc_model_fully_consuming.
Goal True. idtac "END|prosa.analysis.facts.model.restricted_supply.schedule.rs_proc_model_fully_consuming". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.sbf.average.arm_sbf_monotone". Abort.
Check @prosa.analysis.facts.model.sbf.average.arm_sbf_monotone.
Goal True. idtac "END|prosa.analysis.facts.model.sbf.average.arm_sbf_monotone". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.sbf.average.arm_sbf_unit". Abort.
Check @prosa.analysis.facts.model.sbf.average.arm_sbf_unit.
Goal True. idtac "END|prosa.analysis.facts.model.sbf.average.arm_sbf_unit". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.sbf.average.arm_sbf_valid". Abort.
Check @prosa.analysis.facts.model.sbf.average.arm_sbf_valid.
Goal True. idtac "END|prosa.analysis.facts.model.sbf.average.arm_sbf_valid". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.sbf.periodic.prm_sbf_monotone". Abort.
Check @prosa.analysis.facts.model.sbf.periodic.prm_sbf_monotone.
Goal True. idtac "END|prosa.analysis.facts.model.sbf.periodic.prm_sbf_monotone". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.sbf.periodic.prm_sbf_unit". Abort.
Check @prosa.analysis.facts.model.sbf.periodic.prm_sbf_unit.
Goal True. idtac "END|prosa.analysis.facts.model.sbf.periodic.prm_sbf_unit". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.sbf.periodic.prm_sbf_valid_aux_1". Abort.
Check @prosa.analysis.facts.model.sbf.periodic.prm_sbf_valid_aux_1.
Goal True. idtac "END|prosa.analysis.facts.model.sbf.periodic.prm_sbf_valid_aux_1". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.sbf.periodic.prm_sbf_valid_aux_21". Abort.
Check @prosa.analysis.facts.model.sbf.periodic.prm_sbf_valid_aux_21.
Goal True. idtac "END|prosa.analysis.facts.model.sbf.periodic.prm_sbf_valid_aux_21". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.sbf.periodic.prm_sbf_valid_aux_22". Abort.
Check @prosa.analysis.facts.model.sbf.periodic.prm_sbf_valid_aux_22.
Goal True. idtac "END|prosa.analysis.facts.model.sbf.periodic.prm_sbf_valid_aux_22". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.sbf.periodic.prm_sbf_valid_aux_23". Abort.
Check @prosa.analysis.facts.model.sbf.periodic.prm_sbf_valid_aux_23.
Goal True. idtac "END|prosa.analysis.facts.model.sbf.periodic.prm_sbf_valid_aux_23". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.sbf.periodic.prm_sbf_valid_aux_24". Abort.
Check @prosa.analysis.facts.model.sbf.periodic.prm_sbf_valid_aux_24.
Goal True. idtac "END|prosa.analysis.facts.model.sbf.periodic.prm_sbf_valid_aux_24". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.sbf.periodic.prm_sbf_valid_aux_2". Abort.
Check @prosa.analysis.facts.model.sbf.periodic.prm_sbf_valid_aux_2.
Goal True. idtac "END|prosa.analysis.facts.model.sbf.periodic.prm_sbf_valid_aux_2". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.sbf.periodic.prm_sbf_valid". Abort.
Check @prosa.analysis.facts.model.sbf.periodic.prm_sbf_valid.
Goal True. idtac "END|prosa.analysis.facts.model.sbf.periodic.prm_sbf_valid". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.scheduled.scheduled_jobs_at_iff". Abort.
Check @prosa.analysis.facts.model.scheduled.scheduled_jobs_at_iff.
Goal True. idtac "END|prosa.analysis.facts.model.scheduled.scheduled_jobs_at_iff". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.scheduled.scheduled_jobs_at_nil". Abort.
Check @prosa.analysis.facts.model.scheduled.scheduled_jobs_at_nil.
Goal True. idtac "END|prosa.analysis.facts.model.scheduled.scheduled_jobs_at_nil". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.scheduled.not_scheduled_when_idle". Abort.
Check @prosa.analysis.facts.model.scheduled.not_scheduled_when_idle.
Goal True. idtac "END|prosa.analysis.facts.model.scheduled.not_scheduled_when_idle". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.scheduled.scheduled_at_implies_in_served_at". Abort.
Check @prosa.analysis.facts.model.scheduled.scheduled_at_implies_in_served_at.
Goal True. idtac "END|prosa.analysis.facts.model.scheduled.scheduled_at_implies_in_served_at". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.scheduled.scheduled_jobs_at_seq1". Abort.
Check @prosa.analysis.facts.model.scheduled.scheduled_jobs_at_seq1.
Goal True. idtac "END|prosa.analysis.facts.model.scheduled.scheduled_jobs_at_seq1". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.scheduled.scheduled_jobs_at_uni_cases". Abort.
Check @prosa.analysis.facts.model.scheduled.scheduled_jobs_at_uni_cases.
Goal True. idtac "END|prosa.analysis.facts.model.scheduled.scheduled_jobs_at_uni_cases". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.scheduled.scheduled_jobs_at_uni". Abort.
Check @prosa.analysis.facts.model.scheduled.scheduled_jobs_at_uni.
Goal True. idtac "END|prosa.analysis.facts.model.scheduled.scheduled_jobs_at_uni". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.scheduled.scheduled_job_at_scheduled_at". Abort.
Check @prosa.analysis.facts.model.scheduled.scheduled_job_at_scheduled_at.
Goal True. idtac "END|prosa.analysis.facts.model.scheduled.scheduled_job_at_scheduled_at". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.scheduled.scheduled_jobs_at_scheduled_at". Abort.
Check @prosa.analysis.facts.model.scheduled.scheduled_jobs_at_scheduled_at.
Goal True. idtac "END|prosa.analysis.facts.model.scheduled.scheduled_jobs_at_scheduled_at". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.scheduled.scheduled_job_at_none". Abort.
Check @prosa.analysis.facts.model.scheduled.scheduled_job_at_none.
Goal True. idtac "END|prosa.analysis.facts.model.scheduled.scheduled_job_at_none". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.scheduled.is_idle_iff". Abort.
Check @prosa.analysis.facts.model.scheduled.is_idle_iff.
Goal True. idtac "END|prosa.analysis.facts.model.scheduled.is_idle_iff". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.scheduled.is_nonidle_iff". Abort.
Check @prosa.analysis.facts.model.scheduled.is_nonidle_iff.
Goal True. idtac "END|prosa.analysis.facts.model.scheduled.is_nonidle_iff". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.scheduled.scheduled_at_dec". Abort.
Check @prosa.analysis.facts.model.scheduled.scheduled_at_dec.
Goal True. idtac "END|prosa.analysis.facts.model.scheduled.scheduled_at_dec". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.scheduled.scheduled_at_cases". Abort.
Check @prosa.analysis.facts.model.scheduled.scheduled_at_cases.
Goal True. idtac "END|prosa.analysis.facts.model.scheduled.scheduled_at_cases". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.sequential.scheduler_executes_job_with_earliest_arrival". Abort.
Check @prosa.analysis.facts.model.sequential.scheduler_executes_job_with_earliest_arrival.
Goal True. idtac "END|prosa.analysis.facts.model.sequential.scheduler_executes_job_with_earliest_arrival". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.sequential.sequential_tasks_different_tasks". Abort.
Check @prosa.analysis.facts.model.sequential.sequential_tasks_different_tasks.
Goal True. idtac "END|prosa.analysis.facts.model.sequential.sequential_tasks_different_tasks". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.sequential.sequential_tasks_from_readiness". Abort.
Check @prosa.analysis.facts.model.sequential.sequential_tasks_from_readiness.
Goal True. idtac "END|prosa.analysis.facts.model.sequential.sequential_tasks_from_readiness". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.service_of_jobs.service_of_jobs_cat_scheduling_interval". Abort.
Check @prosa.analysis.facts.model.service_of_jobs.service_of_jobs_cat_scheduling_interval.
Goal True. idtac "END|prosa.analysis.facts.model.service_of_jobs.service_of_jobs_cat_scheduling_interval". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.service_of_jobs.service_of_jobs_cat_arrival_interval". Abort.
Check @prosa.analysis.facts.model.service_of_jobs.service_of_jobs_cat_arrival_interval.
Goal True. idtac "END|prosa.analysis.facts.model.service_of_jobs.service_of_jobs_cat_arrival_interval". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.service_of_jobs.service_of_jobs_case_on_pred". Abort.
Check @prosa.analysis.facts.model.service_of_jobs.service_of_jobs_case_on_pred.
Goal True. idtac "END|prosa.analysis.facts.model.service_of_jobs.service_of_jobs_case_on_pred". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.service_of_jobs.service_of_jobs_negate_pred". Abort.
Check @prosa.analysis.facts.model.service_of_jobs.service_of_jobs_negate_pred.
Goal True. idtac "END|prosa.analysis.facts.model.service_of_jobs.service_of_jobs_negate_pred". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.service_of_jobs.service_of_jobs_pred_impl". Abort.
Check @prosa.analysis.facts.model.service_of_jobs.service_of_jobs_pred_impl.
Goal True. idtac "END|prosa.analysis.facts.model.service_of_jobs.service_of_jobs_pred_impl". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.service_of_jobs.service_of_jobs_equiv_pred". Abort.
Check @prosa.analysis.facts.model.service_of_jobs.service_of_jobs_equiv_pred.
Goal True. idtac "END|prosa.analysis.facts.model.service_of_jobs.service_of_jobs_equiv_pred". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.service_of_jobs.service_of_jobs_sum_over_time_interval". Abort.
Check @prosa.analysis.facts.model.service_of_jobs.service_of_jobs_sum_over_time_interval.
Goal True. idtac "END|prosa.analysis.facts.model.service_of_jobs.service_of_jobs_sum_over_time_interval". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.service_of_jobs.service_of_jobs_pred0". Abort.
Check @prosa.analysis.facts.model.service_of_jobs.service_of_jobs_pred0.
Goal True. idtac "END|prosa.analysis.facts.model.service_of_jobs.service_of_jobs_pred0". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.service_of_jobs.service_of_jobs_nsched_or_unsat". Abort.
Check @prosa.analysis.facts.model.service_of_jobs.service_of_jobs_nsched_or_unsat.
Goal True. idtac "END|prosa.analysis.facts.model.service_of_jobs.service_of_jobs_nsched_or_unsat". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.service_of_jobs.service_of_jobs_geq". Abort.
Check @prosa.analysis.facts.model.service_of_jobs.service_of_jobs_geq.
Goal True. idtac "END|prosa.analysis.facts.model.service_of_jobs.service_of_jobs_geq". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.service_of_jobs.service_of_jobs_cat_last". Abort.
Check @prosa.analysis.facts.model.service_of_jobs.service_of_jobs_cat_last.
Goal True. idtac "END|prosa.analysis.facts.model.service_of_jobs.service_of_jobs_cat_last". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.service_of_jobs.service_plus_ahep_eq_service_hep". Abort.
Check @prosa.analysis.facts.model.service_of_jobs.service_plus_ahep_eq_service_hep.
Goal True. idtac "END|prosa.analysis.facts.model.service_of_jobs.service_plus_ahep_eq_service_hep". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.service_of_jobs.service_of_jobs_le_workload". Abort.
Check @prosa.analysis.facts.model.service_of_jobs.service_of_jobs_le_workload.
Goal True. idtac "END|prosa.analysis.facts.model.service_of_jobs.service_of_jobs_le_workload". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.service_of_jobs.workload_eq_service_impl_all_jobs_have_completed". Abort.
Check @prosa.analysis.facts.model.service_of_jobs.workload_eq_service_impl_all_jobs_have_completed.
Goal True. idtac "END|prosa.analysis.facts.model.service_of_jobs.workload_eq_service_impl_all_jobs_have_completed". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.service_of_jobs.all_jobs_have_completed_impl_workload_eq_service". Abort.
Check @prosa.analysis.facts.model.service_of_jobs.all_jobs_have_completed_impl_workload_eq_service.
Goal True. idtac "END|prosa.analysis.facts.model.service_of_jobs.all_jobs_have_completed_impl_workload_eq_service". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.service_of_jobs.all_jobs_have_completed_equiv_workload_eq_service". Abort.
Check @prosa.analysis.facts.model.service_of_jobs.all_jobs_have_completed_equiv_workload_eq_service.
Goal True. idtac "END|prosa.analysis.facts.model.service_of_jobs.all_jobs_have_completed_equiv_workload_eq_service". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.service_of_jobs.service_of_jobs_le_1". Abort.
Check @prosa.analysis.facts.model.service_of_jobs.service_of_jobs_le_1.
Goal True. idtac "END|prosa.analysis.facts.model.service_of_jobs.service_of_jobs_le_1". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.service_of_jobs.service_of_jobs_le_length_of_interval". Abort.
Check @prosa.analysis.facts.model.service_of_jobs.service_of_jobs_le_length_of_interval.
Goal True. idtac "END|prosa.analysis.facts.model.service_of_jobs.service_of_jobs_le_length_of_interval". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.service_of_jobs.service_of_jobs_le_length_of_interval'". Abort.
Check @prosa.analysis.facts.model.service_of_jobs.service_of_jobs_le_length_of_interval'.
Goal True. idtac "END|prosa.analysis.facts.model.service_of_jobs.service_of_jobs_le_length_of_interval'". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.service_of_jobs.service_of_jobs_at_scheduled1". Abort.
Check @prosa.analysis.facts.model.service_of_jobs.service_of_jobs_at_scheduled1.
Goal True. idtac "END|prosa.analysis.facts.model.service_of_jobs.service_of_jobs_at_scheduled1". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.service_of_jobs.service_of_jobs_always_scheduled". Abort.
Check @prosa.analysis.facts.model.service_of_jobs.service_of_jobs_always_scheduled.
Goal True. idtac "END|prosa.analysis.facts.model.service_of_jobs.service_of_jobs_always_scheduled". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.service_of_jobs.cumulative_pred_served_eq_service". Abort.
Check @prosa.analysis.facts.model.service_of_jobs.cumulative_pred_served_eq_service.
Goal True. idtac "END|prosa.analysis.facts.model.service_of_jobs.cumulative_pred_served_eq_service". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.task_arrivals.num_arrivals_of_task_cat". Abort.
Check @prosa.analysis.facts.model.task_arrivals.num_arrivals_of_task_cat.
Goal True. idtac "END|prosa.analysis.facts.model.task_arrivals.num_arrivals_of_task_cat". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.task_arrivals.task_arrivals_between_cat". Abort.
Check @prosa.analysis.facts.model.task_arrivals.task_arrivals_between_cat.
Goal True. idtac "END|prosa.analysis.facts.model.task_arrivals.task_arrivals_between_cat". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.task_arrivals.task_arrivals_up_to_prefix_cat". Abort.
Check @prosa.analysis.facts.model.task_arrivals.task_arrivals_up_to_prefix_cat.
Goal True. idtac "END|prosa.analysis.facts.model.task_arrivals.task_arrivals_up_to_prefix_cat". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.task_arrivals.arrives_in_task_arrivals_up_to". Abort.
Check @prosa.analysis.facts.model.task_arrivals.arrives_in_task_arrivals_up_to.
Goal True. idtac "END|prosa.analysis.facts.model.task_arrivals.arrives_in_task_arrivals_up_to". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.task_arrivals.arrives_in_task_arrivals_at". Abort.
Check @prosa.analysis.facts.model.task_arrivals.arrives_in_task_arrivals_at.
Goal True. idtac "END|prosa.analysis.facts.model.task_arrivals.arrives_in_task_arrivals_at". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.task_arrivals.task_arrivals_cat". Abort.
Check @prosa.analysis.facts.model.task_arrivals.task_arrivals_cat.
Goal True. idtac "END|prosa.analysis.facts.model.task_arrivals.task_arrivals_cat". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.task_arrivals.task_arrivals_up_to_cat". Abort.
Check @prosa.analysis.facts.model.task_arrivals.task_arrivals_up_to_cat.
Goal True. idtac "END|prosa.analysis.facts.model.task_arrivals.task_arrivals_up_to_cat". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.task_arrivals.job_in_task_arrivals_between". Abort.
Check @prosa.analysis.facts.model.task_arrivals.job_in_task_arrivals_between.
Goal True. idtac "END|prosa.analysis.facts.model.task_arrivals.job_in_task_arrivals_between". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.task_arrivals.task_arrivals_between_subset". Abort.
Check @prosa.analysis.facts.model.task_arrivals.task_arrivals_between_subset.
Goal True. idtac "END|prosa.analysis.facts.model.task_arrivals.task_arrivals_between_subset". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.task_arrivals.arrives_in_task_arrivals_implies_arrived". Abort.
Check @prosa.analysis.facts.model.task_arrivals.arrives_in_task_arrivals_implies_arrived.
Goal True. idtac "END|prosa.analysis.facts.model.task_arrivals.arrives_in_task_arrivals_implies_arrived". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.task_arrivals.arrives_in_task_arrivals_before_implies_arrives_before". Abort.
Check @prosa.analysis.facts.model.task_arrivals.arrives_in_task_arrivals_before_implies_arrives_before.
Goal True. idtac "END|prosa.analysis.facts.model.task_arrivals.arrives_in_task_arrivals_before_implies_arrives_before". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.task_arrivals.arrives_in_task_arrivals_implies_job_task". Abort.
Check @prosa.analysis.facts.model.task_arrivals.arrives_in_task_arrivals_implies_job_task.
Goal True. idtac "END|prosa.analysis.facts.model.task_arrivals.arrives_in_task_arrivals_implies_job_task". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.task_arrivals.in_task_arrivals_between_implies_job_of_task". Abort.
Check @prosa.analysis.facts.model.task_arrivals.in_task_arrivals_between_implies_job_of_task.
Goal True. idtac "END|prosa.analysis.facts.model.task_arrivals.in_task_arrivals_between_implies_job_of_task". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.task_arrivals.task_arrivals_nonempty". Abort.
Check @prosa.analysis.facts.model.task_arrivals.task_arrivals_nonempty.
Goal True. idtac "END|prosa.analysis.facts.model.task_arrivals.task_arrivals_nonempty". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.task_arrivals.number_of_task_arrivals_nonzero". Abort.
Check @prosa.analysis.facts.model.task_arrivals.number_of_task_arrivals_nonzero.
Goal True. idtac "END|prosa.analysis.facts.model.task_arrivals.number_of_task_arrivals_nonzero". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.task_arrivals.uniq_task_arrivals". Abort.
Check @prosa.analysis.facts.model.task_arrivals.uniq_task_arrivals.
Goal True. idtac "END|prosa.analysis.facts.model.task_arrivals.uniq_task_arrivals". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.task_arrivals.task_arrivals_between_uniq". Abort.
Check @prosa.analysis.facts.model.task_arrivals.task_arrivals_between_uniq.
Goal True. idtac "END|prosa.analysis.facts.model.task_arrivals.task_arrivals_between_uniq". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.task_arrivals.job_notin_task_arrivals_before". Abort.
Check @prosa.analysis.facts.model.task_arrivals.job_notin_task_arrivals_before.
Goal True. idtac "END|prosa.analysis.facts.model.task_arrivals.job_notin_task_arrivals_before". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.task_arrivals.arrival_lt_implies_strict_prefix". Abort.
Check @prosa.analysis.facts.model.task_arrivals.arrival_lt_implies_strict_prefix.
Goal True. idtac "END|prosa.analysis.facts.model.task_arrivals.arrival_lt_implies_strict_prefix". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.task_arrivals.nth_job_of_task_arrivals". Abort.
Check @prosa.analysis.facts.model.task_arrivals.nth_job_of_task_arrivals.
Goal True. idtac "END|prosa.analysis.facts.model.task_arrivals.nth_job_of_task_arrivals". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.task_arrivals.task_arrivals_between_is_cat_of_task_arrivals_at". Abort.
Check @prosa.analysis.facts.model.task_arrivals.task_arrivals_between_is_cat_of_task_arrivals_at.
Goal True. idtac "END|prosa.analysis.facts.model.task_arrivals.task_arrivals_between_is_cat_of_task_arrivals_at". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.task_arrivals.size_of_task_arrivals_between". Abort.
Check @prosa.analysis.facts.model.task_arrivals.size_of_task_arrivals_between.
Goal True. idtac "END|prosa.analysis.facts.model.task_arrivals.size_of_task_arrivals_between". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.task_arrivals.task_arrivals_between_sorted". Abort.
Check @prosa.analysis.facts.model.task_arrivals.task_arrivals_between_sorted.
Goal True. idtac "END|prosa.analysis.facts.model.task_arrivals.task_arrivals_between_sorted". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.task_cost.job_cost_positive_implies_task_cost_positive". Abort.
Check @prosa.analysis.facts.model.task_cost.job_cost_positive_implies_task_cost_positive.
Goal True. idtac "END|prosa.analysis.facts.model.task_cost.job_cost_positive_implies_task_cost_positive". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.task_cost.sum_job_costs_bounded". Abort.
Check @prosa.analysis.facts.model.task_cost.sum_job_costs_bounded.
Goal True. idtac "END|prosa.analysis.facts.model.task_cost.sum_job_costs_bounded". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.task_schedule.task_served_task_scheduled". Abort.
Check @prosa.analysis.facts.model.task_schedule.task_served_task_scheduled.
Goal True. idtac "END|prosa.analysis.facts.model.task_schedule.task_served_task_scheduled". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.task_schedule.task_served_eq_task_scheduled". Abort.
Check @prosa.analysis.facts.model.task_schedule.task_served_eq_task_scheduled.
Goal True. idtac "END|prosa.analysis.facts.model.task_schedule.task_served_eq_task_scheduled". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.task_schedule.no_task_scheduled_when_idle". Abort.
Check @prosa.analysis.facts.model.task_schedule.no_task_scheduled_when_idle.
Goal True. idtac "END|prosa.analysis.facts.model.task_schedule.no_task_scheduled_when_idle". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.task_schedule.no_task_served_when_idle". Abort.
Check @prosa.analysis.facts.model.task_schedule.no_task_served_when_idle.
Goal True. idtac "END|prosa.analysis.facts.model.task_schedule.no_task_served_when_idle". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.task_schedule.job_of_scheduled_task". Abort.
Check @prosa.analysis.facts.model.task_schedule.job_of_scheduled_task.
Goal True. idtac "END|prosa.analysis.facts.model.task_schedule.job_of_scheduled_task". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.task_schedule.job_of_task_scheduled". Abort.
Check @prosa.analysis.facts.model.task_schedule.job_of_task_scheduled.
Goal True. idtac "END|prosa.analysis.facts.model.task_schedule.job_of_task_scheduled". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.task_schedule.job_of_other_task_scheduled". Abort.
Check @prosa.analysis.facts.model.task_schedule.job_of_other_task_scheduled.
Goal True. idtac "END|prosa.analysis.facts.model.task_schedule.job_of_other_task_scheduled". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.task_schedule.job_of_other_task_scheduled'". Abort.
Check @prosa.analysis.facts.model.task_schedule.job_of_other_task_scheduled'.
Goal True. idtac "END|prosa.analysis.facts.model.task_schedule.job_of_other_task_scheduled'". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.task_schedule.job_of_task_not_served". Abort.
Check @prosa.analysis.facts.model.task_schedule.job_of_task_not_served.
Goal True. idtac "END|prosa.analysis.facts.model.task_schedule.job_of_task_not_served". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.task_schedule.task_served_at_eq_job_of_task". Abort.
Check @prosa.analysis.facts.model.task_schedule.task_served_at_eq_job_of_task.
Goal True. idtac "END|prosa.analysis.facts.model.task_schedule.task_served_at_eq_job_of_task". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.uniprocessor.scheduled_job_at_neq". Abort.
Check @prosa.analysis.facts.model.uniprocessor.scheduled_job_at_neq.
Goal True. idtac "END|prosa.analysis.facts.model.uniprocessor.scheduled_job_at_neq". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.workload.workload_of_jobs_filter". Abort.
Check @prosa.analysis.facts.model.workload.workload_of_jobs_filter.
Goal True. idtac "END|prosa.analysis.facts.model.workload.workload_of_jobs_filter". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.workload.workload_of_jobs_weaken". Abort.
Check @prosa.analysis.facts.model.workload.workload_of_jobs_weaken.
Goal True. idtac "END|prosa.analysis.facts.model.workload.workload_of_jobs_weaken". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.workload.workload_of_jobs0". Abort.
Check @prosa.analysis.facts.model.workload.workload_of_jobs0.
Goal True. idtac "END|prosa.analysis.facts.model.workload.workload_of_jobs0". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.workload.workload_of_jobs_le_sum_over_partitions". Abort.
Check @prosa.analysis.facts.model.workload.workload_of_jobs_le_sum_over_partitions.
Goal True. idtac "END|prosa.analysis.facts.model.workload.workload_of_jobs_le_sum_over_partitions". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.workload.workload_of_jobs_partitioned_by_tasks". Abort.
Check @prosa.analysis.facts.model.workload.workload_of_jobs_partitioned_by_tasks.
Goal True. idtac "END|prosa.analysis.facts.model.workload.workload_of_jobs_partitioned_by_tasks". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.workload.workload_of_other_jobs_split". Abort.
Check @prosa.analysis.facts.model.workload.workload_of_other_jobs_split.
Goal True. idtac "END|prosa.analysis.facts.model.workload.workload_of_other_jobs_split". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.workload.workload_of_jobs_pred0". Abort.
Check @prosa.analysis.facts.model.workload.workload_of_jobs_pred0.
Goal True. idtac "END|prosa.analysis.facts.model.workload.workload_of_jobs_pred0". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.workload.workload_of_jobs_case_on_pred". Abort.
Check @prosa.analysis.facts.model.workload.workload_of_jobs_case_on_pred.
Goal True. idtac "END|prosa.analysis.facts.model.workload.workload_of_jobs_case_on_pred". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.workload.workload_of_jobs_equiv_pred". Abort.
Check @prosa.analysis.facts.model.workload.workload_of_jobs_equiv_pred.
Goal True. idtac "END|prosa.analysis.facts.model.workload.workload_of_jobs_equiv_pred". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.workload.workload_of_job_eq_job_arrival". Abort.
Check @prosa.analysis.facts.model.workload.workload_of_job_eq_job_arrival.
Goal True. idtac "END|prosa.analysis.facts.model.workload.workload_of_job_eq_job_arrival". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.workload.workload_job_and_ahep_eq_workload_hep". Abort.
Check @prosa.analysis.facts.model.workload.workload_job_and_ahep_eq_workload_hep.
Goal True. idtac "END|prosa.analysis.facts.model.workload.workload_job_and_ahep_eq_workload_hep". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.workload.workload_of_jobs_nil_tail". Abort.
Check @prosa.analysis.facts.model.workload.workload_of_jobs_nil_tail.
Goal True. idtac "END|prosa.analysis.facts.model.workload.workload_of_jobs_nil_tail". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.workload.workload_of_jobs_cat". Abort.
Check @prosa.analysis.facts.model.workload.workload_of_jobs_cat.
Goal True. idtac "END|prosa.analysis.facts.model.workload.workload_of_jobs_cat". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.workload.workload_of_jobs_reduce_range". Abort.
Check @prosa.analysis.facts.model.workload.workload_of_jobs_reduce_range.
Goal True. idtac "END|prosa.analysis.facts.model.workload.workload_of_jobs_reduce_range". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.workload.workload_minus_job_cost'". Abort.
Check @prosa.analysis.facts.model.workload.workload_minus_job_cost'.
Goal True. idtac "END|prosa.analysis.facts.model.workload.workload_minus_job_cost'". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.workload.workload_minus_job_cost". Abort.
Check @prosa.analysis.facts.model.workload.workload_minus_job_cost.
Goal True. idtac "END|prosa.analysis.facts.model.workload.workload_minus_job_cost". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.workload.workload_equal_subset". Abort.
Check @prosa.analysis.facts.model.workload.workload_equal_subset.
Goal True. idtac "END|prosa.analysis.facts.model.workload.workload_equal_subset". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.periodic.arrival_separation.consecutive_job_separation". Abort.
Check @prosa.analysis.facts.periodic.arrival_separation.consecutive_job_separation.
Goal True. idtac "END|prosa.analysis.facts.periodic.arrival_separation.consecutive_job_separation". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.periodic.arrival_separation.job_arrival_separation_when_index_diff_is_k". Abort.
Check @prosa.analysis.facts.periodic.arrival_separation.job_arrival_separation_when_index_diff_is_k.
Goal True. idtac "END|prosa.analysis.facts.periodic.arrival_separation.job_arrival_separation_when_index_diff_is_k". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.periodic.arrival_separation.job_sep_periodic". Abort.
Check @prosa.analysis.facts.periodic.arrival_separation.job_sep_periodic.
Goal True. idtac "END|prosa.analysis.facts.periodic.arrival_separation.job_sep_periodic". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.periodic.arrival_times.periodic_arrival_times". Abort.
Check @prosa.analysis.facts.periodic.arrival_times.periodic_arrival_times.
Goal True. idtac "END|prosa.analysis.facts.periodic.arrival_times.periodic_arrival_times". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.periodic.arrival_times.job_arrival_times". Abort.
Check @prosa.analysis.facts.periodic.arrival_times.job_arrival_times.
Goal True. idtac "END|prosa.analysis.facts.periodic.arrival_times.job_arrival_times". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.periodic.arrival_times.job_arr_index". Abort.
Check @prosa.analysis.facts.periodic.arrival_times.job_arr_index.
Goal True. idtac "END|prosa.analysis.facts.periodic.arrival_times.job_arr_index". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.periodic.max_inter_arrival.max_inter_eq_period". Abort.
Check @prosa.analysis.facts.periodic.max_inter_arrival.max_inter_eq_period.
Goal True. idtac "END|prosa.analysis.facts.periodic.max_inter_arrival.max_inter_eq_period". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.periodic.max_inter_arrival.valid_period_is_valid_max_inter_arrival_time". Abort.
Check @prosa.analysis.facts.periodic.max_inter_arrival.valid_period_is_valid_max_inter_arrival_time.
Goal True. idtac "END|prosa.analysis.facts.periodic.max_inter_arrival.valid_period_is_valid_max_inter_arrival_time". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.periodic.max_inter_arrival.periodic_model_respects_max_inter_arrival_model". Abort.
Check @prosa.analysis.facts.periodic.max_inter_arrival.periodic_model_respects_max_inter_arrival_model.
Goal True. idtac "END|prosa.analysis.facts.periodic.max_inter_arrival.periodic_model_respects_max_inter_arrival_model". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.periodic.task_arrivals_size.task_arrivals_size_at_non_arrival". Abort.
Check @prosa.analysis.facts.periodic.task_arrivals_size.task_arrivals_size_at_non_arrival.
Goal True. idtac "END|prosa.analysis.facts.periodic.task_arrivals_size.task_arrivals_size_at_non_arrival". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.periodic.task_arrivals_size.task_arrivals_at_size_cases". Abort.
Check @prosa.analysis.facts.periodic.task_arrivals_size.task_arrivals_at_size_cases.
Goal True. idtac "END|prosa.analysis.facts.periodic.task_arrivals_size.task_arrivals_at_size_cases". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.periodic.task_arrivals_size.size_task_arrivals_between_eq0". Abort.
Check @prosa.analysis.facts.periodic.task_arrivals_size.size_task_arrivals_between_eq0.
Goal True. idtac "END|prosa.analysis.facts.periodic.task_arrivals_size.size_task_arrivals_between_eq0". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.periodic.task_arrivals_size.jobs_exists_later". Abort.
Check @prosa.analysis.facts.periodic.task_arrivals_size.jobs_exists_later.
Goal True. idtac "END|prosa.analysis.facts.periodic.task_arrivals_size.jobs_exists_later". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.periodic.task_arrivals_size.task_arrivals_at_size". Abort.
Check @prosa.analysis.facts.periodic.task_arrivals_size.task_arrivals_at_size.
Goal True. idtac "END|prosa.analysis.facts.periodic.task_arrivals_size.task_arrivals_at_size". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.periodic.task_arrivals_size.size_task_arrivals_up_to_offset". Abort.
Check @prosa.analysis.facts.periodic.task_arrivals_size.size_task_arrivals_up_to_offset.
Goal True. idtac "END|prosa.analysis.facts.periodic.task_arrivals_size.size_task_arrivals_up_to_offset". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.periodic.task_arrivals_size.task_arrivals_up_to_size". Abort.
Check @prosa.analysis.facts.periodic.task_arrivals_size.task_arrivals_up_to_size.
Goal True. idtac "END|prosa.analysis.facts.periodic.task_arrivals_size.task_arrivals_up_to_size". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.periodic.task_arrivals_size.eq_size_of_task_arrivals_seperated_by_period". Abort.
Check @prosa.analysis.facts.periodic.task_arrivals_size.eq_size_of_task_arrivals_seperated_by_period.
Goal True. idtac "END|prosa.analysis.facts.periodic.task_arrivals_size.eq_size_of_task_arrivals_seperated_by_period". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.preemption.job.limited.zero_in_preemption_points". Abort.
Check @prosa.analysis.facts.preemption.job.limited.zero_in_preemption_points.
Goal True. idtac "END|prosa.analysis.facts.preemption.job.limited.zero_in_preemption_points". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.preemption.job.limited.zero_is_first_element". Abort.
Check @prosa.analysis.facts.preemption.job.limited.zero_is_first_element.
Goal True. idtac "END|prosa.analysis.facts.preemption.job.limited.zero_is_first_element". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.preemption.job.limited.list_of_preemption_point_is_not_empty". Abort.
Check @prosa.analysis.facts.preemption.job.limited.list_of_preemption_point_is_not_empty.
Goal True. idtac "END|prosa.analysis.facts.preemption.job.limited.list_of_preemption_point_is_not_empty". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.preemption.job.limited.job_cost_in_nonpreemptive_points". Abort.
Check @prosa.analysis.facts.preemption.job.limited.job_cost_in_nonpreemptive_points.
Goal True. idtac "END|prosa.analysis.facts.preemption.job.limited.job_cost_in_nonpreemptive_points". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.preemption.job.limited.number_of_preemption_points_at_least_two". Abort.
Check @prosa.analysis.facts.preemption.job.limited.number_of_preemption_points_at_least_two.
Goal True. idtac "END|prosa.analysis.facts.preemption.job.limited.number_of_preemption_points_at_least_two". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.preemption.job.limited.antidensity_of_preemption_points". Abort.
Check @prosa.analysis.facts.preemption.job.limited.antidensity_of_preemption_points.
Goal True. idtac "END|prosa.analysis.facts.preemption.job.limited.antidensity_of_preemption_points". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.preemption.job.limited.work_belongs_to_some_nonpreemptive_segment". Abort.
Check @prosa.analysis.facts.preemption.job.limited.work_belongs_to_some_nonpreemptive_segment.
Goal True. idtac "END|prosa.analysis.facts.preemption.job.limited.work_belongs_to_some_nonpreemptive_segment". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.preemption.job.limited.job_parameters_last_np_to_job_limited". Abort.
Check @prosa.analysis.facts.preemption.job.limited.job_parameters_last_np_to_job_limited.
Goal True. idtac "END|prosa.analysis.facts.preemption.job.limited.job_parameters_last_np_to_job_limited". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.preemption.job.limited.job_parameters_max_np_to_job_limited". Abort.
Check @prosa.analysis.facts.preemption.job.limited.job_parameters_max_np_to_job_limited.
Goal True. idtac "END|prosa.analysis.facts.preemption.job.limited.job_parameters_max_np_to_job_limited". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.preemption.job.limited.valid_fixed_preemption_points_model_lemma". Abort.
Check @prosa.analysis.facts.preemption.job.limited.valid_fixed_preemption_points_model_lemma.
Goal True. idtac "END|prosa.analysis.facts.preemption.job.limited.valid_fixed_preemption_points_model_lemma". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.preemption.job.nonpreemptive.valid_fully_nonpreemptive_model". Abort.
Check @prosa.analysis.facts.preemption.job.nonpreemptive.valid_fully_nonpreemptive_model.
Goal True. idtac "END|prosa.analysis.facts.preemption.job.nonpreemptive.valid_fully_nonpreemptive_model". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.preemption.job.nonpreemptive.job_max_nps_is_job_cost". Abort.
Check @prosa.analysis.facts.preemption.job.nonpreemptive.job_max_nps_is_job_cost.
Goal True. idtac "END|prosa.analysis.facts.preemption.job.nonpreemptive.job_max_nps_is_job_cost". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.preemption.job.nonpreemptive.job_last_nps_is_job_cost". Abort.
Check @prosa.analysis.facts.preemption.job.nonpreemptive.job_last_nps_is_job_cost.
Goal True. idtac "END|prosa.analysis.facts.preemption.job.nonpreemptive.job_last_nps_is_job_cost". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.preemption.job.nonpreemptive.no_preemptions_equiv_nonpreemptive". Abort.
Check @prosa.analysis.facts.preemption.job.nonpreemptive.no_preemptions_equiv_nonpreemptive.
Goal True. idtac "END|prosa.analysis.facts.preemption.job.nonpreemptive.no_preemptions_equiv_nonpreemptive". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.preemption.job.preemptive.valid_fully_preemptive_model". Abort.
Check @prosa.analysis.facts.preemption.job.preemptive.valid_fully_preemptive_model.
Goal True. idtac "END|prosa.analysis.facts.preemption.job.preemptive.valid_fully_preemptive_model". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.preemption.job.preemptive.job_max_nps_is_0". Abort.
Check @prosa.analysis.facts.preemption.job.preemptive.job_max_nps_is_0.
Goal True. idtac "END|prosa.analysis.facts.preemption.job.preemptive.job_max_nps_is_0". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.preemption.job.preemptive.job_max_nps_is_ε". Abort.
Check @prosa.analysis.facts.preemption.job.preemptive.job_max_nps_is_ε.
Goal True. idtac "END|prosa.analysis.facts.preemption.job.preemptive.job_max_nps_is_ε". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.preemption.rtc_threshold.floating.floating_preemptive_valid_task_run_to_completion_threshold". Abort.
Check @prosa.analysis.facts.preemption.rtc_threshold.floating.floating_preemptive_valid_task_run_to_completion_threshold.
Goal True. idtac "END|prosa.analysis.facts.preemption.rtc_threshold.floating.floating_preemptive_valid_task_run_to_completion_threshold". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.preemption.rtc_threshold.job_preemptable.preemption_points_of_zero_cost_job". Abort.
Check @prosa.analysis.facts.preemption.rtc_threshold.job_preemptable.preemption_points_of_zero_cost_job.
Goal True. idtac "END|prosa.analysis.facts.preemption.rtc_threshold.job_preemptable.preemption_points_of_zero_cost_job". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.preemption.rtc_threshold.job_preemptable.zero_in_preemption_points". Abort.
Check @prosa.analysis.facts.preemption.rtc_threshold.job_preemptable.zero_in_preemption_points.
Goal True. idtac "END|prosa.analysis.facts.preemption.rtc_threshold.job_preemptable.zero_in_preemption_points". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.preemption.rtc_threshold.job_preemptable.job_cost_in_preemption_points". Abort.
Check @prosa.analysis.facts.preemption.rtc_threshold.job_preemptable.job_cost_in_preemption_points.
Goal True. idtac "END|prosa.analysis.facts.preemption.rtc_threshold.job_preemptable.job_cost_in_preemption_points". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.preemption.rtc_threshold.job_preemptable.size_of_preemption_points". Abort.
Check @prosa.analysis.facts.preemption.rtc_threshold.job_preemptable.size_of_preemption_points.
Goal True. idtac "END|prosa.analysis.facts.preemption.rtc_threshold.job_preemptable.size_of_preemption_points". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.preemption.rtc_threshold.job_preemptable.preemption_points_nondecreasing". Abort.
Check @prosa.analysis.facts.preemption.rtc_threshold.job_preemptable.preemption_points_nondecreasing.
Goal True. idtac "END|prosa.analysis.facts.preemption.rtc_threshold.job_preemptable.preemption_points_nondecreasing". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.preemption.rtc_threshold.job_preemptable.job_cost_is_last_element_of_preemption_points". Abort.
Check @prosa.analysis.facts.preemption.rtc_threshold.job_preemptable.job_cost_is_last_element_of_preemption_points.
Goal True. idtac "END|prosa.analysis.facts.preemption.rtc_threshold.job_preemptable.job_cost_is_last_element_of_preemption_points". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.preemption.rtc_threshold.job_preemptable.job_last_nonpreemptive_segment_positive". Abort.
Check @prosa.analysis.facts.preemption.rtc_threshold.job_preemptable.job_last_nonpreemptive_segment_positive.
Goal True. idtac "END|prosa.analysis.facts.preemption.rtc_threshold.job_preemptable.job_last_nonpreemptive_segment_positive". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.preemption.rtc_threshold.job_preemptable.job_max_nonpreemptive_segment_positive". Abort.
Check @prosa.analysis.facts.preemption.rtc_threshold.job_preemptable.job_max_nonpreemptive_segment_positive.
Goal True. idtac "END|prosa.analysis.facts.preemption.rtc_threshold.job_preemptable.job_max_nonpreemptive_segment_positive". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.preemption.rtc_threshold.job_preemptable.job_max_nonpreemptive_segment_le_job_cost". Abort.
Check @prosa.analysis.facts.preemption.rtc_threshold.job_preemptable.job_max_nonpreemptive_segment_le_job_cost.
Goal True. idtac "END|prosa.analysis.facts.preemption.rtc_threshold.job_preemptable.job_max_nonpreemptive_segment_le_job_cost". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.preemption.rtc_threshold.job_preemptable.job_last_nonpreemptive_segment_le_job_cost". Abort.
Check @prosa.analysis.facts.preemption.rtc_threshold.job_preemptable.job_last_nonpreemptive_segment_le_job_cost.
Goal True. idtac "END|prosa.analysis.facts.preemption.rtc_threshold.job_preemptable.job_last_nonpreemptive_segment_le_job_cost". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.preemption.rtc_threshold.job_preemptable.job_run_to_completion_threshold_positive". Abort.
Check @prosa.analysis.facts.preemption.rtc_threshold.job_preemptable.job_run_to_completion_threshold_positive.
Goal True. idtac "END|prosa.analysis.facts.preemption.rtc_threshold.job_preemptable.job_run_to_completion_threshold_positive". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.preemption.rtc_threshold.job_preemptable.job_run_to_completion_threshold_le_job_cost". Abort.
Check @prosa.analysis.facts.preemption.rtc_threshold.job_preemptable.job_run_to_completion_threshold_le_job_cost.
Goal True. idtac "END|prosa.analysis.facts.preemption.rtc_threshold.job_preemptable.job_run_to_completion_threshold_le_job_cost". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.preemption.rtc_threshold.job_preemptable.job_cannot_be_preempted_within_last_segment". Abort.
Check @prosa.analysis.facts.preemption.rtc_threshold.job_preemptable.job_cannot_be_preempted_within_last_segment.
Goal True. idtac "END|prosa.analysis.facts.preemption.rtc_threshold.job_preemptable.job_cannot_be_preempted_within_last_segment". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.preemption.rtc_threshold.job_preemptable.job_nonpreemptive_after_run_to_completion_threshold". Abort.
Check @prosa.analysis.facts.preemption.rtc_threshold.job_preemptable.job_nonpreemptive_after_run_to_completion_threshold.
Goal True. idtac "END|prosa.analysis.facts.preemption.rtc_threshold.job_preemptable.job_nonpreemptive_after_run_to_completion_threshold". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.preemption.rtc_threshold.limited.number_of_preemption_points_in_task_at_least_two". Abort.
Check @prosa.analysis.facts.preemption.rtc_threshold.limited.number_of_preemption_points_in_task_at_least_two.
Goal True. idtac "END|prosa.analysis.facts.preemption.rtc_threshold.limited.number_of_preemption_points_in_task_at_least_two". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.preemption.rtc_threshold.limited.limited_valid_task_run_to_completion_threshold". Abort.
Check @prosa.analysis.facts.preemption.rtc_threshold.limited.limited_valid_task_run_to_completion_threshold.
Goal True. idtac "END|prosa.analysis.facts.preemption.rtc_threshold.limited.limited_valid_task_run_to_completion_threshold". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.preemption.rtc_threshold.limited.last_segment_eq_cost_minus_rtct". Abort.
Check @prosa.analysis.facts.preemption.rtc_threshold.limited.last_segment_eq_cost_minus_rtct.
Goal True. idtac "END|prosa.analysis.facts.preemption.rtc_threshold.limited.last_segment_eq_cost_minus_rtct". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.preemption.rtc_threshold.nonpreemptive.job_rtc_threshold_is_0". Abort.
Check @prosa.analysis.facts.preemption.rtc_threshold.nonpreemptive.job_rtc_threshold_is_0.
Goal True. idtac "END|prosa.analysis.facts.preemption.rtc_threshold.nonpreemptive.job_rtc_threshold_is_0". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.preemption.rtc_threshold.nonpreemptive.job_rtc_threshold_is_ε". Abort.
Check @prosa.analysis.facts.preemption.rtc_threshold.nonpreemptive.job_rtc_threshold_is_ε.
Goal True. idtac "END|prosa.analysis.facts.preemption.rtc_threshold.nonpreemptive.job_rtc_threshold_is_ε". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.preemption.rtc_threshold.nonpreemptive.fully_nonpreemptive_valid_task_run_to_completion_threshold". Abort.
Check @prosa.analysis.facts.preemption.rtc_threshold.nonpreemptive.fully_nonpreemptive_valid_task_run_to_completion_threshold.
Goal True. idtac "END|prosa.analysis.facts.preemption.rtc_threshold.nonpreemptive.fully_nonpreemptive_valid_task_run_to_completion_threshold". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.preemption.rtc_threshold.preemptive.fully_preemptive_valid_task_run_to_completion_threshold". Abort.
Check @prosa.analysis.facts.preemption.rtc_threshold.preemptive.fully_preemptive_valid_task_run_to_completion_threshold.
Goal True. idtac "END|prosa.analysis.facts.preemption.rtc_threshold.preemptive.fully_preemptive_valid_task_run_to_completion_threshold". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.preemption.task.floating.floating_preemption_points_model_is_model_with_bounded_nonpreemptive_regions". Abort.
Check @prosa.analysis.facts.preemption.task.floating.floating_preemption_points_model_is_model_with_bounded_nonpreemptive_regions.
Goal True. idtac "END|prosa.analysis.facts.preemption.task.floating.floating_preemption_points_model_is_model_with_bounded_nonpreemptive_regions". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.preemption.task.floating.floating_preemption_points_model_is_valid_model_with_bounded_nonpreemptive_regions". Abort.
Check @prosa.analysis.facts.preemption.task.floating.floating_preemption_points_model_is_valid_model_with_bounded_nonpreemptive_regions.
Goal True. idtac "END|prosa.analysis.facts.preemption.task.floating.floating_preemption_points_model_is_valid_model_with_bounded_nonpreemptive_regions". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.preemption.task.limited.fixed_preemption_points_model_is_model_with_bounded_nonpreemptive_regions". Abort.
Check @prosa.analysis.facts.preemption.task.limited.fixed_preemption_points_model_is_model_with_bounded_nonpreemptive_regions.
Goal True. idtac "END|prosa.analysis.facts.preemption.task.limited.fixed_preemption_points_model_is_model_with_bounded_nonpreemptive_regions". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.preemption.task.limited.fixed_preemption_points_model_is_valid_model_with_bounded_nonpreemptive_regions". Abort.
Check @prosa.analysis.facts.preemption.task.limited.fixed_preemption_points_model_is_valid_model_with_bounded_nonpreemptive_regions.
Goal True. idtac "END|prosa.analysis.facts.preemption.task.limited.fixed_preemption_points_model_is_valid_model_with_bounded_nonpreemptive_regions". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.preemption.task.nonpreemptive.fully_nonpreemptive_model_is_model_with_bounded_nonpreemptive_regions". Abort.
Check @prosa.analysis.facts.preemption.task.nonpreemptive.fully_nonpreemptive_model_is_model_with_bounded_nonpreemptive_regions.
Goal True. idtac "END|prosa.analysis.facts.preemption.task.nonpreemptive.fully_nonpreemptive_model_is_model_with_bounded_nonpreemptive_regions". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.preemption.task.nonpreemptive.fully_nonpreemptive_model_is_valid_model_with_bounded_nonpreemptive_regions". Abort.
Check @prosa.analysis.facts.preemption.task.nonpreemptive.fully_nonpreemptive_model_is_valid_model_with_bounded_nonpreemptive_regions.
Goal True. idtac "END|prosa.analysis.facts.preemption.task.nonpreemptive.fully_nonpreemptive_model_is_valid_model_with_bounded_nonpreemptive_regions". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.preemption.task.preemptive.fully_preemptive_model_is_model_with_bounded_nonpreemptive_regions". Abort.
Check @prosa.analysis.facts.preemption.task.preemptive.fully_preemptive_model_is_model_with_bounded_nonpreemptive_regions.
Goal True. idtac "END|prosa.analysis.facts.preemption.task.preemptive.fully_preemptive_model_is_model_with_bounded_nonpreemptive_regions". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.preemption.task.preemptive.fully_preemptive_model_is_valid_model_with_bounded_nonpreemptive_segments". Abort.
Check @prosa.analysis.facts.preemption.task.preemptive.fully_preemptive_model_is_valid_model_with_bounded_nonpreemptive_segments.
Goal True. idtac "END|prosa.analysis.facts.preemption.task.preemptive.fully_preemptive_model_is_valid_model_with_bounded_nonpreemptive_segments". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.priority.classes.another_hep_job_antireflexive". Abort.
Check @prosa.analysis.facts.priority.classes.another_hep_job_antireflexive.
Goal True. idtac "END|prosa.analysis.facts.priority.classes.another_hep_job_antireflexive". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.priority.classes.another_hep_job_diff_task". Abort.
Check @prosa.analysis.facts.priority.classes.another_hep_job_diff_task.
Goal True. idtac "END|prosa.analysis.facts.priority.classes.another_hep_job_diff_task". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.priority.classes.another_task_hep_job_taskwise_antireflexive". Abort.
Check @prosa.analysis.facts.priority.classes.another_task_hep_job_taskwise_antireflexive.
Goal True. idtac "END|prosa.analysis.facts.priority.classes.another_task_hep_job_taskwise_antireflexive". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.priority.classes.another_task_hep_job_another_hep_job". Abort.
Check @prosa.analysis.facts.priority.classes.another_task_hep_job_another_hep_job.
Goal True. idtac "END|prosa.analysis.facts.priority.classes.another_task_hep_job_another_hep_job". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.priority.classes.another_hep_job_split_task". Abort.
Check @prosa.analysis.facts.priority.classes.another_hep_job_split_task.
Goal True. idtac "END|prosa.analysis.facts.priority.classes.another_hep_job_split_task". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.priority.classes.another_hep_job_exclusive". Abort.
Check @prosa.analysis.facts.priority.classes.another_hep_job_exclusive.
Goal True. idtac "END|prosa.analysis.facts.priority.classes.another_hep_job_exclusive". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.priority.classes.hp_task_irrefl". Abort.
Check @prosa.analysis.facts.priority.classes.hp_task_irrefl.
Goal True. idtac "END|prosa.analysis.facts.priority.classes.hp_task_irrefl". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.priority.classes.hp_hep_task". Abort.
Check @prosa.analysis.facts.priority.classes.hp_hep_task.
Goal True. idtac "END|prosa.analysis.facts.priority.classes.hp_hep_task". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.priority.classes.ep_hep_task". Abort.
Check @prosa.analysis.facts.priority.classes.ep_hep_task.
Goal True. idtac "END|prosa.analysis.facts.priority.classes.ep_hep_task". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.priority.classes.ep_not_hp_task". Abort.
Check @prosa.analysis.facts.priority.classes.ep_not_hp_task.
Goal True. idtac "END|prosa.analysis.facts.priority.classes.ep_not_hp_task". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.priority.classes.ep_task_sym". Abort.
Check @prosa.analysis.facts.priority.classes.ep_task_sym.
Goal True. idtac "END|prosa.analysis.facts.priority.classes.ep_task_sym". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.priority.classes.hep_hp_ep_task". Abort.
Check @prosa.analysis.facts.priority.classes.hep_hp_ep_task.
Goal True. idtac "END|prosa.analysis.facts.priority.classes.hep_hp_ep_task". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.priority.classes.eq_reflexive". Abort.
Check @prosa.analysis.facts.priority.classes.eq_reflexive.
Goal True. idtac "END|prosa.analysis.facts.priority.classes.eq_reflexive". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.priority.classes.hp_trans". Abort.
Check @prosa.analysis.facts.priority.classes.hp_trans.
Goal True. idtac "END|prosa.analysis.facts.priority.classes.hp_trans". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.priority.classes.hp_hep_trans". Abort.
Check @prosa.analysis.facts.priority.classes.hp_hep_trans.
Goal True. idtac "END|prosa.analysis.facts.priority.classes.hp_hep_trans". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.priority.classes.hep_hp_trans". Abort.
Check @prosa.analysis.facts.priority.classes.hep_hp_trans.
Goal True. idtac "END|prosa.analysis.facts.priority.classes.hep_hp_trans". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.priority.classes.not_hep_hp_task". Abort.
Check @prosa.analysis.facts.priority.classes.not_hep_hp_task.
Goal True. idtac "END|prosa.analysis.facts.priority.classes.not_hep_hp_task". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.priority.classes.not_hp_hep_task". Abort.
Check @prosa.analysis.facts.priority.classes.not_hp_hep_task.
Goal True. idtac "END|prosa.analysis.facts.priority.classes.not_hp_hep_task". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.priority.classes.nhp_ep_nhep_task". Abort.
Check @prosa.analysis.facts.priority.classes.nhp_ep_nhep_task.
Goal True. idtac "END|prosa.analysis.facts.priority.classes.nhp_ep_nhep_task". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.priority.classes.respects_sequential_tasks". Abort.
Check @prosa.analysis.facts.priority.classes.respects_sequential_tasks.
Goal True. idtac "END|prosa.analysis.facts.priority.classes.respects_sequential_tasks". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.priority.classes.hep_job_implies_hep_task". Abort.
Check @prosa.analysis.facts.priority.classes.hep_job_implies_hep_task.
Goal True. idtac "END|prosa.analysis.facts.priority.classes.hep_job_implies_hep_task". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.priority.classes.hp_task_implies_hep_job". Abort.
Check @prosa.analysis.facts.priority.classes.hp_task_implies_hep_job.
Goal True. idtac "END|prosa.analysis.facts.priority.classes.hp_task_implies_hep_job". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.priority.edf.hep_job_deadline". Abort.
Check @prosa.analysis.facts.priority.edf.hep_job_deadline.
Goal True. idtac "END|prosa.analysis.facts.priority.edf.hep_job_deadline". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.priority.edf.hep_job_task_deadline". Abort.
Check @prosa.analysis.facts.priority.edf.hep_job_task_deadline.
Goal True. idtac "END|prosa.analysis.facts.priority.edf.hep_job_task_deadline". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.priority.edf.hep_job_arrival_edf". Abort.
Check @prosa.analysis.facts.priority.edf.hep_job_arrival_edf.
Goal True. idtac "END|prosa.analysis.facts.priority.edf.hep_job_arrival_edf". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.priority.edf.EDF_respects_sequential_tasks". Abort.
Check @prosa.analysis.facts.priority.edf.EDF_respects_sequential_tasks.
Goal True. idtac "END|prosa.analysis.facts.priority.edf.EDF_respects_sequential_tasks". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.priority.edf.EDF_implies_sequential_tasks". Abort.
Check @prosa.analysis.facts.priority.edf.EDF_implies_sequential_tasks.
Goal True. idtac "END|prosa.analysis.facts.priority.edf.EDF_implies_sequential_tasks". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.priority.elf.hep_job_elf_gel". Abort.
Check @prosa.analysis.facts.priority.elf.hep_job_elf_gel.
Goal True. idtac "END|prosa.analysis.facts.priority.elf.hep_job_elf_gel". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.priority.elf.hep_job_arrival_elf". Abort.
Check @prosa.analysis.facts.priority.elf.hep_job_arrival_elf.
Goal True. idtac "END|prosa.analysis.facts.priority.elf.hep_job_arrival_elf". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.priority.elf.ELF_is_reflexive". Abort.
Check @prosa.analysis.facts.priority.elf.ELF_is_reflexive.
Goal True. idtac "END|prosa.analysis.facts.priority.elf.ELF_is_reflexive". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.priority.elf.ELF_is_transitive". Abort.
Check @prosa.analysis.facts.priority.elf.ELF_is_transitive.
Goal True. idtac "END|prosa.analysis.facts.priority.elf.ELF_is_transitive". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.priority.elf.ELF_is_total". Abort.
Check @prosa.analysis.facts.priority.elf.ELF_is_total.
Goal True. idtac "END|prosa.analysis.facts.priority.elf.ELF_is_total". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.priority.elf.ELF_is_JLFP_FP_compatible". Abort.
Check @prosa.analysis.facts.priority.elf.ELF_is_JLFP_FP_compatible.
Goal True. idtac "END|prosa.analysis.facts.priority.elf.ELF_is_JLFP_FP_compatible". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.priority.elf.ELF_respects_sequential_tasks". Abort.
Check @prosa.analysis.facts.priority.elf.ELF_respects_sequential_tasks.
Goal True. idtac "END|prosa.analysis.facts.priority.elf.ELF_respects_sequential_tasks". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.priority.elf.ELF_implies_sequential_tasks". Abort.
Check @prosa.analysis.facts.priority.elf.ELF_implies_sequential_tasks.
Goal True. idtac "END|prosa.analysis.facts.priority.elf.ELF_implies_sequential_tasks". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.priority.fifo.hep_job_arrival_FIFO". Abort.
Check @prosa.analysis.facts.priority.fifo.hep_job_arrival_FIFO.
Goal True. idtac "END|prosa.analysis.facts.priority.fifo.hep_job_arrival_FIFO". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.priority.fifo.not_hep_job_arrival_FIFO". Abort.
Check @prosa.analysis.facts.priority.fifo.not_hep_job_arrival_FIFO.
Goal True. idtac "END|prosa.analysis.facts.priority.fifo.not_hep_job_arrival_FIFO". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.priority.fifo.not_hep_job_FIFO". Abort.
Check @prosa.analysis.facts.priority.fifo.not_hep_job_FIFO.
Goal True. idtac "END|prosa.analysis.facts.priority.fifo.not_hep_job_FIFO". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.priority.fifo.not_hep_job_always_higher_priority_FIFO". Abort.
Check @prosa.analysis.facts.priority.fifo.not_hep_job_always_higher_priority_FIFO.
Goal True. idtac "END|prosa.analysis.facts.priority.fifo.not_hep_job_always_higher_priority_FIFO". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.priority.fifo.FIFO_implies_no_priority_inversion". Abort.
Check @prosa.analysis.facts.priority.fifo.FIFO_implies_no_priority_inversion.
Goal True. idtac "END|prosa.analysis.facts.priority.fifo.FIFO_implies_no_priority_inversion". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.priority.fifo.scheduled_implies_higher_priority_completed". Abort.
Check @prosa.analysis.facts.priority.fifo.scheduled_implies_higher_priority_completed.
Goal True. idtac "END|prosa.analysis.facts.priority.fifo.scheduled_implies_higher_priority_completed". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.priority.fifo.FIFO_implies_no_pi". Abort.
Check @prosa.analysis.facts.priority.fifo.FIFO_implies_no_pi.
Goal True. idtac "END|prosa.analysis.facts.priority.fifo.FIFO_implies_no_pi". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.priority.fifo.FIFO_implies_no_service_inversion". Abort.
Check @prosa.analysis.facts.priority.fifo.FIFO_implies_no_service_inversion.
Goal True. idtac "END|prosa.analysis.facts.priority.fifo.FIFO_implies_no_service_inversion". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.priority.fifo.tasks_execute_sequentially". Abort.
Check @prosa.analysis.facts.priority.fifo.tasks_execute_sequentially.
Goal True. idtac "END|prosa.analysis.facts.priority.fifo.tasks_execute_sequentially". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.priority.fifo.fifo_respects_sequential_tasks". Abort.
Check @prosa.analysis.facts.priority.fifo.fifo_respects_sequential_tasks.
Goal True. idtac "END|prosa.analysis.facts.priority.fifo.fifo_respects_sequential_tasks". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.priority.fifo.no_preemptions_under_FIFO". Abort.
Check @prosa.analysis.facts.priority.fifo.no_preemptions_under_FIFO.
Goal True. idtac "END|prosa.analysis.facts.priority.fifo.no_preemptions_under_FIFO". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.priority.fifo.FIFO_is_nonpreemptive". Abort.
Check @prosa.analysis.facts.priority.fifo.FIFO_is_nonpreemptive.
Goal True. idtac "END|prosa.analysis.facts.priority.fifo.FIFO_is_nonpreemptive". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.priority.fifo_ahep_bound.bound_on_hep_workload". Abort.
Check @prosa.analysis.facts.priority.fifo_ahep_bound.bound_on_hep_workload.
Goal True. idtac "END|prosa.analysis.facts.priority.fifo_ahep_bound.bound_on_hep_workload". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.priority.gel.hep_job_priority_point". Abort.
Check @prosa.analysis.facts.priority.gel.hep_job_priority_point.
Goal True. idtac "END|prosa.analysis.facts.priority.gel.hep_job_priority_point". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.priority.gel.hep_job_arrival_gel". Abort.
Check @prosa.analysis.facts.priority.gel.hep_job_arrival_gel.
Goal True. idtac "END|prosa.analysis.facts.priority.gel.hep_job_arrival_gel". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.priority.gel.hep_job_arrives_before". Abort.
Check @prosa.analysis.facts.priority.gel.hep_job_arrives_before.
Goal True. idtac "END|prosa.analysis.facts.priority.gel.hep_job_arrives_before". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.priority.gel.hep_job_arrives_after_zero". Abort.
Check @prosa.analysis.facts.priority.gel.hep_job_arrives_after_zero.
Goal True. idtac "END|prosa.analysis.facts.priority.gel.hep_job_arrives_after_zero". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.priority.gel.GEL_respects_sequential_tasks". Abort.
Check @prosa.analysis.facts.priority.gel.GEL_respects_sequential_tasks.
Goal True. idtac "END|prosa.analysis.facts.priority.gel.GEL_respects_sequential_tasks". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.priority.gel.GEL_implies_sequential_tasks". Abort.
Check @prosa.analysis.facts.priority.gel.GEL_implies_sequential_tasks.
Goal True. idtac "END|prosa.analysis.facts.priority.gel.GEL_implies_sequential_tasks". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.priority.inversion.sched_itself_implies_no_priority_inversion". Abort.
Check @prosa.analysis.facts.priority.inversion.sched_itself_implies_no_priority_inversion.
Goal True. idtac "END|prosa.analysis.facts.priority.inversion.sched_itself_implies_no_priority_inversion". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.priority.inversion.priority_inversion_scheduled_at". Abort.
Check @prosa.analysis.facts.priority.inversion.priority_inversion_scheduled_at.
Goal True. idtac "END|prosa.analysis.facts.priority.inversion.priority_inversion_scheduled_at". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.priority.inversion.no_priority_inversion_when_idle". Abort.
Check @prosa.analysis.facts.priority.inversion.no_priority_inversion_when_idle.
Goal True. idtac "END|prosa.analysis.facts.priority.inversion.no_priority_inversion_when_idle". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.priority.inversion.priority_inversion_hep_job". Abort.
Check @prosa.analysis.facts.priority.inversion.priority_inversion_hep_job.
Goal True. idtac "END|prosa.analysis.facts.priority.inversion.priority_inversion_hep_job". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.priority.inversion.no_priority_inversion_when_hep_job_scheduled". Abort.
Check @prosa.analysis.facts.priority.inversion.no_priority_inversion_when_hep_job_scheduled.
Goal True. idtac "END|prosa.analysis.facts.priority.inversion.no_priority_inversion_when_hep_job_scheduled". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.priority.inversion.uni_priority_inversion_P". Abort.
Check @prosa.analysis.facts.priority.inversion.uni_priority_inversion_P.
Goal True. idtac "END|prosa.analysis.facts.priority.inversion.uni_priority_inversion_P". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.priority.inversion.cumulative_priority_inversion_cat". Abort.
Check @prosa.analysis.facts.priority.inversion.cumulative_priority_inversion_cat.
Goal True. idtac "END|prosa.analysis.facts.priority.inversion.cumulative_priority_inversion_cat". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.priority.jlfp_with_fp.other_ep_task". Abort.
Check @prosa.analysis.facts.priority.jlfp_with_fp.other_ep_task.
Goal True. idtac "END|prosa.analysis.facts.priority.jlfp_with_fp.other_ep_task". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.priority.jlfp_with_fp.hep_job_of_ep_other_task". Abort.
Check @prosa.analysis.facts.priority.jlfp_with_fp.hep_job_of_ep_other_task.
Goal True. idtac "END|prosa.analysis.facts.priority.jlfp_with_fp.hep_job_of_ep_other_task". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.priority.jlfp_with_fp.hep_workload_from_other_ep_partitioned_by_tasks". Abort.
Check @prosa.analysis.facts.priority.jlfp_with_fp.hep_workload_from_other_ep_partitioned_by_tasks.
Goal True. idtac "END|prosa.analysis.facts.priority.jlfp_with_fp.hep_workload_from_other_ep_partitioned_by_tasks". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.priority.jlfp_with_fp.from_hp_task". Abort.
Check @prosa.analysis.facts.priority.jlfp_with_fp.from_hp_task.
Goal True. idtac "END|prosa.analysis.facts.priority.jlfp_with_fp.from_hp_task". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.priority.jlfp_with_fp.hep_from_hp_task". Abort.
Check @prosa.analysis.facts.priority.jlfp_with_fp.hep_from_hp_task.
Goal True. idtac "END|prosa.analysis.facts.priority.jlfp_with_fp.hep_from_hp_task". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.priority.jlfp_with_fp.hep_from_ep_task". Abort.
Check @prosa.analysis.facts.priority.jlfp_with_fp.hep_from_ep_task.
Goal True. idtac "END|prosa.analysis.facts.priority.jlfp_with_fp.hep_from_ep_task". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.priority.jlfp_with_fp.hep_hp_workload_hp". Abort.
Check @prosa.analysis.facts.priority.jlfp_with_fp.hep_hp_workload_hp.
Goal True. idtac "END|prosa.analysis.facts.priority.jlfp_with_fp.hep_hp_workload_hp". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.priority.jlfp_with_fp.hep_workload_partitioning_taskwise". Abort.
Check @prosa.analysis.facts.priority.jlfp_with_fp.hep_workload_partitioning_taskwise.
Goal True. idtac "END|prosa.analysis.facts.priority.jlfp_with_fp.hep_workload_partitioning_taskwise". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.priority.sequential.early_hep_job_is_scheduled". Abort.
Check @prosa.analysis.facts.priority.sequential.early_hep_job_is_scheduled.
Goal True. idtac "END|prosa.analysis.facts.priority.sequential.early_hep_job_is_scheduled". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.readiness.backlogged.mem_backlogged_jobs". Abort.
Check @prosa.analysis.facts.readiness.backlogged.mem_backlogged_jobs.
Goal True. idtac "END|prosa.analysis.facts.readiness.backlogged.mem_backlogged_jobs". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.readiness.backlogged.backlogged_job_arrives_in". Abort.
Check @prosa.analysis.facts.readiness.backlogged.backlogged_job_arrives_in.
Goal True. idtac "END|prosa.analysis.facts.readiness.backlogged.backlogged_job_arrives_in". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.readiness.backlogged.backlogged_prefix_invariance". Abort.
Check @prosa.analysis.facts.readiness.backlogged.backlogged_prefix_invariance.
Goal True. idtac "END|prosa.analysis.facts.readiness.backlogged.backlogged_prefix_invariance". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.readiness.backlogged.backlogged_prefix_invariance'". Abort.
Check @prosa.analysis.facts.readiness.backlogged.backlogged_prefix_invariance'.
Goal True. idtac "END|prosa.analysis.facts.readiness.backlogged.backlogged_prefix_invariance'". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.readiness.backlogged.backlogged_jobs_prefix_invariance". Abort.
Check @prosa.analysis.facts.readiness.backlogged.backlogged_jobs_prefix_invariance.
Goal True. idtac "END|prosa.analysis.facts.readiness.backlogged.backlogged_jobs_prefix_invariance". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.readiness.basic.basic_readiness_nonclairvoyance". Abort.
Check @prosa.analysis.facts.readiness.basic.basic_readiness_nonclairvoyance.
Goal True. idtac "END|prosa.analysis.facts.readiness.basic.basic_readiness_nonclairvoyance". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.readiness.basic.basic_readiness_compliance". Abort.
Check @prosa.analysis.facts.readiness.basic.basic_readiness_compliance.
Goal True. idtac "END|prosa.analysis.facts.readiness.basic.basic_readiness_compliance". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.readiness.basic.basic_readiness_is_work_bearing_readiness". Abort.
Check @prosa.analysis.facts.readiness.basic.basic_readiness_is_work_bearing_readiness.
Goal True. idtac "END|prosa.analysis.facts.readiness.basic.basic_readiness_is_work_bearing_readiness". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.readiness.sequential.sequential_readiness_is_sequential". Abort.
Check @prosa.analysis.facts.readiness.sequential.sequential_readiness_is_sequential.
Goal True. idtac "END|prosa.analysis.facts.readiness.sequential.sequential_readiness_is_sequential". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.readiness.sequential.sequential_readiness_nonclairvoyance". Abort.
Check @prosa.analysis.facts.readiness.sequential.sequential_readiness_nonclairvoyance.
Goal True. idtac "END|prosa.analysis.facts.readiness.sequential.sequential_readiness_nonclairvoyance". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.readiness.sequential.sequential_readiness_implies_sequential_tasks". Abort.
Check @prosa.analysis.facts.readiness.sequential.sequential_readiness_implies_sequential_tasks.
Goal True. idtac "END|prosa.analysis.facts.readiness.sequential.sequential_readiness_implies_sequential_tasks". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.readiness.sequential.sequential_readiness_implies_work_bearing_readiness". Abort.
Check @prosa.analysis.facts.readiness.sequential.sequential_readiness_implies_work_bearing_readiness.
Goal True. idtac "END|prosa.analysis.facts.readiness.sequential.sequential_readiness_implies_work_bearing_readiness". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.readiness_interference.no_hep_ready_implies_no_another_hep_interference". Abort.
Check @prosa.analysis.facts.readiness_interference.no_hep_ready_implies_no_another_hep_interference.
Goal True. idtac "END|prosa.analysis.facts.readiness_interference.no_hep_ready_implies_no_another_hep_interference". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.readiness_interference.no_hep_ready_implies_no_service_inversion". Abort.
Check @prosa.analysis.facts.readiness_interference.no_hep_ready_implies_no_service_inversion.
Goal True. idtac "END|prosa.analysis.facts.readiness_interference.no_hep_ready_implies_no_service_inversion". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.shifted_job_costs.job_costs_shifted". Abort.
Check @prosa.analysis.facts.shifted_job_costs.job_costs_shifted.
Goal True. idtac "END|prosa.analysis.facts.shifted_job_costs.job_costs_shifted". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.shifted_job_costs.job_costs_in_oi". Abort.
Check @prosa.analysis.facts.shifted_job_costs.job_costs_in_oi.
Goal True. idtac "END|prosa.analysis.facts.shifted_job_costs.job_costs_in_oi". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.shifted_job_costs.job_costs_shifted_valid". Abort.
Check @prosa.analysis.facts.shifted_job_costs.job_costs_shifted_valid.
Goal True. idtac "END|prosa.analysis.facts.shifted_job_costs.job_costs_shifted_valid". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.sporadic.arrival_bound.max_sporadic_arrivals". Abort.
Check @prosa.analysis.facts.sporadic.arrival_bound.max_sporadic_arrivals.
Goal True. idtac "END|prosa.analysis.facts.sporadic.arrival_bound.max_sporadic_arrivals". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.sporadic.arrival_bound.arrival_of_nth_job". Abort.
Check @prosa.analysis.facts.sporadic.arrival_bound.arrival_of_nth_job.
Goal True. idtac "END|prosa.analysis.facts.sporadic.arrival_bound.arrival_of_nth_job". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.sporadic.arrival_bound.minimum_distance_for_n_sporadic_arrivals". Abort.
Check @prosa.analysis.facts.sporadic.arrival_bound.minimum_distance_for_n_sporadic_arrivals.
Goal True. idtac "END|prosa.analysis.facts.sporadic.arrival_bound.minimum_distance_for_n_sporadic_arrivals". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.sporadic.arrival_bound.sporadic_task_arrivals_bound". Abort.
Check @prosa.analysis.facts.sporadic.arrival_bound.sporadic_task_arrivals_bound.
Goal True. idtac "END|prosa.analysis.facts.sporadic.arrival_bound.sporadic_task_arrivals_bound". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.sporadic.arrival_sequence.size_task_arrivals_at_leq_one". Abort.
Check @prosa.analysis.facts.sporadic.arrival_sequence.size_task_arrivals_at_leq_one.
Goal True. idtac "END|prosa.analysis.facts.sporadic.arrival_sequence.size_task_arrivals_at_leq_one". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.sporadic.arrival_sequence.only_j_in_task_arrivals_at_j". Abort.
Check @prosa.analysis.facts.sporadic.arrival_sequence.only_j_in_task_arrivals_at_j.
Goal True. idtac "END|prosa.analysis.facts.sporadic.arrival_sequence.only_j_in_task_arrivals_at_j". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.sporadic.arrival_sequence.only_j_at_job_arrival_j". Abort.
Check @prosa.analysis.facts.sporadic.arrival_sequence.only_j_at_job_arrival_j.
Goal True. idtac "END|prosa.analysis.facts.sporadic.arrival_sequence.only_j_at_job_arrival_j". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.sporadic.arrival_sequence.index_j_in_task_arrivals_at". Abort.
Check @prosa.analysis.facts.sporadic.arrival_sequence.index_j_in_task_arrivals_at.
Goal True. idtac "END|prosa.analysis.facts.sporadic.arrival_sequence.index_j_in_task_arrivals_at". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.sporadic.arrival_sequence.prev_job_arr_lt". Abort.
Check @prosa.analysis.facts.sporadic.arrival_sequence.prev_job_arr_lt.
Goal True. idtac "END|prosa.analysis.facts.sporadic.arrival_sequence.prev_job_arr_lt". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.sporadic.arrival_sequence.task_arrivals_at_as_task_arrivals_between". Abort.
Check @prosa.analysis.facts.sporadic.arrival_sequence.task_arrivals_at_as_task_arrivals_between.
Goal True. idtac "END|prosa.analysis.facts.sporadic.arrival_sequence.task_arrivals_at_as_task_arrivals_between". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.sporadic.arrival_sequence.prev_job_cat". Abort.
Check @prosa.analysis.facts.sporadic.arrival_sequence.prev_job_cat.
Goal True. idtac "END|prosa.analysis.facts.sporadic.arrival_sequence.prev_job_cat". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.sporadic.arrival_times.lower_index_implies_earlier_arrival". Abort.
Check @prosa.analysis.facts.sporadic.arrival_times.lower_index_implies_earlier_arrival.
Goal True. idtac "END|prosa.analysis.facts.sporadic.arrival_times.lower_index_implies_earlier_arrival". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.sporadic.arrival_times.same_jobs_iff_same_arr". Abort.
Check @prosa.analysis.facts.sporadic.arrival_times.same_jobs_iff_same_arr.
Goal True. idtac "END|prosa.analysis.facts.sporadic.arrival_times.same_jobs_iff_same_arr". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.sporadic.arrival_times.uneq_job_uneq_arr". Abort.
Check @prosa.analysis.facts.sporadic.arrival_times.uneq_job_uneq_arr.
Goal True. idtac "END|prosa.analysis.facts.sporadic.arrival_times.uneq_job_uneq_arr". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.suspension.suspended_implies_job_not_ready". Abort.
Check @prosa.analysis.facts.suspension.suspended_implies_job_not_ready.
Goal True. idtac "END|prosa.analysis.facts.suspension.suspended_implies_job_not_ready". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.suspension.suspended_implies_not_scheduled". Abort.
Check @prosa.analysis.facts.suspension.suspended_implies_not_scheduled.
Goal True. idtac "END|prosa.analysis.facts.suspension.suspended_implies_not_scheduled". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.suspension.suspended_implies_arrived". Abort.
Check @prosa.analysis.facts.suspension.suspended_implies_arrived.
Goal True. idtac "END|prosa.analysis.facts.suspension.suspended_implies_arrived". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.suspension.suspended_implies_pending". Abort.
Check @prosa.analysis.facts.suspension.suspended_implies_pending.
Goal True. idtac "END|prosa.analysis.facts.suspension.suspended_implies_pending". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.suspension.suspended_implies_not_backlogged". Abort.
Check @prosa.analysis.facts.suspension.suspended_implies_not_backlogged.
Goal True. idtac "END|prosa.analysis.facts.suspension.suspended_implies_not_backlogged". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.suspension.pending_and_not_suspended_implies_ready". Abort.
Check @prosa.analysis.facts.suspension.pending_and_not_suspended_implies_ready.
Goal True. idtac "END|prosa.analysis.facts.suspension.pending_and_not_suspended_implies_ready". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.suspension.suspension_bounded_trivial". Abort.
Check @prosa.analysis.facts.suspension.suspension_bounded_trivial.
Goal True. idtac "END|prosa.analysis.facts.suspension.suspension_bounded_trivial". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.suspension.suspension_bounded_longer_interval". Abort.
Check @prosa.analysis.facts.suspension.suspension_bounded_longer_interval.
Goal True. idtac "END|prosa.analysis.facts.suspension.suspension_bounded_longer_interval". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.suspension.suspension_bounded_in_interval_aux". Abort.
Check @prosa.analysis.facts.suspension.suspension_bounded_in_interval_aux.
Goal True. idtac "END|prosa.analysis.facts.suspension.suspension_bounded_in_interval_aux". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.suspension.exists_some_point". Abort.
Check @prosa.analysis.facts.suspension.exists_some_point.
Goal True. idtac "END|prosa.analysis.facts.suspension.exists_some_point". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.suspension.suspension_bounded_in_interval". Abort.
Check @prosa.analysis.facts.suspension.suspension_bounded_in_interval.
Goal True. idtac "END|prosa.analysis.facts.suspension.suspension_bounded_in_interval". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.tdma.TDMA_cycle_ge_each_time_slot". Abort.
Check @prosa.analysis.facts.tdma.TDMA_cycle_ge_each_time_slot.
Goal True. idtac "END|prosa.analysis.facts.tdma.TDMA_cycle_ge_each_time_slot". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.tdma.TDMA_cycle_positive". Abort.
Check @prosa.analysis.facts.tdma.TDMA_cycle_positive.
Goal True. idtac "END|prosa.analysis.facts.tdma.TDMA_cycle_positive". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.tdma.Offset_lt_cycle". Abort.
Check @prosa.analysis.facts.tdma.Offset_lt_cycle.
Goal True. idtac "END|prosa.analysis.facts.tdma.Offset_lt_cycle". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.tdma.Offset_add_slot_leq_cycle". Abort.
Check @prosa.analysis.facts.tdma.Offset_add_slot_leq_cycle.
Goal True. idtac "END|prosa.analysis.facts.tdma.Offset_add_slot_leq_cycle". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.tdma.relation_offset". Abort.
Check @prosa.analysis.facts.tdma.relation_offset.
Goal True. idtac "END|prosa.analysis.facts.tdma.relation_offset". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.tdma.task_in_time_slot_uniq". Abort.
Check @prosa.analysis.facts.tdma.task_in_time_slot_uniq.
Goal True. idtac "END|prosa.analysis.facts.tdma.task_in_time_slot_uniq". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.transform.edf_opt.t1_relevant". Abort.
Check @prosa.analysis.facts.transform.edf_opt.t1_relevant.
Goal True. idtac "END|prosa.analysis.facts.transform.edf_opt.t1_relevant". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.transform.edf_opt.fsc_search_successful". Abort.
Check @prosa.analysis.facts.transform.edf_opt.fsc_search_successful.
Goal True. idtac "END|prosa.analysis.facts.transform.edf_opt.fsc_search_successful". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.transform.edf_opt.fsc_search_result". Abort.
Check @prosa.analysis.facts.transform.edf_opt.fsc_search_result.
Goal True. idtac "END|prosa.analysis.facts.transform.edf_opt.fsc_search_result". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.transform.edf_opt.fsc_not_idle". Abort.
Check @prosa.analysis.facts.transform.edf_opt.fsc_not_idle.
Goal True. idtac "END|prosa.analysis.facts.transform.edf_opt.fsc_not_idle". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.transform.edf_opt.fsc_found_job_arrival". Abort.
Check @prosa.analysis.facts.transform.edf_opt.fsc_found_job_arrival.
Goal True. idtac "END|prosa.analysis.facts.transform.edf_opt.fsc_found_job_arrival". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.transform.edf_opt.fsc_range". Abort.
Check @prosa.analysis.facts.transform.edf_opt.fsc_range.
Goal True. idtac "END|prosa.analysis.facts.transform.edf_opt.fsc_range". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.transform.edf_opt.fsc_range1". Abort.
Check @prosa.analysis.facts.transform.edf_opt.fsc_range1.
Goal True. idtac "END|prosa.analysis.facts.transform.edf_opt.fsc_range1". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.transform.edf_opt.fsc_found_job_deadline". Abort.
Check @prosa.analysis.facts.transform.edf_opt.fsc_found_job_deadline.
Goal True. idtac "END|prosa.analysis.facts.transform.edf_opt.fsc_found_job_deadline". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.transform.edf_opt.fsc_no_later_deadline". Abort.
Check @prosa.analysis.facts.transform.edf_opt.fsc_no_later_deadline.
Goal True. idtac "END|prosa.analysis.facts.transform.edf_opt.fsc_no_later_deadline". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.transform.edf_opt.scheduled_job_in_sched_has_later_deadline". Abort.
Check @prosa.analysis.facts.transform.edf_opt.scheduled_job_in_sched_has_later_deadline.
Goal True. idtac "END|prosa.analysis.facts.transform.edf_opt.scheduled_job_in_sched_has_later_deadline". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.transform.edf_opt.mea_completed_jobs". Abort.
Check @prosa.analysis.facts.transform.edf_opt.mea_completed_jobs.
Goal True. idtac "END|prosa.analysis.facts.transform.edf_opt.mea_completed_jobs". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.transform.edf_opt.mea_no_deadline_misses". Abort.
Check @prosa.analysis.facts.transform.edf_opt.mea_no_deadline_misses.
Goal True. idtac "END|prosa.analysis.facts.transform.edf_opt.mea_no_deadline_misses". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.transform.edf_opt.mea_scheduled_job_has_later_deadline". Abort.
Check @prosa.analysis.facts.transform.edf_opt.mea_scheduled_job_has_later_deadline.
Goal True. idtac "END|prosa.analysis.facts.transform.edf_opt.mea_scheduled_job_has_later_deadline". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.transform.edf_opt.mea_guarantee_dl_orig". Abort.
Check @prosa.analysis.facts.transform.edf_opt.mea_guarantee_dl_orig.
Goal True. idtac "END|prosa.analysis.facts.transform.edf_opt.mea_guarantee_dl_orig". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.transform.edf_opt.mea_guarantee_fsc_is_j_edf". Abort.
Check @prosa.analysis.facts.transform.edf_opt.mea_guarantee_fsc_is_j_edf.
Goal True. idtac "END|prosa.analysis.facts.transform.edf_opt.mea_guarantee_fsc_is_j_edf". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.transform.edf_opt.mea_guarantee_deadlines". Abort.
Check @prosa.analysis.facts.transform.edf_opt.mea_guarantee_deadlines.
Goal True. idtac "END|prosa.analysis.facts.transform.edf_opt.mea_guarantee_deadlines". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.transform.edf_opt.mea_guarantee_case_t'_past_deadline". Abort.
Check @prosa.analysis.facts.transform.edf_opt.mea_guarantee_case_t'_past_deadline.
Goal True. idtac "END|prosa.analysis.facts.transform.edf_opt.mea_guarantee_case_t'_past_deadline". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.transform.edf_opt.mea_guarantee_case_t'_before_deadline". Abort.
Check @prosa.analysis.facts.transform.edf_opt.mea_guarantee_case_t'_before_deadline.
Goal True. idtac "END|prosa.analysis.facts.transform.edf_opt.mea_guarantee_case_t'_before_deadline". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.transform.edf_opt.make_edf_at_guarantee". Abort.
Check @prosa.analysis.facts.transform.edf_opt.make_edf_at_guarantee.
Goal True. idtac "END|prosa.analysis.facts.transform.edf_opt.make_edf_at_guarantee". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.transform.edf_opt.mea_jobs_must_arrive". Abort.
Check @prosa.analysis.facts.transform.edf_opt.mea_jobs_must_arrive.
Goal True. idtac "END|prosa.analysis.facts.transform.edf_opt.mea_jobs_must_arrive". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.transform.edf_opt.mea_job_scheduled". Abort.
Check @prosa.analysis.facts.transform.edf_opt.mea_job_scheduled.
Goal True. idtac "END|prosa.analysis.facts.transform.edf_opt.mea_job_scheduled". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.transform.edf_opt.mea_job_scheduled'". Abort.
Check @prosa.analysis.facts.transform.edf_opt.mea_job_scheduled'.
Goal True. idtac "END|prosa.analysis.facts.transform.edf_opt.mea_job_scheduled'". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.transform.edf_opt.mea_jobs_come_from_arrival_sequence". Abort.
Check @prosa.analysis.facts.transform.edf_opt.mea_jobs_come_from_arrival_sequence.
Goal True. idtac "END|prosa.analysis.facts.transform.edf_opt.mea_jobs_come_from_arrival_sequence". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.transform.edf_opt.mea_EDF_widen". Abort.
Check @prosa.analysis.facts.transform.edf_opt.mea_EDF_widen.
Goal True. idtac "END|prosa.analysis.facts.transform.edf_opt.mea_EDF_widen". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.transform.edf_opt.edf_prefix_well_formedness". Abort.
Check @prosa.analysis.facts.transform.edf_opt.edf_prefix_well_formedness.
Goal True. idtac "END|prosa.analysis.facts.transform.edf_opt.edf_prefix_well_formedness". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.transform.edf_opt.edf_prefix_jobs_must_arrive". Abort.
Check @prosa.analysis.facts.transform.edf_opt.edf_prefix_jobs_must_arrive.
Goal True. idtac "END|prosa.analysis.facts.transform.edf_opt.edf_prefix_jobs_must_arrive". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.transform.edf_opt.edf_prefix_scheduled_job_has_later_deadline". Abort.
Check @prosa.analysis.facts.transform.edf_opt.edf_prefix_scheduled_job_has_later_deadline.
Goal True. idtac "END|prosa.analysis.facts.transform.edf_opt.edf_prefix_scheduled_job_has_later_deadline". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.transform.edf_opt.edf_prefix_job_scheduled". Abort.
Check @prosa.analysis.facts.transform.edf_opt.edf_prefix_job_scheduled.
Goal True. idtac "END|prosa.analysis.facts.transform.edf_opt.edf_prefix_job_scheduled". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.transform.edf_opt.edf_prefix_job_scheduled'". Abort.
Check @prosa.analysis.facts.transform.edf_opt.edf_prefix_job_scheduled'.
Goal True. idtac "END|prosa.analysis.facts.transform.edf_opt.edf_prefix_job_scheduled'". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.transform.edf_opt.edf_prefix_jobs_come_from_arrival_sequence". Abort.
Check @prosa.analysis.facts.transform.edf_opt.edf_prefix_jobs_come_from_arrival_sequence.
Goal True. idtac "END|prosa.analysis.facts.transform.edf_opt.edf_prefix_jobs_come_from_arrival_sequence". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.transform.edf_opt.edf_prefix_guarantee". Abort.
Check @prosa.analysis.facts.transform.edf_opt.edf_prefix_guarantee.
Goal True. idtac "END|prosa.analysis.facts.transform.edf_opt.edf_prefix_guarantee". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.transform.edf_opt.edf_prefix_inclusion". Abort.
Check @prosa.analysis.facts.transform.edf_opt.edf_prefix_inclusion.
Goal True. idtac "END|prosa.analysis.facts.transform.edf_opt.edf_prefix_inclusion". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.transform.edf_opt.edf_finite_prefix". Abort.
Check @prosa.analysis.facts.transform.edf_opt.edf_finite_prefix.
Goal True. idtac "END|prosa.analysis.facts.transform.edf_opt.edf_finite_prefix". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.transform.edf_opt.edf_transform_ensures_edf". Abort.
Check @prosa.analysis.facts.transform.edf_opt.edf_transform_ensures_edf.
Goal True. idtac "END|prosa.analysis.facts.transform.edf_opt.edf_transform_ensures_edf". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.transform.edf_opt.edf_transform_completed_jobs_dont_execute". Abort.
Check @prosa.analysis.facts.transform.edf_opt.edf_transform_completed_jobs_dont_execute.
Goal True. idtac "END|prosa.analysis.facts.transform.edf_opt.edf_transform_completed_jobs_dont_execute". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.transform.edf_opt.edf_transform_jobs_must_arrive". Abort.
Check @prosa.analysis.facts.transform.edf_opt.edf_transform_jobs_must_arrive.
Goal True. idtac "END|prosa.analysis.facts.transform.edf_opt.edf_transform_jobs_must_arrive". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.transform.edf_opt.edf_transform_deadlines_met". Abort.
Check @prosa.analysis.facts.transform.edf_opt.edf_transform_deadlines_met.
Goal True. idtac "END|prosa.analysis.facts.transform.edf_opt.edf_transform_deadlines_met". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.transform.edf_opt.edf_transform_job_scheduled". Abort.
Check @prosa.analysis.facts.transform.edf_opt.edf_transform_job_scheduled.
Goal True. idtac "END|prosa.analysis.facts.transform.edf_opt.edf_transform_job_scheduled". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.transform.edf_opt.edf_transform_job_scheduled'". Abort.
Check @prosa.analysis.facts.transform.edf_opt.edf_transform_job_scheduled'.
Goal True. idtac "END|prosa.analysis.facts.transform.edf_opt.edf_transform_job_scheduled'". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.transform.edf_opt.edf_transform_jobs_come_from_arrival_sequence". Abort.
Check @prosa.analysis.facts.transform.edf_opt.edf_transform_jobs_come_from_arrival_sequence.
Goal True. idtac "END|prosa.analysis.facts.transform.edf_opt.edf_transform_jobs_come_from_arrival_sequence". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.transform.edf_opt.edf_schedule_is_valid". Abort.
Check @prosa.analysis.facts.transform.edf_opt.edf_schedule_is_valid.
Goal True. idtac "END|prosa.analysis.facts.transform.edf_opt.edf_schedule_is_valid". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.transform.edf_opt.edf_schedule_meets_all_deadlines". Abort.
Check @prosa.analysis.facts.transform.edf_opt.edf_schedule_meets_all_deadlines.
Goal True. idtac "END|prosa.analysis.facts.transform.edf_opt.edf_schedule_meets_all_deadlines". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.transform.edf_opt.edf_schedule_meets_all_deadlines_wrt_arrivals". Abort.
Check @prosa.analysis.facts.transform.edf_opt.edf_schedule_meets_all_deadlines_wrt_arrivals.
Goal True. idtac "END|prosa.analysis.facts.transform.edf_opt.edf_schedule_meets_all_deadlines_wrt_arrivals". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.transform.edf_wc.non_idle_swap_maintains_work_conservation_t1". Abort.
Check @prosa.analysis.facts.transform.edf_wc.non_idle_swap_maintains_work_conservation_t1.
Goal True. idtac "END|prosa.analysis.facts.transform.edf_wc.non_idle_swap_maintains_work_conservation_t1". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.transform.edf_wc.non_idle_swap_maintains_work_conservation_t2". Abort.
Check @prosa.analysis.facts.transform.edf_wc.non_idle_swap_maintains_work_conservation_t2.
Goal True. idtac "END|prosa.analysis.facts.transform.edf_wc.non_idle_swap_maintains_work_conservation_t2". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.transform.edf_wc.non_idle_swap_maintains_work_conservation_LEQ_t1". Abort.
Check @prosa.analysis.facts.transform.edf_wc.non_idle_swap_maintains_work_conservation_LEQ_t1.
Goal True. idtac "END|prosa.analysis.facts.transform.edf_wc.non_idle_swap_maintains_work_conservation_LEQ_t1". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.transform.edf_wc.non_idle_swap_maintains_work_conservation_GT_t2". Abort.
Check @prosa.analysis.facts.transform.edf_wc.non_idle_swap_maintains_work_conservation_GT_t2.
Goal True. idtac "END|prosa.analysis.facts.transform.edf_wc.non_idle_swap_maintains_work_conservation_GT_t2". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.transform.edf_wc.non_idle_swap_maintains_work_conservation_BET_t1_t2". Abort.
Check @prosa.analysis.facts.transform.edf_wc.non_idle_swap_maintains_work_conservation_BET_t1_t2.
Goal True. idtac "END|prosa.analysis.facts.transform.edf_wc.non_idle_swap_maintains_work_conservation_BET_t1_t2". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.transform.edf_wc.fsc_swap_maintains_work_conservation". Abort.
Check @prosa.analysis.facts.transform.edf_wc.fsc_swap_maintains_work_conservation.
Goal True. idtac "END|prosa.analysis.facts.transform.edf_wc.fsc_swap_maintains_work_conservation". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.transform.edf_wc.mea_maintains_work_conservation". Abort.
Check @prosa.analysis.facts.transform.edf_wc.mea_maintains_work_conservation.
Goal True. idtac "END|prosa.analysis.facts.transform.edf_wc.mea_maintains_work_conservation". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.transform.edf_wc.scheduled_behavior_premises". Abort.
Check @prosa.analysis.facts.transform.edf_wc.scheduled_behavior_premises.
Goal True. idtac "END|prosa.analysis.facts.transform.edf_wc.scheduled_behavior_premises". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.transform.edf_wc.edf_transform_prefix_maintains_work_conservation". Abort.
Check @prosa.analysis.facts.transform.edf_wc.edf_transform_prefix_maintains_work_conservation.
Goal True. idtac "END|prosa.analysis.facts.transform.edf_wc.edf_transform_prefix_maintains_work_conservation". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.transform.edf_wc.sched_satisfies_behavior_premises". Abort.
Check @prosa.analysis.facts.transform.edf_wc.sched_satisfies_behavior_premises.
Goal True. idtac "END|prosa.analysis.facts.transform.edf_wc.sched_satisfies_behavior_premises". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.transform.edf_wc.edf_transform_maintains_work_conservation". Abort.
Check @prosa.analysis.facts.transform.edf_wc.edf_transform_maintains_work_conservation.
Goal True. idtac "END|prosa.analysis.facts.transform.edf_wc.edf_transform_maintains_work_conservation". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.transform.replace_at.replace_at_def". Abort.
Check @prosa.analysis.facts.transform.replace_at.replace_at_def.
Goal True. idtac "END|prosa.analysis.facts.transform.replace_at.replace_at_def". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.transform.replace_at.rest_of_schedule_invariant". Abort.
Check @prosa.analysis.facts.transform.replace_at.rest_of_schedule_invariant.
Goal True. idtac "END|prosa.analysis.facts.transform.replace_at.rest_of_schedule_invariant". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.transform.replace_at.service_at_other_times_invariant". Abort.
Check @prosa.analysis.facts.transform.replace_at.service_at_other_times_invariant.
Goal True. idtac "END|prosa.analysis.facts.transform.replace_at.service_at_other_times_invariant". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.transform.replace_at.service_delta". Abort.
Check @prosa.analysis.facts.transform.replace_at.service_delta.
Goal True. idtac "END|prosa.analysis.facts.transform.replace_at.service_delta". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.transform.replace_at.service_in_replaced". Abort.
Check @prosa.analysis.facts.transform.replace_at.service_in_replaced.
Goal True. idtac "END|prosa.analysis.facts.transform.replace_at.service_in_replaced". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.transform.replace_at.service_at_of_others_invariant". Abort.
Check @prosa.analysis.facts.transform.replace_at.service_at_of_others_invariant.
Goal True. idtac "END|prosa.analysis.facts.transform.replace_at.service_at_of_others_invariant". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.transform.replace_at.service_during_of_others_invariant". Abort.
Check @prosa.analysis.facts.transform.replace_at.service_during_of_others_invariant.
Goal True. idtac "END|prosa.analysis.facts.transform.replace_at.service_during_of_others_invariant". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.transform.swaps.trivial_swap". Abort.
Check @prosa.analysis.facts.transform.swaps.trivial_swap.
Goal True. idtac "END|prosa.analysis.facts.transform.swaps.trivial_swap". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.transform.swaps.trivial_swap_service_invariant". Abort.
Check @prosa.analysis.facts.transform.swaps.trivial_swap_service_invariant.
Goal True. idtac "END|prosa.analysis.facts.transform.swaps.trivial_swap_service_invariant". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.transform.swaps.swap_other_times_invariant". Abort.
Check @prosa.analysis.facts.transform.swaps.swap_other_times_invariant.
Goal True. idtac "END|prosa.analysis.facts.transform.swaps.swap_other_times_invariant". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.transform.swaps.swap_job_scheduled_t1". Abort.
Check @prosa.analysis.facts.transform.swaps.swap_job_scheduled_t1.
Goal True. idtac "END|prosa.analysis.facts.transform.swaps.swap_job_scheduled_t1". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.transform.swaps.swap_job_scheduled_t2". Abort.
Check @prosa.analysis.facts.transform.swaps.swap_job_scheduled_t2.
Goal True. idtac "END|prosa.analysis.facts.transform.swaps.swap_job_scheduled_t2". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.transform.swaps.swap_job_scheduled_other_times". Abort.
Check @prosa.analysis.facts.transform.swaps.swap_job_scheduled_other_times.
Goal True. idtac "END|prosa.analysis.facts.transform.swaps.swap_job_scheduled_other_times". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.transform.swaps.swap_job_scheduled_cases". Abort.
Check @prosa.analysis.facts.transform.swaps.swap_job_scheduled_cases.
Goal True. idtac "END|prosa.analysis.facts.transform.swaps.swap_job_scheduled_cases". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.transform.swaps.swap_job_scheduled". Abort.
Check @prosa.analysis.facts.transform.swaps.swap_job_scheduled.
Goal True. idtac "END|prosa.analysis.facts.transform.swaps.swap_job_scheduled". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.transform.swaps.swap_job_scheduled_original_cases". Abort.
Check @prosa.analysis.facts.transform.swaps.swap_job_scheduled_original_cases.
Goal True. idtac "END|prosa.analysis.facts.transform.swaps.swap_job_scheduled_original_cases". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.transform.swaps.swap_job_scheduled_original". Abort.
Check @prosa.analysis.facts.transform.swaps.swap_job_scheduled_original.
Goal True. idtac "END|prosa.analysis.facts.transform.swaps.swap_job_scheduled_original". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.transform.swaps.swap_before_invariant". Abort.
Check @prosa.analysis.facts.transform.swaps.swap_before_invariant.
Goal True. idtac "END|prosa.analysis.facts.transform.swaps.swap_before_invariant". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.transform.swaps.swap_after_invariant". Abort.
Check @prosa.analysis.facts.transform.swaps.swap_after_invariant.
Goal True. idtac "END|prosa.analysis.facts.transform.swaps.swap_after_invariant". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.transform.swaps.service_before_swap_invariant". Abort.
Check @prosa.analysis.facts.transform.swaps.service_before_swap_invariant.
Goal True. idtac "END|prosa.analysis.facts.transform.swaps.service_before_swap_invariant". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.transform.swaps.service_after_swap_invariant". Abort.
Check @prosa.analysis.facts.transform.swaps.service_after_swap_invariant.
Goal True. idtac "END|prosa.analysis.facts.transform.swaps.service_after_swap_invariant". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.transform.swaps.service_of_others_invariant". Abort.
Check @prosa.analysis.facts.transform.swaps.service_of_others_invariant.
Goal True. idtac "END|prosa.analysis.facts.transform.swaps.service_of_others_invariant". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.transform.swaps.swapped_service_bound". Abort.
Check @prosa.analysis.facts.transform.swaps.swapped_service_bound.
Goal True. idtac "END|prosa.analysis.facts.transform.swaps.swapped_service_bound". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.transform.swaps.swapped_completed_jobs_dont_execute". Abort.
Check @prosa.analysis.facts.transform.swaps.swapped_completed_jobs_dont_execute.
Goal True. idtac "END|prosa.analysis.facts.transform.swaps.swapped_completed_jobs_dont_execute". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.transform.swaps.swapped_jobs_come_from_arrival_sequence". Abort.
Check @prosa.analysis.facts.transform.swaps.swapped_jobs_come_from_arrival_sequence.
Goal True. idtac "END|prosa.analysis.facts.transform.swaps.swapped_jobs_come_from_arrival_sequence". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.transform.swaps.uninvolved_implies_deadline_met". Abort.
Check @prosa.analysis.facts.transform.swaps.uninvolved_implies_deadline_met.
Goal True. idtac "END|prosa.analysis.facts.transform.swaps.uninvolved_implies_deadline_met". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.transform.swaps.moved_earlier_implies_deadline_met". Abort.
Check @prosa.analysis.facts.transform.swaps.moved_earlier_implies_deadline_met.
Goal True. idtac "END|prosa.analysis.facts.transform.swaps.moved_earlier_implies_deadline_met". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.transform.swaps.moved_later_implies_deadline_met". Abort.
Check @prosa.analysis.facts.transform.swaps.moved_later_implies_deadline_met.
Goal True. idtac "END|prosa.analysis.facts.transform.swaps.moved_later_implies_deadline_met". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.transform.swaps.edf_swap_no_deadline_misses_introduced". Abort.
Check @prosa.analysis.facts.transform.swaps.edf_swap_no_deadline_misses_introduced.
Goal True. idtac "END|prosa.analysis.facts.transform.swaps.edf_swap_no_deadline_misses_introduced". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.transform.wc_correctness.is_work_conserving_at". Abort.
Check @prosa.analysis.facts.transform.wc_correctness.is_work_conserving_at.
Goal True. idtac "END|prosa.analysis.facts.transform.wc_correctness.is_work_conserving_at". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.transform.wc_correctness.swap_candidate_is_in_future". Abort.
Check @prosa.analysis.facts.transform.wc_correctness.swap_candidate_is_in_future.
Goal True. idtac "END|prosa.analysis.facts.transform.wc_correctness.swap_candidate_is_in_future". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.transform.wc_correctness.fsc_respects_has_arrived". Abort.
Check @prosa.analysis.facts.transform.wc_correctness.fsc_respects_has_arrived.
Goal True. idtac "END|prosa.analysis.facts.transform.wc_correctness.fsc_respects_has_arrived". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.transform.wc_correctness.swap_jobs_must_arrive_to_execute". Abort.
Check @prosa.analysis.facts.transform.wc_correctness.swap_jobs_must_arrive_to_execute.
Goal True. idtac "END|prosa.analysis.facts.transform.wc_correctness.swap_jobs_must_arrive_to_execute". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.transform.wc_correctness.fsc_jobs_must_be_ready_to_execute". Abort.
Check @prosa.analysis.facts.transform.wc_correctness.fsc_jobs_must_be_ready_to_execute.
Goal True. idtac "END|prosa.analysis.facts.transform.wc_correctness.fsc_jobs_must_be_ready_to_execute". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.transform.wc_correctness.mwa_service_bound". Abort.
Check @prosa.analysis.facts.transform.wc_correctness.mwa_service_bound.
Goal True. idtac "END|prosa.analysis.facts.transform.wc_correctness.mwa_service_bound". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.transform.wc_correctness.mwa_ready_job_also_ready_in_original_schedule". Abort.
Check @prosa.analysis.facts.transform.wc_correctness.mwa_ready_job_also_ready_in_original_schedule.
Goal True. idtac "END|prosa.analysis.facts.transform.wc_correctness.mwa_ready_job_also_ready_in_original_schedule". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.transform.wc_correctness.max_dl_is_greatest_dl". Abort.
Check @prosa.analysis.facts.transform.wc_correctness.max_dl_is_greatest_dl.
Goal True. idtac "END|prosa.analysis.facts.transform.wc_correctness.max_dl_is_greatest_dl". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.transform.wc_correctness.order". Abort.
Check @prosa.analysis.facts.transform.wc_correctness.order.
Goal True. idtac "END|prosa.analysis.facts.transform.wc_correctness.order". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.transform.wc_correctness.search_result". Abort.
Check @prosa.analysis.facts.transform.wc_correctness.search_result.
Goal True. idtac "END|prosa.analysis.facts.transform.wc_correctness.search_result". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.transform.wc_correctness.make_wc_at_case_result_found". Abort.
Check @prosa.analysis.facts.transform.wc_correctness.make_wc_at_case_result_found.
Goal True. idtac "END|prosa.analysis.facts.transform.wc_correctness.make_wc_at_case_result_found". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.transform.wc_correctness.no_relevant_state_in_range". Abort.
Check @prosa.analysis.facts.transform.wc_correctness.no_relevant_state_in_range.
Goal True. idtac "END|prosa.analysis.facts.transform.wc_correctness.no_relevant_state_in_range". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.transform.wc_correctness.service_of_j_is_less_than_cost". Abort.
Check @prosa.analysis.facts.transform.wc_correctness.service_of_j_is_less_than_cost.
Goal True. idtac "END|prosa.analysis.facts.transform.wc_correctness.service_of_j_is_less_than_cost". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.transform.wc_correctness.t_is_less_than_deadline_of_j". Abort.
Check @prosa.analysis.facts.transform.wc_correctness.t_is_less_than_deadline_of_j.
Goal True. idtac "END|prosa.analysis.facts.transform.wc_correctness.t_is_less_than_deadline_of_j". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.transform.wc_correctness.equal_service_t_max_dl". Abort.
Check @prosa.analysis.facts.transform.wc_correctness.equal_service_t_max_dl.
Goal True. idtac "END|prosa.analysis.facts.transform.wc_correctness.equal_service_t_max_dl". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.transform.wc_correctness.j_misses_deadline". Abort.
Check @prosa.analysis.facts.transform.wc_correctness.j_misses_deadline.
Goal True. idtac "END|prosa.analysis.facts.transform.wc_correctness.j_misses_deadline". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.transform.wc_correctness.make_wc_at_case_result_none". Abort.
Check @prosa.analysis.facts.transform.wc_correctness.make_wc_at_case_result_none.
Goal True. idtac "END|prosa.analysis.facts.transform.wc_correctness.make_wc_at_case_result_none". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.transform.wc_correctness.mwa_finds_ready_jobs". Abort.
Check @prosa.analysis.facts.transform.wc_correctness.mwa_finds_ready_jobs.
Goal True. idtac "END|prosa.analysis.facts.transform.wc_correctness.mwa_finds_ready_jobs". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.transform.wc_correctness.mwa_establishes_wc". Abort.
Check @prosa.analysis.facts.transform.wc_correctness.mwa_establishes_wc.
Goal True. idtac "END|prosa.analysis.facts.transform.wc_correctness.mwa_establishes_wc". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.transform.wc_correctness.mwa_jobs_come_from_arrival_sequence". Abort.
Check @prosa.analysis.facts.transform.wc_correctness.mwa_jobs_come_from_arrival_sequence.
Goal True. idtac "END|prosa.analysis.facts.transform.wc_correctness.mwa_jobs_come_from_arrival_sequence". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.transform.wc_correctness.mwa_jobs_must_be_ready_to_execute". Abort.
Check @prosa.analysis.facts.transform.wc_correctness.mwa_jobs_must_be_ready_to_execute.
Goal True. idtac "END|prosa.analysis.facts.transform.wc_correctness.mwa_jobs_must_be_ready_to_execute". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.transform.wc_correctness.mwa_all_deadlines_of_arrivals_met". Abort.
Check @prosa.analysis.facts.transform.wc_correctness.mwa_all_deadlines_of_arrivals_met.
Goal True. idtac "END|prosa.analysis.facts.transform.wc_correctness.mwa_all_deadlines_of_arrivals_met". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.transform.wc_correctness.wc_transform_prefix_inclusion". Abort.
Check @prosa.analysis.facts.transform.wc_correctness.wc_transform_prefix_inclusion.
Goal True. idtac "END|prosa.analysis.facts.transform.wc_correctness.wc_transform_prefix_inclusion". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.transform.wc_correctness.wc_prefix_service_bound". Abort.
Check @prosa.analysis.facts.transform.wc_correctness.wc_prefix_service_bound.
Goal True. idtac "END|prosa.analysis.facts.transform.wc_correctness.wc_prefix_service_bound". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.transform.wc_correctness.wc_prefix_job_meets_deadline". Abort.
Check @prosa.analysis.facts.transform.wc_correctness.wc_prefix_job_meets_deadline.
Goal True. idtac "END|prosa.analysis.facts.transform.wc_correctness.wc_prefix_job_meets_deadline". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.transform.wc_correctness.wc_prefix_jobs_come_from_arrival_sequence". Abort.
Check @prosa.analysis.facts.transform.wc_correctness.wc_prefix_jobs_come_from_arrival_sequence.
Goal True. idtac "END|prosa.analysis.facts.transform.wc_correctness.wc_prefix_jobs_come_from_arrival_sequence". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.transform.wc_correctness.wc_prefix_jobs_must_be_ready_to_execute". Abort.
Check @prosa.analysis.facts.transform.wc_correctness.wc_prefix_jobs_must_be_ready_to_execute.
Goal True. idtac "END|prosa.analysis.facts.transform.wc_correctness.wc_prefix_jobs_must_be_ready_to_execute". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.transform.wc_correctness.wc_jobs_come_from_arrival_sequence". Abort.
Check @prosa.analysis.facts.transform.wc_correctness.wc_jobs_come_from_arrival_sequence.
Goal True. idtac "END|prosa.analysis.facts.transform.wc_correctness.wc_jobs_come_from_arrival_sequence". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.transform.wc_correctness.wc_jobs_must_be_ready_to_execute". Abort.
Check @prosa.analysis.facts.transform.wc_correctness.wc_jobs_must_be_ready_to_execute.
Goal True. idtac "END|prosa.analysis.facts.transform.wc_correctness.wc_jobs_must_be_ready_to_execute". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.transform.wc_correctness.wc_all_deadlines_of_arrivals_met". Abort.
Check @prosa.analysis.facts.transform.wc_correctness.wc_all_deadlines_of_arrivals_met.
Goal True. idtac "END|prosa.analysis.facts.transform.wc_correctness.wc_all_deadlines_of_arrivals_met". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.transform.wc_correctness.wc_is_work_conserving_at". Abort.
Check @prosa.analysis.facts.transform.wc_correctness.wc_is_work_conserving_at.
Goal True. idtac "END|prosa.analysis.facts.transform.wc_correctness.wc_is_work_conserving_at". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.transform.wc_correctness.wc_is_work_conserving". Abort.
Check @prosa.analysis.facts.transform.wc_correctness.wc_is_work_conserving.
Goal True. idtac "END|prosa.analysis.facts.transform.wc_correctness.wc_is_work_conserving". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.transform.wc_correctness.wc_transform_correctness". Abort.
Check @prosa.analysis.facts.transform.wc_correctness.wc_transform_correctness.
Goal True. idtac "END|prosa.analysis.facts.transform.wc_correctness.wc_transform_correctness". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.workload.edf_athep_bound.total_workload_shorten_range". Abort.
Check @prosa.analysis.facts.workload.edf_athep_bound.total_workload_shorten_range.
Goal True. idtac "END|prosa.analysis.facts.workload.edf_athep_bound.total_workload_shorten_range". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.workload.edf_athep_bound.sum_of_workloads_is_at_most_bound_on_total_hep_workload". Abort.
Check @prosa.analysis.facts.workload.edf_athep_bound.sum_of_workloads_is_at_most_bound_on_total_hep_workload.
Goal True. idtac "END|prosa.analysis.facts.workload.edf_athep_bound.sum_of_workloads_is_at_most_bound_on_total_hep_workload". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.workload.edf_athep_bound.bound_on_athep_workload_is_valid". Abort.
Check @prosa.analysis.facts.workload.edf_athep_bound.bound_on_athep_workload_is_valid.
Goal True. idtac "END|prosa.analysis.facts.workload.edf_athep_bound.bound_on_athep_workload_is_valid". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.workload.edf_athep_bound.bound_on_athep_workload_monotone". Abort.
Check @prosa.analysis.facts.workload.edf_athep_bound.bound_on_athep_workload_monotone.
Goal True. idtac "END|prosa.analysis.facts.workload.edf_athep_bound.bound_on_athep_workload_monotone". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.workload.elf_athep_bound.total_ep_tsk_workload_shorten_range". Abort.
Check @prosa.analysis.facts.workload.elf_athep_bound.total_ep_tsk_workload_shorten_range.
Goal True. idtac "END|prosa.analysis.facts.workload.elf_athep_bound.total_ep_tsk_workload_shorten_range". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.workload.elf_athep_bound.sum_of_ep_tsk_workloads_is_at_most_bound_on_ep_task_workload". Abort.
Check @prosa.analysis.facts.workload.elf_athep_bound.sum_of_ep_tsk_workloads_is_at_most_bound_on_ep_task_workload.
Goal True. idtac "END|prosa.analysis.facts.workload.elf_athep_bound.sum_of_ep_tsk_workloads_is_at_most_bound_on_ep_task_workload". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.workload.elf_athep_bound.sum_of_hp_tsk_workloads_is_at_most_bound_on_hp_task_workload". Abort.
Check @prosa.analysis.facts.workload.elf_athep_bound.sum_of_hp_tsk_workloads_is_at_most_bound_on_hp_task_workload.
Goal True. idtac "END|prosa.analysis.facts.workload.elf_athep_bound.sum_of_hp_tsk_workloads_is_at_most_bound_on_hp_task_workload". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.workload.elf_athep_bound.sum_of_hep_workloads_partitioned". Abort.
Check @prosa.analysis.facts.workload.elf_athep_bound.sum_of_hep_workloads_partitioned.
Goal True. idtac "END|prosa.analysis.facts.workload.elf_athep_bound.sum_of_hep_workloads_partitioned". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.workload.elf_athep_bound.sum_of_workloads_is_at_most_bound_on_total_hep_workload". Abort.
Check @prosa.analysis.facts.workload.elf_athep_bound.sum_of_workloads_is_at_most_bound_on_total_hep_workload.
Goal True. idtac "END|prosa.analysis.facts.workload.elf_athep_bound.sum_of_workloads_is_at_most_bound_on_total_hep_workload". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.workload.elf_athep_bound.bound_on_athep_workload_is_valid". Abort.
Check @prosa.analysis.facts.workload.elf_athep_bound.bound_on_athep_workload_is_valid.
Goal True. idtac "END|prosa.analysis.facts.workload.elf_athep_bound.bound_on_athep_workload_is_valid". Abort.
Goal True. idtac "BEGIN|prosa.analysis.transform.edf_trans.earlier_deadline". Abort.
Check @prosa.analysis.transform.edf_trans.earlier_deadline.
Goal True. idtac "END|prosa.analysis.transform.edf_trans.earlier_deadline". Abort.
Goal True. idtac "BEGIN|prosa.analysis.transform.edf_trans.relevant_pstate". Abort.
Check @prosa.analysis.transform.edf_trans.relevant_pstate.
Goal True. idtac "END|prosa.analysis.transform.edf_trans.relevant_pstate". Abort.
Goal True. idtac "BEGIN|prosa.analysis.transform.edf_trans.find_swap_candidate". Abort.
Check @prosa.analysis.transform.edf_trans.find_swap_candidate.
Goal True. idtac "END|prosa.analysis.transform.edf_trans.find_swap_candidate". Abort.
Goal True. idtac "BEGIN|prosa.analysis.transform.edf_trans.make_edf_at". Abort.
Check @prosa.analysis.transform.edf_trans.make_edf_at.
Goal True. idtac "END|prosa.analysis.transform.edf_trans.make_edf_at". Abort.
Goal True. idtac "BEGIN|prosa.analysis.transform.edf_trans.edf_transform_prefix". Abort.
Check @prosa.analysis.transform.edf_trans.edf_transform_prefix.
Goal True. idtac "END|prosa.analysis.transform.edf_trans.edf_transform_prefix". Abort.
Goal True. idtac "BEGIN|prosa.analysis.transform.edf_trans.edf_transform". Abort.
Check @prosa.analysis.transform.edf_trans.edf_transform.
Goal True. idtac "END|prosa.analysis.transform.edf_trans.edf_transform". Abort.
Goal True. idtac "BEGIN|prosa.analysis.transform.prefix.prefix_map". Abort.
Check @prosa.analysis.transform.prefix.prefix_map.
Goal True. idtac "END|prosa.analysis.transform.prefix.prefix_map". Abort.
Goal True. idtac "BEGIN|prosa.analysis.transform.prefix.prefix_map_property_invariance". Abort.
Check @prosa.analysis.transform.prefix.prefix_map_property_invariance.
Goal True. idtac "END|prosa.analysis.transform.prefix.prefix_map_property_invariance". Abort.
Goal True. idtac "BEGIN|prosa.analysis.transform.prefix.prefix_map_pointwise_property". Abort.
Check @prosa.analysis.transform.prefix.prefix_map_pointwise_property.
Goal True. idtac "END|prosa.analysis.transform.prefix.prefix_map_pointwise_property". Abort.
Goal True. idtac "BEGIN|prosa.analysis.transform.swap.replace_at". Abort.
Check @prosa.analysis.transform.swap.replace_at.
Goal True. idtac "END|prosa.analysis.transform.swap.replace_at". Abort.
Goal True. idtac "BEGIN|prosa.analysis.transform.swap.swapped". Abort.
Check @prosa.analysis.transform.swap.swapped.
Goal True. idtac "END|prosa.analysis.transform.swap.swapped". Abort.
Goal True. idtac "BEGIN|prosa.analysis.transform.wc_trans.relevant_pstate". Abort.
Check @prosa.analysis.transform.wc_trans.relevant_pstate.
Goal True. idtac "END|prosa.analysis.transform.wc_trans.relevant_pstate". Abort.
Goal True. idtac "BEGIN|prosa.analysis.transform.wc_trans.max_deadline_for_jobs_arrived_before". Abort.
Check @prosa.analysis.transform.wc_trans.max_deadline_for_jobs_arrived_before.
Goal True. idtac "END|prosa.analysis.transform.wc_trans.max_deadline_for_jobs_arrived_before". Abort.
Goal True. idtac "BEGIN|prosa.analysis.transform.wc_trans.find_swap_candidate". Abort.
Check @prosa.analysis.transform.wc_trans.find_swap_candidate.
Goal True. idtac "END|prosa.analysis.transform.wc_trans.find_swap_candidate". Abort.
Goal True. idtac "BEGIN|prosa.analysis.transform.wc_trans.make_wc_at". Abort.
Check @prosa.analysis.transform.wc_trans.make_wc_at.
Goal True. idtac "END|prosa.analysis.transform.wc_trans.make_wc_at". Abort.
Goal True. idtac "BEGIN|prosa.analysis.transform.wc_trans.wc_transform_prefix". Abort.
Check @prosa.analysis.transform.wc_trans.wc_transform_prefix.
Goal True. idtac "END|prosa.analysis.transform.wc_trans.wc_transform_prefix". Abort.
Goal True. idtac "BEGIN|prosa.analysis.transform.wc_trans.wc_transform". Abort.
Check @prosa.analysis.transform.wc_trans.wc_transform.
Goal True. idtac "END|prosa.analysis.transform.wc_trans.wc_transform". Abort.
Goal True. idtac "BEGIN|prosa.behavior.arrival_sequence.arrival_sequence". Abort.
Check @prosa.behavior.arrival_sequence.arrival_sequence.
Goal True. idtac "END|prosa.behavior.arrival_sequence.arrival_sequence". Abort.
Goal True. idtac "BEGIN|prosa.behavior.arrival_sequence.arrivals_at". Abort.
Check @prosa.behavior.arrival_sequence.arrivals_at.
Goal True. idtac "END|prosa.behavior.arrival_sequence.arrivals_at". Abort.
Goal True. idtac "BEGIN|prosa.behavior.arrival_sequence.arrives_at". Abort.
Check @prosa.behavior.arrival_sequence.arrives_at.
Goal True. idtac "END|prosa.behavior.arrival_sequence.arrives_at". Abort.
Goal True. idtac "BEGIN|prosa.behavior.arrival_sequence.arrives_in". Abort.
Check @prosa.behavior.arrival_sequence.arrives_in.
Goal True. idtac "END|prosa.behavior.arrival_sequence.arrives_in". Abort.
Goal True. idtac "BEGIN|prosa.behavior.arrival_sequence.consistent_arrival_times". Abort.
Check @prosa.behavior.arrival_sequence.consistent_arrival_times.
Goal True. idtac "END|prosa.behavior.arrival_sequence.consistent_arrival_times". Abort.
Goal True. idtac "BEGIN|prosa.behavior.arrival_sequence.arrival_sequence_uniq". Abort.
Check @prosa.behavior.arrival_sequence.arrival_sequence_uniq.
Goal True. idtac "END|prosa.behavior.arrival_sequence.arrival_sequence_uniq". Abort.
Goal True. idtac "BEGIN|prosa.behavior.arrival_sequence.valid_arrival_sequence". Abort.
Check @prosa.behavior.arrival_sequence.valid_arrival_sequence.
Goal True. idtac "END|prosa.behavior.arrival_sequence.valid_arrival_sequence". Abort.
Goal True. idtac "BEGIN|prosa.behavior.arrival_sequence.has_arrived". Abort.
Check @prosa.behavior.arrival_sequence.has_arrived.
Goal True. idtac "END|prosa.behavior.arrival_sequence.has_arrived". Abort.
Goal True. idtac "BEGIN|prosa.behavior.arrival_sequence.arrived_before". Abort.
Check @prosa.behavior.arrival_sequence.arrived_before.
Goal True. idtac "END|prosa.behavior.arrival_sequence.arrived_before". Abort.
Goal True. idtac "BEGIN|prosa.behavior.arrival_sequence.arrived_between". Abort.
Check @prosa.behavior.arrival_sequence.arrived_between.
Goal True. idtac "END|prosa.behavior.arrival_sequence.arrived_between". Abort.
Goal True. idtac "BEGIN|prosa.behavior.arrival_sequence.arrivals_between". Abort.
Check @prosa.behavior.arrival_sequence.arrivals_between.
Goal True. idtac "END|prosa.behavior.arrival_sequence.arrivals_between". Abort.
Goal True. idtac "BEGIN|prosa.behavior.arrival_sequence.arrivals_up_to". Abort.
Check @prosa.behavior.arrival_sequence.arrivals_up_to.
Goal True. idtac "END|prosa.behavior.arrival_sequence.arrivals_up_to". Abort.
Goal True. idtac "BEGIN|prosa.behavior.arrival_sequence.arrivals_before". Abort.
Check @prosa.behavior.arrival_sequence.arrivals_before.
Goal True. idtac "END|prosa.behavior.arrival_sequence.arrivals_before". Abort.
Goal True. idtac "BEGIN|prosa.behavior.arrival_sequence.arrivals_between_P". Abort.
Check @prosa.behavior.arrival_sequence.arrivals_between_P.
Goal True. idtac "END|prosa.behavior.arrival_sequence.arrivals_between_P". Abort.
Goal True. idtac "BEGIN|prosa.behavior.job.JobType". Abort.
Check @prosa.behavior.job.JobType.
Goal True. idtac "END|prosa.behavior.job.JobType". Abort.
Goal True. idtac "BEGIN|prosa.behavior.job.work". Abort.
Check @prosa.behavior.job.work.
Goal True. idtac "END|prosa.behavior.job.work". Abort.
Goal True. idtac "BEGIN|prosa.behavior.job.JobCost". Abort.
Check @prosa.behavior.job.JobCost.
Goal True. idtac "END|prosa.behavior.job.JobCost". Abort.
Goal True. idtac "BEGIN|prosa.behavior.job.JobArrival". Abort.
Check @prosa.behavior.job.JobArrival.
Goal True. idtac "END|prosa.behavior.job.JobArrival". Abort.
Goal True. idtac "BEGIN|prosa.behavior.job.JobDeadline". Abort.
Check @prosa.behavior.job.JobDeadline.
Goal True. idtac "END|prosa.behavior.job.JobDeadline". Abort.
Goal True. idtac "BEGIN|prosa.behavior.ready.JobReady". Abort.
Check @prosa.behavior.ready.JobReady.
Goal True. idtac "END|prosa.behavior.ready.JobReady". Abort.
Goal True. idtac "BEGIN|prosa.behavior.ready.backlogged". Abort.
Check @prosa.behavior.ready.backlogged.
Goal True. idtac "END|prosa.behavior.ready.backlogged". Abort.
Goal True. idtac "BEGIN|prosa.behavior.ready.jobs_come_from_arrival_sequence". Abort.
Check @prosa.behavior.ready.jobs_come_from_arrival_sequence.
Goal True. idtac "END|prosa.behavior.ready.jobs_come_from_arrival_sequence". Abort.
Goal True. idtac "BEGIN|prosa.behavior.ready.jobs_must_arrive_to_execute". Abort.
Check @prosa.behavior.ready.jobs_must_arrive_to_execute.
Goal True. idtac "END|prosa.behavior.ready.jobs_must_arrive_to_execute". Abort.
Goal True. idtac "BEGIN|prosa.behavior.ready.jobs_must_be_ready_to_execute". Abort.
Check @prosa.behavior.ready.jobs_must_be_ready_to_execute.
Goal True. idtac "END|prosa.behavior.ready.jobs_must_be_ready_to_execute". Abort.
Goal True. idtac "BEGIN|prosa.behavior.ready.completed_jobs_dont_execute". Abort.
Check @prosa.behavior.ready.completed_jobs_dont_execute.
Goal True. idtac "END|prosa.behavior.ready.completed_jobs_dont_execute". Abort.
Goal True. idtac "BEGIN|prosa.behavior.ready.valid_schedule". Abort.
Check @prosa.behavior.ready.valid_schedule.
Goal True. idtac "END|prosa.behavior.ready.valid_schedule". Abort.
Goal True. idtac "BEGIN|prosa.behavior.schedule.ProcessorState". Abort.
Check @prosa.behavior.schedule.ProcessorState.
Goal True. idtac "END|prosa.behavior.schedule.ProcessorState". Abort.
Goal True. idtac "BEGIN|prosa.behavior.schedule.scheduled_in". Abort.
Check @prosa.behavior.schedule.scheduled_in.
Goal True. idtac "END|prosa.behavior.schedule.scheduled_in". Abort.
Goal True. idtac "BEGIN|prosa.behavior.schedule.supply_in". Abort.
Check @prosa.behavior.schedule.supply_in.
Goal True. idtac "END|prosa.behavior.schedule.supply_in". Abort.
Goal True. idtac "BEGIN|prosa.behavior.schedule.service_in". Abort.
Check @prosa.behavior.schedule.service_in.
Goal True. idtac "END|prosa.behavior.schedule.service_in". Abort.
Goal True. idtac "BEGIN|prosa.behavior.schedule.schedule". Abort.
Check @prosa.behavior.schedule.schedule.
Goal True. idtac "END|prosa.behavior.schedule.schedule". Abort.
Goal True. idtac "BEGIN|prosa.behavior.service.scheduled_at". Abort.
Check @prosa.behavior.service.scheduled_at.
Goal True. idtac "END|prosa.behavior.service.scheduled_at". Abort.
Goal True. idtac "BEGIN|prosa.behavior.service.service_at". Abort.
Check @prosa.behavior.service.service_at.
Goal True. idtac "END|prosa.behavior.service.service_at". Abort.
Goal True. idtac "BEGIN|prosa.behavior.service.receives_service_at". Abort.
Check @prosa.behavior.service.receives_service_at.
Goal True. idtac "END|prosa.behavior.service.receives_service_at". Abort.
Goal True. idtac "BEGIN|prosa.behavior.service.service_during". Abort.
Check @prosa.behavior.service.service_during.
Goal True. idtac "END|prosa.behavior.service.service_during". Abort.
Goal True. idtac "BEGIN|prosa.behavior.service.service". Abort.
Check @prosa.behavior.service.service.
Goal True. idtac "END|prosa.behavior.service.service". Abort.
Goal True. idtac "BEGIN|prosa.behavior.service.completed_by". Abort.
Check @prosa.behavior.service.completed_by.
Goal True. idtac "END|prosa.behavior.service.completed_by". Abort.
Goal True. idtac "BEGIN|prosa.behavior.service.completes_at". Abort.
Check @prosa.behavior.service.completes_at.
Goal True. idtac "END|prosa.behavior.service.completes_at". Abort.
Goal True. idtac "BEGIN|prosa.behavior.service.job_response_time_bound". Abort.
Check @prosa.behavior.service.job_response_time_bound.
Goal True. idtac "END|prosa.behavior.service.job_response_time_bound". Abort.
Goal True. idtac "BEGIN|prosa.behavior.service.job_meets_deadline". Abort.
Check @prosa.behavior.service.job_meets_deadline.
Goal True. idtac "END|prosa.behavior.service.job_meets_deadline". Abort.
Goal True. idtac "BEGIN|prosa.behavior.service.pending". Abort.
Check @prosa.behavior.service.pending.
Goal True. idtac "END|prosa.behavior.service.pending". Abort.
Goal True. idtac "BEGIN|prosa.behavior.service.pending_earlier_and_at". Abort.
Check @prosa.behavior.service.pending_earlier_and_at.
Goal True. idtac "END|prosa.behavior.service.pending_earlier_and_at". Abort.
Goal True. idtac "BEGIN|prosa.behavior.service.remaining_cost". Abort.
Check @prosa.behavior.service.remaining_cost.
Goal True. idtac "END|prosa.behavior.service.remaining_cost". Abort.
Goal True. idtac "BEGIN|prosa.behavior.time.duration". Abort.
Check @prosa.behavior.time.duration.
Goal True. idtac "END|prosa.behavior.time.duration". Abort.
Goal True. idtac "BEGIN|prosa.behavior.time.instant". Abort.
Check @prosa.behavior.time.instant.
Goal True. idtac "END|prosa.behavior.time.instant". Abort.
Goal True. idtac "BEGIN|prosa.implementation.definitions.arrival_bound.task_arrivals_bound". Abort.
Check @prosa.implementation.definitions.arrival_bound.task_arrivals_bound.
Goal True. idtac "END|prosa.implementation.definitions.arrival_bound.task_arrivals_bound". Abort.
Goal True. idtac "BEGIN|prosa.implementation.definitions.arrival_bound.task_arrivals_bound_eqdef". Abort.
Check @prosa.implementation.definitions.arrival_bound.task_arrivals_bound_eqdef.
Goal True. idtac "END|prosa.implementation.definitions.arrival_bound.task_arrivals_bound_eqdef". Abort.
Goal True. idtac "BEGIN|prosa.implementation.definitions.arrival_bound.eqn_task_arrivals_bound". Abort.
Check @prosa.implementation.definitions.arrival_bound.eqn_task_arrivals_bound.
Goal True. idtac "END|prosa.implementation.definitions.arrival_bound.eqn_task_arrivals_bound". Abort.
Goal True. idtac "BEGIN|prosa.implementation.definitions.extrapolated_arrival_curve.ArrivalCurvePrefix". Abort.
Check @prosa.implementation.definitions.extrapolated_arrival_curve.ArrivalCurvePrefix.
Goal True. idtac "END|prosa.implementation.definitions.extrapolated_arrival_curve.ArrivalCurvePrefix". Abort.
Goal True. idtac "BEGIN|prosa.implementation.definitions.extrapolated_arrival_curve.inter_arrival_to_prefix". Abort.
Check @prosa.implementation.definitions.extrapolated_arrival_curve.inter_arrival_to_prefix.
Goal True. idtac "END|prosa.implementation.definitions.extrapolated_arrival_curve.inter_arrival_to_prefix". Abort.
Goal True. idtac "BEGIN|prosa.implementation.definitions.extrapolated_arrival_curve.horizon_of". Abort.
Check @prosa.implementation.definitions.extrapolated_arrival_curve.horizon_of.
Goal True. idtac "END|prosa.implementation.definitions.extrapolated_arrival_curve.horizon_of". Abort.
Goal True. idtac "BEGIN|prosa.implementation.definitions.extrapolated_arrival_curve.steps_of". Abort.
Check @prosa.implementation.definitions.extrapolated_arrival_curve.steps_of.
Goal True. idtac "END|prosa.implementation.definitions.extrapolated_arrival_curve.steps_of". Abort.
Goal True. idtac "BEGIN|prosa.implementation.definitions.extrapolated_arrival_curve.time_steps_of". Abort.
Check @prosa.implementation.definitions.extrapolated_arrival_curve.time_steps_of.
Goal True. idtac "END|prosa.implementation.definitions.extrapolated_arrival_curve.time_steps_of". Abort.
Goal True. idtac "BEGIN|prosa.implementation.definitions.extrapolated_arrival_curve.step_at". Abort.
Check @prosa.implementation.definitions.extrapolated_arrival_curve.step_at.
Goal True. idtac "END|prosa.implementation.definitions.extrapolated_arrival_curve.step_at". Abort.
Goal True. idtac "BEGIN|prosa.implementation.definitions.extrapolated_arrival_curve.value_at". Abort.
Check @prosa.implementation.definitions.extrapolated_arrival_curve.value_at.
Goal True. idtac "END|prosa.implementation.definitions.extrapolated_arrival_curve.value_at". Abort.
Goal True. idtac "BEGIN|prosa.implementation.definitions.extrapolated_arrival_curve.extrapolated_arrival_curve". Abort.
Check @prosa.implementation.definitions.extrapolated_arrival_curve.extrapolated_arrival_curve.
Goal True. idtac "END|prosa.implementation.definitions.extrapolated_arrival_curve.extrapolated_arrival_curve". Abort.
Goal True. idtac "BEGIN|prosa.implementation.definitions.extrapolated_arrival_curve.positive_horizon". Abort.
Check @prosa.implementation.definitions.extrapolated_arrival_curve.positive_horizon.
Goal True. idtac "END|prosa.implementation.definitions.extrapolated_arrival_curve.positive_horizon". Abort.
Goal True. idtac "BEGIN|prosa.implementation.definitions.extrapolated_arrival_curve.large_horizon". Abort.
Check @prosa.implementation.definitions.extrapolated_arrival_curve.large_horizon.
Goal True. idtac "END|prosa.implementation.definitions.extrapolated_arrival_curve.large_horizon". Abort.
Goal True. idtac "BEGIN|prosa.implementation.definitions.extrapolated_arrival_curve.large_horizon_dec". Abort.
Check @prosa.implementation.definitions.extrapolated_arrival_curve.large_horizon_dec.
Goal True. idtac "END|prosa.implementation.definitions.extrapolated_arrival_curve.large_horizon_dec". Abort.
Goal True. idtac "BEGIN|prosa.implementation.definitions.extrapolated_arrival_curve.large_horizon_P". Abort.
Check @prosa.implementation.definitions.extrapolated_arrival_curve.large_horizon_P.
Goal True. idtac "END|prosa.implementation.definitions.extrapolated_arrival_curve.large_horizon_P". Abort.
Goal True. idtac "BEGIN|prosa.implementation.definitions.extrapolated_arrival_curve.no_inf_arrivals". Abort.
Check @prosa.implementation.definitions.extrapolated_arrival_curve.no_inf_arrivals.
Goal True. idtac "END|prosa.implementation.definitions.extrapolated_arrival_curve.no_inf_arrivals". Abort.
Goal True. idtac "BEGIN|prosa.implementation.definitions.extrapolated_arrival_curve.specified_bursts". Abort.
Check @prosa.implementation.definitions.extrapolated_arrival_curve.specified_bursts.
Goal True. idtac "END|prosa.implementation.definitions.extrapolated_arrival_curve.specified_bursts". Abort.
Goal True. idtac "BEGIN|prosa.implementation.definitions.extrapolated_arrival_curve.ltn_steps". Abort.
Check @prosa.implementation.definitions.extrapolated_arrival_curve.ltn_steps.
Goal True. idtac "END|prosa.implementation.definitions.extrapolated_arrival_curve.ltn_steps". Abort.
Goal True. idtac "BEGIN|prosa.implementation.definitions.extrapolated_arrival_curve.sorted_ltn_steps". Abort.
Check @prosa.implementation.definitions.extrapolated_arrival_curve.sorted_ltn_steps.
Goal True. idtac "END|prosa.implementation.definitions.extrapolated_arrival_curve.sorted_ltn_steps". Abort.
Goal True. idtac "BEGIN|prosa.implementation.definitions.extrapolated_arrival_curve.valid_arrival_curve_prefix". Abort.
Check @prosa.implementation.definitions.extrapolated_arrival_curve.valid_arrival_curve_prefix.
Goal True. idtac "END|prosa.implementation.definitions.extrapolated_arrival_curve.valid_arrival_curve_prefix". Abort.
Goal True. idtac "BEGIN|prosa.implementation.definitions.extrapolated_arrival_curve.valid_arrival_curve_prefix_dec". Abort.
Check @prosa.implementation.definitions.extrapolated_arrival_curve.valid_arrival_curve_prefix_dec.
Goal True. idtac "END|prosa.implementation.definitions.extrapolated_arrival_curve.valid_arrival_curve_prefix_dec". Abort.
Goal True. idtac "BEGIN|prosa.implementation.definitions.extrapolated_arrival_curve.valid_arrival_curve_prefix_P". Abort.
Check @prosa.implementation.definitions.extrapolated_arrival_curve.valid_arrival_curve_prefix_P.
Goal True. idtac "END|prosa.implementation.definitions.extrapolated_arrival_curve.valid_arrival_curve_prefix_P". Abort.
Goal True. idtac "BEGIN|prosa.implementation.definitions.extrapolated_arrival_curve.leq_steps". Abort.
Check @prosa.implementation.definitions.extrapolated_arrival_curve.leq_steps.
Goal True. idtac "END|prosa.implementation.definitions.extrapolated_arrival_curve.leq_steps". Abort.
Goal True. idtac "BEGIN|prosa.implementation.definitions.extrapolated_arrival_curve.sorted_leq_steps". Abort.
Check @prosa.implementation.definitions.extrapolated_arrival_curve.sorted_leq_steps.
Goal True. idtac "END|prosa.implementation.definitions.extrapolated_arrival_curve.sorted_leq_steps". Abort.
Goal True. idtac "BEGIN|prosa.implementation.definitions.generic_scheduler.PointwisePolicy". Abort.
Check @prosa.implementation.definitions.generic_scheduler.PointwisePolicy.
Goal True. idtac "END|prosa.implementation.definitions.generic_scheduler.PointwisePolicy". Abort.
Goal True. idtac "BEGIN|prosa.implementation.definitions.generic_scheduler.empty_schedule". Abort.
Check @prosa.implementation.definitions.generic_scheduler.empty_schedule.
Goal True. idtac "END|prosa.implementation.definitions.generic_scheduler.empty_schedule". Abort.
Goal True. idtac "BEGIN|prosa.implementation.definitions.generic_scheduler.schedule_up_to". Abort.
Check @prosa.implementation.definitions.generic_scheduler.schedule_up_to.
Goal True. idtac "END|prosa.implementation.definitions.generic_scheduler.schedule_up_to". Abort.
Goal True. idtac "BEGIN|prosa.implementation.definitions.generic_scheduler.generic_schedule". Abort.
Check @prosa.implementation.definitions.generic_scheduler.generic_schedule.
Goal True. idtac "END|prosa.implementation.definitions.generic_scheduler.generic_schedule". Abort.
Goal True. idtac "BEGIN|prosa.implementation.definitions.ideal_uni_scheduler.prev_job_nonpreemptive". Abort.
Check @prosa.implementation.definitions.ideal_uni_scheduler.prev_job_nonpreemptive.
Goal True. idtac "END|prosa.implementation.definitions.ideal_uni_scheduler.prev_job_nonpreemptive". Abort.
Goal True. idtac "BEGIN|prosa.implementation.definitions.ideal_uni_scheduler.allocation_at". Abort.
Check @prosa.implementation.definitions.ideal_uni_scheduler.allocation_at.
Goal True. idtac "END|prosa.implementation.definitions.ideal_uni_scheduler.allocation_at". Abort.
Goal True. idtac "BEGIN|prosa.implementation.definitions.ideal_uni_scheduler.pmc_uni_schedule". Abort.
Check @prosa.implementation.definitions.ideal_uni_scheduler.pmc_uni_schedule.
Goal True. idtac "END|prosa.implementation.definitions.ideal_uni_scheduler.pmc_uni_schedule". Abort.
Goal True. idtac "BEGIN|prosa.implementation.definitions.ideal_uni_scheduler.choose_highest_prio_job". Abort.
Check @prosa.implementation.definitions.ideal_uni_scheduler.choose_highest_prio_job.
Goal True. idtac "END|prosa.implementation.definitions.ideal_uni_scheduler.choose_highest_prio_job". Abort.
Goal True. idtac "BEGIN|prosa.implementation.definitions.ideal_uni_scheduler.uni_schedule". Abort.
Check @prosa.implementation.definitions.ideal_uni_scheduler.uni_schedule.
Goal True. idtac "END|prosa.implementation.definitions.ideal_uni_scheduler.uni_schedule". Abort.
Goal True. idtac "BEGIN|prosa.implementation.definitions.job_constructor.Task". Abort.
Check @prosa.implementation.definitions.job_constructor.Task.
Goal True. idtac "END|prosa.implementation.definitions.job_constructor.Task". Abort.
Goal True. idtac "BEGIN|prosa.implementation.definitions.job_constructor.Job". Abort.
Check @prosa.implementation.definitions.job_constructor.Job.
Goal True. idtac "END|prosa.implementation.definitions.job_constructor.Job". Abort.
Goal True. idtac "BEGIN|prosa.implementation.definitions.job_constructor.generate_job_at". Abort.
Check @prosa.implementation.definitions.job_constructor.generate_job_at.
Goal True. idtac "END|prosa.implementation.definitions.job_constructor.generate_job_at". Abort.
Goal True. idtac "BEGIN|prosa.implementation.definitions.job_constructor.generate_jobs_at". Abort.
Check @prosa.implementation.definitions.job_constructor.generate_jobs_at.
Goal True. idtac "END|prosa.implementation.definitions.job_constructor.generate_jobs_at". Abort.
Goal True. idtac "BEGIN|prosa.implementation.definitions.maximal_arrival_sequence.suffix_sum". Abort.
Check @prosa.implementation.definitions.maximal_arrival_sequence.suffix_sum.
Goal True. idtac "END|prosa.implementation.definitions.maximal_arrival_sequence.suffix_sum". Abort.
Goal True. idtac "BEGIN|prosa.implementation.definitions.maximal_arrival_sequence.jobs_remaining". Abort.
Check @prosa.implementation.definitions.maximal_arrival_sequence.jobs_remaining.
Goal True. idtac "END|prosa.implementation.definitions.maximal_arrival_sequence.jobs_remaining". Abort.
Goal True. idtac "BEGIN|prosa.implementation.definitions.maximal_arrival_sequence.next_max_arrival". Abort.
Check @prosa.implementation.definitions.maximal_arrival_sequence.next_max_arrival.
Goal True. idtac "END|prosa.implementation.definitions.maximal_arrival_sequence.next_max_arrival". Abort.
Goal True. idtac "BEGIN|prosa.implementation.definitions.maximal_arrival_sequence.extend_arrival_prefix". Abort.
Check @prosa.implementation.definitions.maximal_arrival_sequence.extend_arrival_prefix.
Goal True. idtac "END|prosa.implementation.definitions.maximal_arrival_sequence.extend_arrival_prefix". Abort.
Goal True. idtac "BEGIN|prosa.implementation.definitions.maximal_arrival_sequence.maximal_arrival_prefix". Abort.
Check @prosa.implementation.definitions.maximal_arrival_sequence.maximal_arrival_prefix.
Goal True. idtac "END|prosa.implementation.definitions.maximal_arrival_sequence.maximal_arrival_prefix". Abort.
Goal True. idtac "BEGIN|prosa.implementation.definitions.maximal_arrival_sequence.max_arrivals_at". Abort.
Check @prosa.implementation.definitions.maximal_arrival_sequence.max_arrivals_at.
Goal True. idtac "END|prosa.implementation.definitions.maximal_arrival_sequence.max_arrivals_at". Abort.
Goal True. idtac "BEGIN|prosa.implementation.definitions.maximal_arrival_sequence.concrete_arrival_sequence". Abort.
Check @prosa.implementation.definitions.maximal_arrival_sequence.concrete_arrival_sequence.
Goal True. idtac "END|prosa.implementation.definitions.maximal_arrival_sequence.concrete_arrival_sequence". Abort.
Goal True. idtac "BEGIN|prosa.implementation.definitions.task.concrete_task". Abort.
Check @prosa.implementation.definitions.task.concrete_task.
Goal True. idtac "END|prosa.implementation.definitions.task.concrete_task". Abort.
Goal True. idtac "BEGIN|prosa.implementation.definitions.task.task_eqdef". Abort.
Check @prosa.implementation.definitions.task.task_eqdef.
Goal True. idtac "END|prosa.implementation.definitions.task.task_eqdef". Abort.
Goal True. idtac "BEGIN|prosa.implementation.definitions.task.eqn_task". Abort.
Check @prosa.implementation.definitions.task.eqn_task.
Goal True. idtac "END|prosa.implementation.definitions.task.eqn_task". Abort.
Goal True. idtac "BEGIN|prosa.implementation.definitions.task.concrete_job". Abort.
Check @prosa.implementation.definitions.task.concrete_job.
Goal True. idtac "END|prosa.implementation.definitions.task.concrete_job". Abort.
Goal True. idtac "BEGIN|prosa.implementation.definitions.task.get_arrival_curve_prefix". Abort.
Check @prosa.implementation.definitions.task.get_arrival_curve_prefix.
Goal True. idtac "END|prosa.implementation.definitions.task.get_arrival_curve_prefix". Abort.
Goal True. idtac "BEGIN|prosa.implementation.definitions.task.concrete_max_arrivals". Abort.
Check @prosa.implementation.definitions.task.concrete_max_arrivals.
Goal True. idtac "END|prosa.implementation.definitions.task.concrete_max_arrivals". Abort.
Goal True. idtac "BEGIN|prosa.implementation.definitions.task.job_eqdef". Abort.
Check @prosa.implementation.definitions.task.job_eqdef.
Goal True. idtac "END|prosa.implementation.definitions.task.job_eqdef". Abort.
Goal True. idtac "BEGIN|prosa.implementation.definitions.task.eqn_job". Abort.
Check @prosa.implementation.definitions.task.eqn_job.
Goal True. idtac "END|prosa.implementation.definitions.task.eqn_job". Abort.
Goal True. idtac "BEGIN|prosa.implementation.definitions.task.TaskCost". Abort.
Check @prosa.implementation.definitions.task.TaskCost.
Goal True. idtac "END|prosa.implementation.definitions.task.TaskCost". Abort.
Goal True. idtac "BEGIN|prosa.implementation.definitions.task.TaskPriority". Abort.
Check @prosa.implementation.definitions.task.TaskPriority.
Goal True. idtac "END|prosa.implementation.definitions.task.TaskPriority". Abort.
Goal True. idtac "BEGIN|prosa.implementation.definitions.task.TaskDeadline". Abort.
Check @prosa.implementation.definitions.task.TaskDeadline.
Goal True. idtac "END|prosa.implementation.definitions.task.TaskDeadline". Abort.
Goal True. idtac "BEGIN|prosa.implementation.definitions.task.ConcreteMaxArrivals". Abort.
Check @prosa.implementation.definitions.task.ConcreteMaxArrivals.
Goal True. idtac "END|prosa.implementation.definitions.task.ConcreteMaxArrivals". Abort.
Goal True. idtac "BEGIN|prosa.implementation.definitions.task.JobTask". Abort.
Check @prosa.implementation.definitions.task.JobTask.
Goal True. idtac "END|prosa.implementation.definitions.task.JobTask". Abort.
Goal True. idtac "BEGIN|prosa.implementation.definitions.task.JobArrival". Abort.
Check @prosa.implementation.definitions.task.JobArrival.
Goal True. idtac "END|prosa.implementation.definitions.task.JobArrival". Abort.
Goal True. idtac "BEGIN|prosa.implementation.definitions.task.JobCost". Abort.
Check @prosa.implementation.definitions.task.JobCost.
Goal True. idtac "END|prosa.implementation.definitions.task.JobCost". Abort.
Goal True. idtac "BEGIN|prosa.implementation.facts.extrapolated_arrival_curve.ltn_steps_is_transitive". Abort.
Check @prosa.implementation.facts.extrapolated_arrival_curve.ltn_steps_is_transitive.
Goal True. idtac "END|prosa.implementation.facts.extrapolated_arrival_curve.ltn_steps_is_transitive". Abort.
Goal True. idtac "BEGIN|prosa.implementation.facts.extrapolated_arrival_curve.leq_steps_is_reflexive". Abort.
Check @prosa.implementation.facts.extrapolated_arrival_curve.leq_steps_is_reflexive.
Goal True. idtac "END|prosa.implementation.facts.extrapolated_arrival_curve.leq_steps_is_reflexive". Abort.
Goal True. idtac "BEGIN|prosa.implementation.facts.extrapolated_arrival_curve.leq_steps_is_transitive". Abort.
Check @prosa.implementation.facts.extrapolated_arrival_curve.leq_steps_is_transitive.
Goal True. idtac "END|prosa.implementation.facts.extrapolated_arrival_curve.leq_steps_is_transitive". Abort.
Goal True. idtac "BEGIN|prosa.implementation.facts.extrapolated_arrival_curve.value_at_monotone". Abort.
Check @prosa.implementation.facts.extrapolated_arrival_curve.value_at_monotone.
Goal True. idtac "END|prosa.implementation.facts.extrapolated_arrival_curve.value_at_monotone". Abort.
Goal True. idtac "BEGIN|prosa.implementation.facts.extrapolated_arrival_curve.value_at_change_is_in_steps_of". Abort.
Check @prosa.implementation.facts.extrapolated_arrival_curve.value_at_change_is_in_steps_of.
Goal True. idtac "END|prosa.implementation.facts.extrapolated_arrival_curve.value_at_change_is_in_steps_of". Abort.
Goal True. idtac "BEGIN|prosa.implementation.facts.extrapolated_arrival_curve.sorted_ltn_steps_imply_sorted_leq_steps_steps". Abort.
Check @prosa.implementation.facts.extrapolated_arrival_curve.sorted_ltn_steps_imply_sorted_leq_steps_steps.
Goal True. idtac "END|prosa.implementation.facts.extrapolated_arrival_curve.sorted_ltn_steps_imply_sorted_leq_steps_steps". Abort.
Goal True. idtac "BEGIN|prosa.implementation.facts.extrapolated_arrival_curve.step_at_0_is_00". Abort.
Check @prosa.implementation.facts.extrapolated_arrival_curve.step_at_0_is_00.
Goal True. idtac "END|prosa.implementation.facts.extrapolated_arrival_curve.step_at_0_is_00". Abort.
Goal True. idtac "BEGIN|prosa.implementation.facts.extrapolated_arrival_curve.step_at_agrees_with_steps_of". Abort.
Check @prosa.implementation.facts.extrapolated_arrival_curve.step_at_agrees_with_steps_of.
Goal True. idtac "END|prosa.implementation.facts.extrapolated_arrival_curve.step_at_agrees_with_steps_of". Abort.
Goal True. idtac "BEGIN|prosa.implementation.facts.extrapolated_arrival_curve.extrapolated_arrival_curve_is_monotone". Abort.
Check @prosa.implementation.facts.extrapolated_arrival_curve.extrapolated_arrival_curve_is_monotone.
Goal True. idtac "END|prosa.implementation.facts.extrapolated_arrival_curve.extrapolated_arrival_curve_is_monotone". Abort.
Goal True. idtac "BEGIN|prosa.implementation.facts.extrapolated_arrival_curve.extrapolated_arrival_curve_change". Abort.
Check @prosa.implementation.facts.extrapolated_arrival_curve.extrapolated_arrival_curve_change.
Goal True. idtac "END|prosa.implementation.facts.extrapolated_arrival_curve.extrapolated_arrival_curve_change". Abort.
Goal True. idtac "BEGIN|prosa.implementation.facts.generic_schedule.schedule_up_to_def". Abort.
Check @prosa.implementation.facts.generic_schedule.schedule_up_to_def.
Goal True. idtac "END|prosa.implementation.facts.generic_schedule.schedule_up_to_def". Abort.
Goal True. idtac "BEGIN|prosa.implementation.facts.generic_schedule.schedule_up_to_unfold". Abort.
Check @prosa.implementation.facts.generic_schedule.schedule_up_to_unfold.
Goal True. idtac "END|prosa.implementation.facts.generic_schedule.schedule_up_to_unfold". Abort.
Goal True. idtac "BEGIN|prosa.implementation.facts.generic_schedule.schedule_up_to_widen". Abort.
Check @prosa.implementation.facts.generic_schedule.schedule_up_to_widen.
Goal True. idtac "END|prosa.implementation.facts.generic_schedule.schedule_up_to_widen". Abort.
Goal True. idtac "BEGIN|prosa.implementation.facts.generic_schedule.schedule_up_to_empty". Abort.
Check @prosa.implementation.facts.generic_schedule.schedule_up_to_empty.
Goal True. idtac "END|prosa.implementation.facts.generic_schedule.schedule_up_to_empty". Abort.
Goal True. idtac "BEGIN|prosa.implementation.facts.generic_schedule.schedule_up_to_prefix_inclusion". Abort.
Check @prosa.implementation.facts.generic_schedule.schedule_up_to_prefix_inclusion.
Goal True. idtac "END|prosa.implementation.facts.generic_schedule.schedule_up_to_prefix_inclusion". Abort.
Goal True. idtac "BEGIN|prosa.implementation.facts.generic_schedule.schedule_up_to_identical_prefix". Abort.
Check @prosa.implementation.facts.generic_schedule.schedule_up_to_identical_prefix.
Goal True. idtac "END|prosa.implementation.facts.generic_schedule.schedule_up_to_identical_prefix". Abort.
Goal True. idtac "BEGIN|prosa.implementation.facts.ideal_uni.preemption_aware.allocation_at_idle". Abort.
Check @prosa.implementation.facts.ideal_uni.preemption_aware.allocation_at_idle.
Goal True. idtac "END|prosa.implementation.facts.ideal_uni.preemption_aware.allocation_at_idle". Abort.
Goal True. idtac "BEGIN|prosa.implementation.facts.ideal_uni.preemption_aware.idle_schedule_no_backlogged_jobs". Abort.
Check @prosa.implementation.facts.ideal_uni.preemption_aware.idle_schedule_no_backlogged_jobs.
Goal True. idtac "END|prosa.implementation.facts.ideal_uni.preemption_aware.idle_schedule_no_backlogged_jobs". Abort.
Goal True. idtac "BEGIN|prosa.implementation.facts.ideal_uni.preemption_aware.np_schedule_work_conserving". Abort.
Check @prosa.implementation.facts.ideal_uni.preemption_aware.np_schedule_work_conserving.
Goal True. idtac "END|prosa.implementation.facts.ideal_uni.preemption_aware.np_schedule_work_conserving". Abort.
Goal True. idtac "BEGIN|prosa.implementation.facts.ideal_uni.preemption_aware.np_schedule_jobs_from_arrival_sequence". Abort.
Check @prosa.implementation.facts.ideal_uni.preemption_aware.np_schedule_jobs_from_arrival_sequence.
Goal True. idtac "END|prosa.implementation.facts.ideal_uni.preemption_aware.np_schedule_jobs_from_arrival_sequence". Abort.
Goal True. idtac "BEGIN|prosa.implementation.facts.ideal_uni.preemption_aware.chosen_job_is_ready". Abort.
Check @prosa.implementation.facts.ideal_uni.preemption_aware.chosen_job_is_ready.
Goal True. idtac "END|prosa.implementation.facts.ideal_uni.preemption_aware.chosen_job_is_ready". Abort.
Goal True. idtac "BEGIN|prosa.implementation.facts.ideal_uni.preemption_aware.jobs_must_be_ready". Abort.
Check @prosa.implementation.facts.ideal_uni.preemption_aware.jobs_must_be_ready.
Goal True. idtac "END|prosa.implementation.facts.ideal_uni.preemption_aware.jobs_must_be_ready". Abort.
Goal True. idtac "BEGIN|prosa.implementation.facts.ideal_uni.preemption_aware.np_schedule_valid". Abort.
Check @prosa.implementation.facts.ideal_uni.preemption_aware.np_schedule_valid.
Goal True. idtac "END|prosa.implementation.facts.ideal_uni.preemption_aware.np_schedule_valid". Abort.
Goal True. idtac "BEGIN|prosa.implementation.facts.ideal_uni.preemption_aware.np_job_remains_scheduled". Abort.
Check @prosa.implementation.facts.ideal_uni.preemption_aware.np_job_remains_scheduled.
Goal True. idtac "END|prosa.implementation.facts.ideal_uni.preemption_aware.np_job_remains_scheduled". Abort.
Goal True. idtac "BEGIN|prosa.implementation.facts.ideal_uni.preemption_aware.np_consistent". Abort.
Check @prosa.implementation.facts.ideal_uni.preemption_aware.np_consistent.
Goal True. idtac "END|prosa.implementation.facts.ideal_uni.preemption_aware.np_consistent". Abort.
Goal True. idtac "BEGIN|prosa.implementation.facts.ideal_uni.preemption_aware.np_respects_preemption_model". Abort.
Check @prosa.implementation.facts.ideal_uni.preemption_aware.np_respects_preemption_model.
Goal True. idtac "END|prosa.implementation.facts.ideal_uni.preemption_aware.np_respects_preemption_model". Abort.
Goal True. idtac "BEGIN|prosa.implementation.facts.ideal_uni.prio_aware.uni_schedule_work_conserving". Abort.
Check @prosa.implementation.facts.ideal_uni.prio_aware.uni_schedule_work_conserving.
Goal True. idtac "END|prosa.implementation.facts.ideal_uni.prio_aware.uni_schedule_work_conserving". Abort.
Goal True. idtac "BEGIN|prosa.implementation.facts.ideal_uni.prio_aware.uni_schedule_valid". Abort.
Check @prosa.implementation.facts.ideal_uni.prio_aware.uni_schedule_valid.
Goal True. idtac "END|prosa.implementation.facts.ideal_uni.prio_aware.uni_schedule_valid". Abort.
Goal True. idtac "BEGIN|prosa.implementation.facts.ideal_uni.prio_aware.schedule_respects_preemption_model". Abort.
Check @prosa.implementation.facts.ideal_uni.prio_aware.schedule_respects_preemption_model.
Goal True. idtac "END|prosa.implementation.facts.ideal_uni.prio_aware.schedule_respects_preemption_model". Abort.
Goal True. idtac "BEGIN|prosa.implementation.facts.ideal_uni.prio_aware.scheduled_job_is_supremum". Abort.
Check @prosa.implementation.facts.ideal_uni.prio_aware.scheduled_job_is_supremum.
Goal True. idtac "END|prosa.implementation.facts.ideal_uni.prio_aware.scheduled_job_is_supremum". Abort.
Goal True. idtac "BEGIN|prosa.implementation.facts.ideal_uni.prio_aware.schedule_respects_policy". Abort.
Check @prosa.implementation.facts.ideal_uni.prio_aware.schedule_respects_policy.
Goal True. idtac "END|prosa.implementation.facts.ideal_uni.prio_aware.schedule_respects_policy". Abort.
Goal True. idtac "BEGIN|prosa.implementation.facts.job_constructor.job_generation_valid_number". Abort.
Check @prosa.implementation.facts.job_constructor.job_generation_valid_number.
Goal True. idtac "END|prosa.implementation.facts.job_constructor.job_generation_valid_number". Abort.
Goal True. idtac "BEGIN|prosa.implementation.facts.job_constructor.generate_jobs_at_unique". Abort.
Check @prosa.implementation.facts.job_constructor.generate_jobs_at_unique.
Goal True. idtac "END|prosa.implementation.facts.job_constructor.generate_jobs_at_unique". Abort.
Goal True. idtac "BEGIN|prosa.implementation.facts.job_constructor.job_arrival_consistent". Abort.
Check @prosa.implementation.facts.job_constructor.job_arrival_consistent.
Goal True. idtac "END|prosa.implementation.facts.job_constructor.job_arrival_consistent". Abort.
Goal True. idtac "BEGIN|prosa.implementation.facts.job_constructor.arrivals_at_unique". Abort.
Check @prosa.implementation.facts.job_constructor.arrivals_at_unique.
Goal True. idtac "END|prosa.implementation.facts.job_constructor.arrivals_at_unique". Abort.
Goal True. idtac "BEGIN|prosa.implementation.facts.job_constructor.arrivals_between_unique". Abort.
Check @prosa.implementation.facts.job_constructor.arrivals_between_unique.
Goal True. idtac "END|prosa.implementation.facts.job_constructor.arrivals_between_unique". Abort.
Goal True. idtac "BEGIN|prosa.implementation.facts.job_constructor.job_generation_valid_jobs". Abort.
Check @prosa.implementation.facts.job_constructor.job_generation_valid_jobs.
Goal True. idtac "END|prosa.implementation.facts.job_constructor.job_generation_valid_jobs". Abort.
Goal True. idtac "BEGIN|prosa.implementation.facts.maximal_arrival_sequence.arr_seq_is_a_set". Abort.
Check @prosa.implementation.facts.maximal_arrival_sequence.arr_seq_is_a_set.
Goal True. idtac "END|prosa.implementation.facts.maximal_arrival_sequence.arr_seq_is_a_set". Abort.
Goal True. idtac "BEGIN|prosa.implementation.facts.maximal_arrival_sequence.concrete_all_jobs_from_taskset". Abort.
Check @prosa.implementation.facts.maximal_arrival_sequence.concrete_all_jobs_from_taskset.
Goal True. idtac "END|prosa.implementation.facts.maximal_arrival_sequence.concrete_all_jobs_from_taskset". Abort.
Goal True. idtac "BEGIN|prosa.implementation.facts.maximal_arrival_sequence.arrival_times_are_consistent". Abort.
Check @prosa.implementation.facts.maximal_arrival_sequence.arrival_times_are_consistent.
Goal True. idtac "END|prosa.implementation.facts.maximal_arrival_sequence.arrival_times_are_consistent". Abort.
Goal True. idtac "BEGIN|prosa.implementation.facts.maximal_arrival_sequence.concrete_valid_job_cost". Abort.
Check @prosa.implementation.facts.maximal_arrival_sequence.concrete_valid_job_cost.
Goal True. idtac "END|prosa.implementation.facts.maximal_arrival_sequence.concrete_valid_job_cost". Abort.
Goal True. idtac "BEGIN|prosa.implementation.facts.maximal_arrival_sequence.task_arrivals_at_eq_generate_jobs_at". Abort.
Check @prosa.implementation.facts.maximal_arrival_sequence.task_arrivals_at_eq_generate_jobs_at.
Goal True. idtac "END|prosa.implementation.facts.maximal_arrival_sequence.task_arrivals_at_eq_generate_jobs_at". Abort.
Goal True. idtac "BEGIN|prosa.implementation.facts.maximal_arrival_sequence.task_arrivals_at_eq". Abort.
Check @prosa.implementation.facts.maximal_arrival_sequence.task_arrivals_at_eq.
Goal True. idtac "END|prosa.implementation.facts.maximal_arrival_sequence.task_arrivals_at_eq". Abort.
Goal True. idtac "BEGIN|prosa.implementation.facts.maximal_arrival_sequence.number_of_task_arrivals_eq". Abort.
Check @prosa.implementation.facts.maximal_arrival_sequence.number_of_task_arrivals_eq.
Goal True. idtac "END|prosa.implementation.facts.maximal_arrival_sequence.number_of_task_arrivals_eq". Abort.
Goal True. idtac "BEGIN|prosa.implementation.facts.maximal_arrival_sequence.extend_horizon_size". Abort.
Check @prosa.implementation.facts.maximal_arrival_sequence.extend_horizon_size.
Goal True. idtac "END|prosa.implementation.facts.maximal_arrival_sequence.extend_horizon_size". Abort.
Goal True. idtac "BEGIN|prosa.implementation.facts.maximal_arrival_sequence.prefix_up_to_size". Abort.
Check @prosa.implementation.facts.maximal_arrival_sequence.prefix_up_to_size.
Goal True. idtac "END|prosa.implementation.facts.maximal_arrival_sequence.prefix_up_to_size". Abort.
Goal True. idtac "BEGIN|prosa.implementation.facts.maximal_arrival_sequence.n_arrivals_at_prefix_inclusion1". Abort.
Check @prosa.implementation.facts.maximal_arrival_sequence.n_arrivals_at_prefix_inclusion1.
Goal True. idtac "END|prosa.implementation.facts.maximal_arrival_sequence.n_arrivals_at_prefix_inclusion1". Abort.
Goal True. idtac "BEGIN|prosa.implementation.facts.maximal_arrival_sequence.n_arrivals_at_prefix_inclusion". Abort.
Check @prosa.implementation.facts.maximal_arrival_sequence.n_arrivals_at_prefix_inclusion.
Goal True. idtac "END|prosa.implementation.facts.maximal_arrival_sequence.n_arrivals_at_prefix_inclusion". Abort.
Goal True. idtac "BEGIN|prosa.implementation.facts.maximal_arrival_sequence.max_arrivals_at_next_max_arrivals_eq". Abort.
Check @prosa.implementation.facts.maximal_arrival_sequence.max_arrivals_at_next_max_arrivals_eq.
Goal True. idtac "END|prosa.implementation.facts.maximal_arrival_sequence.max_arrivals_at_next_max_arrivals_eq". Abort.
Goal True. idtac "BEGIN|prosa.implementation.facts.maximal_arrival_sequence.n_arrivals_at_leq". Abort.
Check @prosa.implementation.facts.maximal_arrival_sequence.n_arrivals_at_leq.
Goal True. idtac "END|prosa.implementation.facts.maximal_arrival_sequence.n_arrivals_at_leq". Abort.
Goal True. idtac "BEGIN|prosa.implementation.facts.maximal_arrival_sequence.concrete_is_arrival_curve". Abort.
Check @prosa.implementation.facts.maximal_arrival_sequence.concrete_is_arrival_curve.
Goal True. idtac "END|prosa.implementation.facts.maximal_arrival_sequence.concrete_is_arrival_curve". Abort.
Goal True. idtac "BEGIN|prosa.model.aggregate.service_of_jobs.service_of_jobs_at". Abort.
Check @prosa.model.aggregate.service_of_jobs.service_of_jobs_at.
Goal True. idtac "END|prosa.model.aggregate.service_of_jobs.service_of_jobs_at". Abort.
Goal True. idtac "BEGIN|prosa.model.aggregate.service_of_jobs.service_of_jobs". Abort.
Check @prosa.model.aggregate.service_of_jobs.service_of_jobs.
Goal True. idtac "END|prosa.model.aggregate.service_of_jobs.service_of_jobs". Abort.
Goal True. idtac "BEGIN|prosa.model.aggregate.service_of_jobs.service_of_higher_or_equal_priority_jobs". Abort.
Check @prosa.model.aggregate.service_of_jobs.service_of_higher_or_equal_priority_jobs.
Goal True. idtac "END|prosa.model.aggregate.service_of_jobs.service_of_higher_or_equal_priority_jobs". Abort.
Goal True. idtac "BEGIN|prosa.model.aggregate.service_of_jobs.service_of_other_hep_jobs". Abort.
Check @prosa.model.aggregate.service_of_jobs.service_of_other_hep_jobs.
Goal True. idtac "END|prosa.model.aggregate.service_of_jobs.service_of_other_hep_jobs". Abort.
Goal True. idtac "BEGIN|prosa.model.aggregate.service_of_jobs.service_of_other_task_hep_jobs". Abort.
Check @prosa.model.aggregate.service_of_jobs.service_of_other_task_hep_jobs.
Goal True. idtac "END|prosa.model.aggregate.service_of_jobs.service_of_other_task_hep_jobs". Abort.
Goal True. idtac "BEGIN|prosa.model.aggregate.service_of_jobs.service_of_hep_jobs". Abort.
Check @prosa.model.aggregate.service_of_jobs.service_of_hep_jobs.
Goal True. idtac "END|prosa.model.aggregate.service_of_jobs.service_of_hep_jobs". Abort.
Goal True. idtac "BEGIN|prosa.model.aggregate.service_of_jobs.task_service_of_jobs_in". Abort.
Check @prosa.model.aggregate.service_of_jobs.task_service_of_jobs_in.
Goal True. idtac "END|prosa.model.aggregate.service_of_jobs.task_service_of_jobs_in". Abort.
Goal True. idtac "BEGIN|prosa.model.aggregate.service_of_jobs.total_service_of_jobs_in". Abort.
Check @prosa.model.aggregate.service_of_jobs.total_service_of_jobs_in.
Goal True. idtac "END|prosa.model.aggregate.service_of_jobs.total_service_of_jobs_in". Abort.
Goal True. idtac "BEGIN|prosa.model.aggregate.workload.workload_of_jobs". Abort.
Check @prosa.model.aggregate.workload.workload_of_jobs.
Goal True. idtac "END|prosa.model.aggregate.workload.workload_of_jobs". Abort.
Goal True. idtac "BEGIN|prosa.model.aggregate.workload.task_workload". Abort.
Check @prosa.model.aggregate.workload.task_workload.
Goal True. idtac "END|prosa.model.aggregate.workload.task_workload". Abort.
Goal True. idtac "BEGIN|prosa.model.aggregate.workload.task_workload_between". Abort.
Check @prosa.model.aggregate.workload.task_workload_between.
Goal True. idtac "END|prosa.model.aggregate.workload.task_workload_between". Abort.
Goal True. idtac "BEGIN|prosa.model.aggregate.workload.workload_of_job". Abort.
Check @prosa.model.aggregate.workload.workload_of_job.
Goal True. idtac "END|prosa.model.aggregate.workload.workload_of_job". Abort.
Goal True. idtac "BEGIN|prosa.model.aggregate.workload.total_workload". Abort.
Check @prosa.model.aggregate.workload.total_workload.
Goal True. idtac "END|prosa.model.aggregate.workload.total_workload". Abort.
Goal True. idtac "BEGIN|prosa.model.aggregate.workload.total_workload_between". Abort.
Check @prosa.model.aggregate.workload.total_workload_between.
Goal True. idtac "END|prosa.model.aggregate.workload.total_workload_between". Abort.
Goal True. idtac "BEGIN|prosa.model.aggregate.workload.workload_of_hep_jobs". Abort.
Check @prosa.model.aggregate.workload.workload_of_hep_jobs.
Goal True. idtac "END|prosa.model.aggregate.workload.workload_of_hep_jobs". Abort.
Goal True. idtac "BEGIN|prosa.model.aggregate.workload.workload_of_other_hep_jobs". Abort.
Check @prosa.model.aggregate.workload.workload_of_other_hep_jobs.
Goal True. idtac "END|prosa.model.aggregate.workload.workload_of_other_hep_jobs". Abort.
Goal True. idtac "BEGIN|prosa.model.composite.valid_task_arrival_sequence.valid_task_arrival_sequence". Abort.
Check @prosa.model.composite.valid_task_arrival_sequence.valid_task_arrival_sequence.
Goal True. idtac "END|prosa.model.composite.valid_task_arrival_sequence.valid_task_arrival_sequence". Abort.
Goal True. idtac "BEGIN|prosa.model.composite.valid_task_arrival_sequence.valid_task_arrival_sequence_valid_arrivals". Abort.
Check @prosa.model.composite.valid_task_arrival_sequence.valid_task_arrival_sequence_valid_arrivals.
Goal True. idtac "END|prosa.model.composite.valid_task_arrival_sequence.valid_task_arrival_sequence_valid_arrivals". Abort.
Goal True. idtac "BEGIN|prosa.model.composite.valid_task_arrival_sequence.valid_task_arrival_sequence_valid_costs". Abort.
Check @prosa.model.composite.valid_task_arrival_sequence.valid_task_arrival_sequence_valid_costs.
Goal True. idtac "END|prosa.model.composite.valid_task_arrival_sequence.valid_task_arrival_sequence_valid_costs". Abort.
Goal True. idtac "BEGIN|prosa.model.composite.valid_task_arrival_sequence.valid_task_arrival_sequence_from_taskset". Abort.
Check @prosa.model.composite.valid_task_arrival_sequence.valid_task_arrival_sequence_from_taskset.
Goal True. idtac "END|prosa.model.composite.valid_task_arrival_sequence.valid_task_arrival_sequence_from_taskset". Abort.
Goal True. idtac "BEGIN|prosa.model.composite.valid_task_arrival_sequence.valid_task_arrival_sequence_respects_max". Abort.
Check @prosa.model.composite.valid_task_arrival_sequence.valid_task_arrival_sequence_respects_max.
Goal True. idtac "END|prosa.model.composite.valid_task_arrival_sequence.valid_task_arrival_sequence_respects_max". Abort.
Goal True. idtac "BEGIN|prosa.model.composite.valid_task_arrival_sequence.valid_task_arrival_sequence_valid_curve". Abort.
Check @prosa.model.composite.valid_task_arrival_sequence.valid_task_arrival_sequence_valid_curve.
Goal True. idtac "END|prosa.model.composite.valid_task_arrival_sequence.valid_task_arrival_sequence_valid_curve". Abort.
Goal True. idtac "BEGIN|prosa.model.job.properties.job_cost_positive". Abort.
Check @prosa.model.job.properties.job_cost_positive.
Goal True. idtac "END|prosa.model.job.properties.job_cost_positive". Abort.
Goal True. idtac "BEGIN|prosa.model.job.properties.arrivals_have_positive_job_costs". Abort.
Check @prosa.model.job.properties.arrivals_have_positive_job_costs.
Goal True. idtac "END|prosa.model.job.properties.arrivals_have_positive_job_costs". Abort.
Goal True. idtac "BEGIN|prosa.model.preemption.limited_preemptive.JobPreemptionPoints". Abort.
Check @prosa.model.preemption.limited_preemptive.JobPreemptionPoints.
Goal True. idtac "END|prosa.model.preemption.limited_preemptive.JobPreemptionPoints". Abort.
Goal True. idtac "BEGIN|prosa.model.preemption.limited_preemptive.beginning_of_execution_in_preemption_points". Abort.
Check @prosa.model.preemption.limited_preemptive.beginning_of_execution_in_preemption_points.
Goal True. idtac "END|prosa.model.preemption.limited_preemptive.beginning_of_execution_in_preemption_points". Abort.
Goal True. idtac "BEGIN|prosa.model.preemption.limited_preemptive.end_of_execution_in_preemption_points". Abort.
Check @prosa.model.preemption.limited_preemptive.end_of_execution_in_preemption_points.
Goal True. idtac "END|prosa.model.preemption.limited_preemptive.end_of_execution_in_preemption_points". Abort.
Goal True. idtac "BEGIN|prosa.model.preemption.limited_preemptive.preemption_points_is_nondecreasing_sequence". Abort.
Check @prosa.model.preemption.limited_preemptive.preemption_points_is_nondecreasing_sequence.
Goal True. idtac "END|prosa.model.preemption.limited_preemptive.preemption_points_is_nondecreasing_sequence". Abort.
Goal True. idtac "BEGIN|prosa.model.preemption.limited_preemptive.valid_limited_preemptions_job_model". Abort.
Check @prosa.model.preemption.limited_preemptive.valid_limited_preemptions_job_model.
Goal True. idtac "END|prosa.model.preemption.limited_preemptive.valid_limited_preemptions_job_model". Abort.
Goal True. idtac "BEGIN|prosa.model.preemption.parameter.JobPreemptable". Abort.
Check @prosa.model.preemption.parameter.JobPreemptable.
Goal True. idtac "END|prosa.model.preemption.parameter.JobPreemptable". Abort.
Goal True. idtac "BEGIN|prosa.model.preemption.parameter.job_preemption_points". Abort.
Check @prosa.model.preemption.parameter.job_preemption_points.
Goal True. idtac "END|prosa.model.preemption.parameter.job_preemption_points". Abort.
Goal True. idtac "BEGIN|prosa.model.preemption.parameter.conversion_preserves_equivalence". Abort.
Check @prosa.model.preemption.parameter.conversion_preserves_equivalence.
Goal True. idtac "END|prosa.model.preemption.parameter.conversion_preserves_equivalence". Abort.
Goal True. idtac "BEGIN|prosa.model.preemption.parameter.lengths_of_segments". Abort.
Check @prosa.model.preemption.parameter.lengths_of_segments.
Goal True. idtac "END|prosa.model.preemption.parameter.lengths_of_segments". Abort.
Goal True. idtac "BEGIN|prosa.model.preemption.parameter.job_max_nonpreemptive_segment". Abort.
Check @prosa.model.preemption.parameter.job_max_nonpreemptive_segment.
Goal True. idtac "END|prosa.model.preemption.parameter.job_max_nonpreemptive_segment". Abort.
Goal True. idtac "BEGIN|prosa.model.preemption.parameter.job_last_nonpreemptive_segment". Abort.
Check @prosa.model.preemption.parameter.job_last_nonpreemptive_segment.
Goal True. idtac "END|prosa.model.preemption.parameter.job_last_nonpreemptive_segment". Abort.
Goal True. idtac "BEGIN|prosa.model.preemption.parameter.job_rtct". Abort.
Check @prosa.model.preemption.parameter.job_rtct.
Goal True. idtac "END|prosa.model.preemption.parameter.job_rtct". Abort.
Goal True. idtac "BEGIN|prosa.model.preemption.parameter.preempted_at". Abort.
Check @prosa.model.preemption.parameter.preempted_at.
Goal True. idtac "END|prosa.model.preemption.parameter.preempted_at". Abort.
Goal True. idtac "BEGIN|prosa.model.preemption.parameter.job_cannot_become_nonpreemptive_before_execution". Abort.
Check @prosa.model.preemption.parameter.job_cannot_become_nonpreemptive_before_execution.
Goal True. idtac "END|prosa.model.preemption.parameter.job_cannot_become_nonpreemptive_before_execution". Abort.
Goal True. idtac "BEGIN|prosa.model.preemption.parameter.job_cannot_be_nonpreemptive_after_completion". Abort.
Check @prosa.model.preemption.parameter.job_cannot_be_nonpreemptive_after_completion.
Goal True. idtac "END|prosa.model.preemption.parameter.job_cannot_be_nonpreemptive_after_completion". Abort.
Goal True. idtac "BEGIN|prosa.model.preemption.parameter.not_preemptive_implies_scheduled". Abort.
Check @prosa.model.preemption.parameter.not_preemptive_implies_scheduled.
Goal True. idtac "END|prosa.model.preemption.parameter.not_preemptive_implies_scheduled". Abort.
Goal True. idtac "BEGIN|prosa.model.preemption.parameter.execution_starts_with_preemption_point". Abort.
Check @prosa.model.preemption.parameter.execution_starts_with_preemption_point.
Goal True. idtac "END|prosa.model.preemption.parameter.execution_starts_with_preemption_point". Abort.
Goal True. idtac "BEGIN|prosa.model.preemption.parameter.valid_preemption_model". Abort.
Check @prosa.model.preemption.parameter.valid_preemption_model.
Goal True. idtac "END|prosa.model.preemption.parameter.valid_preemption_model". Abort.
Goal True. idtac "BEGIN|prosa.model.preemption.parameter.no_superfluous_preemptions". Abort.
Check @prosa.model.preemption.parameter.no_superfluous_preemptions.
Goal True. idtac "END|prosa.model.preemption.parameter.no_superfluous_preemptions". Abort.
Goal True. idtac "BEGIN|prosa.model.priority.coercion.FP_to_JLFP". Abort.
Check @prosa.model.priority.coercion.FP_to_JLFP.
Goal True. idtac "END|prosa.model.priority.coercion.FP_to_JLFP". Abort.
Goal True. idtac "BEGIN|prosa.model.priority.coercion.JLFP_to_JLDP". Abort.
Check @prosa.model.priority.coercion.JLFP_to_JLDP.
Goal True. idtac "END|prosa.model.priority.coercion.JLFP_to_JLDP". Abort.
Goal True. idtac "BEGIN|prosa.model.priority.coercion.hep_job_at_jlfp". Abort.
Check @prosa.model.priority.coercion.hep_job_at_jlfp.
Goal True. idtac "END|prosa.model.priority.coercion.hep_job_at_jlfp". Abort.
Goal True. idtac "BEGIN|prosa.model.priority.coercion.hep_job_at_fp". Abort.
Check @prosa.model.priority.coercion.hep_job_at_fp.
Goal True. idtac "END|prosa.model.priority.coercion.hep_job_at_fp". Abort.
Goal True. idtac "BEGIN|prosa.model.priority.coercion.reflexive_priorities_FP_implies_JLFP". Abort.
Check @prosa.model.priority.coercion.reflexive_priorities_FP_implies_JLFP.
Goal True. idtac "END|prosa.model.priority.coercion.reflexive_priorities_FP_implies_JLFP". Abort.
Goal True. idtac "BEGIN|prosa.model.priority.coercion.transitive_priorities_FP_implies_JLFP". Abort.
Check @prosa.model.priority.coercion.transitive_priorities_FP_implies_JLFP.
Goal True. idtac "END|prosa.model.priority.coercion.transitive_priorities_FP_implies_JLFP". Abort.
Goal True. idtac "BEGIN|prosa.model.priority.coercion.total_priorities_FP_implies_JLFP". Abort.
Check @prosa.model.priority.coercion.total_priorities_FP_implies_JLFP.
Goal True. idtac "END|prosa.model.priority.coercion.total_priorities_FP_implies_JLFP". Abort.
Goal True. idtac "BEGIN|prosa.model.priority.coercion.reflexive_priorities_JLFP_implies_JLDP". Abort.
Check @prosa.model.priority.coercion.reflexive_priorities_JLFP_implies_JLDP.
Goal True. idtac "END|prosa.model.priority.coercion.reflexive_priorities_JLFP_implies_JLDP". Abort.
Goal True. idtac "BEGIN|prosa.model.priority.coercion.transitive_priorities_JLFP_implies_JLDP". Abort.
Check @prosa.model.priority.coercion.transitive_priorities_JLFP_implies_JLDP.
Goal True. idtac "END|prosa.model.priority.coercion.transitive_priorities_JLFP_implies_JLDP". Abort.
Goal True. idtac "BEGIN|prosa.model.priority.coercion.total_priorities_JLFP_implies_JLDP". Abort.
Check @prosa.model.priority.coercion.total_priorities_JLFP_implies_JLDP.
Goal True. idtac "END|prosa.model.priority.coercion.total_priorities_JLFP_implies_JLDP". Abort.
Goal True. idtac "BEGIN|prosa.model.priority.deadline_monotonic.DM". Abort.
Check @prosa.model.priority.deadline_monotonic.DM.
Goal True. idtac "END|prosa.model.priority.deadline_monotonic.DM". Abort.
Goal True. idtac "BEGIN|prosa.model.priority.deadline_monotonic.DM_is_reflexive". Abort.
Check @prosa.model.priority.deadline_monotonic.DM_is_reflexive.
Goal True. idtac "END|prosa.model.priority.deadline_monotonic.DM_is_reflexive". Abort.
Goal True. idtac "BEGIN|prosa.model.priority.deadline_monotonic.DM_is_transitive". Abort.
Check @prosa.model.priority.deadline_monotonic.DM_is_transitive.
Goal True. idtac "END|prosa.model.priority.deadline_monotonic.DM_is_transitive". Abort.
Goal True. idtac "BEGIN|prosa.model.priority.deadline_monotonic.DM_is_total". Abort.
Check @prosa.model.priority.deadline_monotonic.DM_is_total.
Goal True. idtac "END|prosa.model.priority.deadline_monotonic.DM_is_total". Abort.
Goal True. idtac "BEGIN|prosa.model.priority.definitions.FP_policy". Abort.
Check @prosa.model.priority.definitions.FP_policy.
Goal True. idtac "END|prosa.model.priority.definitions.FP_policy". Abort.
Goal True. idtac "BEGIN|prosa.model.priority.definitions.JLFP_policy". Abort.
Check @prosa.model.priority.definitions.JLFP_policy.
Goal True. idtac "END|prosa.model.priority.definitions.JLFP_policy". Abort.
Goal True. idtac "BEGIN|prosa.model.priority.definitions.JLDP_policy". Abort.
Check @prosa.model.priority.definitions.JLDP_policy.
Goal True. idtac "END|prosa.model.priority.definitions.JLDP_policy". Abort.
Goal True. idtac "BEGIN|prosa.model.priority.definitions.reflexive_priorities". Abort.
Check @prosa.model.priority.definitions.reflexive_priorities.
Goal True. idtac "END|prosa.model.priority.definitions.reflexive_priorities". Abort.
Goal True. idtac "BEGIN|prosa.model.priority.definitions.transitive_priorities". Abort.
Check @prosa.model.priority.definitions.transitive_priorities.
Goal True. idtac "END|prosa.model.priority.definitions.transitive_priorities". Abort.
Goal True. idtac "BEGIN|prosa.model.priority.definitions.total_priorities". Abort.
Check @prosa.model.priority.definitions.total_priorities.
Goal True. idtac "END|prosa.model.priority.definitions.total_priorities". Abort.
Goal True. idtac "BEGIN|prosa.model.priority.definitions.reflexive_job_priorities". Abort.
Check @prosa.model.priority.definitions.reflexive_job_priorities.
Goal True. idtac "END|prosa.model.priority.definitions.reflexive_job_priorities". Abort.
Goal True. idtac "BEGIN|prosa.model.priority.definitions.transitive_job_priorities". Abort.
Check @prosa.model.priority.definitions.transitive_job_priorities.
Goal True. idtac "END|prosa.model.priority.definitions.transitive_job_priorities". Abort.
Goal True. idtac "BEGIN|prosa.model.priority.definitions.total_job_priorities". Abort.
Check @prosa.model.priority.definitions.total_job_priorities.
Goal True. idtac "END|prosa.model.priority.definitions.total_job_priorities". Abort.
Goal True. idtac "BEGIN|prosa.model.priority.definitions.policy_respects_sequential_tasks". Abort.
Check @prosa.model.priority.definitions.policy_respects_sequential_tasks.
Goal True. idtac "END|prosa.model.priority.definitions.policy_respects_sequential_tasks". Abort.
Goal True. idtac "BEGIN|prosa.model.priority.definitions.policy_is_FIFO". Abort.
Check @prosa.model.priority.definitions.policy_is_FIFO.
Goal True. idtac "END|prosa.model.priority.definitions.policy_is_FIFO". Abort.
Goal True. idtac "BEGIN|prosa.model.priority.definitions.reflexive_task_priorities". Abort.
Check @prosa.model.priority.definitions.reflexive_task_priorities.
Goal True. idtac "END|prosa.model.priority.definitions.reflexive_task_priorities". Abort.
Goal True. idtac "BEGIN|prosa.model.priority.definitions.transitive_task_priorities". Abort.
Check @prosa.model.priority.definitions.transitive_task_priorities.
Goal True. idtac "END|prosa.model.priority.definitions.transitive_task_priorities". Abort.
Goal True. idtac "BEGIN|prosa.model.priority.definitions.total_task_priorities". Abort.
Check @prosa.model.priority.definitions.total_task_priorities.
Goal True. idtac "END|prosa.model.priority.definitions.total_task_priorities". Abort.
Goal True. idtac "BEGIN|prosa.model.priority.definitions.antisymmetric_over_taskset". Abort.
Check @prosa.model.priority.definitions.antisymmetric_over_taskset.
Goal True. idtac "END|prosa.model.priority.definitions.antisymmetric_over_taskset". Abort.
Goal True. idtac "BEGIN|prosa.model.priority.definitions.another_hep_job". Abort.
Check @prosa.model.priority.definitions.another_hep_job.
Goal True. idtac "END|prosa.model.priority.definitions.another_hep_job". Abort.
Goal True. idtac "BEGIN|prosa.model.priority.definitions.another_task_hep_job". Abort.
Check @prosa.model.priority.definitions.another_task_hep_job.
Goal True. idtac "END|prosa.model.priority.definitions.another_task_hep_job". Abort.
Goal True. idtac "BEGIN|prosa.model.priority.definitions.another_hep_job_of_same_task". Abort.
Check @prosa.model.priority.definitions.another_hep_job_of_same_task.
Goal True. idtac "END|prosa.model.priority.definitions.another_hep_job_of_same_task". Abort.
Goal True. idtac "BEGIN|prosa.model.priority.definitions.hp_task". Abort.
Check @prosa.model.priority.definitions.hp_task.
Goal True. idtac "END|prosa.model.priority.definitions.hp_task". Abort.
Goal True. idtac "BEGIN|prosa.model.priority.definitions.ep_task". Abort.
Check @prosa.model.priority.definitions.ep_task.
Goal True. idtac "END|prosa.model.priority.definitions.ep_task". Abort.
Goal True. idtac "BEGIN|prosa.model.priority.edf.EDF". Abort.
Check @prosa.model.priority.edf.EDF.
Goal True. idtac "END|prosa.model.priority.edf.EDF". Abort.
Goal True. idtac "BEGIN|prosa.model.priority.edf.EDF_is_reflexive". Abort.
Check @prosa.model.priority.edf.EDF_is_reflexive.
Goal True. idtac "END|prosa.model.priority.edf.EDF_is_reflexive". Abort.
Goal True. idtac "BEGIN|prosa.model.priority.edf.EDF_is_transitive". Abort.
Check @prosa.model.priority.edf.EDF_is_transitive.
Goal True. idtac "END|prosa.model.priority.edf.EDF_is_transitive". Abort.
Goal True. idtac "BEGIN|prosa.model.priority.edf.EDF_is_total". Abort.
Check @prosa.model.priority.edf.EDF_is_total.
Goal True. idtac "END|prosa.model.priority.edf.EDF_is_total". Abort.
Goal True. idtac "BEGIN|prosa.model.priority.elf.ELF". Abort.
Check @prosa.model.priority.elf.ELF.
Goal True. idtac "END|prosa.model.priority.elf.ELF". Abort.
Goal True. idtac "BEGIN|prosa.model.priority.fifo.FIFO". Abort.
Check @prosa.model.priority.fifo.FIFO.
Goal True. idtac "END|prosa.model.priority.fifo.FIFO". Abort.
Goal True. idtac "BEGIN|prosa.model.priority.fifo.FIFO_is_reflexive". Abort.
Check @prosa.model.priority.fifo.FIFO_is_reflexive.
Goal True. idtac "END|prosa.model.priority.fifo.FIFO_is_reflexive". Abort.
Goal True. idtac "BEGIN|prosa.model.priority.fifo.FIFO_is_transitive". Abort.
Check @prosa.model.priority.fifo.FIFO_is_transitive.
Goal True. idtac "END|prosa.model.priority.fifo.FIFO_is_transitive". Abort.
Goal True. idtac "BEGIN|prosa.model.priority.fifo.FIFO_is_total". Abort.
Check @prosa.model.priority.fifo.FIFO_is_total.
Goal True. idtac "END|prosa.model.priority.fifo.FIFO_is_total". Abort.
Goal True. idtac "BEGIN|prosa.model.priority.gel.offset". Abort.
Check @prosa.model.priority.gel.offset.
Goal True. idtac "END|prosa.model.priority.gel.offset". Abort.
Goal True. idtac "BEGIN|prosa.model.priority.gel.PriorityPoint". Abort.
Check @prosa.model.priority.gel.PriorityPoint.
Goal True. idtac "END|prosa.model.priority.gel.PriorityPoint". Abort.
Goal True. idtac "BEGIN|prosa.model.priority.gel.job_priority_point". Abort.
Check @prosa.model.priority.gel.job_priority_point.
Goal True. idtac "END|prosa.model.priority.gel.job_priority_point". Abort.
Goal True. idtac "BEGIN|prosa.model.priority.gel.GEL". Abort.
Check @prosa.model.priority.gel.GEL.
Goal True. idtac "END|prosa.model.priority.gel.GEL". Abort.
Goal True. idtac "BEGIN|prosa.model.priority.gel.GEL_is_reflexive". Abort.
Check @prosa.model.priority.gel.GEL_is_reflexive.
Goal True. idtac "END|prosa.model.priority.gel.GEL_is_reflexive". Abort.
Goal True. idtac "BEGIN|prosa.model.priority.gel.GEL_is_transitive". Abort.
Check @prosa.model.priority.gel.GEL_is_transitive.
Goal True. idtac "END|prosa.model.priority.gel.GEL_is_transitive". Abort.
Goal True. idtac "BEGIN|prosa.model.priority.gel.GEL_is_total". Abort.
Check @prosa.model.priority.gel.GEL_is_total.
Goal True. idtac "END|prosa.model.priority.gel.GEL_is_total". Abort.
Goal True. idtac "BEGIN|prosa.model.priority.numeric_fixed_priority.TaskPriority". Abort.
Check @prosa.model.priority.numeric_fixed_priority.TaskPriority.
Goal True. idtac "END|prosa.model.priority.numeric_fixed_priority.TaskPriority". Abort.
Goal True. idtac "BEGIN|prosa.model.priority.numeric_fixed_priority.NFPA_is_reflexive". Abort.
Check @prosa.model.priority.numeric_fixed_priority.NFPA_is_reflexive.
Goal True. idtac "END|prosa.model.priority.numeric_fixed_priority.NFPA_is_reflexive". Abort.
Goal True. idtac "BEGIN|prosa.model.priority.numeric_fixed_priority.NFPA_is_transitive". Abort.
Check @prosa.model.priority.numeric_fixed_priority.NFPA_is_transitive.
Goal True. idtac "END|prosa.model.priority.numeric_fixed_priority.NFPA_is_transitive". Abort.
Goal True. idtac "BEGIN|prosa.model.priority.numeric_fixed_priority.NFPA_is_total". Abort.
Check @prosa.model.priority.numeric_fixed_priority.NFPA_is_total.
Goal True. idtac "END|prosa.model.priority.numeric_fixed_priority.NFPA_is_total". Abort.
Goal True. idtac "BEGIN|prosa.model.priority.numeric_fixed_priority.NFPD_is_reflexive". Abort.
Check @prosa.model.priority.numeric_fixed_priority.NFPD_is_reflexive.
Goal True. idtac "END|prosa.model.priority.numeric_fixed_priority.NFPD_is_reflexive". Abort.
Goal True. idtac "BEGIN|prosa.model.priority.numeric_fixed_priority.NFPD_is_transitive". Abort.
Check @prosa.model.priority.numeric_fixed_priority.NFPD_is_transitive.
Goal True. idtac "END|prosa.model.priority.numeric_fixed_priority.NFPD_is_transitive". Abort.
Goal True. idtac "BEGIN|prosa.model.priority.numeric_fixed_priority.NFPD_is_total". Abort.
Check @prosa.model.priority.numeric_fixed_priority.NFPD_is_total.
Goal True. idtac "END|prosa.model.priority.numeric_fixed_priority.NFPD_is_total". Abort.
Goal True. idtac "BEGIN|prosa.model.priority.rate_monotonic.RM". Abort.
Check @prosa.model.priority.rate_monotonic.RM.
Goal True. idtac "END|prosa.model.priority.rate_monotonic.RM". Abort.
Goal True. idtac "BEGIN|prosa.model.priority.rate_monotonic.RM_is_reflexive". Abort.
Check @prosa.model.priority.rate_monotonic.RM_is_reflexive.
Goal True. idtac "END|prosa.model.priority.rate_monotonic.RM_is_reflexive". Abort.
Goal True. idtac "BEGIN|prosa.model.priority.rate_monotonic.RM_is_transitive". Abort.
Check @prosa.model.priority.rate_monotonic.RM_is_transitive.
Goal True. idtac "END|prosa.model.priority.rate_monotonic.RM_is_transitive". Abort.
Goal True. idtac "BEGIN|prosa.model.priority.rate_monotonic.RM_is_total". Abort.
Check @prosa.model.priority.rate_monotonic.RM_is_total.
Goal True. idtac "END|prosa.model.priority.rate_monotonic.RM_is_total". Abort.
Goal True. idtac "BEGIN|prosa.model.processor.ideal.processor_state". Abort.
Check @prosa.model.processor.ideal.processor_state.
Goal True. idtac "END|prosa.model.processor.ideal.processor_state". Abort.
Goal True. idtac "BEGIN|prosa.model.processor.ideal.ideal_is_idle". Abort.
Check @prosa.model.processor.ideal.ideal_is_idle.
Goal True. idtac "END|prosa.model.processor.ideal.ideal_is_idle". Abort.
Goal True. idtac "BEGIN|prosa.model.processor.ideal_uni_exceed.exceedance_processor_state". Abort.
Check @prosa.model.processor.ideal_uni_exceed.exceedance_processor_state.
Goal True. idtac "END|prosa.model.processor.ideal_uni_exceed.exceedance_processor_state". Abort.
Goal True. idtac "BEGIN|prosa.model.processor.ideal_uni_exceed.exceedance_processor_state_eqdef". Abort.
Check @prosa.model.processor.ideal_uni_exceed.exceedance_processor_state_eqdef.
Goal True. idtac "END|prosa.model.processor.ideal_uni_exceed.exceedance_processor_state_eqdef". Abort.
Goal True. idtac "BEGIN|prosa.model.processor.ideal_uni_exceed.eqn_exceedance_processor_state". Abort.
Check @prosa.model.processor.ideal_uni_exceed.eqn_exceedance_processor_state.
Goal True. idtac "END|prosa.model.processor.ideal_uni_exceed.eqn_exceedance_processor_state". Abort.
Goal True. idtac "BEGIN|prosa.model.processor.ideal_uni_exceed.exceedance_scheduled_on". Abort.
Check @prosa.model.processor.ideal_uni_exceed.exceedance_scheduled_on.
Goal True. idtac "END|prosa.model.processor.ideal_uni_exceed.exceedance_scheduled_on". Abort.
Goal True. idtac "BEGIN|prosa.model.processor.ideal_uni_exceed.exceedance_supply_on". Abort.
Check @prosa.model.processor.ideal_uni_exceed.exceedance_supply_on.
Goal True. idtac "END|prosa.model.processor.ideal_uni_exceed.exceedance_supply_on". Abort.
Goal True. idtac "BEGIN|prosa.model.processor.ideal_uni_exceed.exceedance_service_on". Abort.
Check @prosa.model.processor.ideal_uni_exceed.exceedance_service_on.
Goal True. idtac "END|prosa.model.processor.ideal_uni_exceed.exceedance_service_on". Abort.
Goal True. idtac "BEGIN|prosa.model.processor.ideal_uni_exceed.exceedance_proc_state". Abort.
Check @prosa.model.processor.ideal_uni_exceed.exceedance_proc_state.
Goal True. idtac "END|prosa.model.processor.ideal_uni_exceed.exceedance_proc_state". Abort.
Goal True. idtac "BEGIN|prosa.model.processor.multiprocessor.processor". Abort.
Check @prosa.model.processor.multiprocessor.processor.
Goal True. idtac "END|prosa.model.processor.multiprocessor.processor". Abort.
Goal True. idtac "BEGIN|prosa.model.processor.multiprocessor.multiprocessor_state". Abort.
Check @prosa.model.processor.multiprocessor.multiprocessor_state.
Goal True. idtac "END|prosa.model.processor.multiprocessor.multiprocessor_state". Abort.
Goal True. idtac "BEGIN|prosa.model.processor.multiprocessor.multiproc_scheduled_on". Abort.
Check @prosa.model.processor.multiprocessor.multiproc_scheduled_on.
Goal True. idtac "END|prosa.model.processor.multiprocessor.multiproc_scheduled_on". Abort.
Goal True. idtac "BEGIN|prosa.model.processor.multiprocessor.multiproc_supply_on". Abort.
Check @prosa.model.processor.multiprocessor.multiproc_supply_on.
Goal True. idtac "END|prosa.model.processor.multiprocessor.multiproc_supply_on". Abort.
Goal True. idtac "BEGIN|prosa.model.processor.multiprocessor.multiproc_service_on". Abort.
Check @prosa.model.processor.multiprocessor.multiproc_service_on.
Goal True. idtac "END|prosa.model.processor.multiprocessor.multiproc_service_on". Abort.
Goal True. idtac "BEGIN|prosa.model.processor.multiprocessor.multiproc_service_in_eq". Abort.
Check @prosa.model.processor.multiprocessor.multiproc_service_in_eq.
Goal True. idtac "END|prosa.model.processor.multiprocessor.multiproc_service_in_eq". Abort.
Goal True. idtac "BEGIN|prosa.model.processor.overhead_resource_model.time_spent_in_dispatch". Abort.
Check @prosa.model.processor.overhead_resource_model.time_spent_in_dispatch.
Goal True. idtac "END|prosa.model.processor.overhead_resource_model.time_spent_in_dispatch". Abort.
Goal True. idtac "BEGIN|prosa.model.processor.overhead_resource_model.time_spent_in_context_switch". Abort.
Check @prosa.model.processor.overhead_resource_model.time_spent_in_context_switch.
Goal True. idtac "END|prosa.model.processor.overhead_resource_model.time_spent_in_context_switch". Abort.
Goal True. idtac "BEGIN|prosa.model.processor.overhead_resource_model.time_spent_in_CRPD". Abort.
Check @prosa.model.processor.overhead_resource_model.time_spent_in_CRPD.
Goal True. idtac "END|prosa.model.processor.overhead_resource_model.time_spent_in_CRPD". Abort.
Goal True. idtac "BEGIN|prosa.model.processor.overhead_resource_model.time_spent_in_dispatch_is_bounded_by". Abort.
Check @prosa.model.processor.overhead_resource_model.time_spent_in_dispatch_is_bounded_by.
Goal True. idtac "END|prosa.model.processor.overhead_resource_model.time_spent_in_dispatch_is_bounded_by". Abort.
Goal True. idtac "BEGIN|prosa.model.processor.overhead_resource_model.time_spent_in_context_switch_is_bounded_by". Abort.
Check @prosa.model.processor.overhead_resource_model.time_spent_in_context_switch_is_bounded_by.
Goal True. idtac "END|prosa.model.processor.overhead_resource_model.time_spent_in_context_switch_is_bounded_by". Abort.
Goal True. idtac "BEGIN|prosa.model.processor.overhead_resource_model.time_spent_in_CRPD_is_bounded_by". Abort.
Check @prosa.model.processor.overhead_resource_model.time_spent_in_CRPD_is_bounded_by.
Goal True. idtac "END|prosa.model.processor.overhead_resource_model.time_spent_in_CRPD_is_bounded_by". Abort.
Goal True. idtac "BEGIN|prosa.model.processor.overhead_resource_model.dispatch_precedes_context_switch". Abort.
Check @prosa.model.processor.overhead_resource_model.dispatch_precedes_context_switch.
Goal True. idtac "END|prosa.model.processor.overhead_resource_model.dispatch_precedes_context_switch". Abort.
Goal True. idtac "BEGIN|prosa.model.processor.overhead_resource_model.context_switch_precedes_progress". Abort.
Check @prosa.model.processor.overhead_resource_model.context_switch_precedes_progress.
Goal True. idtac "END|prosa.model.processor.overhead_resource_model.context_switch_precedes_progress". Abort.
Goal True. idtac "BEGIN|prosa.model.processor.overhead_resource_model.context_switch_precedes_CRPD". Abort.
Check @prosa.model.processor.overhead_resource_model.context_switch_precedes_CRPD.
Goal True. idtac "END|prosa.model.processor.overhead_resource_model.context_switch_precedes_CRPD". Abort.
Goal True. idtac "BEGIN|prosa.model.processor.overhead_resource_model.overhead_resource_model". Abort.
Check @prosa.model.processor.overhead_resource_model.overhead_resource_model.
Goal True. idtac "END|prosa.model.processor.overhead_resource_model.overhead_resource_model". Abort.
Goal True. idtac "BEGIN|prosa.model.processor.overheads.proc_state". Abort.
Check @prosa.model.processor.overheads.proc_state.
Goal True. idtac "END|prosa.model.processor.overheads.proc_state". Abort.
Goal True. idtac "BEGIN|prosa.model.processor.overheads.overheads_scheduled_on". Abort.
Check @prosa.model.processor.overheads.overheads_scheduled_on.
Goal True. idtac "END|prosa.model.processor.overheads.overheads_scheduled_on". Abort.
Goal True. idtac "BEGIN|prosa.model.processor.overheads.overheads_supply_on". Abort.
Check @prosa.model.processor.overheads.overheads_supply_on.
Goal True. idtac "END|prosa.model.processor.overheads.overheads_supply_on". Abort.
Goal True. idtac "BEGIN|prosa.model.processor.overheads.overheads_service_on". Abort.
Check @prosa.model.processor.overheads.overheads_service_on.
Goal True. idtac "END|prosa.model.processor.overheads.overheads_service_on". Abort.
Goal True. idtac "BEGIN|prosa.model.processor.overheads.processor_state". Abort.
Check @prosa.model.processor.overheads.processor_state.
Goal True. idtac "END|prosa.model.processor.overheads.processor_state". Abort.
Goal True. idtac "BEGIN|prosa.model.processor.overheads.scheduled_job". Abort.
Check @prosa.model.processor.overheads.scheduled_job.
Goal True. idtac "END|prosa.model.processor.overheads.scheduled_job". Abort.
Goal True. idtac "BEGIN|prosa.model.processor.overheads.is_progress". Abort.
Check @prosa.model.processor.overheads.is_progress.
Goal True. idtac "END|prosa.model.processor.overheads.is_progress". Abort.
Goal True. idtac "BEGIN|prosa.model.processor.overheads.is_context_switch". Abort.
Check @prosa.model.processor.overheads.is_context_switch.
Goal True. idtac "END|prosa.model.processor.overheads.is_context_switch". Abort.
Goal True. idtac "BEGIN|prosa.model.processor.overheads.is_dispatch". Abort.
Check @prosa.model.processor.overheads.is_dispatch.
Goal True. idtac "END|prosa.model.processor.overheads.is_dispatch". Abort.
Goal True. idtac "BEGIN|prosa.model.processor.overheads.is_CRPD". Abort.
Check @prosa.model.processor.overheads.is_CRPD.
Goal True. idtac "END|prosa.model.processor.overheads.is_CRPD". Abort.
Goal True. idtac "BEGIN|prosa.model.processor.overheads.total_time_in_dispatch". Abort.
Check @prosa.model.processor.overheads.total_time_in_dispatch.
Goal True. idtac "END|prosa.model.processor.overheads.total_time_in_dispatch". Abort.
Goal True. idtac "BEGIN|prosa.model.processor.overheads.total_time_in_context_switch". Abort.
Check @prosa.model.processor.overheads.total_time_in_context_switch.
Goal True. idtac "END|prosa.model.processor.overheads.total_time_in_context_switch". Abort.
Goal True. idtac "BEGIN|prosa.model.processor.overheads.total_time_in_CRPD". Abort.
Check @prosa.model.processor.overheads.total_time_in_CRPD.
Goal True. idtac "END|prosa.model.processor.overheads.total_time_in_CRPD". Abort.
Goal True. idtac "BEGIN|prosa.model.processor.platform_properties.unit_service_proc_model". Abort.
Check @prosa.model.processor.platform_properties.unit_service_proc_model.
Goal True. idtac "END|prosa.model.processor.platform_properties.unit_service_proc_model". Abort.
Goal True. idtac "BEGIN|prosa.model.processor.platform_properties.ideal_progress_proc_model". Abort.
Check @prosa.model.processor.platform_properties.ideal_progress_proc_model.
Goal True. idtac "END|prosa.model.processor.platform_properties.ideal_progress_proc_model". Abort.
Goal True. idtac "BEGIN|prosa.model.processor.platform_properties.uniprocessor_model". Abort.
Check @prosa.model.processor.platform_properties.uniprocessor_model.
Goal True. idtac "END|prosa.model.processor.platform_properties.uniprocessor_model". Abort.
Goal True. idtac "BEGIN|prosa.model.processor.platform_properties.unit_supply_proc_model". Abort.
Check @prosa.model.processor.platform_properties.unit_supply_proc_model.
Goal True. idtac "END|prosa.model.processor.platform_properties.unit_supply_proc_model". Abort.
Goal True. idtac "BEGIN|prosa.model.processor.platform_properties.unit_supply_is_unit_service". Abort.
Check @prosa.model.processor.platform_properties.unit_supply_is_unit_service.
Goal True. idtac "END|prosa.model.processor.platform_properties.unit_supply_is_unit_service". Abort.
Goal True. idtac "BEGIN|prosa.model.processor.platform_properties.fully_consuming_proc_model". Abort.
Check @prosa.model.processor.platform_properties.fully_consuming_proc_model.
Goal True. idtac "END|prosa.model.processor.platform_properties.fully_consuming_proc_model". Abort.
Goal True. idtac "BEGIN|prosa.model.processor.restricted_supply.processor_state". Abort.
Check @prosa.model.processor.restricted_supply.processor_state.
Goal True. idtac "END|prosa.model.processor.restricted_supply.processor_state". Abort.
Goal True. idtac "BEGIN|prosa.model.processor.restricted_supply.rs_scheduled_on". Abort.
Check @prosa.model.processor.restricted_supply.rs_scheduled_on.
Goal True. idtac "END|prosa.model.processor.restricted_supply.rs_scheduled_on". Abort.
Goal True. idtac "BEGIN|prosa.model.processor.restricted_supply.rs_supply_on". Abort.
Check @prosa.model.processor.restricted_supply.rs_supply_on.
Goal True. idtac "END|prosa.model.processor.restricted_supply.rs_supply_on". Abort.
Goal True. idtac "BEGIN|prosa.model.processor.restricted_supply.rs_service_on". Abort.
Check @prosa.model.processor.restricted_supply.rs_service_on.
Goal True. idtac "END|prosa.model.processor.restricted_supply.rs_service_on". Abort.
Goal True. idtac "BEGIN|prosa.model.processor.restricted_supply.rs_processor_state". Abort.
Check @prosa.model.processor.restricted_supply.rs_processor_state.
Goal True. idtac "END|prosa.model.processor.restricted_supply.rs_processor_state". Abort.
Goal True. idtac "BEGIN|prosa.model.processor.spin.processor_state". Abort.
Check @prosa.model.processor.spin.processor_state.
Goal True. idtac "END|prosa.model.processor.spin.processor_state". Abort.
Goal True. idtac "BEGIN|prosa.model.processor.spin.spin_scheduled_on". Abort.
Check @prosa.model.processor.spin.spin_scheduled_on.
Goal True. idtac "END|prosa.model.processor.spin.spin_scheduled_on". Abort.
Goal True. idtac "BEGIN|prosa.model.processor.spin.spin_supply_on". Abort.
Check @prosa.model.processor.spin.spin_supply_on.
Goal True. idtac "END|prosa.model.processor.spin.spin_supply_on". Abort.
Goal True. idtac "BEGIN|prosa.model.processor.spin.spin_service_on". Abort.
Check @prosa.model.processor.spin.spin_service_on.
Goal True. idtac "END|prosa.model.processor.spin.spin_service_on". Abort.
Goal True. idtac "BEGIN|prosa.model.processor.spin.pstate_instance". Abort.
Check @prosa.model.processor.spin.pstate_instance.
Goal True. idtac "END|prosa.model.processor.spin.pstate_instance". Abort.
Goal True. idtac "BEGIN|prosa.model.processor.supply.supply_at". Abort.
Check @prosa.model.processor.supply.supply_at.
Goal True. idtac "END|prosa.model.processor.supply.supply_at". Abort.
Goal True. idtac "BEGIN|prosa.model.processor.supply.supply_during". Abort.
Check @prosa.model.processor.supply.supply_during.
Goal True. idtac "END|prosa.model.processor.supply.supply_during". Abort.
Goal True. idtac "BEGIN|prosa.model.processor.supply.has_supply". Abort.
Check @prosa.model.processor.supply.has_supply.
Goal True. idtac "END|prosa.model.processor.supply.has_supply". Abort.
Goal True. idtac "BEGIN|prosa.model.processor.supply.is_blackout". Abort.
Check @prosa.model.processor.supply.is_blackout.
Goal True. idtac "END|prosa.model.processor.supply.is_blackout". Abort.
Goal True. idtac "BEGIN|prosa.model.processor.supply.blackout_during". Abort.
Check @prosa.model.processor.supply.blackout_during.
Goal True. idtac "END|prosa.model.processor.supply.blackout_during". Abort.
Goal True. idtac "BEGIN|prosa.model.processor.varspeed.processor_state". Abort.
Check @prosa.model.processor.varspeed.processor_state.
Goal True. idtac "END|prosa.model.processor.varspeed.processor_state". Abort.
Goal True. idtac "BEGIN|prosa.model.processor.varspeed.varspeed_scheduled_on". Abort.
Check @prosa.model.processor.varspeed.varspeed_scheduled_on.
Goal True. idtac "END|prosa.model.processor.varspeed.varspeed_scheduled_on". Abort.
Goal True. idtac "BEGIN|prosa.model.processor.varspeed.varspeed_supply_on". Abort.
Check @prosa.model.processor.varspeed.varspeed_supply_on.
Goal True. idtac "END|prosa.model.processor.varspeed.varspeed_supply_on". Abort.
Goal True. idtac "BEGIN|prosa.model.processor.varspeed.varspeed_service_on". Abort.
Check @prosa.model.processor.varspeed.varspeed_service_on.
Goal True. idtac "END|prosa.model.processor.varspeed.varspeed_service_on". Abort.
Goal True. idtac "BEGIN|prosa.model.processor.varspeed.pstate_instance". Abort.
Check @prosa.model.processor.varspeed.pstate_instance.
Goal True. idtac "END|prosa.model.processor.varspeed.pstate_instance". Abort.
Goal True. idtac "BEGIN|prosa.model.readiness.jitter.JobJitter". Abort.
Check @prosa.model.readiness.jitter.JobJitter.
Goal True. idtac "END|prosa.model.readiness.jitter.JobJitter". Abort.
Goal True. idtac "BEGIN|prosa.model.readiness.jitter.is_released". Abort.
Check @prosa.model.readiness.jitter.is_released.
Goal True. idtac "END|prosa.model.readiness.jitter.is_released". Abort.
Goal True. idtac "BEGIN|prosa.model.readiness.suspension.JobSuspension". Abort.
Check @prosa.model.readiness.suspension.JobSuspension.
Goal True. idtac "END|prosa.model.readiness.suspension.JobSuspension". Abort.
Goal True. idtac "BEGIN|prosa.model.readiness.suspension.suspension_has_passed". Abort.
Check @prosa.model.readiness.suspension.suspension_has_passed.
Goal True. idtac "END|prosa.model.readiness.suspension.suspension_has_passed". Abort.
Goal True. idtac "BEGIN|prosa.model.readiness.suspension.suspended". Abort.
Check @prosa.model.readiness.suspension.suspended.
Goal True. idtac "END|prosa.model.readiness.suspension.suspended". Abort.
Goal True. idtac "BEGIN|prosa.model.readiness.suspension.total_suspension". Abort.
Check @prosa.model.readiness.suspension.total_suspension.
Goal True. idtac "END|prosa.model.readiness.suspension.total_suspension". Abort.
Goal True. idtac "BEGIN|prosa.model.schedule.edf.EDF_at". Abort.
Check @prosa.model.schedule.edf.EDF_at.
Goal True. idtac "END|prosa.model.schedule.edf.EDF_at". Abort.
Goal True. idtac "BEGIN|prosa.model.schedule.edf.EDF_schedule". Abort.
Check @prosa.model.schedule.edf.EDF_schedule.
Goal True. idtac "END|prosa.model.schedule.edf.EDF_schedule". Abort.
Goal True. idtac "BEGIN|prosa.model.schedule.limited_preemptive.schedule_respects_preemption_model". Abort.
Check @prosa.model.schedule.limited_preemptive.schedule_respects_preemption_model.
Goal True. idtac "END|prosa.model.schedule.limited_preemptive.schedule_respects_preemption_model". Abort.
Goal True. idtac "BEGIN|prosa.model.schedule.nonpreemptive.nonpreemptive_schedule". Abort.
Check @prosa.model.schedule.nonpreemptive.nonpreemptive_schedule.
Goal True. idtac "END|prosa.model.schedule.nonpreemptive.nonpreemptive_schedule". Abort.
Goal True. idtac "BEGIN|prosa.model.schedule.preemption_time.preemption_time". Abort.
Check @prosa.model.schedule.preemption_time.preemption_time.
Goal True. idtac "END|prosa.model.schedule.preemption_time.preemption_time". Abort.
Goal True. idtac "BEGIN|prosa.model.schedule.priority_driven.respects_JLDP_policy_at_preemption_point". Abort.
Check @prosa.model.schedule.priority_driven.respects_JLDP_policy_at_preemption_point.
Goal True. idtac "END|prosa.model.schedule.priority_driven.respects_JLDP_policy_at_preemption_point". Abort.
Goal True. idtac "BEGIN|prosa.model.schedule.priority_driven.respects_JLFP_policy_at_preemption_point". Abort.
Check @prosa.model.schedule.priority_driven.respects_JLFP_policy_at_preemption_point.
Goal True. idtac "END|prosa.model.schedule.priority_driven.respects_JLFP_policy_at_preemption_point". Abort.
Goal True. idtac "BEGIN|prosa.model.schedule.priority_driven.respects_FP_policy_at_preemption_point". Abort.
Check @prosa.model.schedule.priority_driven.respects_FP_policy_at_preemption_point.
Goal True. idtac "END|prosa.model.schedule.priority_driven.respects_FP_policy_at_preemption_point". Abort.
Goal True. idtac "BEGIN|prosa.model.schedule.scheduled.scheduled_jobs_at". Abort.
Check @prosa.model.schedule.scheduled.scheduled_jobs_at.
Goal True. idtac "END|prosa.model.schedule.scheduled.scheduled_jobs_at". Abort.
Goal True. idtac "BEGIN|prosa.model.schedule.scheduled.scheduled_job_at". Abort.
Check @prosa.model.schedule.scheduled.scheduled_job_at.
Goal True. idtac "END|prosa.model.schedule.scheduled.scheduled_job_at". Abort.
Goal True. idtac "BEGIN|prosa.model.schedule.scheduled.is_idle". Abort.
Check @prosa.model.schedule.scheduled.is_idle.
Goal True. idtac "END|prosa.model.schedule.scheduled.is_idle". Abort.
Goal True. idtac "BEGIN|prosa.model.schedule.tdma.TDMA_slot". Abort.
Check @prosa.model.schedule.tdma.TDMA_slot.
Goal True. idtac "END|prosa.model.schedule.tdma.TDMA_slot". Abort.
Goal True. idtac "BEGIN|prosa.model.schedule.tdma.TDMA_slot_order". Abort.
Check @prosa.model.schedule.tdma.TDMA_slot_order.
Goal True. idtac "END|prosa.model.schedule.tdma.TDMA_slot_order". Abort.
Goal True. idtac "BEGIN|prosa.model.schedule.tdma.TDMAPolicy". Abort.
Check @prosa.model.schedule.tdma.TDMAPolicy.
Goal True. idtac "END|prosa.model.schedule.tdma.TDMAPolicy". Abort.
Goal True. idtac "BEGIN|prosa.model.schedule.tdma.transitive_slot_order". Abort.
Check @prosa.model.schedule.tdma.transitive_slot_order.
Goal True. idtac "END|prosa.model.schedule.tdma.transitive_slot_order". Abort.
Goal True. idtac "BEGIN|prosa.model.schedule.tdma.total_slot_order". Abort.
Check @prosa.model.schedule.tdma.total_slot_order.
Goal True. idtac "END|prosa.model.schedule.tdma.total_slot_order". Abort.
Goal True. idtac "BEGIN|prosa.model.schedule.tdma.antisymmetric_slot_order". Abort.
Check @prosa.model.schedule.tdma.antisymmetric_slot_order.
Goal True. idtac "END|prosa.model.schedule.tdma.antisymmetric_slot_order". Abort.
Goal True. idtac "BEGIN|prosa.model.schedule.tdma.valid_time_slot". Abort.
Check @prosa.model.schedule.tdma.valid_time_slot.
Goal True. idtac "END|prosa.model.schedule.tdma.valid_time_slot". Abort.
Goal True. idtac "BEGIN|prosa.model.schedule.tdma.valid_TDMAPolicy". Abort.
Check @prosa.model.schedule.tdma.valid_TDMAPolicy.
Goal True. idtac "END|prosa.model.schedule.tdma.valid_TDMAPolicy". Abort.
Goal True. idtac "BEGIN|prosa.model.schedule.tdma.TDMA_cycle". Abort.
Check @prosa.model.schedule.tdma.TDMA_cycle.
Goal True. idtac "END|prosa.model.schedule.tdma.TDMA_cycle". Abort.
Goal True. idtac "BEGIN|prosa.model.schedule.tdma.task_slot_offset". Abort.
Check @prosa.model.schedule.tdma.task_slot_offset.
Goal True. idtac "END|prosa.model.schedule.tdma.task_slot_offset". Abort.
Goal True. idtac "BEGIN|prosa.model.schedule.tdma.task_in_time_slot". Abort.
Check @prosa.model.schedule.tdma.task_in_time_slot.
Goal True. idtac "END|prosa.model.schedule.tdma.task_in_time_slot". Abort.
Goal True. idtac "BEGIN|prosa.model.schedule.tdma.job_in_time_slot". Abort.
Check @prosa.model.schedule.tdma.job_in_time_slot.
Goal True. idtac "END|prosa.model.schedule.tdma.job_in_time_slot". Abort.
Goal True. idtac "BEGIN|prosa.model.schedule.tdma.sched_implies_in_slot". Abort.
Check @prosa.model.schedule.tdma.sched_implies_in_slot.
Goal True. idtac "END|prosa.model.schedule.tdma.sched_implies_in_slot". Abort.
Goal True. idtac "BEGIN|prosa.model.schedule.tdma.backlogged_implies_not_in_slot_or_other_job_sched". Abort.
Check @prosa.model.schedule.tdma.backlogged_implies_not_in_slot_or_other_job_sched.
Goal True. idtac "END|prosa.model.schedule.tdma.backlogged_implies_not_in_slot_or_other_job_sched". Abort.
Goal True. idtac "BEGIN|prosa.model.schedule.tdma.respects_TDMA_policy". Abort.
Check @prosa.model.schedule.tdma.respects_TDMA_policy.
Goal True. idtac "END|prosa.model.schedule.tdma.respects_TDMA_policy". Abort.
Goal True. idtac "BEGIN|prosa.model.schedule.work_conserving.work_conserving". Abort.
Check @prosa.model.schedule.work_conserving.work_conserving.
Goal True. idtac "END|prosa.model.schedule.work_conserving.work_conserving". Abort.
Goal True. idtac "BEGIN|prosa.model.schedule.work_conserving.jobs_backlogged_at". Abort.
Check @prosa.model.schedule.work_conserving.jobs_backlogged_at.
Goal True. idtac "END|prosa.model.schedule.work_conserving.jobs_backlogged_at". Abort.
Goal True. idtac "BEGIN|prosa.model.task.absolute_deadline.job_deadline_from_task_deadline". Abort.
Check @prosa.model.task.absolute_deadline.job_deadline_from_task_deadline.
Goal True. idtac "END|prosa.model.task.absolute_deadline.job_deadline_from_task_deadline". Abort.
Goal True. idtac "BEGIN|prosa.model.task.arrival.curve_as_rbf.task_max_rbf". Abort.
Check @prosa.model.task.arrival.curve_as_rbf.task_max_rbf.
Goal True. idtac "END|prosa.model.task.arrival.curve_as_rbf.task_max_rbf". Abort.
Goal True. idtac "BEGIN|prosa.model.task.arrival.curve_as_rbf.task_min_rbf". Abort.
Check @prosa.model.task.arrival.curve_as_rbf.task_min_rbf.
Goal True. idtac "END|prosa.model.task.arrival.curve_as_rbf.task_min_rbf". Abort.
Goal True. idtac "BEGIN|prosa.model.task.arrival.curve_as_rbf.MaxArrivalsRBF". Abort.
Check @prosa.model.task.arrival.curve_as_rbf.MaxArrivalsRBF.
Goal True. idtac "END|prosa.model.task.arrival.curve_as_rbf.MaxArrivalsRBF". Abort.
Goal True. idtac "BEGIN|prosa.model.task.arrival.curve_as_rbf.MinArrivalsRBF". Abort.
Check @prosa.model.task.arrival.curve_as_rbf.MinArrivalsRBF.
Goal True. idtac "END|prosa.model.task.arrival.curve_as_rbf.MinArrivalsRBF". Abort.
Goal True. idtac "BEGIN|prosa.model.task.arrival.curve_as_rbf.valid_arrival_curve_to_max_rbf". Abort.
Check @prosa.model.task.arrival.curve_as_rbf.valid_arrival_curve_to_max_rbf.
Goal True. idtac "END|prosa.model.task.arrival.curve_as_rbf.valid_arrival_curve_to_max_rbf". Abort.
Goal True. idtac "BEGIN|prosa.model.task.arrival.curve_as_rbf.valid_arrival_curve_to_min_rbf". Abort.
Check @prosa.model.task.arrival.curve_as_rbf.valid_arrival_curve_to_min_rbf.
Goal True. idtac "END|prosa.model.task.arrival.curve_as_rbf.valid_arrival_curve_to_min_rbf". Abort.
Goal True. idtac "BEGIN|prosa.model.task.arrival.curve_as_rbf.respects_arrival_curve_to_max_rbf". Abort.
Check @prosa.model.task.arrival.curve_as_rbf.respects_arrival_curve_to_max_rbf.
Goal True. idtac "END|prosa.model.task.arrival.curve_as_rbf.respects_arrival_curve_to_max_rbf". Abort.
Goal True. idtac "BEGIN|prosa.model.task.arrival.curve_as_rbf.respects_arrival_curve_to_min_rbf". Abort.
Check @prosa.model.task.arrival.curve_as_rbf.respects_arrival_curve_to_min_rbf.
Goal True. idtac "END|prosa.model.task.arrival.curve_as_rbf.respects_arrival_curve_to_min_rbf". Abort.
Goal True. idtac "BEGIN|prosa.model.task.arrival.curve_as_rbf.valid_taskset_arrival_curve_to_max_rbf". Abort.
Check @prosa.model.task.arrival.curve_as_rbf.valid_taskset_arrival_curve_to_max_rbf.
Goal True. idtac "END|prosa.model.task.arrival.curve_as_rbf.valid_taskset_arrival_curve_to_max_rbf". Abort.
Goal True. idtac "BEGIN|prosa.model.task.arrival.curve_as_rbf.valid_taskset_arrival_curve_to_min_rbf". Abort.
Check @prosa.model.task.arrival.curve_as_rbf.valid_taskset_arrival_curve_to_min_rbf.
Goal True. idtac "END|prosa.model.task.arrival.curve_as_rbf.valid_taskset_arrival_curve_to_min_rbf". Abort.
Goal True. idtac "BEGIN|prosa.model.task.arrival.curve_as_rbf.taskset_respects_arrival_curve_to_max_rbf". Abort.
Check @prosa.model.task.arrival.curve_as_rbf.taskset_respects_arrival_curve_to_max_rbf.
Goal True. idtac "END|prosa.model.task.arrival.curve_as_rbf.taskset_respects_arrival_curve_to_max_rbf". Abort.
Goal True. idtac "BEGIN|prosa.model.task.arrival.curve_as_rbf.taskset_respects_arrival_curve_to_min_rbf". Abort.
Check @prosa.model.task.arrival.curve_as_rbf.taskset_respects_arrival_curve_to_min_rbf.
Goal True. idtac "END|prosa.model.task.arrival.curve_as_rbf.taskset_respects_arrival_curve_to_min_rbf". Abort.
Goal True. idtac "BEGIN|prosa.model.task.arrival.curves.MaxArrivals". Abort.
Check @prosa.model.task.arrival.curves.MaxArrivals.
Goal True. idtac "END|prosa.model.task.arrival.curves.MaxArrivals". Abort.
Goal True. idtac "BEGIN|prosa.model.task.arrival.curves.MinArrivals". Abort.
Check @prosa.model.task.arrival.curves.MinArrivals.
Goal True. idtac "END|prosa.model.task.arrival.curves.MinArrivals". Abort.
Goal True. idtac "BEGIN|prosa.model.task.arrival.curves.MinSeparation". Abort.
Check @prosa.model.task.arrival.curves.MinSeparation.
Goal True. idtac "END|prosa.model.task.arrival.curves.MinSeparation". Abort.
Goal True. idtac "BEGIN|prosa.model.task.arrival.curves.MaxSeparation". Abort.
Check @prosa.model.task.arrival.curves.MaxSeparation.
Goal True. idtac "END|prosa.model.task.arrival.curves.MaxSeparation". Abort.
Goal True. idtac "BEGIN|prosa.model.task.arrival.curves.valid_arrival_curve". Abort.
Check @prosa.model.task.arrival.curves.valid_arrival_curve.
Goal True. idtac "END|prosa.model.task.arrival.curves.valid_arrival_curve". Abort.
Goal True. idtac "BEGIN|prosa.model.task.arrival.curves.respects_max_arrivals". Abort.
Check @prosa.model.task.arrival.curves.respects_max_arrivals.
Goal True. idtac "END|prosa.model.task.arrival.curves.respects_max_arrivals". Abort.
Goal True. idtac "BEGIN|prosa.model.task.arrival.curves.respects_min_arrivals". Abort.
Check @prosa.model.task.arrival.curves.respects_min_arrivals.
Goal True. idtac "END|prosa.model.task.arrival.curves.respects_min_arrivals". Abort.
Goal True. idtac "BEGIN|prosa.model.task.arrival.curves.respects_min_separation". Abort.
Check @prosa.model.task.arrival.curves.respects_min_separation.
Goal True. idtac "END|prosa.model.task.arrival.curves.respects_min_separation". Abort.
Goal True. idtac "BEGIN|prosa.model.task.arrival.curves.respects_max_separation". Abort.
Check @prosa.model.task.arrival.curves.respects_max_separation.
Goal True. idtac "END|prosa.model.task.arrival.curves.respects_max_separation". Abort.
Goal True. idtac "BEGIN|prosa.model.task.arrival.curves.valid_taskset_arrival_curve". Abort.
Check @prosa.model.task.arrival.curves.valid_taskset_arrival_curve.
Goal True. idtac "END|prosa.model.task.arrival.curves.valid_taskset_arrival_curve". Abort.
Goal True. idtac "BEGIN|prosa.model.task.arrival.curves.taskset_respects_max_arrivals". Abort.
Check @prosa.model.task.arrival.curves.taskset_respects_max_arrivals.
Goal True. idtac "END|prosa.model.task.arrival.curves.taskset_respects_max_arrivals". Abort.
Goal True. idtac "BEGIN|prosa.model.task.arrival.curves.taskset_respects_min_arrivals". Abort.
Check @prosa.model.task.arrival.curves.taskset_respects_min_arrivals.
Goal True. idtac "END|prosa.model.task.arrival.curves.taskset_respects_min_arrivals". Abort.
Goal True. idtac "BEGIN|prosa.model.task.arrival.curves.taskset_respects_max_separation". Abort.
Check @prosa.model.task.arrival.curves.taskset_respects_max_separation.
Goal True. idtac "END|prosa.model.task.arrival.curves.taskset_respects_max_separation". Abort.
Goal True. idtac "BEGIN|prosa.model.task.arrival.curves.taskset_respects_min_separation". Abort.
Check @prosa.model.task.arrival.curves.taskset_respects_min_separation.
Goal True. idtac "END|prosa.model.task.arrival.curves.taskset_respects_min_separation". Abort.
Goal True. idtac "BEGIN|prosa.model.task.arrival.periodic.PeriodicModel". Abort.
Check @prosa.model.task.arrival.periodic.PeriodicModel.
Goal True. idtac "END|prosa.model.task.arrival.periodic.PeriodicModel". Abort.
Goal True. idtac "BEGIN|prosa.model.task.arrival.periodic.valid_period". Abort.
Check @prosa.model.task.arrival.periodic.valid_period.
Goal True. idtac "END|prosa.model.task.arrival.periodic.valid_period". Abort.
Goal True. idtac "BEGIN|prosa.model.task.arrival.periodic.respects_periodic_task_model". Abort.
Check @prosa.model.task.arrival.periodic.respects_periodic_task_model.
Goal True. idtac "END|prosa.model.task.arrival.periodic.respects_periodic_task_model". Abort.
Goal True. idtac "BEGIN|prosa.model.task.arrival.periodic.valid_periods". Abort.
Check @prosa.model.task.arrival.periodic.valid_periods.
Goal True. idtac "END|prosa.model.task.arrival.periodic.valid_periods". Abort.
Goal True. idtac "BEGIN|prosa.model.task.arrival.periodic.taskset_respects_periodic_task_model". Abort.
Check @prosa.model.task.arrival.periodic.taskset_respects_periodic_task_model.
Goal True. idtac "END|prosa.model.task.arrival.periodic.taskset_respects_periodic_task_model". Abort.
Goal True. idtac "BEGIN|prosa.model.task.arrival.periodic_as_sporadic.periodic_as_sporadic". Abort.
Check @prosa.model.task.arrival.periodic_as_sporadic.periodic_as_sporadic.
Goal True. idtac "END|prosa.model.task.arrival.periodic_as_sporadic.periodic_as_sporadic". Abort.
Goal True. idtac "BEGIN|prosa.model.task.arrival.periodic_as_sporadic.valid_period_is_valid_inter_arrival_time". Abort.
Check @prosa.model.task.arrival.periodic_as_sporadic.valid_period_is_valid_inter_arrival_time.
Goal True. idtac "END|prosa.model.task.arrival.periodic_as_sporadic.valid_period_is_valid_inter_arrival_time". Abort.
Goal True. idtac "BEGIN|prosa.model.task.arrival.periodic_as_sporadic.periodic_task_respects_sporadic_task_model". Abort.
Check @prosa.model.task.arrival.periodic_as_sporadic.periodic_task_respects_sporadic_task_model.
Goal True. idtac "END|prosa.model.task.arrival.periodic_as_sporadic.periodic_task_respects_sporadic_task_model". Abort.
Goal True. idtac "BEGIN|prosa.model.task.arrival.periodic_as_sporadic.valid_periods_are_valid_inter_arrival_times". Abort.
Check @prosa.model.task.arrival.periodic_as_sporadic.valid_periods_are_valid_inter_arrival_times.
Goal True. idtac "END|prosa.model.task.arrival.periodic_as_sporadic.valid_periods_are_valid_inter_arrival_times". Abort.
Goal True. idtac "BEGIN|prosa.model.task.arrival.periodic_as_sporadic.periodic_task_sets_respect_sporadic_task_model". Abort.
Check @prosa.model.task.arrival.periodic_as_sporadic.periodic_task_sets_respect_sporadic_task_model.
Goal True. idtac "END|prosa.model.task.arrival.periodic_as_sporadic.periodic_task_sets_respect_sporadic_task_model". Abort.
Goal True. idtac "BEGIN|prosa.model.task.arrival.request_bound_functions.MaxRequestBound". Abort.
Check @prosa.model.task.arrival.request_bound_functions.MaxRequestBound.
Goal True. idtac "END|prosa.model.task.arrival.request_bound_functions.MaxRequestBound". Abort.
Goal True. idtac "BEGIN|prosa.model.task.arrival.request_bound_functions.MinRequestBound". Abort.
Check @prosa.model.task.arrival.request_bound_functions.MinRequestBound.
Goal True. idtac "END|prosa.model.task.arrival.request_bound_functions.MinRequestBound". Abort.
Goal True. idtac "BEGIN|prosa.model.task.arrival.request_bound_functions.valid_request_bound_function". Abort.
Check @prosa.model.task.arrival.request_bound_functions.valid_request_bound_function.
Goal True. idtac "END|prosa.model.task.arrival.request_bound_functions.valid_request_bound_function". Abort.
Goal True. idtac "BEGIN|prosa.model.task.arrival.request_bound_functions.respects_max_request_bound". Abort.
Check @prosa.model.task.arrival.request_bound_functions.respects_max_request_bound.
Goal True. idtac "END|prosa.model.task.arrival.request_bound_functions.respects_max_request_bound". Abort.
Goal True. idtac "BEGIN|prosa.model.task.arrival.request_bound_functions.respects_min_request_bound". Abort.
Check @prosa.model.task.arrival.request_bound_functions.respects_min_request_bound.
Goal True. idtac "END|prosa.model.task.arrival.request_bound_functions.respects_min_request_bound". Abort.
Goal True. idtac "BEGIN|prosa.model.task.arrival.request_bound_functions.valid_taskset_request_bound_function". Abort.
Check @prosa.model.task.arrival.request_bound_functions.valid_taskset_request_bound_function.
Goal True. idtac "END|prosa.model.task.arrival.request_bound_functions.valid_taskset_request_bound_function". Abort.
Goal True. idtac "BEGIN|prosa.model.task.arrival.request_bound_functions.taskset_respects_max_request_bound". Abort.
Check @prosa.model.task.arrival.request_bound_functions.taskset_respects_max_request_bound.
Goal True. idtac "END|prosa.model.task.arrival.request_bound_functions.taskset_respects_max_request_bound". Abort.
Goal True. idtac "BEGIN|prosa.model.task.arrival.request_bound_functions.taskset_respects_min_request_bound". Abort.
Check @prosa.model.task.arrival.request_bound_functions.taskset_respects_min_request_bound.
Goal True. idtac "END|prosa.model.task.arrival.request_bound_functions.taskset_respects_min_request_bound". Abort.
Goal True. idtac "BEGIN|prosa.model.task.arrival.sporadic.SporadicModel". Abort.
Check @prosa.model.task.arrival.sporadic.SporadicModel.
Goal True. idtac "END|prosa.model.task.arrival.sporadic.SporadicModel". Abort.
Goal True. idtac "BEGIN|prosa.model.task.arrival.sporadic.valid_task_min_inter_arrival_time". Abort.
Check @prosa.model.task.arrival.sporadic.valid_task_min_inter_arrival_time.
Goal True. idtac "END|prosa.model.task.arrival.sporadic.valid_task_min_inter_arrival_time". Abort.
Goal True. idtac "BEGIN|prosa.model.task.arrival.sporadic.valid_taskset_inter_arrival_times". Abort.
Check @prosa.model.task.arrival.sporadic.valid_taskset_inter_arrival_times.
Goal True. idtac "END|prosa.model.task.arrival.sporadic.valid_taskset_inter_arrival_times". Abort.
Goal True. idtac "BEGIN|prosa.model.task.arrival.sporadic.respects_sporadic_task_model". Abort.
Check @prosa.model.task.arrival.sporadic.respects_sporadic_task_model.
Goal True. idtac "END|prosa.model.task.arrival.sporadic.respects_sporadic_task_model". Abort.
Goal True. idtac "BEGIN|prosa.model.task.arrival.sporadic.taskset_respects_sporadic_task_model". Abort.
Check @prosa.model.task.arrival.sporadic.taskset_respects_sporadic_task_model.
Goal True. idtac "END|prosa.model.task.arrival.sporadic.taskset_respects_sporadic_task_model". Abort.
Goal True. idtac "BEGIN|prosa.model.task.arrival.sporadic_as_curve.MaxArrivalsSporadic". Abort.
Check @prosa.model.task.arrival.sporadic_as_curve.MaxArrivalsSporadic.
Goal True. idtac "END|prosa.model.task.arrival.sporadic_as_curve.MaxArrivalsSporadic". Abort.
Goal True. idtac "BEGIN|prosa.model.task.arrival.sporadic_as_curve.sporadic_arrival_curve_valid". Abort.
Check @prosa.model.task.arrival.sporadic_as_curve.sporadic_arrival_curve_valid.
Goal True. idtac "END|prosa.model.task.arrival.sporadic_as_curve.sporadic_arrival_curve_valid". Abort.
Goal True. idtac "BEGIN|prosa.model.task.arrival.sporadic_as_curve.sporadic_task_sets_arrival_curve_valid". Abort.
Check @prosa.model.task.arrival.sporadic_as_curve.sporadic_task_sets_arrival_curve_valid.
Goal True. idtac "END|prosa.model.task.arrival.sporadic_as_curve.sporadic_task_sets_arrival_curve_valid". Abort.
Goal True. idtac "BEGIN|prosa.model.task.arrival.sporadic_as_curve.sporadic_arrival_curve_respects_max_arrivals". Abort.
Check @prosa.model.task.arrival.sporadic_as_curve.sporadic_arrival_curve_respects_max_arrivals.
Goal True. idtac "END|prosa.model.task.arrival.sporadic_as_curve.sporadic_arrival_curve_respects_max_arrivals". Abort.
Goal True. idtac "BEGIN|prosa.model.task.arrival.sporadic_as_curve.sporadic_task_sets_respects_max_arrivals". Abort.
Check @prosa.model.task.arrival.sporadic_as_curve.sporadic_task_sets_respects_max_arrivals.
Goal True. idtac "END|prosa.model.task.arrival.sporadic_as_curve.sporadic_task_sets_respects_max_arrivals". Abort.
Goal True. idtac "BEGIN|prosa.model.task.arrival.task_max_inter_arrival.TaskMaxInterArrival". Abort.
Check @prosa.model.task.arrival.task_max_inter_arrival.TaskMaxInterArrival.
Goal True. idtac "END|prosa.model.task.arrival.task_max_inter_arrival.TaskMaxInterArrival". Abort.
Goal True. idtac "BEGIN|prosa.model.task.arrival.task_max_inter_arrival.positive_task_max_inter_arrival_time". Abort.
Check @prosa.model.task.arrival.task_max_inter_arrival.positive_task_max_inter_arrival_time.
Goal True. idtac "END|prosa.model.task.arrival.task_max_inter_arrival.positive_task_max_inter_arrival_time". Abort.
Goal True. idtac "BEGIN|prosa.model.task.arrival.task_max_inter_arrival.arr_sep_task_max_inter_arrival". Abort.
Check @prosa.model.task.arrival.task_max_inter_arrival.arr_sep_task_max_inter_arrival.
Goal True. idtac "END|prosa.model.task.arrival.task_max_inter_arrival.arr_sep_task_max_inter_arrival". Abort.
Goal True. idtac "BEGIN|prosa.model.task.arrival.task_max_inter_arrival.valid_task_max_inter_arrival_time". Abort.
Check @prosa.model.task.arrival.task_max_inter_arrival.valid_task_max_inter_arrival_time.
Goal True. idtac "END|prosa.model.task.arrival.task_max_inter_arrival.valid_task_max_inter_arrival_time". Abort.
Goal True. idtac "BEGIN|prosa.model.task.arrival.task_max_inter_arrival.taskset_respects_task_max_inter_arrival_model". Abort.
Check @prosa.model.task.arrival.task_max_inter_arrival.taskset_respects_task_max_inter_arrival_model.
Goal True. idtac "END|prosa.model.task.arrival.task_max_inter_arrival.taskset_respects_task_max_inter_arrival_model". Abort.
Goal True. idtac "BEGIN|prosa.model.task.arrivals.task_arrivals_between". Abort.
Check @prosa.model.task.arrivals.task_arrivals_between.
Goal True. idtac "END|prosa.model.task.arrivals.task_arrivals_between". Abort.
Goal True. idtac "BEGIN|prosa.model.task.arrivals.task_arrivals_up_to". Abort.
Check @prosa.model.task.arrivals.task_arrivals_up_to.
Goal True. idtac "END|prosa.model.task.arrivals.task_arrivals_up_to". Abort.
Goal True. idtac "BEGIN|prosa.model.task.arrivals.task_arrivals_before". Abort.
Check @prosa.model.task.arrivals.task_arrivals_before.
Goal True. idtac "END|prosa.model.task.arrivals.task_arrivals_before". Abort.
Goal True. idtac "BEGIN|prosa.model.task.arrivals.task_arrivals_at". Abort.
Check @prosa.model.task.arrivals.task_arrivals_at.
Goal True. idtac "END|prosa.model.task.arrivals.task_arrivals_at". Abort.
Goal True. idtac "BEGIN|prosa.model.task.arrivals.number_of_task_arrivals". Abort.
Check @prosa.model.task.arrivals.number_of_task_arrivals.
Goal True. idtac "END|prosa.model.task.arrivals.number_of_task_arrivals". Abort.
Goal True. idtac "BEGIN|prosa.model.task.arrivals.cost_of_task_arrivals". Abort.
Check @prosa.model.task.arrivals.cost_of_task_arrivals.
Goal True. idtac "END|prosa.model.task.arrivals.cost_of_task_arrivals". Abort.
Goal True. idtac "BEGIN|prosa.model.task.arrivals.task_arrivals_with_deadline_within". Abort.
Check @prosa.model.task.arrivals.task_arrivals_with_deadline_within.
Goal True. idtac "END|prosa.model.task.arrivals.task_arrivals_with_deadline_within". Abort.
Goal True. idtac "BEGIN|prosa.model.task.arrivals.number_of_task_arrivals_with_deadline_within". Abort.
Check @prosa.model.task.arrivals.number_of_task_arrivals_with_deadline_within.
Goal True. idtac "END|prosa.model.task.arrivals.number_of_task_arrivals_with_deadline_within". Abort.
Goal True. idtac "BEGIN|prosa.model.task.arrivals.task_arrivals_up_to_job_arrival". Abort.
Check @prosa.model.task.arrivals.task_arrivals_up_to_job_arrival.
Goal True. idtac "END|prosa.model.task.arrivals.task_arrivals_up_to_job_arrival". Abort.
Goal True. idtac "BEGIN|prosa.model.task.arrivals.task_arrivals_before_job_arrival". Abort.
Check @prosa.model.task.arrivals.task_arrivals_before_job_arrival.
Goal True. idtac "END|prosa.model.task.arrivals.task_arrivals_before_job_arrival". Abort.
Goal True. idtac "BEGIN|prosa.model.task.arrivals.task_arrivals_at_job_arrival". Abort.
Check @prosa.model.task.arrivals.task_arrivals_at_job_arrival.
Goal True. idtac "END|prosa.model.task.arrivals.task_arrivals_at_job_arrival". Abort.
Goal True. idtac "BEGIN|prosa.model.task.arrivals.job_index". Abort.
Check @prosa.model.task.arrivals.job_index.
Goal True. idtac "END|prosa.model.task.arrivals.job_index". Abort.
Goal True. idtac "BEGIN|prosa.model.task.arrivals.prev_job". Abort.
Check @prosa.model.task.arrivals.prev_job.
Goal True. idtac "END|prosa.model.task.arrivals.prev_job". Abort.
Goal True. idtac "BEGIN|prosa.model.task.concept.TaskType". Abort.
Check @prosa.model.task.concept.TaskType.
Goal True. idtac "END|prosa.model.task.concept.TaskType". Abort.
Goal True. idtac "BEGIN|prosa.model.task.concept.JobTask". Abort.
Check @prosa.model.task.concept.JobTask.
Goal True. idtac "END|prosa.model.task.concept.JobTask". Abort.
Goal True. idtac "BEGIN|prosa.model.task.concept.TaskDeadline". Abort.
Check @prosa.model.task.concept.TaskDeadline.
Goal True. idtac "END|prosa.model.task.concept.TaskDeadline". Abort.
Goal True. idtac "BEGIN|prosa.model.task.concept.TaskCost". Abort.
Check @prosa.model.task.concept.TaskCost.
Goal True. idtac "END|prosa.model.task.concept.TaskCost". Abort.
Goal True. idtac "BEGIN|prosa.model.task.concept.TaskMinCost". Abort.
Check @prosa.model.task.concept.TaskMinCost.
Goal True. idtac "END|prosa.model.task.concept.TaskMinCost". Abort.
Goal True. idtac "BEGIN|prosa.model.task.concept.task_cost_positive". Abort.
Check @prosa.model.task.concept.task_cost_positive.
Goal True. idtac "END|prosa.model.task.concept.task_cost_positive". Abort.
Goal True. idtac "BEGIN|prosa.model.task.concept.task_cost_at_most_deadline". Abort.
Check @prosa.model.task.concept.task_cost_at_most_deadline.
Goal True. idtac "END|prosa.model.task.concept.task_cost_at_most_deadline". Abort.
Goal True. idtac "BEGIN|prosa.model.task.concept.valid_job_cost". Abort.
Check @prosa.model.task.concept.valid_job_cost.
Goal True. idtac "END|prosa.model.task.concept.valid_job_cost". Abort.
Goal True. idtac "BEGIN|prosa.model.task.concept.jobs_have_valid_job_costs". Abort.
Check @prosa.model.task.concept.jobs_have_valid_job_costs.
Goal True. idtac "END|prosa.model.task.concept.jobs_have_valid_job_costs". Abort.
Goal True. idtac "BEGIN|prosa.model.task.concept.arrivals_have_valid_job_costs". Abort.
Check @prosa.model.task.concept.arrivals_have_valid_job_costs.
Goal True. idtac "END|prosa.model.task.concept.arrivals_have_valid_job_costs". Abort.
Goal True. idtac "BEGIN|prosa.model.task.concept.valid_min_job_cost". Abort.
Check @prosa.model.task.concept.valid_min_job_cost.
Goal True. idtac "END|prosa.model.task.concept.valid_min_job_cost". Abort.
Goal True. idtac "BEGIN|prosa.model.task.concept.jobs_have_valid_min_job_costs". Abort.
Check @prosa.model.task.concept.jobs_have_valid_min_job_costs.
Goal True. idtac "END|prosa.model.task.concept.jobs_have_valid_min_job_costs". Abort.
Goal True. idtac "BEGIN|prosa.model.task.concept.arrivals_have_valid_min_job_costs". Abort.
Check @prosa.model.task.concept.arrivals_have_valid_min_job_costs.
Goal True. idtac "END|prosa.model.task.concept.arrivals_have_valid_min_job_costs". Abort.
Goal True. idtac "BEGIN|prosa.model.task.concept.TaskSet". Abort.
Check @prosa.model.task.concept.TaskSet.
Goal True. idtac "END|prosa.model.task.concept.TaskSet". Abort.
Goal True. idtac "BEGIN|prosa.model.task.concept.all_jobs_from_taskset". Abort.
Check @prosa.model.task.concept.all_jobs_from_taskset.
Goal True. idtac "END|prosa.model.task.concept.all_jobs_from_taskset". Abort.
Goal True. idtac "BEGIN|prosa.model.task.concept.same_task". Abort.
Check @prosa.model.task.concept.same_task.
Goal True. idtac "END|prosa.model.task.concept.same_task". Abort.
Goal True. idtac "BEGIN|prosa.model.task.concept.same_task_sym". Abort.
Check @prosa.model.task.concept.same_task_sym.
Goal True. idtac "END|prosa.model.task.concept.same_task_sym". Abort.
Goal True. idtac "BEGIN|prosa.model.task.concept.job_of_task". Abort.
Check @prosa.model.task.concept.job_of_task.
Goal True. idtac "END|prosa.model.task.concept.job_of_task". Abort.
Goal True. idtac "BEGIN|prosa.model.task.concept.diff_task". Abort.
Check @prosa.model.task.concept.diff_task.
Goal True. idtac "END|prosa.model.task.concept.diff_task". Abort.
Goal True. idtac "BEGIN|prosa.model.task.jitter.TaskJitter". Abort.
Check @prosa.model.task.jitter.TaskJitter.
Goal True. idtac "END|prosa.model.task.jitter.TaskJitter". Abort.
Goal True. idtac "BEGIN|prosa.model.task.jitter.valid_jitter". Abort.
Check @prosa.model.task.jitter.valid_jitter.
Goal True. idtac "END|prosa.model.task.jitter.valid_jitter". Abort.
Goal True. idtac "BEGIN|prosa.model.task.jitter.valid_jitter_bounds". Abort.
Check @prosa.model.task.jitter.valid_jitter_bounds.
Goal True. idtac "END|prosa.model.task.jitter.valid_jitter_bounds". Abort.
Goal True. idtac "BEGIN|prosa.model.task.offset.TaskOffset". Abort.
Check @prosa.model.task.offset.TaskOffset.
Goal True. idtac "END|prosa.model.task.offset.TaskOffset". Abort.
Goal True. idtac "BEGIN|prosa.model.task.offset.no_jobs_before_offset". Abort.
Check @prosa.model.task.offset.no_jobs_before_offset.
Goal True. idtac "END|prosa.model.task.offset.no_jobs_before_offset". Abort.
Goal True. idtac "BEGIN|prosa.model.task.offset.job_released_at_offset". Abort.
Check @prosa.model.task.offset.job_released_at_offset.
Goal True. idtac "END|prosa.model.task.offset.job_released_at_offset". Abort.
Goal True. idtac "BEGIN|prosa.model.task.offset.valid_offset". Abort.
Check @prosa.model.task.offset.valid_offset.
Goal True. idtac "END|prosa.model.task.offset.valid_offset". Abort.
Goal True. idtac "BEGIN|prosa.model.task.offset.valid_offsets". Abort.
Check @prosa.model.task.offset.valid_offsets.
Goal True. idtac "END|prosa.model.task.offset.valid_offsets". Abort.
Goal True. idtac "BEGIN|prosa.model.task.offset.task_offsets". Abort.
Check @prosa.model.task.offset.task_offsets.
Goal True. idtac "END|prosa.model.task.offset.task_offsets". Abort.
Goal True. idtac "BEGIN|prosa.model.task.offset.max_task_offset". Abort.
Check @prosa.model.task.offset.max_task_offset.
Goal True. idtac "END|prosa.model.task.offset.max_task_offset". Abort.
Goal True. idtac "BEGIN|prosa.model.task.preemption.floating_nonpreemptive.job_respects_task_max_np_segment". Abort.
Check @prosa.model.task.preemption.floating_nonpreemptive.job_respects_task_max_np_segment.
Goal True. idtac "END|prosa.model.task.preemption.floating_nonpreemptive.job_respects_task_max_np_segment". Abort.
Goal True. idtac "BEGIN|prosa.model.task.preemption.floating_nonpreemptive.valid_model_with_floating_nonpreemptive_regions". Abort.
Check @prosa.model.task.preemption.floating_nonpreemptive.valid_model_with_floating_nonpreemptive_regions.
Goal True. idtac "END|prosa.model.task.preemption.floating_nonpreemptive.valid_model_with_floating_nonpreemptive_regions". Abort.
Goal True. idtac "BEGIN|prosa.model.task.preemption.fully_nonpreemptive.fully_nonpreemptive_task_model". Abort.
Check @prosa.model.task.preemption.fully_nonpreemptive.fully_nonpreemptive_task_model.
Goal True. idtac "END|prosa.model.task.preemption.fully_nonpreemptive.fully_nonpreemptive_task_model". Abort.
Goal True. idtac "BEGIN|prosa.model.task.preemption.fully_preemptive.fully_preemptive_task_model". Abort.
Check @prosa.model.task.preemption.fully_preemptive.fully_preemptive_task_model.
Goal True. idtac "END|prosa.model.task.preemption.fully_preemptive.fully_preemptive_task_model". Abort.
Goal True. idtac "BEGIN|prosa.model.task.preemption.limited_preemptive.task_beginning_of_execution_in_preemption_points". Abort.
Check @prosa.model.task.preemption.limited_preemptive.task_beginning_of_execution_in_preemption_points.
Goal True. idtac "END|prosa.model.task.preemption.limited_preemptive.task_beginning_of_execution_in_preemption_points". Abort.
Goal True. idtac "BEGIN|prosa.model.task.preemption.limited_preemptive.task_end_of_execution_in_preemption_points". Abort.
Check @prosa.model.task.preemption.limited_preemptive.task_end_of_execution_in_preemption_points.
Goal True. idtac "END|prosa.model.task.preemption.limited_preemptive.task_end_of_execution_in_preemption_points". Abort.
Goal True. idtac "BEGIN|prosa.model.task.preemption.limited_preemptive.nondecreasing_task_preemption_points". Abort.
Check @prosa.model.task.preemption.limited_preemptive.nondecreasing_task_preemption_points.
Goal True. idtac "END|prosa.model.task.preemption.limited_preemptive.nondecreasing_task_preemption_points". Abort.
Goal True. idtac "BEGIN|prosa.model.task.preemption.limited_preemptive.consistent_job_segment_count". Abort.
Check @prosa.model.task.preemption.limited_preemptive.consistent_job_segment_count.
Goal True. idtac "END|prosa.model.task.preemption.limited_preemptive.consistent_job_segment_count". Abort.
Goal True. idtac "BEGIN|prosa.model.task.preemption.limited_preemptive.job_respects_segment_lengths". Abort.
Check @prosa.model.task.preemption.limited_preemptive.job_respects_segment_lengths.
Goal True. idtac "END|prosa.model.task.preemption.limited_preemptive.job_respects_segment_lengths". Abort.
Goal True. idtac "BEGIN|prosa.model.task.preemption.limited_preemptive.task_segments_are_nonempty". Abort.
Check @prosa.model.task.preemption.limited_preemptive.task_segments_are_nonempty.
Goal True. idtac "END|prosa.model.task.preemption.limited_preemptive.task_segments_are_nonempty". Abort.
Goal True. idtac "BEGIN|prosa.model.task.preemption.limited_preemptive.valid_fixed_preemption_points_task_model". Abort.
Check @prosa.model.task.preemption.limited_preemptive.valid_fixed_preemption_points_task_model.
Goal True. idtac "END|prosa.model.task.preemption.limited_preemptive.valid_fixed_preemption_points_task_model". Abort.
Goal True. idtac "BEGIN|prosa.model.task.preemption.limited_preemptive.valid_fixed_preemption_points_model". Abort.
Check @prosa.model.task.preemption.limited_preemptive.valid_fixed_preemption_points_model.
Goal True. idtac "END|prosa.model.task.preemption.limited_preemptive.valid_fixed_preemption_points_model". Abort.
Goal True. idtac "BEGIN|prosa.model.task.preemption.parameters.TaskMaxNonpreemptiveSegment". Abort.
Check @prosa.model.task.preemption.parameters.TaskMaxNonpreemptiveSegment.
Goal True. idtac "END|prosa.model.task.preemption.parameters.TaskMaxNonpreemptiveSegment". Abort.
Goal True. idtac "BEGIN|prosa.model.task.preemption.parameters.TaskRunToCompletionThreshold". Abort.
Check @prosa.model.task.preemption.parameters.TaskRunToCompletionThreshold.
Goal True. idtac "END|prosa.model.task.preemption.parameters.TaskRunToCompletionThreshold". Abort.
Goal True. idtac "BEGIN|prosa.model.task.preemption.parameters.TaskPreemptionPoints". Abort.
Check @prosa.model.task.preemption.parameters.TaskPreemptionPoints.
Goal True. idtac "END|prosa.model.task.preemption.parameters.TaskPreemptionPoints". Abort.
Goal True. idtac "BEGIN|prosa.model.task.preemption.parameters.task_max_nonpr_segment". Abort.
Check @prosa.model.task.preemption.parameters.task_max_nonpr_segment.
Goal True. idtac "END|prosa.model.task.preemption.parameters.task_max_nonpr_segment". Abort.
Goal True. idtac "BEGIN|prosa.model.task.preemption.parameters.task_last_nonpr_segment". Abort.
Check @prosa.model.task.preemption.parameters.task_last_nonpr_segment.
Goal True. idtac "END|prosa.model.task.preemption.parameters.task_last_nonpr_segment". Abort.
Goal True. idtac "BEGIN|prosa.model.task.preemption.parameters.TaskPreemptionPoints_to_TaskMaxNonpreemptiveSegment_conversion". Abort.
Check @prosa.model.task.preemption.parameters.TaskPreemptionPoints_to_TaskMaxNonpreemptiveSegment_conversion.
Goal True. idtac "END|prosa.model.task.preemption.parameters.TaskPreemptionPoints_to_TaskMaxNonpreemptiveSegment_conversion". Abort.
Goal True. idtac "BEGIN|prosa.model.task.preemption.parameters.job_respects_max_nonpreemptive_segment". Abort.
Check @prosa.model.task.preemption.parameters.job_respects_max_nonpreemptive_segment.
Goal True. idtac "END|prosa.model.task.preemption.parameters.job_respects_max_nonpreemptive_segment". Abort.
Goal True. idtac "BEGIN|prosa.model.task.preemption.parameters.nonpreemptive_regions_have_bounded_length". Abort.
Check @prosa.model.task.preemption.parameters.nonpreemptive_regions_have_bounded_length.
Goal True. idtac "END|prosa.model.task.preemption.parameters.nonpreemptive_regions_have_bounded_length". Abort.
Goal True. idtac "BEGIN|prosa.model.task.preemption.parameters.model_with_bounded_nonpreemptive_segments". Abort.
Check @prosa.model.task.preemption.parameters.model_with_bounded_nonpreemptive_segments.
Goal True. idtac "END|prosa.model.task.preemption.parameters.model_with_bounded_nonpreemptive_segments". Abort.
Goal True. idtac "BEGIN|prosa.model.task.preemption.parameters.valid_model_with_bounded_nonpreemptive_segments". Abort.
Check @prosa.model.task.preemption.parameters.valid_model_with_bounded_nonpreemptive_segments.
Goal True. idtac "END|prosa.model.task.preemption.parameters.valid_model_with_bounded_nonpreemptive_segments". Abort.
Goal True. idtac "BEGIN|prosa.model.task.preemption.parameters.task_rtc_bounded_by_cost". Abort.
Check @prosa.model.task.preemption.parameters.task_rtc_bounded_by_cost.
Goal True. idtac "END|prosa.model.task.preemption.parameters.task_rtc_bounded_by_cost". Abort.
Goal True. idtac "BEGIN|prosa.model.task.preemption.parameters.job_respects_task_rtc". Abort.
Check @prosa.model.task.preemption.parameters.job_respects_task_rtc.
Goal True. idtac "END|prosa.model.task.preemption.parameters.job_respects_task_rtc". Abort.
Goal True. idtac "BEGIN|prosa.model.task.preemption.parameters.valid_task_run_to_completion_threshold". Abort.
Check @prosa.model.task.preemption.parameters.valid_task_run_to_completion_threshold.
Goal True. idtac "END|prosa.model.task.preemption.parameters.valid_task_run_to_completion_threshold". Abort.
Goal True. idtac "BEGIN|prosa.model.task.sequentiality.sequential_tasks". Abort.
Check @prosa.model.task.sequentiality.sequential_tasks.
Goal True. idtac "END|prosa.model.task.sequentiality.sequential_tasks". Abort.
Goal True. idtac "BEGIN|prosa.model.task.sequentiality.prior_jobs_complete". Abort.
Check @prosa.model.task.sequentiality.prior_jobs_complete.
Goal True. idtac "END|prosa.model.task.sequentiality.prior_jobs_complete". Abort.
Goal True. idtac "BEGIN|prosa.model.task.suspension.dynamic.TaskTotalSuspension". Abort.
Check @prosa.model.task.suspension.dynamic.TaskTotalSuspension.
Goal True. idtac "END|prosa.model.task.suspension.dynamic.TaskTotalSuspension". Abort.
Goal True. idtac "BEGIN|prosa.model.task.suspension.dynamic.valid_dynamic_suspensions". Abort.
Check @prosa.model.task.suspension.dynamic.valid_dynamic_suspensions.
Goal True. idtac "END|prosa.model.task.suspension.dynamic.valid_dynamic_suspensions". Abort.
Goal True. idtac "BEGIN|prosa.results.generality.elf.elf_generalizes_gel". Abort.
Check @prosa.results.generality.elf.elf_generalizes_gel.
Goal True. idtac "END|prosa.results.generality.elf.elf_generalizes_gel". Abort.
Goal True. idtac "BEGIN|prosa.results.generality.elf.elf_is_fixed_priority". Abort.
Check @prosa.results.generality.elf.elf_is_fixed_priority.
Goal True. idtac "END|prosa.results.generality.elf.elf_is_fixed_priority". Abort.
Goal True. idtac "BEGIN|prosa.results.generality.elf.elf_generalizes_fixed_priority". Abort.
Check @prosa.results.generality.elf.elf_generalizes_fixed_priority.
Goal True. idtac "END|prosa.results.generality.elf.elf_generalizes_fixed_priority". Abort.
Goal True. idtac "BEGIN|prosa.results.generality.gel.gel_generalizes_edf". Abort.
Check @prosa.results.generality.gel.gel_generalizes_edf.
Goal True. idtac "END|prosa.results.generality.gel.gel_generalizes_edf". Abort.
Goal True. idtac "BEGIN|prosa.results.generality.gel.gel_generalizes_fifo". Abort.
Check @prosa.results.generality.gel.gel_generalizes_fifo.
Goal True. idtac "END|prosa.results.generality.gel.gel_generalizes_fifo". Abort.
Goal True. idtac "BEGIN|prosa.results.generality.gel.pp_delta". Abort.
Check @prosa.results.generality.gel.pp_delta.
Goal True. idtac "END|prosa.results.generality.gel.pp_delta". Abort.
Goal True. idtac "BEGIN|prosa.results.generality.gel.backlogged_job_has_lower_gel_prio". Abort.
Check @prosa.results.generality.gel.backlogged_job_has_lower_gel_prio.
Goal True. idtac "END|prosa.results.generality.gel.backlogged_job_has_lower_gel_prio". Abort.
Goal True. idtac "BEGIN|prosa.results.generality.gel.gel_conditionally_generalizes_fp". Abort.
Check @prosa.results.generality.gel.gel_conditionally_generalizes_fp.
Goal True. idtac "END|prosa.results.generality.gel.gel_conditionally_generalizes_fp". Abort.
Goal True. idtac "BEGIN|prosa.results.optimality.edf.EDF_optimality". Abort.
Check @prosa.results.optimality.edf.EDF_optimality.
Goal True. idtac "END|prosa.results.optimality.edf.EDF_optimality". Abort.
Goal True. idtac "BEGIN|prosa.results.optimality.edf.EDF_WC_optimality". Abort.
Check @prosa.results.optimality.edf.EDF_WC_optimality.
Goal True. idtac "END|prosa.results.optimality.edf.EDF_WC_optimality". Abort.
Goal True. idtac "BEGIN|prosa.results.optimality.edf.EDF_priority_compliant_WC_optimality". Abort.
Check @prosa.results.optimality.edf.EDF_priority_compliant_WC_optimality.
Goal True. idtac "END|prosa.results.optimality.edf.EDF_priority_compliant_WC_optimality". Abort.
Goal True. idtac "BEGIN|prosa.results.optimality.edf.weak_EDF_optimality". Abort.
Check @prosa.results.optimality.edf.weak_EDF_optimality.
Goal True. idtac "END|prosa.results.optimality.edf.weak_EDF_optimality". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.arm.edf.floating_nonpreemptive.busy_window_recurrence_solution". Abort.
Check @prosa.results.rta.arm.edf.floating_nonpreemptive.busy_window_recurrence_solution.
Goal True. idtac "END|prosa.results.rta.arm.edf.floating_nonpreemptive.busy_window_recurrence_solution". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.arm.edf.floating_nonpreemptive.rta_recurrence_solution". Abort.
Check @prosa.results.rta.arm.edf.floating_nonpreemptive.rta_recurrence_solution.
Goal True. idtac "END|prosa.results.rta.arm.edf.floating_nonpreemptive.rta_recurrence_solution". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.arm.edf.floating_nonpreemptive.uniprocessor_response_time_bound_floating_edf". Abort.
Check @prosa.results.rta.arm.edf.floating_nonpreemptive.uniprocessor_response_time_bound_floating_edf.
Goal True. idtac "END|prosa.results.rta.arm.edf.floating_nonpreemptive.uniprocessor_response_time_bound_floating_edf". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.arm.edf.fully_nonpreemptive.busy_window_recurrence_solution". Abort.
Check @prosa.results.rta.arm.edf.fully_nonpreemptive.busy_window_recurrence_solution.
Goal True. idtac "END|prosa.results.rta.arm.edf.fully_nonpreemptive.busy_window_recurrence_solution". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.arm.edf.fully_nonpreemptive.rta_recurrence_solution". Abort.
Check @prosa.results.rta.arm.edf.fully_nonpreemptive.rta_recurrence_solution.
Goal True. idtac "END|prosa.results.rta.arm.edf.fully_nonpreemptive.rta_recurrence_solution". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.arm.edf.fully_nonpreemptive.uniprocessor_response_time_bound_fully_nonpreemptive_edf". Abort.
Check @prosa.results.rta.arm.edf.fully_nonpreemptive.uniprocessor_response_time_bound_fully_nonpreemptive_edf.
Goal True. idtac "END|prosa.results.rta.arm.edf.fully_nonpreemptive.uniprocessor_response_time_bound_fully_nonpreemptive_edf". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.arm.edf.fully_preemptive.busy_window_recurrence_solution". Abort.
Check @prosa.results.rta.arm.edf.fully_preemptive.busy_window_recurrence_solution.
Goal True. idtac "END|prosa.results.rta.arm.edf.fully_preemptive.busy_window_recurrence_solution". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.arm.edf.fully_preemptive.rta_recurrence_solution". Abort.
Check @prosa.results.rta.arm.edf.fully_preemptive.rta_recurrence_solution.
Goal True. idtac "END|prosa.results.rta.arm.edf.fully_preemptive.rta_recurrence_solution". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.arm.edf.fully_preemptive.uniprocessor_response_time_bound_fully_preemptive_edf". Abort.
Check @prosa.results.rta.arm.edf.fully_preemptive.uniprocessor_response_time_bound_fully_preemptive_edf.
Goal True. idtac "END|prosa.results.rta.arm.edf.fully_preemptive.uniprocessor_response_time_bound_fully_preemptive_edf". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.arm.edf.limited_preemptive.busy_window_recurrence_solution". Abort.
Check @prosa.results.rta.arm.edf.limited_preemptive.busy_window_recurrence_solution.
Goal True. idtac "END|prosa.results.rta.arm.edf.limited_preemptive.busy_window_recurrence_solution". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.arm.edf.limited_preemptive.rta_recurrence_solution". Abort.
Check @prosa.results.rta.arm.edf.limited_preemptive.rta_recurrence_solution.
Goal True. idtac "END|prosa.results.rta.arm.edf.limited_preemptive.rta_recurrence_solution". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.arm.edf.limited_preemptive.uniprocessor_response_time_bound_limited_edf". Abort.
Check @prosa.results.rta.arm.edf.limited_preemptive.uniprocessor_response_time_bound_limited_edf.
Goal True. idtac "END|prosa.results.rta.arm.edf.limited_preemptive.uniprocessor_response_time_bound_limited_edf". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.arm.fifo.bounded_nps.busy_window_recurrence_solution". Abort.
Check @prosa.results.rta.arm.fifo.bounded_nps.busy_window_recurrence_solution.
Goal True. idtac "END|prosa.results.rta.arm.fifo.bounded_nps.busy_window_recurrence_solution". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.arm.fifo.bounded_nps.rta_recurrence_solution". Abort.
Check @prosa.results.rta.arm.fifo.bounded_nps.rta_recurrence_solution.
Goal True. idtac "END|prosa.results.rta.arm.fifo.bounded_nps.rta_recurrence_solution". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.arm.fifo.bounded_nps.uniprocessor_response_time_bound_fifo". Abort.
Check @prosa.results.rta.arm.fifo.bounded_nps.uniprocessor_response_time_bound_fifo.
Goal True. idtac "END|prosa.results.rta.arm.fifo.bounded_nps.uniprocessor_response_time_bound_fifo". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.arm.fp.floating_nonpreemptive.busy_window_recurrence_solution". Abort.
Check @prosa.results.rta.arm.fp.floating_nonpreemptive.busy_window_recurrence_solution.
Goal True. idtac "END|prosa.results.rta.arm.fp.floating_nonpreemptive.busy_window_recurrence_solution". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.arm.fp.floating_nonpreemptive.rta_recurrence_solution". Abort.
Check @prosa.results.rta.arm.fp.floating_nonpreemptive.rta_recurrence_solution.
Goal True. idtac "END|prosa.results.rta.arm.fp.floating_nonpreemptive.rta_recurrence_solution". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.arm.fp.floating_nonpreemptive.uniprocessor_response_time_bound_floating_fp". Abort.
Check @prosa.results.rta.arm.fp.floating_nonpreemptive.uniprocessor_response_time_bound_floating_fp.
Goal True. idtac "END|prosa.results.rta.arm.fp.floating_nonpreemptive.uniprocessor_response_time_bound_floating_fp". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.arm.fp.fully_nonpreemptive.busy_window_recurrence_solution". Abort.
Check @prosa.results.rta.arm.fp.fully_nonpreemptive.busy_window_recurrence_solution.
Goal True. idtac "END|prosa.results.rta.arm.fp.fully_nonpreemptive.busy_window_recurrence_solution". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.arm.fp.fully_nonpreemptive.rta_recurrence_solution". Abort.
Check @prosa.results.rta.arm.fp.fully_nonpreemptive.rta_recurrence_solution.
Goal True. idtac "END|prosa.results.rta.arm.fp.fully_nonpreemptive.rta_recurrence_solution". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.arm.fp.fully_nonpreemptive.uniprocessor_response_time_bound_fully_non_preemptive_fp". Abort.
Check @prosa.results.rta.arm.fp.fully_nonpreemptive.uniprocessor_response_time_bound_fully_non_preemptive_fp.
Goal True. idtac "END|prosa.results.rta.arm.fp.fully_nonpreemptive.uniprocessor_response_time_bound_fully_non_preemptive_fp". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.arm.fp.fully_preemptive.busy_window_recurrence_solution". Abort.
Check @prosa.results.rta.arm.fp.fully_preemptive.busy_window_recurrence_solution.
Goal True. idtac "END|prosa.results.rta.arm.fp.fully_preemptive.busy_window_recurrence_solution". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.arm.fp.fully_preemptive.rta_recurrence_solution". Abort.
Check @prosa.results.rta.arm.fp.fully_preemptive.rta_recurrence_solution.
Goal True. idtac "END|prosa.results.rta.arm.fp.fully_preemptive.rta_recurrence_solution". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.arm.fp.fully_preemptive.uniprocessor_response_time_bound_fully_preemptive_fp". Abort.
Check @prosa.results.rta.arm.fp.fully_preemptive.uniprocessor_response_time_bound_fully_preemptive_fp.
Goal True. idtac "END|prosa.results.rta.arm.fp.fully_preemptive.uniprocessor_response_time_bound_fully_preemptive_fp". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.arm.fp.limited_preemptive.busy_window_recurrence_solution". Abort.
Check @prosa.results.rta.arm.fp.limited_preemptive.busy_window_recurrence_solution.
Goal True. idtac "END|prosa.results.rta.arm.fp.limited_preemptive.busy_window_recurrence_solution". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.arm.fp.limited_preemptive.rta_recurrence_solution". Abort.
Check @prosa.results.rta.arm.fp.limited_preemptive.rta_recurrence_solution.
Goal True. idtac "END|prosa.results.rta.arm.fp.limited_preemptive.rta_recurrence_solution". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.arm.fp.limited_preemptive.uniprocessor_response_time_bound_limited_fp". Abort.
Check @prosa.results.rta.arm.fp.limited_preemptive.uniprocessor_response_time_bound_limited_fp.
Goal True. idtac "END|prosa.results.rta.arm.fp.limited_preemptive.uniprocessor_response_time_bound_limited_fp". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.exc.fp.fully_nonpreemptive.busy_window_recurrence_solution". Abort.
Check @prosa.results.rta.exc.fp.fully_nonpreemptive.busy_window_recurrence_solution.
Goal True. idtac "END|prosa.results.rta.exc.fp.fully_nonpreemptive.busy_window_recurrence_solution". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.exc.fp.fully_nonpreemptive.rta_recurrence_solution". Abort.
Check @prosa.results.rta.exc.fp.fully_nonpreemptive.rta_recurrence_solution.
Goal True. idtac "END|prosa.results.rta.exc.fp.fully_nonpreemptive.rta_recurrence_solution". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.exc.fp.fully_nonpreemptive.uniprocessor_response_time_bound_fully_nonpreemptive_fp". Abort.
Check @prosa.results.rta.exc.fp.fully_nonpreemptive.uniprocessor_response_time_bound_fully_nonpreemptive_fp.
Goal True. idtac "END|prosa.results.rta.exc.fp.fully_nonpreemptive.uniprocessor_response_time_bound_fully_nonpreemptive_fp". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.ideal.edf.bounded_nps.is_in_search_space". Abort.
Check @prosa.results.rta.ideal.edf.bounded_nps.is_in_search_space.
Goal True. idtac "END|prosa.results.rta.ideal.edf.bounded_nps.is_in_search_space". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.ideal.edf.bounded_nps.blocking_bound_decreasing". Abort.
Check @prosa.results.rta.ideal.edf.bounded_nps.blocking_bound_decreasing.
Goal True. idtac "END|prosa.results.rta.ideal.edf.bounded_nps.blocking_bound_decreasing". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.ideal.edf.bounded_nps.task_with_equal_deadline_exists". Abort.
Check @prosa.results.rta.ideal.edf.bounded_nps.task_with_equal_deadline_exists.
Goal True. idtac "END|prosa.results.rta.ideal.edf.bounded_nps.task_with_equal_deadline_exists". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.ideal.edf.bounded_nps.search_space_inclusion". Abort.
Check @prosa.results.rta.ideal.edf.bounded_nps.search_space_inclusion.
Goal True. idtac "END|prosa.results.rta.ideal.edf.bounded_nps.search_space_inclusion". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.ideal.edf.bounded_nps.uniprocessor_response_time_bound_edf_with_bounded_nonpreemptive_segments". Abort.
Check @prosa.results.rta.ideal.edf.bounded_nps.uniprocessor_response_time_bound_edf_with_bounded_nonpreemptive_segments.
Goal True. idtac "END|prosa.results.rta.ideal.edf.bounded_nps.uniprocessor_response_time_bound_edf_with_bounded_nonpreemptive_segments". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.ideal.edf.bounded_pi.task_rbf_changes_at". Abort.
Check @prosa.results.rta.ideal.edf.bounded_pi.task_rbf_changes_at.
Goal True. idtac "END|prosa.results.rta.ideal.edf.bounded_pi.task_rbf_changes_at". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.ideal.edf.bounded_pi.bound_on_total_hep_workload_changes_at". Abort.
Check @prosa.results.rta.ideal.edf.bounded_pi.bound_on_total_hep_workload_changes_at.
Goal True. idtac "END|prosa.results.rta.ideal.edf.bounded_pi.bound_on_total_hep_workload_changes_at". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.ideal.edf.bounded_pi.priority_inversion_changes_at". Abort.
Check @prosa.results.rta.ideal.edf.bounded_pi.priority_inversion_changes_at.
Goal True. idtac "END|prosa.results.rta.ideal.edf.bounded_pi.priority_inversion_changes_at". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.ideal.edf.bounded_pi.is_in_search_space". Abort.
Check @prosa.results.rta.ideal.edf.bounded_pi.is_in_search_space.
Goal True. idtac "END|prosa.results.rta.ideal.edf.bounded_pi.is_in_search_space". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.ideal.edf.bounded_pi.instantiated_task_interference_is_bounded". Abort.
Check @prosa.results.rta.ideal.edf.bounded_pi.instantiated_task_interference_is_bounded.
Goal True. idtac "END|prosa.results.rta.ideal.edf.bounded_pi.instantiated_task_interference_is_bounded". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.ideal.edf.bounded_pi.A_is_in_concrete_search_space". Abort.
Check @prosa.results.rta.ideal.edf.bounded_pi.A_is_in_concrete_search_space.
Goal True. idtac "END|prosa.results.rta.ideal.edf.bounded_pi.A_is_in_concrete_search_space". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.ideal.edf.bounded_pi.correct_search_space". Abort.
Check @prosa.results.rta.ideal.edf.bounded_pi.correct_search_space.
Goal True. idtac "END|prosa.results.rta.ideal.edf.bounded_pi.correct_search_space". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.ideal.edf.bounded_pi.uniprocessor_response_time_bound_edf". Abort.
Check @prosa.results.rta.ideal.edf.bounded_pi.uniprocessor_response_time_bound_edf.
Goal True. idtac "END|prosa.results.rta.ideal.edf.bounded_pi.uniprocessor_response_time_bound_edf". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.ideal.edf.floating_nonpreemptive.uniprocessor_response_time_bound_edf_with_floating_nonpreemptive_regions". Abort.
Check @prosa.results.rta.ideal.edf.floating_nonpreemptive.uniprocessor_response_time_bound_edf_with_floating_nonpreemptive_regions.
Goal True. idtac "END|prosa.results.rta.ideal.edf.floating_nonpreemptive.uniprocessor_response_time_bound_edf_with_floating_nonpreemptive_regions". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.ideal.edf.fully_nonpreemptive.uniprocessor_response_time_bound_fully_nonpreemptive_edf". Abort.
Check @prosa.results.rta.ideal.edf.fully_nonpreemptive.uniprocessor_response_time_bound_fully_nonpreemptive_edf.
Goal True. idtac "END|prosa.results.rta.ideal.edf.fully_nonpreemptive.uniprocessor_response_time_bound_fully_nonpreemptive_edf". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.ideal.edf.fully_preemptive.uniprocessor_response_time_bound_fully_preemptive_edf". Abort.
Check @prosa.results.rta.ideal.edf.fully_preemptive.uniprocessor_response_time_bound_fully_preemptive_edf.
Goal True. idtac "END|prosa.results.rta.ideal.edf.fully_preemptive.uniprocessor_response_time_bound_fully_preemptive_edf". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.ideal.edf.limited_preemptive.uniprocessor_response_time_bound_edf_with_fixed_preemption_points". Abort.
Check @prosa.results.rta.ideal.edf.limited_preemptive.uniprocessor_response_time_bound_edf_with_fixed_preemption_points.
Goal True. idtac "END|prosa.results.rta.ideal.edf.limited_preemptive.uniprocessor_response_time_bound_edf_with_fixed_preemption_points". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.ideal.elf.bounded_pi.priority_inversion_bound". Abort.
Check @prosa.results.rta.ideal.elf.bounded_pi.priority_inversion_bound.
Goal True. idtac "END|prosa.results.rta.ideal.elf.bounded_pi.priority_inversion_bound". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.ideal.elf.bounded_pi.priority_inversion_is_bounded". Abort.
Check @prosa.results.rta.ideal.elf.bounded_pi.priority_inversion_is_bounded.
Goal True. idtac "END|prosa.results.rta.ideal.elf.bounded_pi.priority_inversion_is_bounded". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.ideal.elf.bounded_pi.instantiated_busy_intervals_are_bounded". Abort.
Check @prosa.results.rta.ideal.elf.bounded_pi.instantiated_busy_intervals_are_bounded.
Goal True. idtac "END|prosa.results.rta.ideal.elf.bounded_pi.instantiated_busy_intervals_are_bounded". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.ideal.elf.bounded_pi.total_hp_rbf". Abort.
Check @prosa.results.rta.ideal.elf.bounded_pi.total_hp_rbf.
Goal True. idtac "END|prosa.results.rta.ideal.elf.bounded_pi.total_hp_rbf". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.ideal.elf.bounded_pi.ep_task_intf_interval". Abort.
Check @prosa.results.rta.ideal.elf.bounded_pi.ep_task_intf_interval.
Goal True. idtac "END|prosa.results.rta.ideal.elf.bounded_pi.ep_task_intf_interval". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.ideal.elf.bounded_pi.bound_on_total_ep_workload". Abort.
Check @prosa.results.rta.ideal.elf.bounded_pi.bound_on_total_ep_workload.
Goal True. idtac "END|prosa.results.rta.ideal.elf.bounded_pi.bound_on_total_ep_workload". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.ideal.elf.bounded_pi.task_IBF". Abort.
Check @prosa.results.rta.ideal.elf.bounded_pi.task_IBF.
Goal True. idtac "END|prosa.results.rta.ideal.elf.bounded_pi.task_IBF". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.ideal.elf.bounded_pi.service_of_hp_jobs_from_other_ep_tasks". Abort.
Check @prosa.results.rta.ideal.elf.bounded_pi.service_of_hp_jobs_from_other_ep_tasks.
Goal True. idtac "END|prosa.results.rta.ideal.elf.bounded_pi.service_of_hp_jobs_from_other_ep_tasks". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.ideal.elf.bounded_pi.cumulative_intf_ep_task_service_equiv". Abort.
Check @prosa.results.rta.ideal.elf.bounded_pi.cumulative_intf_ep_task_service_equiv.
Goal True. idtac "END|prosa.results.rta.ideal.elf.bounded_pi.cumulative_intf_ep_task_service_equiv". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.ideal.elf.bounded_pi.service_of_hp_jobs_from_other_hp_tasks". Abort.
Check @prosa.results.rta.ideal.elf.bounded_pi.service_of_hp_jobs_from_other_hp_tasks.
Goal True. idtac "END|prosa.results.rta.ideal.elf.bounded_pi.service_of_hp_jobs_from_other_hp_tasks". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.ideal.elf.bounded_pi.cumulative_intf_hp_task_service_equiv". Abort.
Check @prosa.results.rta.ideal.elf.bounded_pi.cumulative_intf_hp_task_service_equiv.
Goal True. idtac "END|prosa.results.rta.ideal.elf.bounded_pi.cumulative_intf_hp_task_service_equiv". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.ideal.elf.bounded_pi.total_workload_shorten_range". Abort.
Check @prosa.results.rta.ideal.elf.bounded_pi.total_workload_shorten_range.
Goal True. idtac "END|prosa.results.rta.ideal.elf.bounded_pi.total_workload_shorten_range". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.ideal.elf.bounded_pi.bound_on_ep_workload". Abort.
Check @prosa.results.rta.ideal.elf.bounded_pi.bound_on_ep_workload.
Goal True. idtac "END|prosa.results.rta.ideal.elf.bounded_pi.bound_on_ep_workload". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.ideal.elf.bounded_pi.bound_on_hp_workload". Abort.
Check @prosa.results.rta.ideal.elf.bounded_pi.bound_on_hp_workload.
Goal True. idtac "END|prosa.results.rta.ideal.elf.bounded_pi.bound_on_hp_workload". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.ideal.elf.bounded_pi.instantiated_task_interference_is_bounded". Abort.
Check @prosa.results.rta.ideal.elf.bounded_pi.instantiated_task_interference_is_bounded.
Goal True. idtac "END|prosa.results.rta.ideal.elf.bounded_pi.instantiated_task_interference_is_bounded". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.ideal.elf.bounded_pi.task_rbf_changes_at". Abort.
Check @prosa.results.rta.ideal.elf.bounded_pi.task_rbf_changes_at.
Goal True. idtac "END|prosa.results.rta.ideal.elf.bounded_pi.task_rbf_changes_at". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.ideal.elf.bounded_pi.bound_on_total_ep_workload_changes_at". Abort.
Check @prosa.results.rta.ideal.elf.bounded_pi.bound_on_total_ep_workload_changes_at.
Goal True. idtac "END|prosa.results.rta.ideal.elf.bounded_pi.bound_on_total_ep_workload_changes_at". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.ideal.elf.bounded_pi.priority_inversion_changes_at". Abort.
Check @prosa.results.rta.ideal.elf.bounded_pi.priority_inversion_changes_at.
Goal True. idtac "END|prosa.results.rta.ideal.elf.bounded_pi.priority_inversion_changes_at". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.ideal.elf.bounded_pi.is_in_search_space". Abort.
Check @prosa.results.rta.ideal.elf.bounded_pi.is_in_search_space.
Goal True. idtac "END|prosa.results.rta.ideal.elf.bounded_pi.is_in_search_space". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.ideal.elf.bounded_pi.A_is_in_concrete_search_space". Abort.
Check @prosa.results.rta.ideal.elf.bounded_pi.A_is_in_concrete_search_space.
Goal True. idtac "END|prosa.results.rta.ideal.elf.bounded_pi.A_is_in_concrete_search_space". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.ideal.elf.bounded_pi.response_time_recurrence_solution_exists". Abort.
Check @prosa.results.rta.ideal.elf.bounded_pi.response_time_recurrence_solution_exists.
Goal True. idtac "END|prosa.results.rta.ideal.elf.bounded_pi.response_time_recurrence_solution_exists". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.ideal.elf.bounded_pi.uniprocessor_response_time_bound_elf". Abort.
Check @prosa.results.rta.ideal.elf.bounded_pi.uniprocessor_response_time_bound_elf.
Goal True. idtac "END|prosa.results.rta.ideal.elf.bounded_pi.uniprocessor_response_time_bound_elf". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.ideal.fifo.bounded_nps.abstractly_work_conserving". Abort.
Check @prosa.results.rta.ideal.fifo.bounded_nps.abstractly_work_conserving.
Goal True. idtac "END|prosa.results.rta.ideal.fifo.bounded_nps.abstractly_work_conserving". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.ideal.fifo.bounded_nps.busy_windows_are_bounded". Abort.
Check @prosa.results.rta.ideal.fifo.bounded_nps.busy_windows_are_bounded.
Goal True. idtac "END|prosa.results.rta.ideal.fifo.bounded_nps.busy_windows_are_bounded". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.ideal.fifo.bounded_nps.no_priority_inversion". Abort.
Check @prosa.results.rta.ideal.fifo.bounded_nps.no_priority_inversion.
Goal True. idtac "END|prosa.results.rta.ideal.fifo.bounded_nps.no_priority_inversion". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.ideal.fifo.bounded_nps.IBF_correct". Abort.
Check @prosa.results.rta.ideal.fifo.bounded_nps.IBF_correct.
Goal True. idtac "END|prosa.results.rta.ideal.fifo.bounded_nps.IBF_correct". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.ideal.fifo.bounded_nps.is_in_concrete_search_space". Abort.
Check @prosa.results.rta.ideal.fifo.bounded_nps.is_in_concrete_search_space.
Goal True. idtac "END|prosa.results.rta.ideal.fifo.bounded_nps.is_in_concrete_search_space". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.ideal.fifo.bounded_nps.search_space_refinement". Abort.
Check @prosa.results.rta.ideal.fifo.bounded_nps.search_space_refinement.
Goal True. idtac "END|prosa.results.rta.ideal.fifo.bounded_nps.search_space_refinement". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.ideal.fifo.bounded_nps.soln_abstract_response_time_recurrence". Abort.
Check @prosa.results.rta.ideal.fifo.bounded_nps.soln_abstract_response_time_recurrence.
Goal True. idtac "END|prosa.results.rta.ideal.fifo.bounded_nps.soln_abstract_response_time_recurrence". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.ideal.fifo.bounded_nps.uniprocessor_response_time_bound_FIFO". Abort.
Check @prosa.results.rta.ideal.fifo.bounded_nps.uniprocessor_response_time_bound_FIFO.
Goal True. idtac "END|prosa.results.rta.ideal.fifo.bounded_nps.uniprocessor_response_time_bound_FIFO". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.ideal.fp.bounded_nps.priority_inversion_is_bounded_by_blocking". Abort.
Check @prosa.results.rta.ideal.fp.bounded_nps.priority_inversion_is_bounded_by_blocking.
Goal True. idtac "END|prosa.results.rta.ideal.fp.bounded_nps.priority_inversion_is_bounded_by_blocking". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.ideal.fp.bounded_nps.priority_inversion_is_bounded". Abort.
Check @prosa.results.rta.ideal.fp.bounded_nps.priority_inversion_is_bounded.
Goal True. idtac "END|prosa.results.rta.ideal.fp.bounded_nps.priority_inversion_is_bounded". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.ideal.fp.bounded_nps.uniprocessor_response_time_bound_fp_with_bounded_nonpreemptive_segments". Abort.
Check @prosa.results.rta.ideal.fp.bounded_nps.uniprocessor_response_time_bound_fp_with_bounded_nonpreemptive_segments.
Goal True. idtac "END|prosa.results.rta.ideal.fp.bounded_nps.uniprocessor_response_time_bound_fp_with_bounded_nonpreemptive_segments". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.ideal.fp.bounded_pi.is_in_search_space". Abort.
Check @prosa.results.rta.ideal.fp.bounded_pi.is_in_search_space.
Goal True. idtac "END|prosa.results.rta.ideal.fp.bounded_pi.is_in_search_space". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.ideal.fp.bounded_pi.instantiated_busy_intervals_are_bounded". Abort.
Check @prosa.results.rta.ideal.fp.bounded_pi.instantiated_busy_intervals_are_bounded.
Goal True. idtac "END|prosa.results.rta.ideal.fp.bounded_pi.instantiated_busy_intervals_are_bounded". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.ideal.fp.bounded_pi.instantiated_task_interference_is_bounded". Abort.
Check @prosa.results.rta.ideal.fp.bounded_pi.instantiated_task_interference_is_bounded.
Goal True. idtac "END|prosa.results.rta.ideal.fp.bounded_pi.instantiated_task_interference_is_bounded". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.ideal.fp.bounded_pi.A_is_in_concrete_search_space". Abort.
Check @prosa.results.rta.ideal.fp.bounded_pi.A_is_in_concrete_search_space.
Goal True. idtac "END|prosa.results.rta.ideal.fp.bounded_pi.A_is_in_concrete_search_space". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.ideal.fp.bounded_pi.correct_search_space". Abort.
Check @prosa.results.rta.ideal.fp.bounded_pi.correct_search_space.
Goal True. idtac "END|prosa.results.rta.ideal.fp.bounded_pi.correct_search_space". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.ideal.fp.bounded_pi.uniprocessor_response_time_bound_fp". Abort.
Check @prosa.results.rta.ideal.fp.bounded_pi.uniprocessor_response_time_bound_fp.
Goal True. idtac "END|prosa.results.rta.ideal.fp.bounded_pi.uniprocessor_response_time_bound_fp". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.ideal.fp.comp.fully_preemptive.uniprocessor_response_time_bound_fully_preemptive_fp". Abort.
Check @prosa.results.rta.ideal.fp.comp.fully_preemptive.uniprocessor_response_time_bound_fully_preemptive_fp.
Goal True. idtac "END|prosa.results.rta.ideal.fp.comp.fully_preemptive.uniprocessor_response_time_bound_fully_preemptive_fp". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.ideal.fp.floating_nonpreemptive.uniprocessor_response_time_bound_fp_with_floating_nonpreemptive_regions". Abort.
Check @prosa.results.rta.ideal.fp.floating_nonpreemptive.uniprocessor_response_time_bound_fp_with_floating_nonpreemptive_regions.
Goal True. idtac "END|prosa.results.rta.ideal.fp.floating_nonpreemptive.uniprocessor_response_time_bound_fp_with_floating_nonpreemptive_regions". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.ideal.fp.fully_nonpreemptive.uniprocessor_response_time_bound_fully_nonpreemptive_fp". Abort.
Check @prosa.results.rta.ideal.fp.fully_nonpreemptive.uniprocessor_response_time_bound_fully_nonpreemptive_fp.
Goal True. idtac "END|prosa.results.rta.ideal.fp.fully_nonpreemptive.uniprocessor_response_time_bound_fully_nonpreemptive_fp". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.ideal.fp.fully_preemptive.uniprocessor_response_time_bound_fully_preemptive_fp". Abort.
Check @prosa.results.rta.ideal.fp.fully_preemptive.uniprocessor_response_time_bound_fully_preemptive_fp.
Goal True. idtac "END|prosa.results.rta.ideal.fp.fully_preemptive.uniprocessor_response_time_bound_fully_preemptive_fp". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.ideal.fp.limited_preemptive.uniprocessor_response_time_bound_fp_with_fixed_preemption_points". Abort.
Check @prosa.results.rta.ideal.fp.limited_preemptive.uniprocessor_response_time_bound_fp_with_fixed_preemption_points.
Goal True. idtac "END|prosa.results.rta.ideal.fp.limited_preemptive.uniprocessor_response_time_bound_fp_with_fixed_preemption_points". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.ideal.fp.nonseq.bounded_pi.instantiated_busy_intervals_are_bounded". Abort.
Check @prosa.results.rta.ideal.fp.nonseq.bounded_pi.instantiated_busy_intervals_are_bounded.
Goal True. idtac "END|prosa.results.rta.ideal.fp.nonseq.bounded_pi.instantiated_busy_intervals_are_bounded". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.ideal.fp.nonseq.bounded_pi.IBF". Abort.
Check @prosa.results.rta.ideal.fp.nonseq.bounded_pi.IBF.
Goal True. idtac "END|prosa.results.rta.ideal.fp.nonseq.bounded_pi.IBF". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.ideal.fp.nonseq.bounded_pi.self_intf_bound_case1". Abort.
Check @prosa.results.rta.ideal.fp.nonseq.bounded_pi.self_intf_bound_case1.
Goal True. idtac "END|prosa.results.rta.ideal.fp.nonseq.bounded_pi.self_intf_bound_case1". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.ideal.fp.nonseq.bounded_pi.self_intf_bound_case2". Abort.
Check @prosa.results.rta.ideal.fp.nonseq.bounded_pi.self_intf_bound_case2.
Goal True. idtac "END|prosa.results.rta.ideal.fp.nonseq.bounded_pi.self_intf_bound_case2". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.ideal.fp.nonseq.bounded_pi.self_intf_bound". Abort.
Check @prosa.results.rta.ideal.fp.nonseq.bounded_pi.self_intf_bound.
Goal True. idtac "END|prosa.results.rta.ideal.fp.nonseq.bounded_pi.self_intf_bound". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.ideal.fp.nonseq.bounded_pi.instantiated_task_interference_is_bounded". Abort.
Check @prosa.results.rta.ideal.fp.nonseq.bounded_pi.instantiated_task_interference_is_bounded.
Goal True. idtac "END|prosa.results.rta.ideal.fp.nonseq.bounded_pi.instantiated_task_interference_is_bounded". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.ideal.fp.nonseq.bounded_pi.is_in_concrete_search_space". Abort.
Check @prosa.results.rta.ideal.fp.nonseq.bounded_pi.is_in_concrete_search_space.
Goal True. idtac "END|prosa.results.rta.ideal.fp.nonseq.bounded_pi.is_in_concrete_search_space". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.ideal.fp.nonseq.bounded_pi.A_is_in_concrete_search_space". Abort.
Check @prosa.results.rta.ideal.fp.nonseq.bounded_pi.A_is_in_concrete_search_space.
Goal True. idtac "END|prosa.results.rta.ideal.fp.nonseq.bounded_pi.A_is_in_concrete_search_space". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.ideal.fp.nonseq.bounded_pi.correct_search_space". Abort.
Check @prosa.results.rta.ideal.fp.nonseq.bounded_pi.correct_search_space.
Goal True. idtac "END|prosa.results.rta.ideal.fp.nonseq.bounded_pi.correct_search_space". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.ideal.fp.nonseq.bounded_pi.uniprocessor_response_time_bound_fp". Abort.
Check @prosa.results.rta.ideal.fp.nonseq.bounded_pi.uniprocessor_response_time_bound_fp.
Goal True. idtac "END|prosa.results.rta.ideal.fp.nonseq.bounded_pi.uniprocessor_response_time_bound_fp". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.ideal.gel.bounded_pi.total_workload_shorten_range". Abort.
Check @prosa.results.rta.ideal.gel.bounded_pi.total_workload_shorten_range.
Goal True. idtac "END|prosa.results.rta.ideal.gel.bounded_pi.total_workload_shorten_range". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.ideal.gel.bounded_pi.sum_of_workloads_is_at_most_bound_on_total_hep_workload". Abort.
Check @prosa.results.rta.ideal.gel.bounded_pi.sum_of_workloads_is_at_most_bound_on_total_hep_workload.
Goal True. idtac "END|prosa.results.rta.ideal.gel.bounded_pi.sum_of_workloads_is_at_most_bound_on_total_hep_workload". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.ideal.gel.bounded_pi.instantiated_task_interference_is_bounded". Abort.
Check @prosa.results.rta.ideal.gel.bounded_pi.instantiated_task_interference_is_bounded.
Goal True. idtac "END|prosa.results.rta.ideal.gel.bounded_pi.instantiated_task_interference_is_bounded". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.ideal.gel.bounded_pi.task_rbf_changes_at". Abort.
Check @prosa.results.rta.ideal.gel.bounded_pi.task_rbf_changes_at.
Goal True. idtac "END|prosa.results.rta.ideal.gel.bounded_pi.task_rbf_changes_at". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.ideal.gel.bounded_pi.bound_on_total_hep_workload_changes_at". Abort.
Check @prosa.results.rta.ideal.gel.bounded_pi.bound_on_total_hep_workload_changes_at.
Goal True. idtac "END|prosa.results.rta.ideal.gel.bounded_pi.bound_on_total_hep_workload_changes_at". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.ideal.gel.bounded_pi.priority_inversion_changes_at". Abort.
Check @prosa.results.rta.ideal.gel.bounded_pi.priority_inversion_changes_at.
Goal True. idtac "END|prosa.results.rta.ideal.gel.bounded_pi.priority_inversion_changes_at". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.ideal.gel.bounded_pi.is_in_search_space". Abort.
Check @prosa.results.rta.ideal.gel.bounded_pi.is_in_search_space.
Goal True. idtac "END|prosa.results.rta.ideal.gel.bounded_pi.is_in_search_space". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.ideal.gel.bounded_pi.A_is_in_concrete_search_space". Abort.
Check @prosa.results.rta.ideal.gel.bounded_pi.A_is_in_concrete_search_space.
Goal True. idtac "END|prosa.results.rta.ideal.gel.bounded_pi.A_is_in_concrete_search_space". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.ideal.gel.bounded_pi.correct_search_space". Abort.
Check @prosa.results.rta.ideal.gel.bounded_pi.correct_search_space.
Goal True. idtac "END|prosa.results.rta.ideal.gel.bounded_pi.correct_search_space". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.ideal.gel.bounded_pi.uniprocessor_response_time_bound_edf". Abort.
Check @prosa.results.rta.ideal.gel.bounded_pi.uniprocessor_response_time_bound_edf.
Goal True. idtac "END|prosa.results.rta.ideal.gel.bounded_pi.uniprocessor_response_time_bound_edf". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.ovh.edf.floating_nonpreemptive.busy_window_recurrence_solution". Abort.
Check @prosa.results.rta.ovh.edf.floating_nonpreemptive.busy_window_recurrence_solution.
Goal True. idtac "END|prosa.results.rta.ovh.edf.floating_nonpreemptive.busy_window_recurrence_solution". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.ovh.edf.floating_nonpreemptive.rta_recurrence_solution". Abort.
Check @prosa.results.rta.ovh.edf.floating_nonpreemptive.rta_recurrence_solution.
Goal True. idtac "END|prosa.results.rta.ovh.edf.floating_nonpreemptive.rta_recurrence_solution". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.ovh.edf.floating_nonpreemptive.uniprocessor_response_time_bound_floating_edf". Abort.
Check @prosa.results.rta.ovh.edf.floating_nonpreemptive.uniprocessor_response_time_bound_floating_edf.
Goal True. idtac "END|prosa.results.rta.ovh.edf.floating_nonpreemptive.uniprocessor_response_time_bound_floating_edf". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.ovh.edf.fully_nonpreemptive.busy_window_recurrence_solution". Abort.
Check @prosa.results.rta.ovh.edf.fully_nonpreemptive.busy_window_recurrence_solution.
Goal True. idtac "END|prosa.results.rta.ovh.edf.fully_nonpreemptive.busy_window_recurrence_solution". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.ovh.edf.fully_nonpreemptive.rta_recurrence_solution". Abort.
Check @prosa.results.rta.ovh.edf.fully_nonpreemptive.rta_recurrence_solution.
Goal True. idtac "END|prosa.results.rta.ovh.edf.fully_nonpreemptive.rta_recurrence_solution". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.ovh.edf.fully_nonpreemptive.uniprocessor_response_time_bound_fully_nonpreemptive_edf". Abort.
Check @prosa.results.rta.ovh.edf.fully_nonpreemptive.uniprocessor_response_time_bound_fully_nonpreemptive_edf.
Goal True. idtac "END|prosa.results.rta.ovh.edf.fully_nonpreemptive.uniprocessor_response_time_bound_fully_nonpreemptive_edf". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.ovh.edf.fully_preemptive.busy_window_recurrence_solution". Abort.
Check @prosa.results.rta.ovh.edf.fully_preemptive.busy_window_recurrence_solution.
Goal True. idtac "END|prosa.results.rta.ovh.edf.fully_preemptive.busy_window_recurrence_solution". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.ovh.edf.fully_preemptive.rta_recurrence_solution". Abort.
Check @prosa.results.rta.ovh.edf.fully_preemptive.rta_recurrence_solution.
Goal True. idtac "END|prosa.results.rta.ovh.edf.fully_preemptive.rta_recurrence_solution". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.ovh.edf.fully_preemptive.uniprocessor_response_time_bound_fully_preemptive_edf". Abort.
Check @prosa.results.rta.ovh.edf.fully_preemptive.uniprocessor_response_time_bound_fully_preemptive_edf.
Goal True. idtac "END|prosa.results.rta.ovh.edf.fully_preemptive.uniprocessor_response_time_bound_fully_preemptive_edf". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.ovh.edf.limited_preemptive.busy_window_recurrence_solution". Abort.
Check @prosa.results.rta.ovh.edf.limited_preemptive.busy_window_recurrence_solution.
Goal True. idtac "END|prosa.results.rta.ovh.edf.limited_preemptive.busy_window_recurrence_solution". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.ovh.edf.limited_preemptive.rta_recurrence_solution". Abort.
Check @prosa.results.rta.ovh.edf.limited_preemptive.rta_recurrence_solution.
Goal True. idtac "END|prosa.results.rta.ovh.edf.limited_preemptive.rta_recurrence_solution". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.ovh.edf.limited_preemptive.uniprocessor_response_time_bound_limited_edf". Abort.
Check @prosa.results.rta.ovh.edf.limited_preemptive.uniprocessor_response_time_bound_limited_edf.
Goal True. idtac "END|prosa.results.rta.ovh.edf.limited_preemptive.uniprocessor_response_time_bound_limited_edf". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.ovh.fifo.bounded_nps.busy_window_recurrence_solution". Abort.
Check @prosa.results.rta.ovh.fifo.bounded_nps.busy_window_recurrence_solution.
Goal True. idtac "END|prosa.results.rta.ovh.fifo.bounded_nps.busy_window_recurrence_solution". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.ovh.fifo.bounded_nps.rta_recurrence_solution". Abort.
Check @prosa.results.rta.ovh.fifo.bounded_nps.rta_recurrence_solution.
Goal True. idtac "END|prosa.results.rta.ovh.fifo.bounded_nps.rta_recurrence_solution". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.ovh.fifo.bounded_nps.uniprocessor_response_time_bound_fifo". Abort.
Check @prosa.results.rta.ovh.fifo.bounded_nps.uniprocessor_response_time_bound_fifo.
Goal True. idtac "END|prosa.results.rta.ovh.fifo.bounded_nps.uniprocessor_response_time_bound_fifo". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.ovh.fp.floating_nonpreemptive.busy_window_recurrence_solution". Abort.
Check @prosa.results.rta.ovh.fp.floating_nonpreemptive.busy_window_recurrence_solution.
Goal True. idtac "END|prosa.results.rta.ovh.fp.floating_nonpreemptive.busy_window_recurrence_solution". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.ovh.fp.floating_nonpreemptive.rta_recurrence_solution". Abort.
Check @prosa.results.rta.ovh.fp.floating_nonpreemptive.rta_recurrence_solution.
Goal True. idtac "END|prosa.results.rta.ovh.fp.floating_nonpreemptive.rta_recurrence_solution". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.ovh.fp.floating_nonpreemptive.uniprocessor_response_time_bound_floating_fp". Abort.
Check @prosa.results.rta.ovh.fp.floating_nonpreemptive.uniprocessor_response_time_bound_floating_fp.
Goal True. idtac "END|prosa.results.rta.ovh.fp.floating_nonpreemptive.uniprocessor_response_time_bound_floating_fp". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.ovh.fp.fully_nonpreemptive.busy_window_recurrence_solution". Abort.
Check @prosa.results.rta.ovh.fp.fully_nonpreemptive.busy_window_recurrence_solution.
Goal True. idtac "END|prosa.results.rta.ovh.fp.fully_nonpreemptive.busy_window_recurrence_solution". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.ovh.fp.fully_nonpreemptive.rta_recurrence_solution". Abort.
Check @prosa.results.rta.ovh.fp.fully_nonpreemptive.rta_recurrence_solution.
Goal True. idtac "END|prosa.results.rta.ovh.fp.fully_nonpreemptive.rta_recurrence_solution". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.ovh.fp.fully_nonpreemptive.uniprocessor_response_time_bound_fully_non_preemptive_fp". Abort.
Check @prosa.results.rta.ovh.fp.fully_nonpreemptive.uniprocessor_response_time_bound_fully_non_preemptive_fp.
Goal True. idtac "END|prosa.results.rta.ovh.fp.fully_nonpreemptive.uniprocessor_response_time_bound_fully_non_preemptive_fp". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.ovh.fp.fully_preemptive.busy_window_recurrence_solution". Abort.
Check @prosa.results.rta.ovh.fp.fully_preemptive.busy_window_recurrence_solution.
Goal True. idtac "END|prosa.results.rta.ovh.fp.fully_preemptive.busy_window_recurrence_solution". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.ovh.fp.fully_preemptive.rta_recurrence_solution". Abort.
Check @prosa.results.rta.ovh.fp.fully_preemptive.rta_recurrence_solution.
Goal True. idtac "END|prosa.results.rta.ovh.fp.fully_preemptive.rta_recurrence_solution". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.ovh.fp.fully_preemptive.uniprocessor_response_time_bound_fully_preemptive_fp". Abort.
Check @prosa.results.rta.ovh.fp.fully_preemptive.uniprocessor_response_time_bound_fully_preemptive_fp.
Goal True. idtac "END|prosa.results.rta.ovh.fp.fully_preemptive.uniprocessor_response_time_bound_fully_preemptive_fp". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.ovh.fp.limited_preemptive.busy_window_recurrence_solution". Abort.
Check @prosa.results.rta.ovh.fp.limited_preemptive.busy_window_recurrence_solution.
Goal True. idtac "END|prosa.results.rta.ovh.fp.limited_preemptive.busy_window_recurrence_solution". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.ovh.fp.limited_preemptive.rta_recurrence_solution". Abort.
Check @prosa.results.rta.ovh.fp.limited_preemptive.rta_recurrence_solution.
Goal True. idtac "END|prosa.results.rta.ovh.fp.limited_preemptive.rta_recurrence_solution". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.ovh.fp.limited_preemptive.uniprocessor_response_time_bound_limited_fp". Abort.
Check @prosa.results.rta.ovh.fp.limited_preemptive.uniprocessor_response_time_bound_limited_fp.
Goal True. idtac "END|prosa.results.rta.ovh.fp.limited_preemptive.uniprocessor_response_time_bound_limited_fp". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.prm.edf.floating_nonpreemptive.busy_window_recurrence_solution". Abort.
Check @prosa.results.rta.prm.edf.floating_nonpreemptive.busy_window_recurrence_solution.
Goal True. idtac "END|prosa.results.rta.prm.edf.floating_nonpreemptive.busy_window_recurrence_solution". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.prm.edf.floating_nonpreemptive.rta_recurrence_solution". Abort.
Check @prosa.results.rta.prm.edf.floating_nonpreemptive.rta_recurrence_solution.
Goal True. idtac "END|prosa.results.rta.prm.edf.floating_nonpreemptive.rta_recurrence_solution". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.prm.edf.floating_nonpreemptive.uniprocessor_response_time_bound_floating_edf". Abort.
Check @prosa.results.rta.prm.edf.floating_nonpreemptive.uniprocessor_response_time_bound_floating_edf.
Goal True. idtac "END|prosa.results.rta.prm.edf.floating_nonpreemptive.uniprocessor_response_time_bound_floating_edf". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.prm.edf.fully_nonpreemptive.busy_window_recurrence_solution". Abort.
Check @prosa.results.rta.prm.edf.fully_nonpreemptive.busy_window_recurrence_solution.
Goal True. idtac "END|prosa.results.rta.prm.edf.fully_nonpreemptive.busy_window_recurrence_solution". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.prm.edf.fully_nonpreemptive.rta_recurrence_solution". Abort.
Check @prosa.results.rta.prm.edf.fully_nonpreemptive.rta_recurrence_solution.
Goal True. idtac "END|prosa.results.rta.prm.edf.fully_nonpreemptive.rta_recurrence_solution". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.prm.edf.fully_nonpreemptive.uniprocessor_response_time_bound_fully_nonpreemptive_edf". Abort.
Check @prosa.results.rta.prm.edf.fully_nonpreemptive.uniprocessor_response_time_bound_fully_nonpreemptive_edf.
Goal True. idtac "END|prosa.results.rta.prm.edf.fully_nonpreemptive.uniprocessor_response_time_bound_fully_nonpreemptive_edf". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.prm.edf.fully_preemptive.busy_window_recurrence_solution". Abort.
Check @prosa.results.rta.prm.edf.fully_preemptive.busy_window_recurrence_solution.
Goal True. idtac "END|prosa.results.rta.prm.edf.fully_preemptive.busy_window_recurrence_solution". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.prm.edf.fully_preemptive.rta_recurrence_solution". Abort.
Check @prosa.results.rta.prm.edf.fully_preemptive.rta_recurrence_solution.
Goal True. idtac "END|prosa.results.rta.prm.edf.fully_preemptive.rta_recurrence_solution". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.prm.edf.fully_preemptive.uniprocessor_response_time_bound_fully_preemptive_edf". Abort.
Check @prosa.results.rta.prm.edf.fully_preemptive.uniprocessor_response_time_bound_fully_preemptive_edf.
Goal True. idtac "END|prosa.results.rta.prm.edf.fully_preemptive.uniprocessor_response_time_bound_fully_preemptive_edf". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.prm.edf.limited_preemptive.busy_window_recurrence_solution". Abort.
Check @prosa.results.rta.prm.edf.limited_preemptive.busy_window_recurrence_solution.
Goal True. idtac "END|prosa.results.rta.prm.edf.limited_preemptive.busy_window_recurrence_solution". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.prm.edf.limited_preemptive.rta_recurrence_solution". Abort.
Check @prosa.results.rta.prm.edf.limited_preemptive.rta_recurrence_solution.
Goal True. idtac "END|prosa.results.rta.prm.edf.limited_preemptive.rta_recurrence_solution". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.prm.edf.limited_preemptive.uniprocessor_response_time_bound_limited_edf". Abort.
Check @prosa.results.rta.prm.edf.limited_preemptive.uniprocessor_response_time_bound_limited_edf.
Goal True. idtac "END|prosa.results.rta.prm.edf.limited_preemptive.uniprocessor_response_time_bound_limited_edf". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.prm.fifo.bounded_nps.busy_window_recurrence_solution". Abort.
Check @prosa.results.rta.prm.fifo.bounded_nps.busy_window_recurrence_solution.
Goal True. idtac "END|prosa.results.rta.prm.fifo.bounded_nps.busy_window_recurrence_solution". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.prm.fifo.bounded_nps.rta_recurrence_solution". Abort.
Check @prosa.results.rta.prm.fifo.bounded_nps.rta_recurrence_solution.
Goal True. idtac "END|prosa.results.rta.prm.fifo.bounded_nps.rta_recurrence_solution". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.prm.fifo.bounded_nps.uniprocessor_response_time_bound_fifo". Abort.
Check @prosa.results.rta.prm.fifo.bounded_nps.uniprocessor_response_time_bound_fifo.
Goal True. idtac "END|prosa.results.rta.prm.fifo.bounded_nps.uniprocessor_response_time_bound_fifo". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.prm.fp.floating_nonpreemptive.busy_window_recurrence_solution". Abort.
Check @prosa.results.rta.prm.fp.floating_nonpreemptive.busy_window_recurrence_solution.
Goal True. idtac "END|prosa.results.rta.prm.fp.floating_nonpreemptive.busy_window_recurrence_solution". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.prm.fp.floating_nonpreemptive.rta_recurrence_solution". Abort.
Check @prosa.results.rta.prm.fp.floating_nonpreemptive.rta_recurrence_solution.
Goal True. idtac "END|prosa.results.rta.prm.fp.floating_nonpreemptive.rta_recurrence_solution". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.prm.fp.floating_nonpreemptive.uniprocessor_response_time_bound_floating_fp". Abort.
Check @prosa.results.rta.prm.fp.floating_nonpreemptive.uniprocessor_response_time_bound_floating_fp.
Goal True. idtac "END|prosa.results.rta.prm.fp.floating_nonpreemptive.uniprocessor_response_time_bound_floating_fp". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.prm.fp.fully_nonpreemptive.busy_window_recurrence_solution". Abort.
Check @prosa.results.rta.prm.fp.fully_nonpreemptive.busy_window_recurrence_solution.
Goal True. idtac "END|prosa.results.rta.prm.fp.fully_nonpreemptive.busy_window_recurrence_solution". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.prm.fp.fully_nonpreemptive.rta_recurrence_solution". Abort.
Check @prosa.results.rta.prm.fp.fully_nonpreemptive.rta_recurrence_solution.
Goal True. idtac "END|prosa.results.rta.prm.fp.fully_nonpreemptive.rta_recurrence_solution". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.prm.fp.fully_nonpreemptive.uniprocessor_response_time_bound_fully_non_preemptive_fp". Abort.
Check @prosa.results.rta.prm.fp.fully_nonpreemptive.uniprocessor_response_time_bound_fully_non_preemptive_fp.
Goal True. idtac "END|prosa.results.rta.prm.fp.fully_nonpreemptive.uniprocessor_response_time_bound_fully_non_preemptive_fp". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.prm.fp.fully_preemptive.busy_window_recurrence_solution". Abort.
Check @prosa.results.rta.prm.fp.fully_preemptive.busy_window_recurrence_solution.
Goal True. idtac "END|prosa.results.rta.prm.fp.fully_preemptive.busy_window_recurrence_solution". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.prm.fp.fully_preemptive.rta_recurrence_solution". Abort.
Check @prosa.results.rta.prm.fp.fully_preemptive.rta_recurrence_solution.
Goal True. idtac "END|prosa.results.rta.prm.fp.fully_preemptive.rta_recurrence_solution". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.prm.fp.fully_preemptive.uniprocessor_response_time_bound_fully_preemptive_fp". Abort.
Check @prosa.results.rta.prm.fp.fully_preemptive.uniprocessor_response_time_bound_fully_preemptive_fp.
Goal True. idtac "END|prosa.results.rta.prm.fp.fully_preemptive.uniprocessor_response_time_bound_fully_preemptive_fp". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.prm.fp.limited_preemptive.busy_window_recurrence_solution". Abort.
Check @prosa.results.rta.prm.fp.limited_preemptive.busy_window_recurrence_solution.
Goal True. idtac "END|prosa.results.rta.prm.fp.limited_preemptive.busy_window_recurrence_solution". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.prm.fp.limited_preemptive.rta_recurrence_solution". Abort.
Check @prosa.results.rta.prm.fp.limited_preemptive.rta_recurrence_solution.
Goal True. idtac "END|prosa.results.rta.prm.fp.limited_preemptive.rta_recurrence_solution". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.prm.fp.limited_preemptive.uniprocessor_response_time_bound_limited_fp". Abort.
Check @prosa.results.rta.prm.fp.limited_preemptive.uniprocessor_response_time_bound_limited_fp.
Goal True. idtac "END|prosa.results.rta.prm.fp.limited_preemptive.uniprocessor_response_time_bound_limited_fp". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.rs.edf.floating_nonpreemptive.busy_window_recurrence_solution". Abort.
Check @prosa.results.rta.rs.edf.floating_nonpreemptive.busy_window_recurrence_solution.
Goal True. idtac "END|prosa.results.rta.rs.edf.floating_nonpreemptive.busy_window_recurrence_solution". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.rs.edf.floating_nonpreemptive.rta_recurrence_solution". Abort.
Check @prosa.results.rta.rs.edf.floating_nonpreemptive.rta_recurrence_solution.
Goal True. idtac "END|prosa.results.rta.rs.edf.floating_nonpreemptive.rta_recurrence_solution". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.rs.edf.floating_nonpreemptive.uniprocessor_response_time_bound_floating_edf". Abort.
Check @prosa.results.rta.rs.edf.floating_nonpreemptive.uniprocessor_response_time_bound_floating_edf.
Goal True. idtac "END|prosa.results.rta.rs.edf.floating_nonpreemptive.uniprocessor_response_time_bound_floating_edf". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.rs.edf.fully_nonpreemptive.busy_window_recurrence_solution". Abort.
Check @prosa.results.rta.rs.edf.fully_nonpreemptive.busy_window_recurrence_solution.
Goal True. idtac "END|prosa.results.rta.rs.edf.fully_nonpreemptive.busy_window_recurrence_solution". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.rs.edf.fully_nonpreemptive.rta_recurrence_solution". Abort.
Check @prosa.results.rta.rs.edf.fully_nonpreemptive.rta_recurrence_solution.
Goal True. idtac "END|prosa.results.rta.rs.edf.fully_nonpreemptive.rta_recurrence_solution". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.rs.edf.fully_nonpreemptive.uniprocessor_response_time_bound_fully_nonpreemptive_edf". Abort.
Check @prosa.results.rta.rs.edf.fully_nonpreemptive.uniprocessor_response_time_bound_fully_nonpreemptive_edf.
Goal True. idtac "END|prosa.results.rta.rs.edf.fully_nonpreemptive.uniprocessor_response_time_bound_fully_nonpreemptive_edf". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.rs.edf.fully_preemptive.busy_window_recurrence_solution". Abort.
Check @prosa.results.rta.rs.edf.fully_preemptive.busy_window_recurrence_solution.
Goal True. idtac "END|prosa.results.rta.rs.edf.fully_preemptive.busy_window_recurrence_solution". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.rs.edf.fully_preemptive.rta_recurrence_solution". Abort.
Check @prosa.results.rta.rs.edf.fully_preemptive.rta_recurrence_solution.
Goal True. idtac "END|prosa.results.rta.rs.edf.fully_preemptive.rta_recurrence_solution". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.rs.edf.fully_preemptive.uniprocessor_response_time_bound_fully_preemptive_edf". Abort.
Check @prosa.results.rta.rs.edf.fully_preemptive.uniprocessor_response_time_bound_fully_preemptive_edf.
Goal True. idtac "END|prosa.results.rta.rs.edf.fully_preemptive.uniprocessor_response_time_bound_fully_preemptive_edf". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.rs.edf.limited_preemptive.busy_window_recurrence_solution". Abort.
Check @prosa.results.rta.rs.edf.limited_preemptive.busy_window_recurrence_solution.
Goal True. idtac "END|prosa.results.rta.rs.edf.limited_preemptive.busy_window_recurrence_solution". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.rs.edf.limited_preemptive.rta_recurrence_solution". Abort.
Check @prosa.results.rta.rs.edf.limited_preemptive.rta_recurrence_solution.
Goal True. idtac "END|prosa.results.rta.rs.edf.limited_preemptive.rta_recurrence_solution". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.rs.edf.limited_preemptive.uniprocessor_response_time_bound_limited_edf". Abort.
Check @prosa.results.rta.rs.edf.limited_preemptive.uniprocessor_response_time_bound_limited_edf.
Goal True. idtac "END|prosa.results.rta.rs.edf.limited_preemptive.uniprocessor_response_time_bound_limited_edf". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.rs.elf.floating_nonpreemptive.busy_window_recurrence_solution". Abort.
Check @prosa.results.rta.rs.elf.floating_nonpreemptive.busy_window_recurrence_solution.
Goal True. idtac "END|prosa.results.rta.rs.elf.floating_nonpreemptive.busy_window_recurrence_solution". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.rs.elf.floating_nonpreemptive.rta_recurrence_solution". Abort.
Check @prosa.results.rta.rs.elf.floating_nonpreemptive.rta_recurrence_solution.
Goal True. idtac "END|prosa.results.rta.rs.elf.floating_nonpreemptive.rta_recurrence_solution". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.rs.elf.floating_nonpreemptive.uniprocessor_response_time_bound_floating_elf". Abort.
Check @prosa.results.rta.rs.elf.floating_nonpreemptive.uniprocessor_response_time_bound_floating_elf.
Goal True. idtac "END|prosa.results.rta.rs.elf.floating_nonpreemptive.uniprocessor_response_time_bound_floating_elf". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.rs.elf.fully_nonpreemptive.busy_window_recurrence_solution". Abort.
Check @prosa.results.rta.rs.elf.fully_nonpreemptive.busy_window_recurrence_solution.
Goal True. idtac "END|prosa.results.rta.rs.elf.fully_nonpreemptive.busy_window_recurrence_solution". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.rs.elf.fully_nonpreemptive.rta_recurrence_solution". Abort.
Check @prosa.results.rta.rs.elf.fully_nonpreemptive.rta_recurrence_solution.
Goal True. idtac "END|prosa.results.rta.rs.elf.fully_nonpreemptive.rta_recurrence_solution". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.rs.elf.fully_nonpreemptive.uniprocessor_response_time_bound_fully_nonpreemptive_elf". Abort.
Check @prosa.results.rta.rs.elf.fully_nonpreemptive.uniprocessor_response_time_bound_fully_nonpreemptive_elf.
Goal True. idtac "END|prosa.results.rta.rs.elf.fully_nonpreemptive.uniprocessor_response_time_bound_fully_nonpreemptive_elf". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.rs.elf.fully_preemptive.busy_window_recurrence_solution". Abort.
Check @prosa.results.rta.rs.elf.fully_preemptive.busy_window_recurrence_solution.
Goal True. idtac "END|prosa.results.rta.rs.elf.fully_preemptive.busy_window_recurrence_solution". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.rs.elf.fully_preemptive.rta_recurrence_solution". Abort.
Check @prosa.results.rta.rs.elf.fully_preemptive.rta_recurrence_solution.
Goal True. idtac "END|prosa.results.rta.rs.elf.fully_preemptive.rta_recurrence_solution". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.rs.elf.fully_preemptive.uniprocessor_response_time_bound_fully_preemptive_elf". Abort.
Check @prosa.results.rta.rs.elf.fully_preemptive.uniprocessor_response_time_bound_fully_preemptive_elf.
Goal True. idtac "END|prosa.results.rta.rs.elf.fully_preemptive.uniprocessor_response_time_bound_fully_preemptive_elf". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.rs.elf.limited_preemptive.busy_window_recurrence_solution". Abort.
Check @prosa.results.rta.rs.elf.limited_preemptive.busy_window_recurrence_solution.
Goal True. idtac "END|prosa.results.rta.rs.elf.limited_preemptive.busy_window_recurrence_solution". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.rs.elf.limited_preemptive.rta_recurrence_solution". Abort.
Check @prosa.results.rta.rs.elf.limited_preemptive.rta_recurrence_solution.
Goal True. idtac "END|prosa.results.rta.rs.elf.limited_preemptive.rta_recurrence_solution". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.rs.elf.limited_preemptive.uniprocessor_response_time_bound_limited_elf". Abort.
Check @prosa.results.rta.rs.elf.limited_preemptive.uniprocessor_response_time_bound_limited_elf.
Goal True. idtac "END|prosa.results.rta.rs.elf.limited_preemptive.uniprocessor_response_time_bound_limited_elf". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.rs.fifo.bounded_nps.busy_window_recurrence_solution". Abort.
Check @prosa.results.rta.rs.fifo.bounded_nps.busy_window_recurrence_solution.
Goal True. idtac "END|prosa.results.rta.rs.fifo.bounded_nps.busy_window_recurrence_solution". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.rs.fifo.bounded_nps.rta_recurrence_solution". Abort.
Check @prosa.results.rta.rs.fifo.bounded_nps.rta_recurrence_solution.
Goal True. idtac "END|prosa.results.rta.rs.fifo.bounded_nps.rta_recurrence_solution". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.rs.fifo.bounded_nps.uniprocessor_response_time_bound_fifo". Abort.
Check @prosa.results.rta.rs.fifo.bounded_nps.uniprocessor_response_time_bound_fifo.
Goal True. idtac "END|prosa.results.rta.rs.fifo.bounded_nps.uniprocessor_response_time_bound_fifo". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.rs.fp.floating_nonpreemptive.busy_window_recurrence_solution". Abort.
Check @prosa.results.rta.rs.fp.floating_nonpreemptive.busy_window_recurrence_solution.
Goal True. idtac "END|prosa.results.rta.rs.fp.floating_nonpreemptive.busy_window_recurrence_solution". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.rs.fp.floating_nonpreemptive.rta_recurrence_solution". Abort.
Check @prosa.results.rta.rs.fp.floating_nonpreemptive.rta_recurrence_solution.
Goal True. idtac "END|prosa.results.rta.rs.fp.floating_nonpreemptive.rta_recurrence_solution". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.rs.fp.floating_nonpreemptive.uniprocessor_response_time_bound_floating_fp". Abort.
Check @prosa.results.rta.rs.fp.floating_nonpreemptive.uniprocessor_response_time_bound_floating_fp.
Goal True. idtac "END|prosa.results.rta.rs.fp.floating_nonpreemptive.uniprocessor_response_time_bound_floating_fp". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.rs.fp.fully_nonpreemptive.busy_window_recurrence_solution". Abort.
Check @prosa.results.rta.rs.fp.fully_nonpreemptive.busy_window_recurrence_solution.
Goal True. idtac "END|prosa.results.rta.rs.fp.fully_nonpreemptive.busy_window_recurrence_solution". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.rs.fp.fully_nonpreemptive.rta_recurrence_solution". Abort.
Check @prosa.results.rta.rs.fp.fully_nonpreemptive.rta_recurrence_solution.
Goal True. idtac "END|prosa.results.rta.rs.fp.fully_nonpreemptive.rta_recurrence_solution". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.rs.fp.fully_nonpreemptive.uniprocessor_response_time_bound_fully_nonpreemptive_fp". Abort.
Check @prosa.results.rta.rs.fp.fully_nonpreemptive.uniprocessor_response_time_bound_fully_nonpreemptive_fp.
Goal True. idtac "END|prosa.results.rta.rs.fp.fully_nonpreemptive.uniprocessor_response_time_bound_fully_nonpreemptive_fp". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.rs.fp.fully_preemptive.busy_window_recurrence_solution". Abort.
Check @prosa.results.rta.rs.fp.fully_preemptive.busy_window_recurrence_solution.
Goal True. idtac "END|prosa.results.rta.rs.fp.fully_preemptive.busy_window_recurrence_solution". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.rs.fp.fully_preemptive.rta_recurrence_solution". Abort.
Check @prosa.results.rta.rs.fp.fully_preemptive.rta_recurrence_solution.
Goal True. idtac "END|prosa.results.rta.rs.fp.fully_preemptive.rta_recurrence_solution". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.rs.fp.fully_preemptive.uniprocessor_response_time_bound_fully_preemptive_fp". Abort.
Check @prosa.results.rta.rs.fp.fully_preemptive.uniprocessor_response_time_bound_fully_preemptive_fp.
Goal True. idtac "END|prosa.results.rta.rs.fp.fully_preemptive.uniprocessor_response_time_bound_fully_preemptive_fp". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.rs.fp.limited_preemptive.busy_window_recurrence_solution". Abort.
Check @prosa.results.rta.rs.fp.limited_preemptive.busy_window_recurrence_solution.
Goal True. idtac "END|prosa.results.rta.rs.fp.limited_preemptive.busy_window_recurrence_solution". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.rs.fp.limited_preemptive.rta_recurrence_solution". Abort.
Check @prosa.results.rta.rs.fp.limited_preemptive.rta_recurrence_solution.
Goal True. idtac "END|prosa.results.rta.rs.fp.limited_preemptive.rta_recurrence_solution". Abort.
Goal True. idtac "BEGIN|prosa.results.rta.rs.fp.limited_preemptive.uniprocessor_response_time_bound_limited_fp". Abort.
Check @prosa.results.rta.rs.fp.limited_preemptive.uniprocessor_response_time_bound_limited_fp.
Goal True. idtac "END|prosa.results.rta.rs.fp.limited_preemptive.uniprocessor_response_time_bound_limited_fp". Abort.
Goal True. idtac "BEGIN|prosa.results.transfer_schedulability.criterion.schedulability_transferred". Abort.
Check @prosa.results.transfer_schedulability.criterion.schedulability_transferred.
Goal True. idtac "END|prosa.results.transfer_schedulability.criterion.schedulability_transferred". Abort.
Goal True. idtac "BEGIN|prosa.results.transfer_schedulability.criterion.deadlines_met". Abort.
Check @prosa.results.transfer_schedulability.criterion.deadlines_met.
Goal True. idtac "END|prosa.results.transfer_schedulability.criterion.deadlines_met". Abort.
Goal True. idtac "BEGIN|prosa.results.transfer_schedulability.criterion.ref_cost_bounds_online_cost". Abort.
Check @prosa.results.transfer_schedulability.criterion.ref_cost_bounds_online_cost.
Goal True. idtac "END|prosa.results.transfer_schedulability.criterion.ref_cost_bounds_online_cost". Abort.
Goal True. idtac "BEGIN|prosa.results.transfer_schedulability.criterion.remaining_cost_bound". Abort.
Check @prosa.results.transfer_schedulability.criterion.remaining_cost_bound.
Goal True. idtac "END|prosa.results.transfer_schedulability.criterion.remaining_cost_bound". Abort.
Goal True. idtac "BEGIN|prosa.results.transfer_schedulability.criterion.remcost_service". Abort.
Check @prosa.results.transfer_schedulability.criterion.remcost_service.
Goal True. idtac "END|prosa.results.transfer_schedulability.criterion.remcost_service". Abort.
Goal True. idtac "BEGIN|prosa.results.transfer_schedulability.criterion.remcost_service_during". Abort.
Check @prosa.results.transfer_schedulability.criterion.remcost_service_during.
Goal True. idtac "END|prosa.results.transfer_schedulability.criterion.remcost_service_during". Abort.
Goal True. idtac "BEGIN|prosa.results.transfer_schedulability.criterion.remcost_total_service_during". Abort.
Check @prosa.results.transfer_schedulability.criterion.remcost_total_service_during.
Goal True. idtac "END|prosa.results.transfer_schedulability.criterion.remcost_total_service_during". Abort.
Goal True. idtac "BEGIN|prosa.results.transfer_schedulability.criterion.remaining_cost_invariant". Abort.
Check @prosa.results.transfer_schedulability.criterion.remaining_cost_invariant.
Goal True. idtac "END|prosa.results.transfer_schedulability.criterion.remaining_cost_invariant". Abort.
Goal True. idtac "BEGIN|prosa.results.transfer_schedulability.criterion.online_remaining_cost_bounded". Abort.
Check @prosa.results.transfer_schedulability.criterion.online_remaining_cost_bounded.
Goal True. idtac "END|prosa.results.transfer_schedulability.criterion.online_remaining_cost_bounded". Abort.
Goal True. idtac "BEGIN|prosa.results.transfer_schedulability.criterion.remaining_cost_positive". Abort.
Check @prosa.results.transfer_schedulability.criterion.remaining_cost_positive.
Goal True. idtac "END|prosa.results.transfer_schedulability.criterion.remaining_cost_positive". Abort.
Goal True. idtac "BEGIN|prosa.results.transfer_schedulability.criterion.remaining_cost_zero". Abort.
Check @prosa.results.transfer_schedulability.criterion.remaining_cost_zero.
Goal True. idtac "END|prosa.results.transfer_schedulability.criterion.remaining_cost_zero". Abort.
Goal True. idtac "BEGIN|prosa.results.transfer_schedulability.criterion.critical_jobs". Abort.
Check @prosa.results.transfer_schedulability.criterion.critical_jobs.
Goal True. idtac "END|prosa.results.transfer_schedulability.criterion.critical_jobs". Abort.
Goal True. idtac "BEGIN|prosa.results.transfer_schedulability.criterion.critical_jobs_monotonicity". Abort.
Check @prosa.results.transfer_schedulability.criterion.critical_jobs_monotonicity.
Goal True. idtac "END|prosa.results.transfer_schedulability.criterion.critical_jobs_monotonicity". Abort.
Goal True. idtac "BEGIN|prosa.results.transfer_schedulability.criterion.critical_jobs_dropout". Abort.
Check @prosa.results.transfer_schedulability.criterion.critical_jobs_dropout.
Goal True. idtac "END|prosa.results.transfer_schedulability.criterion.critical_jobs_dropout". Abort.
Goal True. idtac "BEGIN|prosa.results.transfer_schedulability.criterion.critical_jobs_filter_complete". Abort.
Check @prosa.results.transfer_schedulability.criterion.critical_jobs_filter_complete.
Goal True. idtac "END|prosa.results.transfer_schedulability.criterion.critical_jobs_filter_complete". Abort.
Goal True. idtac "BEGIN|prosa.results.transfer_schedulability.criterion.critical_jobs_uniq". Abort.
Check @prosa.results.transfer_schedulability.criterion.critical_jobs_uniq.
Goal True. idtac "END|prosa.results.transfer_schedulability.criterion.critical_jobs_uniq". Abort.
Goal True. idtac "BEGIN|prosa.results.transfer_schedulability.criterion.critical_jobs_min_completion_time". Abort.
Check @prosa.results.transfer_schedulability.criterion.critical_jobs_min_completion_time.
Goal True. idtac "END|prosa.results.transfer_schedulability.criterion.critical_jobs_min_completion_time". Abort.
Goal True. idtac "BEGIN|prosa.results.transfer_schedulability.criterion.critical_jobs_remaining_cost_monotonic". Abort.
Check @prosa.results.transfer_schedulability.criterion.critical_jobs_remaining_cost_monotonic.
Goal True. idtac "END|prosa.results.transfer_schedulability.criterion.critical_jobs_remaining_cost_monotonic". Abort.
Goal True. idtac "BEGIN|prosa.results.transfer_schedulability.criterion.slackless_interval". Abort.
Check @prosa.results.transfer_schedulability.criterion.slackless_interval.
Goal True. idtac "END|prosa.results.transfer_schedulability.criterion.slackless_interval". Abort.
Goal True. idtac "BEGIN|prosa.results.transfer_schedulability.criterion.contiguously_slackless_interval". Abort.
Check @prosa.results.transfer_schedulability.criterion.contiguously_slackless_interval.
Goal True. idtac "END|prosa.results.transfer_schedulability.criterion.contiguously_slackless_interval". Abort.
Goal True. idtac "BEGIN|prosa.results.transfer_schedulability.criterion.transfer_schedulability_criterion". Abort.
Check @prosa.results.transfer_schedulability.criterion.transfer_schedulability_criterion.
Goal True. idtac "END|prosa.results.transfer_schedulability.criterion.transfer_schedulability_criterion". Abort.
Goal True. idtac "BEGIN|prosa.results.transfer_schedulability.criterion.late_in_critical_jobs". Abort.
Check @prosa.results.transfer_schedulability.criterion.late_in_critical_jobs.
Goal True. idtac "END|prosa.results.transfer_schedulability.criterion.late_in_critical_jobs". Abort.
Goal True. idtac "BEGIN|prosa.results.transfer_schedulability.criterion.late_not_at_start". Abort.
Check @prosa.results.transfer_schedulability.criterion.late_not_at_start.
Goal True. idtac "END|prosa.results.transfer_schedulability.criterion.late_not_at_start". Abort.
Goal True. idtac "BEGIN|prosa.results.transfer_schedulability.criterion.nonpositive_slack". Abort.
Check @prosa.results.transfer_schedulability.criterion.nonpositive_slack.
Goal True. idtac "END|prosa.results.transfer_schedulability.criterion.nonpositive_slack". Abort.
Goal True. idtac "BEGIN|prosa.results.transfer_schedulability.criterion.contiguously_nps". Abort.
Check @prosa.results.transfer_schedulability.criterion.contiguously_nps.
Goal True. idtac "END|prosa.results.transfer_schedulability.criterion.contiguously_nps". Abort.
Goal True. idtac "BEGIN|prosa.results.transfer_schedulability.criterion.contiguously_nps_start". Abort.
Check @prosa.results.transfer_schedulability.criterion.contiguously_nps_start.
Goal True. idtac "END|prosa.results.transfer_schedulability.criterion.contiguously_nps_start". Abort.
Goal True. idtac "BEGIN|prosa.results.transfer_schedulability.criterion.contiguously_nps_existence". Abort.
Check @prosa.results.transfer_schedulability.criterion.contiguously_nps_existence.
Goal True. idtac "END|prosa.results.transfer_schedulability.criterion.contiguously_nps_existence". Abort.
Goal True. idtac "BEGIN|prosa.results.transfer_schedulability.criterion.slackless_interval_step_case_completed_job_rem". Abort.
Check @prosa.results.transfer_schedulability.criterion.slackless_interval_step_case_completed_job_rem.
Goal True. idtac "END|prosa.results.transfer_schedulability.criterion.slackless_interval_step_case_completed_job_rem". Abort.
Goal True. idtac "BEGIN|prosa.results.transfer_schedulability.criterion.slackless_interval_step_case_completed_job". Abort.
Check @prosa.results.transfer_schedulability.criterion.slackless_interval_step_case_completed_job.
Goal True. idtac "END|prosa.results.transfer_schedulability.criterion.slackless_interval_step_case_completed_job". Abort.
Goal True. idtac "BEGIN|prosa.results.transfer_schedulability.criterion.slackless_interval_step_case_incomplete_job". Abort.
Check @prosa.results.transfer_schedulability.criterion.slackless_interval_step_case_incomplete_job.
Goal True. idtac "END|prosa.results.transfer_schedulability.criterion.slackless_interval_step_case_incomplete_job". Abort.
Goal True. idtac "BEGIN|prosa.results.transfer_schedulability.criterion.slackless_interval_step". Abort.
Check @prosa.results.transfer_schedulability.criterion.slackless_interval_step.
Goal True. idtac "END|prosa.results.transfer_schedulability.criterion.slackless_interval_step". Abort.
Goal True. idtac "BEGIN|prosa.results.transfer_schedulability.criterion.slackless_interval_continuation". Abort.
Check @prosa.results.transfer_schedulability.criterion.slackless_interval_continuation.
Goal True. idtac "END|prosa.results.transfer_schedulability.criterion.slackless_interval_continuation". Abort.
Goal True. idtac "BEGIN|prosa.results.transfer_schedulability.criterion.slackless_interval_existence". Abort.
Check @prosa.results.transfer_schedulability.criterion.slackless_interval_existence.
Goal True. idtac "END|prosa.results.transfer_schedulability.criterion.slackless_interval_existence". Abort.
Goal True. idtac "BEGIN|prosa.results.transfer_schedulability.criterion.slackless_interval_completion". Abort.
Check @prosa.results.transfer_schedulability.criterion.slackless_interval_completion.
Goal True. idtac "END|prosa.results.transfer_schedulability.criterion.slackless_interval_completion". Abort.
Goal True. idtac "BEGIN|prosa.results.transfer_schedulability.criterion.online_transfer_schedulability_criterion_sufficiency". Abort.
Check @prosa.results.transfer_schedulability.criterion.online_transfer_schedulability_criterion_sufficiency.
Goal True. idtac "END|prosa.results.transfer_schedulability.criterion.online_transfer_schedulability_criterion_sufficiency". Abort.
Goal True. idtac "BEGIN|prosa.results.transfer_schedulability.criterion.online_transfer_schedulability_criterion_ensures_schedulability". Abort.
Check @prosa.results.transfer_schedulability.criterion.online_transfer_schedulability_criterion_ensures_schedulability.
Goal True. idtac "END|prosa.results.transfer_schedulability.criterion.online_transfer_schedulability_criterion_ensures_schedulability". Abort.
Goal True. idtac "BEGIN|prosa.results.transfer_schedulability.criterion.delay_if_no_critical_job_is_scheduled". Abort.
Check @prosa.results.transfer_schedulability.criterion.delay_if_no_critical_job_is_scheduled.
Goal True. idtac "END|prosa.results.transfer_schedulability.criterion.delay_if_no_critical_job_is_scheduled". Abort.
Goal True. idtac "BEGIN|prosa.results.transfer_schedulability.criterion.online_transfer_schedulability_criterion_necessity". Abort.
Check @prosa.results.transfer_schedulability.criterion.online_transfer_schedulability_criterion_necessity.
Goal True. idtac "END|prosa.results.transfer_schedulability.criterion.online_transfer_schedulability_criterion_necessity". Abort.
Goal True. idtac "BEGIN|prosa.results.transfer_schedulability.criterion.ref_transfer_schedulability_criterion_sufficiency". Abort.
Check @prosa.results.transfer_schedulability.criterion.ref_transfer_schedulability_criterion_sufficiency.
Goal True. idtac "END|prosa.results.transfer_schedulability.criterion.ref_transfer_schedulability_criterion_sufficiency". Abort.
Goal True. idtac "BEGIN|prosa.results.transfer_schedulability.criterion.ref_transfer_schedulability_criterion_ensures_schedulability". Abort.
Check @prosa.results.transfer_schedulability.criterion.ref_transfer_schedulability_criterion_ensures_schedulability.
Goal True. idtac "END|prosa.results.transfer_schedulability.criterion.ref_transfer_schedulability_criterion_ensures_schedulability". Abort.
Goal True. idtac "BEGIN|prosa.results.transfer_schedulability.paper_model.JobPredecessors". Abort.
Check @prosa.results.transfer_schedulability.paper_model.JobPredecessors.
Goal True. idtac "END|prosa.results.transfer_schedulability.paper_model.JobPredecessors". Abort.
Goal True. idtac "BEGIN|prosa.results.transfer_schedulability.paper_model.JobDelay". Abort.
Check @prosa.results.transfer_schedulability.paper_model.JobDelay.
Goal True. idtac "END|prosa.results.transfer_schedulability.paper_model.JobDelay". Abort.
Goal True. idtac "BEGIN|prosa.results.transfer_schedulability.paper_model.SystemEvolutions". Abort.
Check @prosa.results.transfer_schedulability.paper_model.SystemEvolutions.
Goal True. idtac "END|prosa.results.transfer_schedulability.paper_model.SystemEvolutions". Abort.
Goal True. idtac "BEGIN|prosa.results.transfer_schedulability.paper_model.Scheduler". Abort.
Check @prosa.results.transfer_schedulability.paper_model.Scheduler.
Goal True. idtac "END|prosa.results.transfer_schedulability.paper_model.Scheduler". Abort.
Goal True. idtac "BEGIN|prosa.results.transfer_schedulability.paper_model.schedulability_transferred_AB". Abort.
Check @prosa.results.transfer_schedulability.paper_model.schedulability_transferred_AB.
Goal True. idtac "END|prosa.results.transfer_schedulability.paper_model.schedulability_transferred_AB". Abort.
Goal True. idtac "BEGIN|prosa.results.transfer_schedulability.paper_model.clairvoyant_criterion". Abort.
Check @prosa.results.transfer_schedulability.paper_model.clairvoyant_criterion.
Goal True. idtac "END|prosa.results.transfer_schedulability.paper_model.clairvoyant_criterion". Abort.
Goal True. idtac "BEGIN|prosa.results.transfer_schedulability.paper_model.clairvoyant_sufficiency". Abort.
Check @prosa.results.transfer_schedulability.paper_model.clairvoyant_sufficiency.
Goal True. idtac "END|prosa.results.transfer_schedulability.paper_model.clairvoyant_sufficiency". Abort.
Goal True. idtac "BEGIN|prosa.results.transfer_schedulability.paper_model.clairvoyant_necessity". Abort.
Check @prosa.results.transfer_schedulability.paper_model.clairvoyant_necessity.
Goal True. idtac "END|prosa.results.transfer_schedulability.paper_model.clairvoyant_necessity". Abort.
Goal True. idtac "BEGIN|prosa.results.transfer_schedulability.paper_model.nonclairvoyant_criterion". Abort.
Check @prosa.results.transfer_schedulability.paper_model.nonclairvoyant_criterion.
Goal True. idtac "END|prosa.results.transfer_schedulability.paper_model.nonclairvoyant_criterion". Abort.
Goal True. idtac "BEGIN|prosa.results.transfer_schedulability.paper_model.nonclairvoyant_sufficiency". Abort.
Check @prosa.results.transfer_schedulability.paper_model.nonclairvoyant_sufficiency.
Goal True. idtac "END|prosa.results.transfer_schedulability.paper_model.nonclairvoyant_sufficiency". Abort.
Goal True. idtac "BEGIN|prosa.results.transfer_schedulability.paper_model.ref_finish_time". Abort.
Check @prosa.results.transfer_schedulability.paper_model.ref_finish_time.
Goal True. idtac "END|prosa.results.transfer_schedulability.paper_model.ref_finish_time". Abort.
Goal True. idtac "BEGIN|prosa.results.transfer_schedulability.paper_model.online_response_time_bound". Abort.
Check @prosa.results.transfer_schedulability.paper_model.online_response_time_bound.
Goal True. idtac "END|prosa.results.transfer_schedulability.paper_model.online_response_time_bound". Abort.
Goal True. idtac "BEGIN|prosa.results.transfer_schedulability.paper_model.online_finish_time". Abort.
Check @prosa.results.transfer_schedulability.paper_model.online_finish_time.
Goal True. idtac "END|prosa.results.transfer_schedulability.paper_model.online_finish_time". Abort.
Goal True. idtac "BEGIN|prosa.results.transfer_schedulability.paper_model.online_finish_time_bounded". Abort.
Check @prosa.results.transfer_schedulability.paper_model.online_finish_time_bounded.
Goal True. idtac "END|prosa.results.transfer_schedulability.paper_model.online_finish_time_bounded". Abort.
Goal True. idtac "BEGIN|prosa.results.transfer_schedulability.paper_model.clairvoyant_sufficiency'". Abort.
Check @prosa.results.transfer_schedulability.paper_model.clairvoyant_sufficiency'.
Goal True. idtac "END|prosa.results.transfer_schedulability.paper_model.clairvoyant_sufficiency'". Abort.
Goal True. idtac "BEGIN|prosa.results.transfer_schedulability.paper_model.nonclairvoyant_sufficiency'". Abort.
Check @prosa.results.transfer_schedulability.paper_model.nonclairvoyant_sufficiency'.
Goal True. idtac "END|prosa.results.transfer_schedulability.paper_model.nonclairvoyant_sufficiency'". Abort.
Goal True. idtac "BEGIN|prosa.results.transfer_schedulability.paper_model.online_finish_time'". Abort.
Check @prosa.results.transfer_schedulability.paper_model.online_finish_time'.
Goal True. idtac "END|prosa.results.transfer_schedulability.paper_model.online_finish_time'". Abort.
Goal True. idtac "BEGIN|prosa.results.transfer_schedulability.paper_model.online_finish_time_bounded'". Abort.
Check @prosa.results.transfer_schedulability.paper_model.online_finish_time_bounded'.
Goal True. idtac "END|prosa.results.transfer_schedulability.paper_model.online_finish_time_bounded'". Abort.
Goal True. idtac "BEGIN|prosa.results.transfer_schedulability.paper_model.clairvoyant_necessity'". Abort.
Check @prosa.results.transfer_schedulability.paper_model.clairvoyant_necessity'.
Goal True. idtac "END|prosa.results.transfer_schedulability.paper_model.clairvoyant_necessity'". Abort.
Goal True. idtac "BEGIN|prosa.util.bigcat.mem_bigcat_nat". Abort.
Check @prosa.util.bigcat.mem_bigcat_nat.
Goal True. idtac "END|prosa.util.bigcat.mem_bigcat_nat". Abort.
Goal True. idtac "BEGIN|prosa.util.bigcat.mem_bigcat_nat_exists". Abort.
Check @prosa.util.bigcat.mem_bigcat_nat_exists.
Goal True. idtac "END|prosa.util.bigcat.mem_bigcat_nat_exists". Abort.
Goal True. idtac "BEGIN|prosa.util.bigcat.mem_bigcat_ord". Abort.
Check @prosa.util.bigcat.mem_bigcat_ord.
Goal True. idtac "END|prosa.util.bigcat.mem_bigcat_ord". Abort.
Goal True. idtac "BEGIN|prosa.util.bigcat.bigcat_nat_uniq". Abort.
Check @prosa.util.bigcat.bigcat_nat_uniq.
Goal True. idtac "END|prosa.util.bigcat.bigcat_nat_uniq". Abort.
Goal True. idtac "BEGIN|prosa.util.bigcat.bigcat_nat_filter_eq_filter_bigcat_nat". Abort.
Check @prosa.util.bigcat.bigcat_nat_filter_eq_filter_bigcat_nat.
Goal True. idtac "END|prosa.util.bigcat.bigcat_nat_filter_eq_filter_bigcat_nat". Abort.
Goal True. idtac "BEGIN|prosa.util.bigcat.size_big_nat". Abort.
Check @prosa.util.bigcat.size_big_nat.
Goal True. idtac "END|prosa.util.bigcat.size_big_nat". Abort.
Goal True. idtac "BEGIN|prosa.util.bigcat.mem_bigcat". Abort.
Check @prosa.util.bigcat.mem_bigcat.
Goal True. idtac "END|prosa.util.bigcat.mem_bigcat". Abort.
Goal True. idtac "BEGIN|prosa.util.bigcat.mem_bigcat_exists". Abort.
Check @prosa.util.bigcat.mem_bigcat_exists.
Goal True. idtac "END|prosa.util.bigcat.mem_bigcat_exists". Abort.
Goal True. idtac "BEGIN|prosa.util.bigcat.bigcat_filter_eq_filter_bigcat". Abort.
Check @prosa.util.bigcat.bigcat_filter_eq_filter_bigcat.
Goal True. idtac "END|prosa.util.bigcat.bigcat_filter_eq_filter_bigcat". Abort.
Goal True. idtac "BEGIN|prosa.util.bigcat.bigcat_uniq". Abort.
Check @prosa.util.bigcat.bigcat_uniq.
Goal True. idtac "END|prosa.util.bigcat.bigcat_uniq". Abort.
Goal True. idtac "BEGIN|prosa.util.bigcat.seq_different_elements_nil". Abort.
Check @prosa.util.bigcat.seq_different_elements_nil.
Goal True. idtac "END|prosa.util.bigcat.seq_different_elements_nil". Abort.
Goal True. idtac "BEGIN|prosa.util.bigcat.bigcat_seq_uniqK". Abort.
Check @prosa.util.bigcat.bigcat_seq_uniqK.
Goal True. idtac "END|prosa.util.bigcat.bigcat_seq_uniqK". Abort.
Goal True. idtac "BEGIN|prosa.util.bigcat.bigcat_partitions". Abort.
Check @prosa.util.bigcat.bigcat_partitions.
Goal True. idtac "END|prosa.util.bigcat.bigcat_partitions". Abort.
Goal True. idtac "BEGIN|prosa.util.bigop.big_pred1_seq". Abort.
Check @prosa.util.bigop.big_pred1_seq.
Goal True. idtac "END|prosa.util.bigop.big_pred1_seq". Abort.
Goal True. idtac "BEGIN|prosa.util.div_mod.eqdivn_leqmodn". Abort.
Check @prosa.util.div_mod.eqdivn_leqmodn.
Goal True. idtac "END|prosa.util.div_mod.eqdivn_leqmodn". Abort.
Goal True. idtac "BEGIN|prosa.util.div_mod.ltdivn_dvdn". Abort.
Check @prosa.util.div_mod.ltdivn_dvdn.
Goal True. idtac "END|prosa.util.div_mod.ltdivn_dvdn". Abort.
Goal True. idtac "BEGIN|prosa.util.div_mod.addn1_modn_commute". Abort.
Check @prosa.util.div_mod.addn1_modn_commute.
Goal True. idtac "END|prosa.util.div_mod.addn1_modn_commute". Abort.
Goal True. idtac "BEGIN|prosa.util.div_mod.addmod_le_mod". Abort.
Check @prosa.util.div_mod.addmod_le_mod.
Goal True. idtac "END|prosa.util.div_mod.addmod_le_mod". Abort.
Goal True. idtac "BEGIN|prosa.util.div_mod.divn_leq". Abort.
Check @prosa.util.div_mod.divn_leq.
Goal True. idtac "END|prosa.util.div_mod.divn_leq". Abort.
Goal True. idtac "BEGIN|prosa.util.div_mod.div_floor". Abort.
Check @prosa.util.div_mod.div_floor.
Goal True. idtac "END|prosa.util.div_mod.div_floor". Abort.
Goal True. idtac "BEGIN|prosa.util.div_mod.div_ceil". Abort.
Check @prosa.util.div_mod.div_ceil.
Goal True. idtac "END|prosa.util.div_mod.div_ceil". Abort.
Goal True. idtac "BEGIN|prosa.util.div_mod.div_ceil0". Abort.
Check @prosa.util.div_mod.div_ceil0.
Goal True. idtac "END|prosa.util.div_mod.div_ceil0". Abort.
Goal True. idtac "BEGIN|prosa.util.div_mod.div_ceil_gt0". Abort.
Check @prosa.util.div_mod.div_ceil_gt0.
Goal True. idtac "END|prosa.util.div_mod.div_ceil_gt0". Abort.
Goal True. idtac "BEGIN|prosa.util.div_mod.div_ceil_monotone1". Abort.
Check @prosa.util.div_mod.div_ceil_monotone1.
Goal True. idtac "END|prosa.util.div_mod.div_ceil_monotone1". Abort.
Goal True. idtac "BEGIN|prosa.util.div_mod.leq_div_ceil_add1". Abort.
Check @prosa.util.div_mod.leq_div_ceil_add1.
Goal True. idtac "END|prosa.util.div_mod.leq_div_ceil_add1". Abort.
Goal True. idtac "BEGIN|prosa.util.div_mod.div_ceil_subadditive". Abort.
Check @prosa.util.div_mod.div_ceil_subadditive.
Goal True. idtac "END|prosa.util.div_mod.div_ceil_subadditive". Abort.
Goal True. idtac "BEGIN|prosa.util.div_mod.div_ceil_multiple". Abort.
Check @prosa.util.div_mod.div_ceil_multiple.
Goal True. idtac "END|prosa.util.div_mod.div_ceil_multiple". Abort.
Goal True. idtac "BEGIN|prosa.util.div_mod.div_floor_add_g". Abort.
Check @prosa.util.div_mod.div_floor_add_g.
Goal True. idtac "END|prosa.util.div_mod.div_floor_add_g". Abort.
Goal True. idtac "BEGIN|prosa.util.div_mod.mod_elim". Abort.
Check @prosa.util.div_mod.mod_elim.
Goal True. idtac "END|prosa.util.div_mod.mod_elim". Abort.
Goal True. idtac "BEGIN|prosa.util.fixpoint.find_fixpoint_from". Abort.
Check @prosa.util.fixpoint.find_fixpoint_from.
Goal True. idtac "END|prosa.util.fixpoint.find_fixpoint_from". Abort.
Goal True. idtac "BEGIN|prosa.util.fixpoint.find_fixpoint". Abort.
Check @prosa.util.fixpoint.find_fixpoint.
Goal True. idtac "END|prosa.util.fixpoint.find_fixpoint". Abort.
Goal True. idtac "BEGIN|prosa.util.fixpoint.ffpf_finds_fixpoint". Abort.
Check @prosa.util.fixpoint.ffpf_finds_fixpoint.
Goal True. idtac "END|prosa.util.fixpoint.ffpf_finds_fixpoint". Abort.
Goal True. idtac "BEGIN|prosa.util.fixpoint.ffp_finds_fixpoint". Abort.
Check @prosa.util.fixpoint.ffp_finds_fixpoint.
Goal True. idtac "END|prosa.util.fixpoint.ffp_finds_fixpoint". Abort.
Goal True. idtac "BEGIN|prosa.util.fixpoint.no_fixpoint_skipped". Abort.
Check @prosa.util.fixpoint.no_fixpoint_skipped.
Goal True. idtac "END|prosa.util.fixpoint.no_fixpoint_skipped". Abort.
Goal True. idtac "BEGIN|prosa.util.fixpoint.ffpf_finds_least_fixpoint". Abort.
Check @prosa.util.fixpoint.ffpf_finds_least_fixpoint.
Goal True. idtac "END|prosa.util.fixpoint.ffpf_finds_least_fixpoint". Abort.
Goal True. idtac "BEGIN|prosa.util.fixpoint.ffp_finds_least_fixpoint". Abort.
Check @prosa.util.fixpoint.ffp_finds_least_fixpoint.
Goal True. idtac "END|prosa.util.fixpoint.ffp_finds_least_fixpoint". Abort.
Goal True. idtac "BEGIN|prosa.util.fixpoint.ffpf_finds_positive_fixpoint". Abort.
Check @prosa.util.fixpoint.ffpf_finds_positive_fixpoint.
Goal True. idtac "END|prosa.util.fixpoint.ffpf_finds_positive_fixpoint". Abort.
Goal True. idtac "BEGIN|prosa.util.fixpoint.ffp_finds_positive_fixpoint". Abort.
Check @prosa.util.fixpoint.ffp_finds_positive_fixpoint.
Goal True. idtac "END|prosa.util.fixpoint.ffp_finds_positive_fixpoint". Abort.
Goal True. idtac "BEGIN|prosa.util.fixpoint.ffpf_finds_none". Abort.
Check @prosa.util.fixpoint.ffpf_finds_none.
Goal True. idtac "END|prosa.util.fixpoint.ffpf_finds_none". Abort.
Goal True. idtac "BEGIN|prosa.util.fixpoint.ffp_finds_none". Abort.
Check @prosa.util.fixpoint.ffp_finds_none.
Goal True. idtac "END|prosa.util.fixpoint.ffp_finds_none". Abort.
Goal True. idtac "BEGIN|prosa.util.fixpoint.find_max_fixpoint_of_seq". Abort.
Check @prosa.util.fixpoint.find_max_fixpoint_of_seq.
Goal True. idtac "END|prosa.util.fixpoint.find_max_fixpoint_of_seq". Abort.
Goal True. idtac "BEGIN|prosa.util.fixpoint.fmfs_finds_fixpoint". Abort.
Check @prosa.util.fixpoint.fmfs_finds_fixpoint.
Goal True. idtac "END|prosa.util.fixpoint.fmfs_finds_fixpoint". Abort.
Goal True. idtac "BEGIN|prosa.util.fixpoint.fmfs_is_maximum". Abort.
Check @prosa.util.fixpoint.fmfs_is_maximum.
Goal True. idtac "END|prosa.util.fixpoint.fmfs_is_maximum". Abort.
Goal True. idtac "BEGIN|prosa.util.fixpoint.find_max_fixpoint". Abort.
Check @prosa.util.fixpoint.find_max_fixpoint.
Goal True. idtac "END|prosa.util.fixpoint.find_max_fixpoint". Abort.
Goal True. idtac "BEGIN|prosa.util.fixpoint.fmf_finds_fixpoint". Abort.
Check @prosa.util.fixpoint.fmf_finds_fixpoint.
Goal True. idtac "END|prosa.util.fixpoint.fmf_finds_fixpoint". Abort.
Goal True. idtac "BEGIN|prosa.util.fixpoint.fmf_is_maximum". Abort.
Check @prosa.util.fixpoint.fmf_is_maximum.
Goal True. idtac "END|prosa.util.fixpoint.fmf_is_maximum". Abort.
Goal True. idtac "BEGIN|prosa.util.lcmseq.lcml". Abort.
Check @prosa.util.lcmseq.lcml.
Goal True. idtac "END|prosa.util.lcmseq.lcml". Abort.
Goal True. idtac "BEGIN|prosa.util.lcmseq.int_divides_lcm_in_seq". Abort.
Check @prosa.util.lcmseq.int_divides_lcm_in_seq.
Goal True. idtac "END|prosa.util.lcmseq.int_divides_lcm_in_seq". Abort.
Goal True. idtac "BEGIN|prosa.util.lcmseq.lcm_seq_divides_lcm_super". Abort.
Check @prosa.util.lcmseq.lcm_seq_divides_lcm_super.
Goal True. idtac "END|prosa.util.lcmseq.lcm_seq_divides_lcm_super". Abort.
Goal True. idtac "BEGIN|prosa.util.lcmseq.lcm_seq_is_mult_of_all_ints". Abort.
Check @prosa.util.lcmseq.lcm_seq_is_mult_of_all_ints.
Goal True. idtac "END|prosa.util.lcmseq.lcm_seq_is_mult_of_all_ints". Abort.
Goal True. idtac "BEGIN|prosa.util.lcmseq.all_pos_implies_lcml_pos". Abort.
Check @prosa.util.lcmseq.all_pos_implies_lcml_pos.
Goal True. idtac "END|prosa.util.lcmseq.all_pos_implies_lcml_pos". Abort.
Goal True. idtac "BEGIN|prosa.util.list.max0". Abort.
Check @prosa.util.list.max0.
Goal True. idtac "END|prosa.util.list.max0". Abort.
Goal True. idtac "BEGIN|prosa.util.list.first0". Abort.
Check @prosa.util.list.first0.
Goal True. idtac "END|prosa.util.list.first0". Abort.
Goal True. idtac "BEGIN|prosa.util.list.last0". Abort.
Check @prosa.util.list.last0.
Goal True. idtac "END|prosa.util.list.last0". Abort.
Goal True. idtac "BEGIN|prosa.util.list.last0_cons". Abort.
Check @prosa.util.list.last0_cons.
Goal True. idtac "END|prosa.util.list.last0_cons". Abort.
Goal True. idtac "BEGIN|prosa.util.list.last0_cat". Abort.
Check @prosa.util.list.last0_cat.
Goal True. idtac "END|prosa.util.list.last0_cat". Abort.
Goal True. idtac "BEGIN|prosa.util.list.last0_nth". Abort.
Check @prosa.util.list.last0_nth.
Goal True. idtac "END|prosa.util.list.last0_nth". Abort.
Goal True. idtac "BEGIN|prosa.util.list.last0_ex_cat". Abort.
Check @prosa.util.list.last0_ex_cat.
Goal True. idtac "END|prosa.util.list.last0_ex_cat". Abort.
Goal True. idtac "BEGIN|prosa.util.list.last0_filter". Abort.
Check @prosa.util.list.last0_filter.
Goal True. idtac "END|prosa.util.list.last0_filter". Abort.
Goal True. idtac "BEGIN|prosa.util.list.max0_cons". Abort.
Check @prosa.util.list.max0_cons.
Goal True. idtac "END|prosa.util.list.max0_cons". Abort.
Goal True. idtac "BEGIN|prosa.util.list.max0_of_uniform_set". Abort.
Check @prosa.util.list.max0_of_uniform_set.
Goal True. idtac "END|prosa.util.list.max0_of_uniform_set". Abort.
Goal True. idtac "BEGIN|prosa.util.list.in_max0_le". Abort.
Check @prosa.util.list.in_max0_le.
Goal True. idtac "END|prosa.util.list.in_max0_le". Abort.
Goal True. idtac "BEGIN|prosa.util.list.max0_in_seq". Abort.
Check @prosa.util.list.max0_in_seq.
Goal True. idtac "END|prosa.util.list.max0_in_seq". Abort.
Goal True. idtac "BEGIN|prosa.util.list.max0_2cons_eq". Abort.
Check @prosa.util.list.max0_2cons_eq.
Goal True. idtac "END|prosa.util.list.max0_2cons_eq". Abort.
Goal True. idtac "BEGIN|prosa.util.list.max0_2cons_le". Abort.
Check @prosa.util.list.max0_2cons_le.
Goal True. idtac "END|prosa.util.list.max0_2cons_le". Abort.
Goal True. idtac "BEGIN|prosa.util.list.max0_rem0". Abort.
Check @prosa.util.list.max0_rem0.
Goal True. idtac "END|prosa.util.list.max0_rem0". Abort.
Goal True. idtac "BEGIN|prosa.util.list.last_of_seq_le_max_of_seq". Abort.
Check @prosa.util.list.last_of_seq_le_max_of_seq.
Goal True. idtac "END|prosa.util.list.last_of_seq_le_max_of_seq". Abort.
Goal True. idtac "BEGIN|prosa.util.list.max_of_dominating_seq". Abort.
Check @prosa.util.list.max_of_dominating_seq.
Goal True. idtac "END|prosa.util.list.max_of_dominating_seq". Abort.
Goal True. idtac "BEGIN|prosa.util.list.rem_in". Abort.
Check @prosa.util.list.rem_in.
Goal True. idtac "END|prosa.util.list.rem_in". Abort.
Goal True. idtac "BEGIN|prosa.util.list.in_neq_impl_rem_in". Abort.
Check @prosa.util.list.in_neq_impl_rem_in.
Goal True. idtac "END|prosa.util.list.in_neq_impl_rem_in". Abort.
Goal True. idtac "BEGIN|prosa.util.list.filter_size_rem". Abort.
Check @prosa.util.list.filter_size_rem.
Goal True. idtac "END|prosa.util.list.filter_size_rem". Abort.
Goal True. idtac "BEGIN|prosa.util.list.in_seq_equiv_undup". Abort.
Check @prosa.util.list.in_seq_equiv_undup.
Goal True. idtac "END|prosa.util.list.in_seq_equiv_undup". Abort.
Goal True. idtac "BEGIN|prosa.util.list.nth0_cons". Abort.
Check @prosa.util.list.nth0_cons.
Goal True. idtac "END|prosa.util.list.nth0_cons". Abort.
Goal True. idtac "BEGIN|prosa.util.list.seq1_some". Abort.
Check @prosa.util.list.seq1_some.
Goal True. idtac "END|prosa.util.list.seq1_some". Abort.
Goal True. idtac "BEGIN|prosa.util.list.seq_elim_last". Abort.
Check @prosa.util.list.seq_elim_last.
Goal True. idtac "END|prosa.util.list.seq_elim_last". Abort.
Goal True. idtac "BEGIN|prosa.util.list.in_cat". Abort.
Check @prosa.util.list.in_cat.
Goal True. idtac "END|prosa.util.list.in_cat". Abort.
Goal True. idtac "BEGIN|prosa.util.list.subseq_leq_size". Abort.
Check @prosa.util.list.subseq_leq_size.
Goal True. idtac "END|prosa.util.list.subseq_leq_size". Abort.
Goal True. idtac "BEGIN|prosa.util.list.in_zip". Abort.
Check @prosa.util.list.in_zip.
Goal True. idtac "END|prosa.util.list.in_zip". Abort.
Goal True. idtac "BEGIN|prosa.util.list.filter_in_pred0". Abort.
Check @prosa.util.list.filter_in_pred0.
Goal True. idtac "END|prosa.util.list.filter_in_pred0". Abort.
Goal True. idtac "BEGIN|prosa.util.list.eq_ind_in_seq". Abort.
Check @prosa.util.list.eq_ind_in_seq.
Goal True. idtac "END|prosa.util.list.eq_ind_in_seq". Abort.
Goal True. idtac "BEGIN|prosa.util.list.default_or_in". Abort.
Check @prosa.util.list.default_or_in.
Goal True. idtac "END|prosa.util.list.default_or_in". Abort.
Goal True. idtac "BEGIN|prosa.util.list.exists_two". Abort.
Check @prosa.util.list.exists_two.
Goal True. idtac "END|prosa.util.list.exists_two". Abort.
Goal True. idtac "BEGIN|prosa.util.list.has_all_nilp". Abort.
Check @prosa.util.list.has_all_nilp.
Goal True. idtac "END|prosa.util.list.has_all_nilp". Abort.
Goal True. idtac "BEGIN|prosa.util.list.sorted_split". Abort.
Check @prosa.util.list.sorted_split.
Goal True. idtac "END|prosa.util.list.sorted_split". Abort.
Goal True. idtac "BEGIN|prosa.util.list.sorted_cat". Abort.
Check @prosa.util.list.sorted_cat.
Goal True. idtac "END|prosa.util.list.sorted_cat". Abort.
Goal True. idtac "BEGIN|prosa.util.list.nonnil_last". Abort.
Check @prosa.util.list.nonnil_last.
Goal True. idtac "END|prosa.util.list.nonnil_last". Abort.
Goal True. idtac "BEGIN|prosa.util.list.filter_last_mem". Abort.
Check @prosa.util.list.filter_last_mem.
Goal True. idtac "END|prosa.util.list.filter_last_mem". Abort.
Goal True. idtac "BEGIN|prosa.util.list.rem_all". Abort.
Check @prosa.util.list.rem_all.
Goal True. idtac "END|prosa.util.list.rem_all". Abort.
Goal True. idtac "BEGIN|prosa.util.list.nin_rem_all". Abort.
Check @prosa.util.list.nin_rem_all.
Goal True. idtac "END|prosa.util.list.nin_rem_all". Abort.
Goal True. idtac "BEGIN|prosa.util.list.in_rem_all". Abort.
Check @prosa.util.list.in_rem_all.
Goal True. idtac "END|prosa.util.list.in_rem_all". Abort.
Goal True. idtac "BEGIN|prosa.util.list.rem_lt_id". Abort.
Check @prosa.util.list.rem_lt_id.
Goal True. idtac "END|prosa.util.list.rem_lt_id". Abort.
Goal True. idtac "BEGIN|prosa.util.list.range". Abort.
Check @prosa.util.list.range.
Goal True. idtac "END|prosa.util.list.range". Abort.
Goal True. idtac "BEGIN|prosa.util.list.iotaD_impl". Abort.
Check @prosa.util.list.iotaD_impl.
Goal True. idtac "END|prosa.util.list.iotaD_impl". Abort.
Goal True. idtac "BEGIN|prosa.util.list.index_iota_lt_step". Abort.
Check @prosa.util.list.index_iota_lt_step.
Goal True. idtac "END|prosa.util.list.index_iota_lt_step". Abort.
Goal True. idtac "BEGIN|prosa.util.list.index_iota_cat". Abort.
Check @prosa.util.list.index_iota_cat.
Goal True. idtac "END|prosa.util.list.index_iota_cat". Abort.
Goal True. idtac "BEGIN|prosa.util.list.range_filter_2cons". Abort.
Check @prosa.util.list.range_filter_2cons.
Goal True. idtac "END|prosa.util.list.range_filter_2cons". Abort.
Goal True. idtac "BEGIN|prosa.util.list.index_iota_filter_eqx". Abort.
Check @prosa.util.list.index_iota_filter_eqx.
Goal True. idtac "END|prosa.util.list.index_iota_filter_eqx". Abort.
Goal True. idtac "BEGIN|prosa.util.list.index_iota_filter_singl". Abort.
Check @prosa.util.list.index_iota_filter_singl.
Goal True. idtac "END|prosa.util.list.index_iota_filter_singl". Abort.
Goal True. idtac "BEGIN|prosa.util.list.index_iota_filter_inxs". Abort.
Check @prosa.util.list.index_iota_filter_inxs.
Goal True. idtac "END|prosa.util.list.index_iota_filter_inxs". Abort.
Goal True. idtac "BEGIN|prosa.util.list.index_iota_filter_step". Abort.
Check @prosa.util.list.index_iota_filter_step.
Goal True. idtac "END|prosa.util.list.index_iota_filter_step". Abort.
Goal True. idtac "BEGIN|prosa.util.list.range_iota_filter_step". Abort.
Check @prosa.util.list.range_iota_filter_step.
Goal True. idtac "END|prosa.util.list.range_iota_filter_step". Abort.
Goal True. idtac "BEGIN|prosa.util.list.iota_filter_gt". Abort.
Check @prosa.util.list.iota_filter_gt.
Goal True. idtac "END|prosa.util.list.iota_filter_gt". Abort.
Goal True. idtac "BEGIN|prosa.util.list.sub_count_seq". Abort.
Check @prosa.util.list.sub_count_seq.
Goal True. idtac "END|prosa.util.list.sub_count_seq". Abort.
Goal True. idtac "BEGIN|prosa.util.list.count_predUI'". Abort.
Check @prosa.util.list.count_predUI'.
Goal True. idtac "END|prosa.util.list.count_predUI'". Abort.
Goal True. idtac "BEGIN|prosa.util.list.prefix_of". Abort.
Check @prosa.util.list.prefix_of.
Goal True. idtac "END|prosa.util.list.prefix_of". Abort.
Goal True. idtac "BEGIN|prosa.util.list.strict_prefix_of". Abort.
Check @prosa.util.list.strict_prefix_of.
Goal True. idtac "END|prosa.util.list.strict_prefix_of". Abort.
Goal True. idtac "BEGIN|prosa.util.list.shift_points_pos". Abort.
Check @prosa.util.list.shift_points_pos.
Goal True. idtac "END|prosa.util.list.shift_points_pos". Abort.
Goal True. idtac "BEGIN|prosa.util.list.shift_points_neg". Abort.
Check @prosa.util.list.shift_points_neg.
Goal True. idtac "END|prosa.util.list.shift_points_neg". Abort.
Goal True. idtac "BEGIN|prosa.util.minmax.leq_bigmax_cond_seq". Abort.
Check @prosa.util.minmax.leq_bigmax_cond_seq.
Goal True. idtac "END|prosa.util.minmax.leq_bigmax_cond_seq". Abort.
Goal True. idtac "BEGIN|prosa.util.minmax.leq_bigmax_sup". Abort.
Check @prosa.util.minmax.leq_bigmax_sup.
Goal True. idtac "END|prosa.util.minmax.leq_bigmax_sup". Abort.
Goal True. idtac "BEGIN|prosa.util.minmax.bigmax_leq_seqP". Abort.
Check @prosa.util.minmax.bigmax_leq_seqP.
Goal True. idtac "END|prosa.util.minmax.bigmax_leq_seqP". Abort.
Goal True. idtac "BEGIN|prosa.util.minmax.leq_big_max". Abort.
Check @prosa.util.minmax.leq_big_max.
Goal True. idtac "END|prosa.util.minmax.leq_big_max". Abort.
Goal True. idtac "BEGIN|prosa.util.minmax.bigmax_ord_ltn_identity". Abort.
Check @prosa.util.minmax.bigmax_ord_ltn_identity.
Goal True. idtac "END|prosa.util.minmax.bigmax_ord_ltn_identity". Abort.
Goal True. idtac "BEGIN|prosa.util.minmax.bigmax_ltn_ord". Abort.
Check @prosa.util.minmax.bigmax_ltn_ord.
Goal True. idtac "END|prosa.util.minmax.bigmax_ltn_ord". Abort.
Goal True. idtac "BEGIN|prosa.util.minmax.bigmax_pred". Abort.
Check @prosa.util.minmax.bigmax_pred.
Goal True. idtac "END|prosa.util.minmax.bigmax_pred". Abort.
Goal True. idtac "BEGIN|prosa.util.minmax.bigmax_witness". Abort.
Check @prosa.util.minmax.bigmax_witness.
Goal True. idtac "END|prosa.util.minmax.bigmax_witness". Abort.
Goal True. idtac "BEGIN|prosa.util.minmax.bigmax_witness_diff". Abort.
Check @prosa.util.minmax.bigmax_witness_diff.
Goal True. idtac "END|prosa.util.minmax.bigmax_witness_diff". Abort.
Goal True. idtac "BEGIN|prosa.util.minmax.bigmax_subset". Abort.
Check @prosa.util.minmax.bigmax_subset.
Goal True. idtac "END|prosa.util.minmax.bigmax_subset". Abort.
Goal True. idtac "BEGIN|prosa.util.nat.subnACA". Abort.
Check @prosa.util.nat.subnACA.
Goal True. idtac "END|prosa.util.nat.subnACA". Abort.
Goal True. idtac "BEGIN|prosa.util.nat.leq_subRL_impl". Abort.
Check @prosa.util.nat.leq_subRL_impl.
Goal True. idtac "END|prosa.util.nat.leq_subRL_impl". Abort.
Goal True. idtac "BEGIN|prosa.util.nondecreasing.nondecreasing_sequence". Abort.
Check @prosa.util.nondecreasing.nondecreasing_sequence.
Goal True. idtac "END|prosa.util.nondecreasing.nondecreasing_sequence". Abort.
Goal True. idtac "BEGIN|prosa.util.nondecreasing.increasing_sequence". Abort.
Check @prosa.util.nondecreasing.increasing_sequence.
Goal True. idtac "END|prosa.util.nondecreasing.increasing_sequence". Abort.
Goal True. idtac "BEGIN|prosa.util.nondecreasing.distances". Abort.
Check @prosa.util.nondecreasing.distances.
Goal True. idtac "END|prosa.util.nondecreasing.distances". Abort.
Goal True. idtac "BEGIN|prosa.util.nondecreasing.iota_is_increasing_sequence". Abort.
Check @prosa.util.nondecreasing.iota_is_increasing_sequence.
Goal True. idtac "END|prosa.util.nondecreasing.iota_is_increasing_sequence". Abort.
Goal True. idtac "BEGIN|prosa.util.nondecreasing.increasing_implies_nondecreasing". Abort.
Check @prosa.util.nondecreasing.increasing_implies_nondecreasing.
Goal True. idtac "END|prosa.util.nondecreasing.increasing_implies_nondecreasing". Abort.
Goal True. idtac "BEGIN|prosa.util.nondecreasing.nondec_seq_zero_first". Abort.
Check @prosa.util.nondecreasing.nondec_seq_zero_first.
Goal True. idtac "END|prosa.util.nondecreasing.nondec_seq_zero_first". Abort.
Goal True. idtac "BEGIN|prosa.util.nondecreasing.nondecreasing_sequence_2cons_leVeq". Abort.
Check @prosa.util.nondecreasing.nondecreasing_sequence_2cons_leVeq.
Goal True. idtac "END|prosa.util.nondecreasing.nondecreasing_sequence_2cons_leVeq". Abort.
Goal True. idtac "BEGIN|prosa.util.nondecreasing.nondecreasing_sequence_cons". Abort.
Check @prosa.util.nondecreasing.nondecreasing_sequence_cons.
Goal True. idtac "END|prosa.util.nondecreasing.nondecreasing_sequence_cons". Abort.
Goal True. idtac "BEGIN|prosa.util.nondecreasing.nondecreasing_sequence_add_min". Abort.
Check @prosa.util.nondecreasing.nondecreasing_sequence_add_min.
Goal True. idtac "END|prosa.util.nondecreasing.nondecreasing_sequence_add_min". Abort.
Goal True. idtac "BEGIN|prosa.util.nondecreasing.nondecreasing_sequence_cons_double". Abort.
Check @prosa.util.nondecreasing.nondecreasing_sequence_cons_double.
Goal True. idtac "END|prosa.util.nondecreasing.nondecreasing_sequence_cons_double". Abort.
Goal True. idtac "BEGIN|prosa.util.nondecreasing.nondecreasing_sequence_cons_min". Abort.
Check @prosa.util.nondecreasing.nondecreasing_sequence_cons_min.
Goal True. idtac "END|prosa.util.nondecreasing.nondecreasing_sequence_cons_min". Abort.
Goal True. idtac "BEGIN|prosa.util.nondecreasing.nondecreasing_sequence_cons_smin". Abort.
Check @prosa.util.nondecreasing.nondecreasing_sequence_cons_smin.
Goal True. idtac "END|prosa.util.nondecreasing.nondecreasing_sequence_cons_smin". Abort.
Goal True. idtac "BEGIN|prosa.util.nondecreasing.antidensity_of_nondecreasing_seq". Abort.
Check @prosa.util.nondecreasing.antidensity_of_nondecreasing_seq.
Goal True. idtac "END|prosa.util.nondecreasing.antidensity_of_nondecreasing_seq". Abort.
Goal True. idtac "BEGIN|prosa.util.nondecreasing.belonging_to_segment_of_seq_is_total". Abort.
Check @prosa.util.nondecreasing.belonging_to_segment_of_seq_is_total.
Goal True. idtac "END|prosa.util.nondecreasing.belonging_to_segment_of_seq_is_total". Abort.
Goal True. idtac "BEGIN|prosa.util.nondecreasing.last_is_max_in_nondecreasing_seq". Abort.
Check @prosa.util.nondecreasing.last_is_max_in_nondecreasing_seq.
Goal True. idtac "END|prosa.util.nondecreasing.last_is_max_in_nondecreasing_seq". Abort.
Goal True. idtac "BEGIN|prosa.util.nondecreasing.nodup_sort_2cons_eq". Abort.
Check @prosa.util.nondecreasing.nodup_sort_2cons_eq.
Goal True. idtac "END|prosa.util.nondecreasing.nodup_sort_2cons_eq". Abort.
Goal True. idtac "BEGIN|prosa.util.nondecreasing.nodup_sort_2cons_lt". Abort.
Check @prosa.util.nondecreasing.nodup_sort_2cons_lt.
Goal True. idtac "END|prosa.util.nondecreasing.nodup_sort_2cons_lt". Abort.
Goal True. idtac "BEGIN|prosa.util.nondecreasing.last0_undup". Abort.
Check @prosa.util.nondecreasing.last0_undup.
Goal True. idtac "END|prosa.util.nondecreasing.last0_undup". Abort.
Goal True. idtac "BEGIN|prosa.util.nondecreasing.nondecreasing_sequence_undup". Abort.
Check @prosa.util.nondecreasing.nondecreasing_sequence_undup.
Goal True. idtac "END|prosa.util.nondecreasing.nondecreasing_sequence_undup". Abort.
Goal True. idtac "BEGIN|prosa.util.nondecreasing.undup_nth_le". Abort.
Check @prosa.util.nondecreasing.undup_nth_le.
Goal True. idtac "END|prosa.util.nondecreasing.undup_nth_le". Abort.
Goal True. idtac "BEGIN|prosa.util.nondecreasing.distances_unfold_2cons". Abort.
Check @prosa.util.nondecreasing.distances_unfold_2cons.
Goal True. idtac "END|prosa.util.nondecreasing.distances_unfold_2cons". Abort.
Goal True. idtac "BEGIN|prosa.util.nondecreasing.distances_unfold_2app_last". Abort.
Check @prosa.util.nondecreasing.distances_unfold_2app_last.
Goal True. idtac "END|prosa.util.nondecreasing.distances_unfold_2app_last". Abort.
Goal True. idtac "BEGIN|prosa.util.nondecreasing.distances_unfold_1app_last". Abort.
Check @prosa.util.nondecreasing.distances_unfold_1app_last.
Goal True. idtac "END|prosa.util.nondecreasing.distances_unfold_1app_last". Abort.
Goal True. idtac "BEGIN|prosa.util.nondecreasing.distance_between_neighboring_elements_le_max_distance_in_seq". Abort.
Check @prosa.util.nondecreasing.distance_between_neighboring_elements_le_max_distance_in_seq.
Goal True. idtac "END|prosa.util.nondecreasing.distance_between_neighboring_elements_le_max_distance_in_seq". Abort.
Goal True. idtac "BEGIN|prosa.util.nondecreasing.function_of_distances_is_correct". Abort.
Check @prosa.util.nondecreasing.function_of_distances_is_correct.
Goal True. idtac "END|prosa.util.nondecreasing.function_of_distances_is_correct". Abort.
Goal True. idtac "BEGIN|prosa.util.nondecreasing.size_of_seq_of_distances". Abort.
Check @prosa.util.nondecreasing.size_of_seq_of_distances.
Goal True. idtac "END|prosa.util.nondecreasing.size_of_seq_of_distances". Abort.
Goal True. idtac "BEGIN|prosa.util.nondecreasing.distances_of_iota_ε". Abort.
Check @prosa.util.nondecreasing.distances_of_iota_ε.
Goal True. idtac "END|prosa.util.nondecreasing.distances_of_iota_ε". Abort.
Goal True. idtac "BEGIN|prosa.util.nondecreasing.max_distance_in_nontrivial_seq_is_positive". Abort.
Check @prosa.util.nondecreasing.max_distance_in_nontrivial_seq_is_positive.
Goal True. idtac "END|prosa.util.nondecreasing.max_distance_in_nontrivial_seq_is_positive". Abort.
Goal True. idtac "BEGIN|prosa.util.nondecreasing.last_seq_minus_last_distance_seq". Abort.
Check @prosa.util.nondecreasing.last_seq_minus_last_distance_seq.
Goal True. idtac "END|prosa.util.nondecreasing.last_seq_minus_last_distance_seq". Abort.
Goal True. idtac "BEGIN|prosa.util.nondecreasing.max_distance_in_seq_le_last_element_of_seq". Abort.
Check @prosa.util.nondecreasing.max_distance_in_seq_le_last_element_of_seq.
Goal True. idtac "END|prosa.util.nondecreasing.max_distance_in_seq_le_last_element_of_seq". Abort.
Goal True. idtac "BEGIN|prosa.util.nondecreasing.distances_iota_filtered". Abort.
Check @prosa.util.nondecreasing.distances_iota_filtered.
Goal True. idtac "END|prosa.util.nondecreasing.distances_iota_filtered". Abort.
Goal True. idtac "BEGIN|prosa.util.nondecreasing.distances_positive_undup". Abort.
Check @prosa.util.nondecreasing.distances_positive_undup.
Goal True. idtac "END|prosa.util.nondecreasing.distances_positive_undup". Abort.
Goal True. idtac "BEGIN|prosa.util.nondecreasing.domination_of_distances_implies_domination_of_seq". Abort.
Check @prosa.util.nondecreasing.domination_of_distances_implies_domination_of_seq.
Goal True. idtac "END|prosa.util.nondecreasing.domination_of_distances_implies_domination_of_seq". Abort.
Goal True. idtac "BEGIN|prosa.util.notation.constant". Abort.
Check @prosa.util.notation.constant.
Goal True. idtac "END|prosa.util.notation.constant". Abort.
Goal True. idtac "BEGIN|prosa.util.poet.forall_exists_implied_by_forall_in_zip". Abort.
Check @prosa.util.poet.forall_exists_implied_by_forall_in_zip.
Goal True. idtac "END|prosa.util.poet.forall_exists_implied_by_forall_in_zip". Abort.
Goal True. idtac "BEGIN|prosa.util.rel.monotone". Abort.
Check @prosa.util.rel.monotone.
Goal True. idtac "END|prosa.util.rel.monotone". Abort.
Goal True. idtac "BEGIN|prosa.util.rel.total_over_list". Abort.
Check @prosa.util.rel.total_over_list.
Goal True. idtac "END|prosa.util.rel.total_over_list". Abort.
Goal True. idtac "BEGIN|prosa.util.rel.antisymmetric_over_list". Abort.
Check @prosa.util.rel.antisymmetric_over_list.
Goal True. idtac "END|prosa.util.rel.antisymmetric_over_list". Abort.
Goal True. idtac "BEGIN|prosa.util.search_arg.earliest_pred_element_exists_case". Abort.
Check @prosa.util.search_arg.earliest_pred_element_exists_case.
Goal True. idtac "END|prosa.util.search_arg.earliest_pred_element_exists_case". Abort.
Goal True. idtac "BEGIN|prosa.util.search_arg.search_arg". Abort.
Check @prosa.util.search_arg.search_arg.
Goal True. idtac "END|prosa.util.search_arg.search_arg". Abort.
Goal True. idtac "BEGIN|prosa.util.search_arg.search_arg_none". Abort.
Check @prosa.util.search_arg.search_arg_none.
Goal True. idtac "END|prosa.util.search_arg.search_arg_none". Abort.
Goal True. idtac "BEGIN|prosa.util.search_arg.search_arg_not_none". Abort.
Check @prosa.util.search_arg.search_arg_not_none.
Goal True. idtac "END|prosa.util.search_arg.search_arg_not_none". Abort.
Goal True. idtac "BEGIN|prosa.util.search_arg.search_arg_pred". Abort.
Check @prosa.util.search_arg.search_arg_pred.
Goal True. idtac "END|prosa.util.search_arg.search_arg_pred". Abort.
Goal True. idtac "BEGIN|prosa.util.search_arg.search_arg_in_range". Abort.
Check @prosa.util.search_arg.search_arg_in_range.
Goal True. idtac "END|prosa.util.search_arg.search_arg_in_range". Abort.
Goal True. idtac "BEGIN|prosa.util.search_arg.search_arg_extremum". Abort.
Check @prosa.util.search_arg.search_arg_extremum.
Goal True. idtac "END|prosa.util.search_arg.search_arg_extremum". Abort.
Goal True. idtac "BEGIN|prosa.util.search_arg.prop_on_ex_minn". Abort.
Check @prosa.util.search_arg.prop_on_ex_minn.
Goal True. idtac "END|prosa.util.search_arg.prop_on_ex_minn". Abort.
Goal True. idtac "BEGIN|prosa.util.seqset.set". Abort.
Check @prosa.util.seqset.set.
Goal True. idtac "END|prosa.util.seqset.set". Abort.
Goal True. idtac "BEGIN|prosa.util.seqset.set_of". Abort.
Check @prosa.util.seqset.set_of.
Goal True. idtac "END|prosa.util.seqset.set_of". Abort.
Goal True. idtac "BEGIN|prosa.util.seqset.set_uniq". Abort.
Check @prosa.util.seqset.set_uniq.
Goal True. idtac "END|prosa.util.seqset.set_uniq". Abort.
Goal True. idtac "BEGIN|prosa.util.setoid.leb". Abort.
Check @prosa.util.setoid.leb.
Goal True. idtac "END|prosa.util.setoid.leb". Abort.
Goal True. idtac "BEGIN|prosa.util.setoid.leb_eq". Abort.
Check @prosa.util.setoid.leb_eq.
Goal True. idtac "END|prosa.util.setoid.leb_eq". Abort.
Goal True. idtac "BEGIN|prosa.util.setoid.leqRW". Abort.
Check @prosa.util.setoid.leqRW.
Goal True. idtac "END|prosa.util.setoid.leqRW". Abort.
Goal True. idtac "BEGIN|prosa.util.subadditivity.subadditive_at". Abort.
Check @prosa.util.subadditivity.subadditive_at.
Goal True. idtac "END|prosa.util.subadditivity.subadditive_at". Abort.
Goal True. idtac "BEGIN|prosa.util.subadditivity.subadditive_until". Abort.
Check @prosa.util.subadditivity.subadditive_until.
Goal True. idtac "END|prosa.util.subadditivity.subadditive_until". Abort.
Goal True. idtac "BEGIN|prosa.util.subadditivity.subadditive". Abort.
Check @prosa.util.subadditivity.subadditive.
Goal True. idtac "END|prosa.util.subadditivity.subadditive". Abort.
Goal True. idtac "BEGIN|prosa.util.subadditivity.subadditive_standard". Abort.
Check @prosa.util.subadditivity.subadditive_standard.
Goal True. idtac "END|prosa.util.subadditivity.subadditive_standard". Abort.
Goal True. idtac "BEGIN|prosa.util.subadditivity.subadditive_standard_equivalence". Abort.
Check @prosa.util.subadditivity.subadditive_standard_equivalence.
Goal True. idtac "END|prosa.util.subadditivity.subadditive_standard_equivalence". Abort.
Goal True. idtac "BEGIN|prosa.util.subadditivity.subadditive_leq_mul". Abort.
Check @prosa.util.subadditivity.subadditive_leq_mul.
Goal True. idtac "END|prosa.util.subadditivity.subadditive_leq_mul". Abort.
Goal True. idtac "BEGIN|prosa.util.sum.sum_nat_eq0_nat". Abort.
Check @prosa.util.sum.sum_nat_eq0_nat.
Goal True. idtac "END|prosa.util.sum.sum_nat_eq0_nat". Abort.
Goal True. idtac "BEGIN|prosa.util.sum.sum_nat_gt0". Abort.
Check @prosa.util.sum.sum_nat_gt0.
Goal True. idtac "END|prosa.util.sum.sum_nat_gt0". Abort.
Goal True. idtac "BEGIN|prosa.util.sum.sum_majorant_constant". Abort.
Check @prosa.util.sum.sum_majorant_constant.
Goal True. idtac "END|prosa.util.sum.sum_majorant_constant". Abort.
Goal True. idtac "BEGIN|prosa.util.sum.sum_split_exhaustive_mutually_exclusive_preds". Abort.
Check @prosa.util.sum.sum_split_exhaustive_mutually_exclusive_preds.
Goal True. idtac "END|prosa.util.sum.sum_split_exhaustive_mutually_exclusive_preds". Abort.
Goal True. idtac "BEGIN|prosa.util.sum.bigmax_leq_sum". Abort.
Check @prosa.util.sum.bigmax_leq_sum.
Goal True. idtac "END|prosa.util.sum.bigmax_leq_sum". Abort.
Goal True. idtac "BEGIN|prosa.util.sum.sum_le_subseq". Abort.
Check @prosa.util.sum.sum_le_subseq.
Goal True. idtac "END|prosa.util.sum.sum_le_subseq". Abort.
Goal True. idtac "BEGIN|prosa.util.sum.leq_sum_seq". Abort.
Check @prosa.util.sum.leq_sum_seq.
Goal True. idtac "END|prosa.util.sum.leq_sum_seq". Abort.
Goal True. idtac "BEGIN|prosa.util.sum.eq_sum_seq". Abort.
Check @prosa.util.sum.eq_sum_seq.
Goal True. idtac "END|prosa.util.sum.eq_sum_seq". Abort.
Goal True. idtac "BEGIN|prosa.util.sum.leq_sum_seq_pred". Abort.
Check @prosa.util.sum.leq_sum_seq_pred.
Goal True. idtac "END|prosa.util.sum.leq_sum_seq_pred". Abort.
Goal True. idtac "BEGIN|prosa.util.sum.leq_sum_subseq". Abort.
Check @prosa.util.sum.leq_sum_subseq.
Goal True. idtac "END|prosa.util.sum.leq_sum_subseq". Abort.
Goal True. idtac "BEGIN|prosa.util.sum.leq_sum_sub_uniq". Abort.
Check @prosa.util.sum.leq_sum_sub_uniq.
Goal True. idtac "END|prosa.util.sum.leq_sum_sub_uniq". Abort.
Goal True. idtac "BEGIN|prosa.util.sum.ltn_sum_leq_seq". Abort.
Check @prosa.util.sum.ltn_sum_leq_seq.
Goal True. idtac "END|prosa.util.sum.ltn_sum_leq_seq". Abort.
Goal True. idtac "BEGIN|prosa.util.sum.eq_sum_leq_seq". Abort.
Check @prosa.util.sum.eq_sum_leq_seq.
Goal True. idtac "END|prosa.util.sum.eq_sum_leq_seq". Abort.
Goal True. idtac "BEGIN|prosa.util.sum.sum_of_ones". Abort.
Check @prosa.util.sum.sum_of_ones.
Goal True. idtac "END|prosa.util.sum.sum_of_ones". Abort.
Goal True. idtac "BEGIN|prosa.util.sum.big_nat_eq0". Abort.
Check @prosa.util.sum.big_nat_eq0.
Goal True. idtac "END|prosa.util.sum.big_nat_eq0". Abort.
Goal True. idtac "BEGIN|prosa.util.sum.sum_le_summation_range". Abort.
Check @prosa.util.sum.sum_le_summation_range.
Goal True. idtac "END|prosa.util.sum.sum_le_summation_range". Abort.
Goal True. idtac "BEGIN|prosa.util.sum.big_sum_eq_in_eq_sized_intervals". Abort.
Check @prosa.util.sum.big_sum_eq_in_eq_sized_intervals.
Goal True. idtac "END|prosa.util.sum.big_sum_eq_in_eq_sized_intervals". Abort.
Goal True. idtac "BEGIN|prosa.util.sum.sum_over_partitions_le". Abort.
Check @prosa.util.sum.sum_over_partitions_le.
Goal True. idtac "END|prosa.util.sum.sum_over_partitions_le". Abort.
Goal True. idtac "BEGIN|prosa.util.sum.reorder_summation". Abort.
Check @prosa.util.sum.reorder_summation.
Goal True. idtac "END|prosa.util.sum.reorder_summation". Abort.
Goal True. idtac "BEGIN|prosa.util.sum.sum_over_partitions_eq". Abort.
Check @prosa.util.sum.sum_over_partitions_eq.
Goal True. idtac "END|prosa.util.sum.sum_over_partitions_eq". Abort.
Goal True. idtac "BEGIN|prosa.util.sum.sum_leq_mono". Abort.
Check @prosa.util.sum.sum_leq_mono.
Goal True. idtac "END|prosa.util.sum.sum_leq_mono". Abort.
Goal True. idtac "BEGIN|prosa.util.sum.sum_unit1". Abort.
Check @prosa.util.sum.sum_unit1.
Goal True. idtac "END|prosa.util.sum.sum_unit1". Abort.
Goal True. idtac "BEGIN|prosa.util.sum.pigeonhole_on_interval". Abort.
Check @prosa.util.sum.pigeonhole_on_interval.
Goal True. idtac "END|prosa.util.sum.pigeonhole_on_interval". Abort.
Goal True. idtac "BEGIN|prosa.util.sum.sum_ge_2_seq". Abort.
Check @prosa.util.sum.sum_ge_2_seq.
Goal True. idtac "END|prosa.util.sum.sum_ge_2_seq". Abort.
Goal True. idtac "BEGIN|prosa.util.sum.sum_ge_2_nat". Abort.
Check @prosa.util.sum.sum_ge_2_nat.
Goal True. idtac "END|prosa.util.sum.sum_ge_2_nat". Abort.
Goal True. idtac "BEGIN|prosa.util.superadditivity.superadditive_at". Abort.
Check @prosa.util.superadditivity.superadditive_at.
Goal True. idtac "END|prosa.util.superadditivity.superadditive_at". Abort.
Goal True. idtac "BEGIN|prosa.util.superadditivity.superadditive_until". Abort.
Check @prosa.util.superadditivity.superadditive_until.
Goal True. idtac "END|prosa.util.superadditivity.superadditive_until". Abort.
Goal True. idtac "BEGIN|prosa.util.superadditivity.superadditive". Abort.
Check @prosa.util.superadditivity.superadditive.
Goal True. idtac "END|prosa.util.superadditivity.superadditive". Abort.
Goal True. idtac "BEGIN|prosa.util.superadditivity.superadditive_standard". Abort.
Check @prosa.util.superadditivity.superadditive_standard.
Goal True. idtac "END|prosa.util.superadditivity.superadditive_standard". Abort.
Goal True. idtac "BEGIN|prosa.util.superadditivity.superadditive_standard_equivalence". Abort.
Check @prosa.util.superadditivity.superadditive_standard_equivalence.
Goal True. idtac "END|prosa.util.superadditivity.superadditive_standard_equivalence". Abort.
Goal True. idtac "BEGIN|prosa.util.superadditivity.superadditive_first_zero". Abort.
Check @prosa.util.superadditivity.superadditive_first_zero.
Goal True. idtac "END|prosa.util.superadditivity.superadditive_first_zero". Abort.
Goal True. idtac "BEGIN|prosa.util.superadditivity.superadditive_monotone". Abort.
Check @prosa.util.superadditivity.superadditive_monotone.
Goal True. idtac "END|prosa.util.superadditivity.superadditive_monotone". Abort.
Goal True. idtac "BEGIN|prosa.util.superadditivity.superadditive_leq_mul". Abort.
Check @prosa.util.superadditivity.superadditive_leq_mul.
Goal True. idtac "END|prosa.util.superadditivity.superadditive_leq_mul". Abort.
Goal True. idtac "BEGIN|prosa.util.superadditivity.superadditive_unbounded". Abort.
Check @prosa.util.superadditivity.superadditive_unbounded.
Goal True. idtac "END|prosa.util.superadditivity.superadditive_unbounded". Abort.
Goal True. idtac "BEGIN|prosa.util.superadditivity.minimal_superadditive_extension". Abort.
Check @prosa.util.superadditivity.minimal_superadditive_extension.
Goal True. idtac "END|prosa.util.superadditivity.minimal_superadditive_extension". Abort.
Goal True. idtac "BEGIN|prosa.util.superadditivity.minimal_extension_superadditive_at_horizon". Abort.
Check @prosa.util.superadditivity.minimal_extension_superadditive_at_horizon.
Goal True. idtac "END|prosa.util.superadditivity.minimal_extension_superadditive_at_horizon". Abort.
Goal True. idtac "BEGIN|prosa.util.superadditivity.minimal_extension_superadditive_until". Abort.
Check @prosa.util.superadditivity.minimal_extension_superadditive_until.
Goal True. idtac "END|prosa.util.superadditivity.minimal_extension_superadditive_until". Abort.
Goal True. idtac "BEGIN|prosa.util.supremum.choose_superior". Abort.
Check @prosa.util.supremum.choose_superior.
Goal True. idtac "END|prosa.util.supremum.choose_superior". Abort.
Goal True. idtac "BEGIN|prosa.util.supremum.supremum". Abort.
Check @prosa.util.supremum.supremum.
Goal True. idtac "END|prosa.util.supremum.supremum". Abort.
Goal True. idtac "BEGIN|prosa.util.supremum.supremum_unfold". Abort.
Check @prosa.util.supremum.supremum_unfold.
Goal True. idtac "END|prosa.util.supremum.supremum_unfold". Abort.
Goal True. idtac "BEGIN|prosa.util.supremum.supremum_exists". Abort.
Check @prosa.util.supremum.supremum_exists.
Goal True. idtac "END|prosa.util.supremum.supremum_exists". Abort.
Goal True. idtac "BEGIN|prosa.util.supremum.supremum_none". Abort.
Check @prosa.util.supremum.supremum_none.
Goal True. idtac "END|prosa.util.supremum.supremum_none". Abort.
Goal True. idtac "BEGIN|prosa.util.supremum.supremum_in". Abort.
Check @prosa.util.supremum.supremum_in.
Goal True. idtac "END|prosa.util.supremum.supremum_in". Abort.
Goal True. idtac "BEGIN|prosa.util.supremum.supremum_spec". Abort.
Check @prosa.util.supremum.supremum_spec.
Goal True. idtac "END|prosa.util.supremum.supremum_spec". Abort.
Goal True. idtac "BEGIN|prosa.util.tactics.neqP". Abort.
Check @prosa.util.tactics.neqP.
Goal True. idtac "END|prosa.util.tactics.neqP". Abort.
Goal True. idtac "BEGIN|prosa.util.tactics.modusponens". Abort.
Check @prosa.util.tactics.modusponens.
Goal True. idtac "END|prosa.util.tactics.modusponens". Abort.
Goal True. idtac "BEGIN|prosa.util.unit_growth.unit_growth_function". Abort.
Check @prosa.util.unit_growth.unit_growth_function.
Goal True. idtac "END|prosa.util.unit_growth.unit_growth_function". Abort.
Goal True. idtac "BEGIN|prosa.util.unit_growth.unit_growth_function_k_steps_bounded". Abort.
Check @prosa.util.unit_growth.unit_growth_function_k_steps_bounded.
Goal True. idtac "END|prosa.util.unit_growth.unit_growth_function_k_steps_bounded". Abort.
Goal True. idtac "BEGIN|prosa.util.unit_growth.exists_intermediate_point". Abort.
Check @prosa.util.unit_growth.exists_intermediate_point.
Goal True. idtac "END|prosa.util.unit_growth.exists_intermediate_point". Abort.
Goal True. idtac "BEGIN|prosa.util.unit_growth.exists_intermediate_point_leq". Abort.
Check @prosa.util.unit_growth.exists_intermediate_point_leq.
Goal True. idtac "END|prosa.util.unit_growth.exists_intermediate_point_leq". Abort.
Goal True. idtac "BEGIN|prosa.util.unit_growth.exists_first_intermediate_point". Abort.
Check @prosa.util.unit_growth.exists_first_intermediate_point.
Goal True. idtac "END|prosa.util.unit_growth.exists_first_intermediate_point". Abort.
Goal True. idtac "BEGIN|prosa.util.unit_growth.slowed". Abort.
Check @prosa.util.unit_growth.slowed.
Goal True. idtac "END|prosa.util.unit_growth.slowed". Abort.
Goal True. idtac "BEGIN|prosa.util.unit_growth.slowed_respects_pointwise_leq". Abort.
Check @prosa.util.unit_growth.slowed_respects_pointwise_leq.
Goal True. idtac "END|prosa.util.unit_growth.slowed_respects_pointwise_leq". Abort.
Goal True. idtac "BEGIN|prosa.util.unit_growth.slowed_is_unit_step". Abort.
Check @prosa.util.unit_growth.slowed_is_unit_step.
Goal True. idtac "END|prosa.util.unit_growth.slowed_is_unit_step". Abort.
Goal True. idtac "BEGIN|prosa.util.unit_growth.slowed_respects_monotone". Abort.
Check @prosa.util.unit_growth.slowed_respects_monotone.
Goal True. idtac "END|prosa.util.unit_growth.slowed_respects_monotone". Abort.
Goal True. idtac "BEGIN|prosa.util.unit_growth.slowed_never_exceeds". Abort.
Check @prosa.util.unit_growth.slowed_never_exceeds.
Goal True. idtac "END|prosa.util.unit_growth.slowed_never_exceeds". Abort.
Goal True. idtac "BEGIN|prosa.util.unit_growth.bound_preserved_under_slowed". Abort.
Check @prosa.util.unit_growth.bound_preserved_under_slowed.
Goal True. idtac "END|prosa.util.unit_growth.bound_preserved_under_slowed". Abort.
Goal True. idtac "BEGIN|prosa.util.unit_growth.slowed_subtraction_value_preservation". Abort.
Check @prosa.util.unit_growth.slowed_subtraction_value_preservation.
Goal True. idtac "END|prosa.util.unit_growth.slowed_subtraction_value_preservation". Abort.
